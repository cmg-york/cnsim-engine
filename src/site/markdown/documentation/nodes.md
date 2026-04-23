# Nodes and Behaviors

## Overview

The `ca.yorku.cmg.cnsim.engine.node` package defines the simulator's protocol-neutral abstraction of a participant in the consensus network. A **node** is the object that receives transactions and containers, propagates them, and produces the protocol's local view of the ledger. Protocol-specific logic — how a node reacts to each event — lives *off* the `Node` class, delegated to the event handlers a concrete specialization overrides. A brief architectural recap of how nodes, behaviors, and structures fit together is given in `overview.md`.

The package exposes two interfaces (`INode`, `IMiner`), two abstract classes (`Node`, `PoWNode`), two set/factory types (`NodeSet`, `AbstractNodeFactory`), and one concrete Proof-of-Work variant of the set (`PoWNodeSet`). Concrete node types (`BitcoinNode`, `TangleNode`, `EthereumNode`, …) live in the respective protocol modules and extend the abstractions defined here. Configuration of node sampling and PoW parameters is documented in `configuration.md`; the random sampling itself is described in `samplers.md`.

## The `INode` Interface

`INode` is the protocol-neutral contract every node must satisfy. It is intentionally thin: the engine's main loop only needs to be able to deliver events to a node and ask it for its identity, its ledger view, and its reports. Concretely, the interface groups methods into four bands:

- **Identity and references** — `getID()`, `getStructure()` (the node's `IStructure`, i.e. blockchain, DAG, or whatever the protocol defines), `getAverageConnectedness()`, `setSimulation(Simulation)`.
- **Event handlers** — `event_NodeReceivesClientTransaction(Transaction, long)`, `event_NodeReceivesPropagatedTransaction(Transaction, long)`, `event_NodeReceivesPropagatedContainer(ITxContainer)`, `event_NodeCompletesValidation(ITxContainer, long)`. These are the protocol seam: the `Event_*` classes in `ca.yorku.cmg.cnsim.engine.event` (see `events.md`) invoke the matching `event_*` method on their target node, and the node's concrete type decides what happens next.
- **Report handlers** — `event_PrintPeriodicReport(long)`, `event_PrintBeliefReport(long[], long)`, `event_PrintStructureReport(long)`, `event_NodeStatusReport(long)`, plus the lower-level hooks they forward to (`periodicReport()`, `beliefReport(long[], long)`, `structureReport()`, `nodeStatusReport()`) and the every-event hook `timeAdvancementReport()`. The scheduling of the corresponding events and the `Reporter` contract are covered in `reporting.md`.
- **Lifecycle and labelling** — `close(INode)` for end-of-simulation cleanup, and `setBehavior(String)` / `getBehavior()` for a protocol-defined label (e.g. `"Honest"`, `"Malicious"`) that concrete implementations can use to select a Strategy-style behavior object.

## The `IMiner` Interface

`IMiner extends INode` adds the properties that only make sense for a *mining* node — one that expends computational effort to produce containers. These are:

| Field (getter/setter) | Unit | Meaning |
| --- | --- | --- |
|`hashPower`|GH/s|Hashing rate of the node. The PoW sampler treats the stored value as billions of hashes per second (see `samplers.md`).|
|`electricPower`|Watts|Steady-state power draw of the miner.|
|`electricityCost`|tokens/kWh|Price of electricity in the protocol's native tokens per kilowatt-hour.|
|`totalCycles`|hashes|Cumulative PoW cycles the node has expended — read-only, aggregated over the run.|

`IMiner#getCostPerGH()` is a derived metric: `(electricityCost × electricPower / 1000) / (3600 × hashPower)`, expressed in tokens per billion hashes. The unit chain is spelled out in the Javadoc on `IMiner.java:50-56`.

Non-PoW protocols (e.g., stake-based) are free to skip `IMiner` entirely and extend `Node` directly — the engine never assumes miner-ness at the `INode` seam.

## The `Node` Abstract Class

`Node` is the protocol-neutral implementation of `INode`. It gives concrete subclasses three things: a transaction pool, a network-interface clock, and broadcast helpers. The subclass fills in the event-handling logic.

### State

| Field | Type | Meaning |
| --- | --- | --- |
|`currID` (static)|`int`|Monotonic counter used to mint the next node ID via `Node#getNextNodeID()`; `Node#resetCurrID()` resets it to 1 between experiments.|
|`ID`|`int`|Unique identifier assigned at construction.|
|`sim`|`Simulation`|Back-reference, needed to reach the network, sampler, and event queue.|
|`pool`|`TransactionGroup`|The node's mempool of unvalidated transactions. Added to by `addTransactionToPool(Transaction)`; drained by the various `removeFromPool(...)` overloads.|
|`nextValidationEvent`|`Event_ContainerValidation`|The currently-scheduled validation event for this node, kept here so the node can cancel or replace it.|
|`networkInterfaceBusyUntil`|`long`|Simulation time at which the node's NIC will be free again; `-1` means idle/never-used.|
|`behavior`|`String`|Behavior label (see `setBehavior(String)`).|

### Pool management

`addTransactionToPool(Transaction)` appends to `pool`. Three `removeFromPool(...)` overloads exist — one takes an `ITxContainer` (remove-all of its transactions), one a `Transaction`, one an `int` ID. Each guards against an empty pool so it is safe to call unconditionally.

### Propagation and the network-interface clock

The NIC clock is the non-obvious piece. CNSim models the fact that a node cannot propagate two payloads simultaneously: `Node#getNextTransmissionEndTime(currTime, transDuration)` computes the end time of the next transmission as either `currTime + transDuration` (interface idle) or `networkInterfaceBusyUntil + transDuration` (interface still busy). Every successful schedule call then updates the clock via `setNetworkInterfaceBusyUntil(scheduleTime)`. Both methods carry JML contracts in their Javadoc: non-negative inputs, a monotonicity postcondition on the result, and `assignable \nothing` / `assignable networkInterfaceBusyUntil` clauses — matching the style used elsewhere in the engine and recorded in the contributor's guide.

Two broadcast helpers build on this:

- `broadcastContainer(ITxContainer, long)` loops over every peer in the simulation's `NodeSet`, asks `sim.getNetwork().getTransmissionTime(fromID, toID, txc.getSize())` (see `network.md`), computes `scheduleTime = getNextTransmissionEndTime(time, inter)`, schedules an `Event_ContainerArrival` at that time, and advances the NIC clock. A negative transmission time from `network.md`'s `NOT_CONNECTED = -1` sentinel is *not* checked here — the container version silently forwards the `-1`, which is a known asymmetry with the transaction version below.
- `broadcastTransaction(Transaction, long)` is the same shape but schedules `Event_TransactionPropagation` and *does* reject negative intervals with a descriptive `RuntimeException`. This is the entry point for protocols to gossip a new transaction once they have accepted it into the pool.

### Event-handler skeleton

`Node` marks two event handlers as abstract — `event_NodeCompletesValidation(ITxContainer, long)` and `event_NodeReceivesPropagatedTransaction(Transaction, long)` — because they are the points where protocol semantics necessarily diverge. The remaining handlers have sensible neutral defaults: every `event_Print*Report(...)` handler simply forwards to the corresponding no-event report method (`periodicReport()`, `beliefReport(...)`, `structureReport()`, `nodeStatusReport()`), which is what lets the custom-reporting scheme in `reporting.md` work uniformly across protocols.

### Back-end getters

`getID()`, `getPool()`, `getSim()`, and `setSimulation(Simulation)` are one-liners. `getAverageConnectedness()` is the one composite accessor: it delegates to `sim.getNetwork().getAvgTroughput(getID())`, so the "connectedness" a node reports is actually the average of its incoming+outgoing throughputs across the rest of the network — consistent with the matrix described in `network.md`.

## The `PoWNode` Abstract Class

`PoWNode extends Node implements IMiner`. It is the shared Proof-of-Work scaffolding: hash-power bookkeeping, mining state, validation-event scheduling.

### Mining state

| Field | Type | Meaning |
| --- | --- | --- |
|`hashPower`|`float`|Per-`IMiner`; validated non-negative in `setHashPower(...)`.|
|`electricPower`|`float`|Per-`IMiner`.|
|`electricityCost`|`float`|Per-`IMiner`; validated non-negative in `setElectricityCost(...)`.|
|`totalCycles`|`double`|Running total; incremented by `addCycles(double)`.|
|`prospectiveMiningCycles`|`double`|Cycles provisionally committed to the current mining interval; realized on validation completion.|
|`isMining`|`boolean`|Whether the node is currently mining. Toggled by `startMining(...)` / `stopMining()`.|

### Mining lifecycle

`startMining(double interval)` sets `prospectiveMiningCycles = interval × hashPower` and flips `isMining` on. The no-arg `startMining()` just flips the flag — useful when the prospective count is being managed externally. `stopMining()` clears the flag. `event_NodeCompletesValidation(...)` commits the prospective cycles into `totalCycles` and resets the prospective counter to 0. The Javadoc carries a known-issue TODO about this scheme being inaccurate when validations are cancelled — see `PoWNode.java:269-277`.

### Validation events

Three helpers manage the node's single in-flight validation event:

- `scheduleValidationEvent(ITxContainer, long time)` asks `sim.getSampler().getNodeSampler().getNextMiningInterval(hashPower)` (see `samplers.md`) for a stochastic interval `h`, constructs an `Event_ContainerValidation` at `time + h`, stores it in `nextValidationEvent`, schedules it with the simulation, and returns `h` to the caller.
- `scheduleValidationEvent_Deterministic(ITxContainer, long time)` skips the sampler and schedules at exactly `time`. Useful for tests and for protocols that compute their own interval.
- `resetNextValidationEvent()` and `setNextValidationEvent(Event_ContainerValidation)` let a protocol cancel or replace the in-flight event (for example, when a competing container arrives before the node finishes mining its own).

The PoW event handlers are mostly inherited unchanged. The only non-trivial override is `event_NodeCompletesValidation(...)` for cycle accounting (above); `event_NodeReceivesPropagatedTransaction(...)` is a no-op stub that subclasses override to add the transaction to the pool and react.

## The `AbstractNodeFactory` Class

`AbstractNodeFactory` is the single-method seam between configuration and node construction. It holds references to the `Simulation` and `Sampler` (so concrete factories can draw samples to initialize each new node) and exposes one abstract method:

```java
public abstract INode createNewNode() throws Exception;
```

Every protocol module ships a concrete factory (e.g. `BitcoinNodeFactory`) that uses `sampler.getNodeSampler()` to assign hash power, electric power, and electricity cost to each new node according to the distributions parameterized by the `pow.*` and `node.electric*` keys in `configuration.md`. The factory is what a `NodeSet` calls when `addNode()` fires.

## The `NodeSet` Abstract Class

`NodeSet` owns the `ArrayList<INode> nodes`, a reference to its `AbstractNodeFactory`, and an optional pointer to a single malicious node. It draws the boundary between "maintaining the list" (concrete here) and "creating/closing individual nodes" (abstract — left to the subclass that knows what `INode` specialization is in play).

Concrete-in-this-class behavior:

- `addNodes(int num)` calls `addNode()` that many times; negative `num` raises `ArithmeticException`.
- `pickRandomNode()` samples via `nodeFactory.getSampler().getNodeSampler().getNextRandomNode(nodes.size())` — the same sampler that generates node characteristics, so its seed management (see `samplers.md`) governs which node is picked.
- `pickSpecificNode(int nodeID)` returns `nodes.get(nodeID - 1)`, reflecting the 1-based IDs minted by `Node#getNextNodeID()`.
- `getNodes()`, `getNodeSetCount()`, `getMalicious()`, `setNodeFactory(AbstractNodeFactory)` are the expected one-liners.

Abstract hooks the subclass must supply: `addNode()`, `closeNodes()` (end-of-simulation cleanup and reporting), `debugPrintNodeSet()`, `printNodeSet()` (CSV-per-node for the Nodes output file — see `reporting.md`).

## The `PoWNodeSet` Class

`PoWNodeSet extends NodeSet` is the concrete implementation the engine ships for PoW protocols. Its extra state is a single running sum `totalHashPower` kept in sync as nodes are added.

### Addition

`addNode()` asks the factory for a new `INode`, verifies it implements `IMiner`, adds it to the list, and adds its `getHashPower()` to `totalHashPower`. A non-miner node raises `IllegalStateException` — `PoWNodeSet` refuses to silently hold nodes it cannot aggregate over.

### Close

`closeNodes()` is where the end-of-run reporting handshake happens. For each node it:

1. Calls `n.close(n)` — the node-specific cleanup hook.
2. If `Reporter.reportsNodeEvents()` is on, emits a `Reporter.addNode(simID, nodeID, hashPower, electricPower, electricityCost, totalCycles)` row. This is the same `addNode(...)` call documented in the "New Node Creation" section of `reporting.md`, and it is *why* the modeler must invoke `closeNodes()` at the end of a simulation: per-node hash/cycle data cannot be meaningful until the run is over.
3. If either `Reporter.reportsBeliefs()` or `Reporter.reportsBeliefsShort()` is on, it invokes `n.event_PrintBeliefReport(...)` with the `workload.sampleTransaction` array (parsed via `Config.parseStringToArray(...)` — see `configuration.md`) at `Simulation.currTime`. This produces one final belief snapshot at the end of the run, complementing the periodic ones scheduled by `ReportEventFactory`.

### Aggregation and debug printing

`getTotalHashPower()` exposes the running sum. `debugPrintNodeSet()` returns a human-readable string with ID, hash power, and malicious flag. `printNodeSet()` returns one CSV row per node with `ID, electricPower, hashPower, electricityCost, costPerGH, averageConnectedness, totalCycles` — this is the shape `Reporter` will persist if `reportsNodeEvents()` is on.

Both printers cast each entry to `IMiner` and throw `IllegalStateException` on a non-miner — the same defensive check as in `addNode()`.

## How the Engine Uses the Package

Putting the pieces together, a typical simulation life cycle in a PoW protocol runs as follows:

1. **Setup.** A protocol's `main` class instantiates its concrete `AbstractNodeFactory` with the configured `Simulation` and `Sampler`, wraps it in a `PoWNodeSet`, and calls `nodeSet.addNodes(net.numOfNodes)`. Each node receives its hash power / electric power / electricity cost from the node sampler (see `samplers.md`).
2. **Network binding.** The `NodeSet` is handed to the network via `NetworkFactory.createNetwork(nodeSet, sampler)` (see `network.md`), then to the simulation via `Simulation#setNetwork(...)`.
3. **Workload arrival.** `Event_NewTransactionArrival#happen(...)` invokes the destination node's `event_NodeReceivesClientTransaction(...)`. The protocol's `Node` subclass decides what to do next (validate, propagate, add to the pool) using the inherited helpers — `addTransactionToPool`, `broadcastTransaction`, `scheduleValidationEvent`.
4. **Propagation.** `Event_TransactionPropagation` and `Event_ContainerArrival` events fire `event_NodeReceivesPropagated*` on the receiving node, which mirrors the arrival logic locally.
5. **Validation.** When `Event_ContainerValidation` pops from the queue, `event_NodeCompletesValidation(...)` runs — `PoWNode` commits prospective cycles; the concrete subclass ratifies the container into its `IStructure` and broadcasts it.
6. **Reporting.** Scheduled `Event_Report_*` events and the every-event `timeAdvancementReport()` / periodic `periodicReport()` hooks feed the `Reporter` (see `reporting.md`).
7. **Teardown.** The main class calls `nodeSet.closeNodes()`, which flushes per-node `addNode(...)` rows and a final belief snapshot into the reporter. `Node#resetCurrID()` is invoked between experiments so the next run starts at ID 1.
