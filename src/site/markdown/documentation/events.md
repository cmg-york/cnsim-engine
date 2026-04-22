# Event Ontology

## Overview

CNSim is an event-driven simulator: all changes to the state of the simulated network — transactions arriving, blocks propagating, nodes switching behaviors, samplers being re-seeded, reports being produced — are modeled as discrete `Event` objects that occur at a specific simulated time. A brief architectural recap is given in `overview.md`; this page focuses on the `Event` type hierarchy itself (package `ca.yorku.cmg.cnsim.engine.event`) and on how `Simulation` consumes it.

An `Event` encapsulates *what* happens and *when*. *How* it happens is defined by each subclass's override of `happen(Simulation)`. Nothing else in the simulator advances simulated time: time jumps exactly to the timestamp of whichever `Event` is currently being processed.

## The `Simulation` Main Loop

`Simulation` holds a `PriorityQueue<Event>` ordered by an `EventTimeComparator` (earliest simulated time first). Events are added via `Simulation#schedule(Event)`, and processed by `Simulation#run()`. The loop is short and is the kernel of the whole simulator:

```
while (!queue.isEmpty()) {
    e = queue.poll();
    Simulation.currTime = e.getTime();
    if (Simulation.currTime > terminationTime) break;
    e.happen(this);
}
```

Three things to note:

- **`Simulation.currTime`** is a global, static "now" that advances to each event's timestamp before its `happen(...)` runs. Code executed inside `happen(...)` sees `currTime` equal to the event's own time.
- **Termination.** The loop exits either when the queue drains or when the next event's time would exceed an externally set `terminationTime` (`Simulation#setTerminationTime`).
- **Statistics.** `numEventsScheduled` and `numEventsProcessed` are maintained and surfaced by `Simulation#getStatistics()` at the end of the run.

## The `Event` Base Class

`Event` is a concrete class (not abstract) that subclasses specialize. Its state is minimal:

| Field | Meaning |
| --- | --- |
| `currID` (static) | Monotonic counter used to assign the next event ID. |
| `evtID` | This event's ID, assigned at *processing* time, not construction time. |
| `time` | The simulated time at which the event occurs (non-negative). |
| `ignore` | If true, the event is treated as canceled when processed. |

`Event#getNextEventID()` returns the next global ID; `Event#setTime(long)` / `Event#getTime()` manage the scheduled time; `Event#ignoreEvt()` / `Event#ignoreEvt(boolean)` read and write the ignore flag.

The base `happen(Simulation)` acts as a shared preamble that every subclass is expected to invoke via `super.happen(sim)`. It:

1. Assigns a fresh `evtID` via `getNextEventID()`.
2. If `Reporter.allowsPeriodicReports()` and the current `currID` is a multiple of `reporter.reportingWindow`, loops over all nodes in the simulation and calls `INode#periodicReport()` on each.
3. If `Reporter.allowsTimeAdvancementReports()`, loops over all nodes and calls `INode#timeAdvancementReport()` on each.

This convention — "every subclass calls `super.happen(sim)` first" — is the glue that keeps periodic reporting and time-advancement reporting tied to event processing regardless of which event actually fires. A TODO in `Event.java` notes the intent to formalize this with the Template Method pattern.

## The Event Hierarchy

The concrete subclasses fall naturally into three groups: **domain events** that drive protocol logic, **control events** that change the simulated world mid-run, and **reporting events** that produce output rather than state changes.

| Class | Group | What it does |
| --- | --- | --- |
| `Event_NewTransactionArrival` | Domain | A client transaction enters the system at a specific node. |
| `Event_TransactionPropagation` | Domain | A transaction arrives at a peer via network propagation. |
| `Event_ContainerArrival` | Domain | A container (e.g. a block) arrives at a peer via network propagation. |
| `Event_ContainerValidation` | Domain | A node completes validation of a container it is working on. |
| `Event_HashPowerChange` | Control | A miner's hash power is updated to a new value. |
| `Event_BehaviorChange` | Control | A node swaps to a different behavior strategy. |
| `Event_SeedUpdate` | Control | A multi-sowable sampler is re-seeded. |
| `Event_Report_NodeStatusReport` | Reporting | All nodes produce a status report. |
| `Event_Report_StructureReport` | Reporting | All nodes produce a ledger-structure report. |
| `Event_Report_BeliefReport` | Reporting | All nodes produce a belief report over a sample of transactions. |

### Domain Events

These events carry the simulated protocol forward. Each one holds the domain payload it delivers (a `Transaction`, an `ITxContainer`), the `INode` it is delivered to, and the time of occurrence; its `happen(Simulation)` forwards to the receiving node's `event_[X]` hook.

- **`Event_NewTransactionArrival`** — the entry point for client workload. Its `happen(...)` calls `INode#event_NodeReceivesClientTransaction(Transaction, long)`, logs the event via `Reporter.addEvent(...)` (guarded by `Reporter.reportsEvents()` and `Reporter.reportsNewTransactionArrivalEvents()`), records the transaction itself via `Reporter.addTx(...)` when `Reporter.reportsTransactions()` is on (consulting the `TxConflictRegistry` and `TxDependencyRegistry` for conflict and dependency annotations), advances `ProgressBar`, and — if the transaction is marked as seed-changing by the workload — calls `sim.getSampler().getNodeSampler().updateSeed()`. This last hook is what supports the finality-oriented re-seeding scheme described in `overview.md`.
- **`Event_TransactionPropagation`** — a transaction travels from one peer to another, not from a client. Its `happen(...)` calls `INode#event_NodeReceivesPropagatedTransaction(Transaction, long)` and logs via `Reporter.addEvent(...)` when `Reporter.reportsTransactionPropagationEvents()` is on.
- **`Event_ContainerArrival`** — a validated container (typically a block) reaches a node. Its `happen(...)` calls `INode#event_NodeReceivesPropagatedContainer(ITxContainer)` and, when `Reporter.reportsContainerArrivalEvents()` is on, emits an event log entry that includes the container's contained transaction IDs.
- **`Event_ContainerValidation`** — a node finishes validating its current container. Unlike the propagation/arrival events, this one is the canonical user of the `ignore` flag: if `ignoreEvt()` is true, the node's `event_NodeCompletesValidation(...)` is *not* called, and the event is logged with the type name suffixed by `_Abandoned`. This is how a consensus implementation cancels an in-flight validation when a competing block arrives first.

### Control Events

Control events modify the state of the simulator itself (not the ledger) at a pre-scheduled time. They are how dynamic scenarios — upgrades, attacks, finality re-seeding — are modeled.

- **`Event_HashPowerChange`** — retargets a miner's hash power. The constructor verifies the target node implements `IMiner` and rejects negative values; `happen(...)` calls `IMiner#setHashPower(float)` and logs the event (when `Reporter.reportsEvents()` is on). The previous value is captured at construction time and is available via `getOldHashPower()`.
- **`Event_BehaviorChange`** — swaps a node's behavior strategy, the Strategy-pattern companion described in `overview.md`. `happen(...)` calls `INode#setBehavior(String)` and, for nodes that expose a `setBehaviorStrategy(...)` method (via reflection, to avoid a hard dependency on Bitcoin-specific classes), installs the corresponding strategy object. Strategy classes are looked up in a pluggable `behaviorStrategyRegistry`; `Event_BehaviorChange.registerBehaviorStrategy(name, pkg, cls)` lets protocols register custom strategies without editing this class. For malicious behaviors, an optional `targetTransactionID` and an optional `requiredConfirmations` delay are forwarded to the installed strategy via reflection.
- **`Event_SeedUpdate`** — re-seeds an `IMultiSowable` sampler by calling `IMultiSowable#updateSeed()`. This is the mechanism through which the finality-analysis protocol (see `overview.md`) produces the controlled divergence of `|K|` simulation runs from a shared point in time onward.

### Reporting Events

Reporting events are usually pre-scheduled at simulation start-up, and their `happen(...)` iterates the node set and asks each node to produce a report, without changing state. See `reporting.md` for the full picture; the short version:

- **`Event_Report_NodeStatusReport`** — calls `INode#event_NodeStatusReport(long)` on every node.
- **`Event_Report_StructureReport`** — calls `INode#event_PrintStructureReport(long)` on every node.
- **`Event_Report_BeliefReport`** — reads the sample transaction IDs from the `workload.sampleTransaction` configuration property and calls `INode#event_PrintBeliefReport(long[], long)` on every node; also emits a `Reporter.addEvent(...)` entry when belief-event reporting is enabled.

## Scheduling Events

Events enter the queue via `Simulation#schedule(Event)`. The method also updates `latestKnownEventTime` (useful for placing reporting events after the last workload event) and increments the scheduling counter.

A convenience overload, `Simulation#schedule(TransactionWorkload)`, fans a whole workload out into `Event_NewTransactionArrival` events:

- For each `Transaction` in the workload, an `Event_NewTransactionArrival` is created at the transaction's `creationTime`.
- If the transaction's `nodeID` is `-1`, the destination node is chosen by `NodeSet#pickRandomNode()`; otherwise the specific node is resolved via `NodeSet#pickSpecificNode(long)`.

A TODO in `Simulation.java` flags that this workload-fanout logic ought to move into `TransactionWorkload`; the current location is historical.

## Event Ordering

Ordering is delegated to `EventTimeComparator`, which returns `-1` when `e1` is strictly earlier than `e2` and `1` otherwise. Because the comparator collapses "later" and "equal" into the same branch, ties on `time` are resolved by the priority queue's internal structure rather than by insertion order — callers that care about co-timed ordering must therefore encode that explicitly, e.g. by offsetting times or by scheduling follow-up events from inside a `happen(...)` call.

## Ignoring Events

Rather than removing events from the queue (which is O(n) on a binary heap and awkward for events already captured by other references), CNSim lets callers mark an event to be skipped via `Event#ignoreEvt(true)`. The event is still popped and still receives its `evtID`, but subclasses are free to short-circuit their domain logic.

`Event_ContainerValidation` is the canonical example: when a competing block makes a pending validation obsolete, the original validation event is flagged as ignored, and its `happen(...)` logs the entry with the type suffix `_Abandoned` instead of invoking `INode#event_NodeCompletesValidation(...)`. This keeps the event trail informative (abandoned validations still show up in the log) while avoiding incorrect state changes.

## Reporting Integration

Most subclasses log to `Reporter` by calling `Reporter.addEvent(simID, evtID, simTime, sysTime, type, nodeID, objID, notes)` at the end of their `happen(...)`. The call is guarded by both a global flag (`Reporter.reportsEvents()`) and a per-event-type flag (`Reporter.reportsNewTransactionArrivalEvents()`, `Reporter.reportsTransactionPropagationEvents()`, `Reporter.reportsContainerArrivalEvents()`, `Reporter.reportsContainerValidationEvents()`, `Reporter.reportsSeedUpdateEvents()`, `Reporter.reportsBeliefEvents()`). `Event_HashPowerChange` and `Event_BehaviorChange` currently gate only on `Reporter.reportsEvents()`. Reporting event subclasses rely on the node methods they invoke to emit records (for example, `Reporter.addBeliefEntry(...)` inside a node's `beliefReport(...)` implementation).

See `reporting.md` for the standard-report parameters, configuration flags (`reporter.reportEvents`, `reporter.reportingWindow`, `reporter.beliefReportInterval`, and so on), and output file conventions.

## Extending the Hierarchy

Adding a new event type to CNSim is straightforward:

1. Subclass `Event` (directly — it is not abstract).
2. In the constructor, record whatever payload the event carries and call `super.setTime(time)` so the queue can place it correctly.
3. Override `happen(Simulation sim)`. Call `super.happen(sim)` *first* to keep ID assignment and the periodic/time-advancement hooks working. Then dispatch to the appropriate `INode#event_[X](...)` methods or mutate simulator state.
4. If the event should be logged, call `Reporter.addEvent(...)` (or a more specific reporter method) inside the appropriate `Reporter.reports*()` guard.
5. Schedule instances with `sim.schedule(myEvent)` — either from set-up code, from another event's `happen(...)`, or from a node reacting to something else.

When the new event has a "cancelable" flavor (a scheduled action that may become obsolete), the `ignoreEvt` pattern used by `Event_ContainerValidation` is the recommended approach: hold a reference to the scheduled event at the point that knows about obsolescence, call `ignoreEvt(true)` on it, and have `happen(...)` short-circuit accordingly.
