# Transactions and Containers

## Overview

The `ca.yorku.cmg.cnsim.engine.transaction` package defines the data primitives that flow through the simulator: individual `Transaction` objects, `ITxContainer` collections of them (blocks, pools, DAG vertices), a `TransactionWorkload` for feeding the simulation, and two registries — `TxConflictRegistry` and `TxDependencyRegistry` — that describe how transactions relate to one another. A brief architectural recap is given in `overview.md`; this page focuses on the types in the package and how the rest of the engine consumes them.

A `Transaction` is the unit of work the protocol is asked to order and confirm. An `ITxContainer` is any grouping of transactions a protocol might need — a mempool, a block, a DAG tip's payload. Workloads are bundles of transactions scheduled to arrive at the system at specific times; registries let a workload express relationships (conflicts, dependencies) that the protocol must then respect.

## The `Transaction` Class

`Transaction` is a plain domain object. Its state is:

| Field | Type | Meaning |
| --- | --- | --- |
|`ID`|`long`|Unique identifier for the transaction.|
|`size`|`float`|Size in bytes.|
|`value`|`float`|Fee/value in the protocol's native currency.|
|`creationTime`|`long`|Simulated time (ms from time 0) at which the transaction is created.|
|`nodeID`|`int`|ID of the node where the transaction first arrives; `-1` if unspecified.|
|`seedChanging`|`boolean`|Whether crossing this transaction should trigger a sampler re-seed.|
|`currID` (static)|`int`|Monotonic counter used to mint the next ID via `Transaction#getNextTxID()`.|

The class offers four constructors: a full one (`ID, time, value, size`), a variant with `nodeID`, an empty one (for use with setters), and an ID-only one. Time/value/size must be non-negative; violations raise `ArithmeticException`.

The static pair `Transaction#getNextTxID()` and `Transaction#resetCurrID()` manage the global ID counter; `resetCurrID()` is intended for moving between experiments (each experiment starts at ID 1).

`Transaction#makeSeedChanging()` marks the transaction as seed-changing; `Transaction#isSeedChanging()` reports the flag. When a seed-changing transaction arrives, `Event\_NewTransactionArrival#happen(Simulation)` calls `sim.getSampler().getNodeSampler().updateSeed()` — the entry point for the finality-analysis re-seeding scheme described in `overview.md`. The transaction sampler's own seed is updated earlier, at workload-creation time, by `TransactionWorkload#addTransaction(long)`.

Setters and getters are one-per-field and straightforward. Most methods carry a JML contract block in their Javadoc and are guarded at runtime by small `\_pre`/`\_post` validator helpers.

## The `ITxContainer` Interface

`ITxContainer` is the abstraction every "bag of transactions" in CNSim implements — blocks, mempools, DAG vertex payloads, and whatever new protocol-specific groupings an extender introduces. It exposes:

* **Identity and summaries** — `getID()`, `getCount()`, `getSize()`, `getValue()`.
* **Access** — `getTransactions()` returns the underlying list.
* **Membership** — `contains(Transaction)` and `contains(long)` test by ID.
* **Mutation** — `addTransaction(Transaction)`, `removeTransaction(Transaction)`, `removeNextTx()` (dequeue-style), and `extractGroup(TransactionGroup)` (set difference).
* **Debug** — `printIDs(String sep)` returns a `{id1,id2,...}` rendering used by the event logger (for example, by `Event\_ContainerArrival` when it records which transactions a block carries).

## `TransactionGroup`: the default container

`TransactionGroup` is the concrete `ITxContainer` provided by the engine. It stores transactions in an `ArrayList<Transaction>` plus a `BitSet contents` index keyed on transaction ID, and caches running totals for `totalSize` and `totalValue`. The BitSet makes membership tests and set operations (`overlapsWith`, `fullyContainsSet`, `extractGroup`) cheap, which matters because containers are queried heavily during validation.

Some things worth knowing:

* **File loading.** `TransactionGroup(String fileName, boolean hasHeader)` parses a CSV of transactions — columns `ID, time, value, size, nodeID`. It enforces that transaction IDs start at 1 and strictly increase by 1, and that `time` does not decrease as IDs increase. This is meant for fixtures and tests; live workloads are produced by samplers (see below).
* **Top-N selection.** `getTopN(sizeLimit, Comparator<Transaction>)` returns a `TransactionGroup` containing the highest-ranked transactions (per the comparator) whose cumulative `size` does not exceed `sizeLimit`. Combined with the size/value/ratio comparators described below, this is the utility a protocol uses to assemble the next candidate block.
* **Dependency-aware queries.** The various `satisfiesDependenciesOf(...)` overloads take a `TxDependencyRegistry` and answer "are all dependencies of this transaction (or set) already present in this group?" — using a thread-local scratch `BitSet` to avoid allocation in hot paths. An `\_Incl\_3rdGroup` variant unions a second group into the "satisfied" set, which is useful when checking a candidate block against the blockchain plus an in-progress mempool.
* **Overlap.** `overlapsWith(TransactionGroup)` is delegated to `overlapsWith\_BitSet(...)` (`contents.intersects(...)`) — the legacy nested-loop implementation is dead code kept behind an always-taken `if (true) return ...` guard.

### Transaction Comparators

Three ready-made `Comparator<Transaction>` implementations live alongside `TransactionGroup`:

| Comparator | Orders by |
| --- | --- |
|`TxSizeComparator`|Size ascending (`1` if `t1.size > t2.size`).|
|`TxValueComparator`|Value ascending.|
|`TxValuePerSizeComparator`|Value-per-size *descending* — best "fee per byte" first (returns `1` when `t1`'s ratio is smaller).|

All three reject `null` inputs with `NullPointerException`. `TxValuePerSizeComparator` treats zero-value transactions as ratio 0 to avoid division by zero. Pass any of them to `TransactionGroup#getTopN(...)` to implement different block-packing policies.

## `TransactionWorkload`: scheduled arrivals

`TransactionWorkload` extends `TransactionGroup` and represents the stream of transactions a simulation will consume. It has two construction paths:

* **Sampler-driven** — `new TransactionWorkload(Sampler)` creates an empty workload tied to a `Sampler`. Subsequent calls to `appendTransactions(long num)` add `num` transactions, each scheduled at the previous `timeEnd` plus `sampler.getTransactionSampler().getNextTransactionArrivalInterval()`. Each transaction's value, size, and arrival-node come from the transaction sampler as well; if the transaction ID matches the sampler's `getSeedChangeTx()` and seed updates are enabled, the transaction is marked seed-changing (`Transaction#makeSeedChanging()`) and the transaction sampler's own seed is updated immediately.
* **File-driven** — `new TransactionWorkload(String fileName, boolean hasHeader)` delegates to `TransactionGroup`'s CSV constructor.

Additional utilities:

* `pickRandomTransactions(int transNo, float percentile)` samples `transNo` transactions uniformly from the first `percentile` fraction of the workload. Used to select the belief-report sample.
* `updateConflicts(TxConflictRegistry, double dispersion, double likelihood)` populates a conflict registry by asking the transaction sampler for a conflict partner for each transaction not yet decided (`getMatch(id) == -2`). Uninitialized partners or invalid targets become "no match"; otherwise the partner must have a *larger* ID (enforced by a runtime check).
* `updateDependencies(TxDependencyRegistry, boolean mandatory, float dispersion, int countMean, float countSD)` asks the transaction sampler to generate a random dependency set for each transaction, then installs it via `TxDependencyRegistry#addDependencies(...)`.

A `Simulation` consumes a workload through `Simulation#schedule(TransactionWorkload)`, which fans each transaction out into an `Event\_NewTransactionArrival` at its `creationTime` — see `events.md` for the event-side of this story.

## Conflict Tracking: `TxConflictRegistry`

Some protocols, e.g., those employing UTXO-style chains need to know that two transactions are in conflict — only one can be confirmed. `TxConflictRegistry` tracks conflicts as an array of pairwise matches over IDs `1..size`, using three sentinel values:

| Value of `match\[i]` | Meaning |
| --- | --- |
|`-2`|Uninitialized — no decision has been made about transaction `i` yet.|
|`-1`|Decided: `i` has no conflict partner.|
|Any `j >= 1`|`i` conflicts with `j` (and symmetrically `match\[j] == i`).|

Key operations:

* `getMatch(id)` returns the current partner (or sentinel), validating that `id` is in range.
* `uninitialized(id)` is sugar for `match\[id] == -2`.
* `setMatch(a, b)` creates a symmetric pair, clearing any previous partners `a` or `b` had. Self-matches (`a == b`) are rejected.
* `noMatch(id)` clears `id`'s match and, if there was a partner, clears the partner's entry too (leaving both at `-1`).
* `neutralize()` resets every entry to `-1` — useful for "no conflicts in this experiment".

`Event\_NewTransactionArrival#happen(Simulation)` consults the conflict registry when logging transactions: the reported conflict partner goes into the transaction log only when `workload.hasConflicts` is set in the configuration.

## Dependency Tracking: `TxDependencyRegistry`

Dependencies capture "transaction `j` cannot be included until all of its dependencies are already included". `TxDependencyRegistry` stores, for each transaction ID `j`, a `BitSet` `deps\[j]` of the transaction IDs it depends on, with the invariant that every `i` in `deps\[j]` satisfies `i < j` (enforced by `addDependency(j, i)`).

Key operations:

* `addDependency(j, i)` sets one bit.
* `addDependencies(id, BitSet)` replaces the entire dependency set for `id`.
* `dependenciesMet(j, satisfiedBits)` returns true iff `deps\[j]` is a subset of `satisfiedBits`. The implementation is `(deps\[j] AND NOT satisfiedBits).isEmpty()` on a clone.
* `dependenciesMetFast(j, satisfiedBits, scratch)` is the same check but reuses a caller-provided scratch `BitSet` — this is the variant `TransactionGroup` calls internally via a `ThreadLocal<BitSet>` so hot paths do not allocate.
* `toBitSet(Collection<Integer>)` and `toBitSet(List<Transaction>)` convert "what has been satisfied" into the `BitSet` shape the lookups expect.
* `toString(int txID)` returns `"-1"` for transactions with no dependencies or a `{i;j;k}` listing otherwise — the format logged by `Event\_NewTransactionArrival` when `workload.hasDependencies` is set.

## How the Engine Uses These Types

Putting it together, a typical run wires the types like this:

1. **Workload construction.** A `Sampler` and a `TransactionWorkload` are created. `appendTransactions(N)` populates the workload with `N` sampler-driven `Transaction` instances, optionally marking one as seed-changing. If the scenario uses conflicts and/or dependencies, `updateConflicts(...)` and `updateDependencies(...)` populate a `TxConflictRegistry` / `TxDependencyRegistry`, which are then attached to the `Simulation` via `Simulation#setConflictRegistry` / `setDependencyRegistry`.
2. **Scheduling.** `Simulation#schedule(TransactionWorkload)` emits one `Event\_NewTransactionArrival` per transaction, routed to `pickRandomNode()` (when `nodeID == -1`) or `pickSpecificNode(nodeID)`.
3. **Arrival.** When an `Event\_NewTransactionArrival` fires, the receiving node's `event\_NodeReceivesClientTransaction(Transaction, long)` runs; if the transaction is seed-changing, the node sampler is re-seeded; the transaction is then (per protocol) placed in the node's `ITxContainer`-flavored mempool.
4. **Propagation.** Peers receive the transaction via `Event\_TransactionPropagation`, which calls `INode#event\_NodeReceivesPropagatedTransaction(Transaction, long)`.
5. **Validation.** When the protocol assembles a candidate container, it typically uses `TransactionGroup#getTopN(sizeLimit, comparator)` — with `TxValuePerSizeComparator` being the canonical "fee market" choice — and checks dependency satisfaction through `TransactionGroup#satisfiesDependenciesOf(...)`. The validated container then propagates via `Event\_ContainerArrival`, which logs its contents with `ITxContainer#printIDs(";")`.
6. **Reporting.** `Event\_NewTransactionArrival` writes to `Reporter.addTx(...)` using the conflict/dependency registries for annotation. See `reporting.md` for the record layout.

See `events.md` for the event-driven half and `reporting.md` for the details of the output files these types contribute to.

## 

