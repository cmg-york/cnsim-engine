# Reporting Mechanism

## Overview

### Architectural Approach

Reporting in CNSim-Engine is handled through the `Reporter` class. The `Reporter` keeps a log of the occurrences of events of different types ("event" here not necessarily equivalently to CNSim `Event` instances). To log an event or other information different parts of the simulator, primarily `Node` objects, call static methods of `Reporter` adding the information to be recorded as parameters to the corresponding call. This marks a reporting action. `Reporter` maintains this information in lists that are saved to the disc once the simulation run ends.

CNSim supports a basic mechanism for reporting basic events (Standard Reporting) as well as a mechanism for triggering custom reports via designated events (Custom Reporting). Standard reporting pertains to events relating to the creation of various objects in the simulation, specifically transactions, nodes, network connections and events in general. These reports are important for reviewing the structure of the network and the workload of transactions after the simulation. However, some or all of them can be switched off for better performance.

Custom reporting is implemented by having simulation objects respond to specified reporting `Event` objects, possibly but not necessarily prescheduled during simulation set-up. Processing of the event (calling of its `happens()` routine) causes the class responsible for responding to it to send reporting information to the Reporter. It is up to the implementor to decide whether the class would offer a report upon requested and what this report will be. Specializations of the `Reporter` class can be utilized for custom reports.

### Formatting and Saving Reports

Currently, event logs are appended as *comma separated* Strings in various arraylists each corresponding to a different kind of event. At the end of the simulation the arraylists are saved to CSV files on the disk following a `flush[Evt Type]` call. A single top-level call `Reporter#flushAll()` drives every built-in flush (and delegates to `Reporter#flushCustomReports()` for user-defined extensions).

#### Output Directory

All log files for a single run land in a per-run directory built at `Reporter` class-load time:

```
<sim.output.directory>/<runId>/
```

The `<sim.output.directory>` prefix comes from the `sim.output.directory` configuration key (falls back to `./log/` if the field is never initialized from config). The `<runId>` is assembled as `<label> - <yyyy.MM.dd HH.mm.ss>`, where `<label>` is:

- The value of `sim.experimentalLabel` when that property is set, or
- Otherwise, the value returned by `Config#getConfigLabel()` (the active config file label).

In addition, a single file `<sim.output.directory>/LatestFileName.txt` is written at the same time; it contains the latest `<runId>` and is intended to help external tooling locate the most recent run directory without having to scan timestamps.

#### File Naming Convention

Inside the run directory, each report category produces its own file:

| Category | Filename | Emitted by |
| --- | --- | --- |
|Event log|`EventLog - <runId>.csv`|`flushEvtReport()`|
|Transaction arrivals|`Input - <runId>.csv`|`flushInputReport()`|
|Nodes|`Nodes - <runId>.csv`|`flushNodeReport()`|
|Network events|`NetLog - <runId>.csv`|`flushNetworkReport()`|
|Belief log (long)|`BeliefLog - <runId>.csv`|`flushBeliefReport()`|
|Belief log (short)|`BeliefLogShort - <runId>.csv`|`flushBeliefReport()`|
|Error log|`ErrorLog - <runId>.txt`|`flushErrorReport()`|
|Execution time|`RunTime - <runId>.csv`|`flushExecTimeReport()`|
|Configuration snapshot|`Config - <runId>.csv`|`flushConfig()`|

Each flush is a no-op when its corresponding toggle is disabled (see per-section **Controlled by** details below). The error log and execution time log have no toggle — they are always written.

### Table of Contents

- [Standard Reports](#standard-reports)
  - [`Event` instance occurrences](#event-instance-occurrences)
  - [New Transaction Arrivals](#new-transaction-arrivals)
  - [New Node Creation](#new-node-creation)
  - [Network Events](#network-events)
  - [Belief Entry](#belief-entry)
  - [Error Entry](#error-entry)
  - [Execution Time](#execution-time)
  - [Configuration Snapshot](#configuration-snapshot)
- [Custom Reports](#custom-reports)
  - [Scheduled Reports](#scheduled-reports)
  - [Periodic and Time Advancement Reports](#periodic-and-time-advancement-reports)
- [Related Configuration Parameters](#related-configuration-parameters)

-----

## Standard Reports

We cover Standard reports first. For each we offer: (a) an overview of what events it pertains to, (b) what method to call in order to record the event, (c) the structure of the information captured, (d) where it is currently called from, (e) how to enable/disable event capture, (f) how to flush the events to a file.

### `Event` instance occurrences

Keeps track of all `Event` type of objects processed.
#### Reporter Method
`Reporter#addEvent(int simID, long evtID, long simTime, long sysTime, String evtType, int nodeInvolved, long objInvolved, String misc)`
#### Parameters
| Parameter      | Column Name | Type   | Meaning                                                                      |
| -------------- | ----------- | ------ | ---------------------------------------------------------------------------- |
| `simID`        | SimID       | int    | The simulation ID in which the event occurs                                  |
| `evtID`        | EventID     | long   | The ID of the event                                                          |
| `simTime`      | SimTime     | long   | The simulation time of the event (ms)                                        |
| `sysTime`      | SysTime     | long   | The system wall-clock time the event was processed (ms since sim start)      |
| `evtType`      | EventType   | String | The event type (typically: `getSimpleName()` of the specializing subclass)   |
| `nodeInvolved` | NodeID      | int    | The node at which the event is happening, or `-1` if none                    |
| `objInvolved`  | ObjectID    | long   | The object involved (transaction or container ID), or `-1` if none           |
| `misc`         | Info        | String | Free-form payload, e.g. contained transaction IDs for container events       |
#### Called From
- `Event_ContainerArrival#happen(Simulation)`
- `Event_ContainerValidation#happen(Simulation)`
- `Event_NewTransactionArrival#happen(Simulation)`
- `Event_TransactionPropagation#happen(Simulation)`
- `Event_SeedUpdate#happen(Simulation)`
- `Event_Report_BeliefReport#happen(Simulation)`
- `Event_HashPowerChange#happen(Simulation)`
- `Event_BehaviorChange#happen(Simulation)`
#### Controlled by
- `Reporter#reportEvents(boolean)` — master switch; when `false`, nothing is appended regardless of per-event flags.
- Per-event-type switches (consulted by each event's `happen(...)` before calling `addEvent`):
  - `Reporter#reportContainerArrivalEvents(boolean)`
  - `Reporter#reportContainerValidationEvents(boolean)`
  - `Reporter#reportNewTransactionArrivalEvents(boolean)`
  - `Reporter#reportTransactionPropagationEvents(boolean)`
  - `Reporter#reportSeedUpdateEvents(boolean)`
  - `Reporter#reportBeliefEvents(boolean)`
#### Output
- `EventLog - <runId>.csv`
- Header: `SimID, EventID, SimTime, SysTime, EventType, NodeID, ObjectID, Info`

-----

### New Transaction Arrivals

Record all new transactions arriving to the system. Output can be used as a workload for future experiments.
#### Reporter Method
Three overloads, used depending on whether conflicts and dependencies are enabled in the workload:

- `Reporter#addTx(int simID, long txID, float size, float value, int nodeID, long simTime)`
- `Reporter#addTx(int simID, long txID, float size, float value, int nodeID, long simTime, int conflictID)`
- `Reporter#addTx(int simID, long txID, float size, float value, int nodeID, long simTime, int conflictID, String dependencies)`
#### Parameters
| Parameter      | Column Name    | Type   | Meaning                                                                                   |
| -------------- | -------------- | ------ | ----------------------------------------------------------------------------------------- |
| `simID`        | SimID          | int    | The simulation ID                                                                         |
| `txID`         | TxID           | long   | The transaction ID                                                                        |
| `size`         | Size           | float  | Transaction size in bytes                                                                 |
| `value`        | Value          | float  | Transaction fee value in local tokens                                                     |
| `nodeID`       | NodeID         | int    | The node at which the transaction first arrives                                           |
| `simTime`      | ArrivalTime    | long   | Simulation time of arrival (ms)                                                           |
| `conflictID`   | ConflictID     | int    | ID of the conflicting transaction, or `-1` if none (emitted by 2nd/3rd overloads)         |
| `dependencies` | DependencyIDs  | String | `{id1;id2;...}`-formatted dependency list, or `-1` if no dependencies (3rd overload only) |

The three-arg overload always writes `conflictID = -1`. The four-arg overload consults `Reporter#reportsSampleTransactionsOnly()` — when enabled, the entry is written only if `txID` is in `workload.sampleTransaction`.

#### Called From
- `Event_NewTransactionArrival#happen(Simulation)` — chooses the overload based on `workload.hasConflicts` and `workload.hasDependencies`.

#### Controlled by
- `Reporter#reportTransactions(boolean)` — if `false`, no transactions are logged.
- `Reporter#reportSampleTransactionsOnly(boolean)` — if `true`, only transactions in `workload.sampleTransaction` are logged (third overload only).

#### Output
- `Input - <runId>.csv`
- Header: `SimID, TxID, Size, Value, NodeID, ArrivalTime, ConflictID, DependencyIDs`

-------

### New Node Creation

Record all new nodes added to the system. Output can be used as a fixture for future experiments.
#### Reporter Method
`Reporter#addNode(int simID, int nodeID, float hashPower, float electricPower, float electricityCost, double totalCycles)`
#### Parameters
| Parameter         | Column Name     | Type   | Meaning                                                    |
| ----------------- | --------------- | ------ | ---------------------------------------------------------- |
| `simID`           | SimID           | int    | The simulation ID                                          |
| `nodeID`          | NodeID          | int    | The node ID                                                |
| `hashPower`       | HashPower       | float  | Hash power in GH/s                                         |
| `electricPower`   | ElectricPower   | float  | Electric power usage in Watts                              |
| `electricityCost` | ElectricityCost | float  | Electricity cost in USD/kWh                                |
| `totalCycles`     | TotalCycles     | double | Total hash cycles performed by the node over the run       |
#### Called From
- `NodeSet#closeNodes()`
	- The modeler must invoke this at the end of each simulation (usually via `Simulation#closeNodes()`).
	- The routine loops over all nodes in the set and calls `addNode(...)`.
	- Rationale: simulation must end before final per-node statistics (e.g., `totalCycles`) are known.
#### Controlled by
- `Reporter#reportNodes(boolean)` — if `false`, no node rows are kept.
#### Output
- `Nodes - <runId>.csv`
- Header: `SimID, NodeID, HashPower, ElectricPower, ElectricityCost, TotalCycles`

----

### Network Events

Record all new point-to-point links added to the system. Output can be used as a fixture for future experiments. For dynamic networks this also logs continuous changes in throughput.
#### Reporter Method
`Reporter#addNetEvent(int simID, int from, int to, float bandwidth, long simTime)`
#### Parameters
| Parameter   | Column Name | Type  | Meaning                                          |
| ----------- | ----------- | ----- | ------------------------------------------------ |
| `simID`     | SimID       | int   | The simulation ID                                |
| `from`      | FromNodeID  | int   | The origin node                                  |
| `to`        | ToNodeID    | int   | The destination node                             |
| `bandwidth` | Bandwidth   | float | Link throughput in bits per second; `0` = no link |
| `simTime`   | Time        | long  | Simulation time at which the change occurred (ms) |
#### Called From
- `AbstractNetwork#setThroughput(int origin, int destination, float throughput)` — called during initial network population and on any run-time throughput update.
#### Controlled by
- `Reporter#reportNetEvents(boolean)` — if `false`, no network rows are kept.
#### Output
- `NetLog - <runId>.csv`
- Header: `SimID, FromNodeID, ToNodeID, Bandwidth, Time`

----

### Belief Entry

Records belief status of nodes to specific samples of transactions. Two output formats are produced in parallel: a *long form* that records every individual (node, tx, time) belief reading, and a *short form* that aggregates — via `BeliefEntryCounter` — a running average per (simID, tx, time).

#### Reporter Method
`Reporter#addBeliefEntry(int simID, int node, long tx, float degBelief, long simTime)`
#### Parameters
| Parameter   | Column Name    | Type  | Meaning                                                                   |
| ----------- | -------------- | ----- | ------------------------------------------------------------------------- |
| `simID`     | SimID          | int   | The simulation ID                                                         |
| `node`      | NodeID         | int   | The node ID expressing the belief                                         |
| `tx`        | TxID           | long  | The transaction ID the belief concerns                                    |
| `degBelief` | Believes / Belief | float | Degree of belief (e.g. `1.0` for believed, `0.0` for not believed)     |
| `simTime`   | Time           | long  | Simulation time at which the belief is recorded (ms)                      |

The long form writes one row per call; the short form accumulates via `BeliefEntryCounter#add(simID, txID, simTime, degBelief)` and the averaged value is emitted only at flush time.

#### Called From
The flow of events that lead to a belief report is as follows:

- An `Event_Report_BeliefReport` object pops from the event queue.
- `Event_Report_BeliefReport#happen(Simulation)` loops over all nodes in the `NodeSet` and calls `INode#event_PrintBeliefReport(long[] sample, long time)`.
- Inside `Node`, `INode#event_PrintBeliefReport` forwards to the abstract `Node#beliefReport(long[] sample, long time)`.
- Concrete nodes (e.g. `BitcoinNode`, `TangleNode`) implement `beliefReport(...)` to call `Reporter#addBeliefEntry(...)` once per sampled transaction.

Minimal example:

```java
public void beliefReport(long[] sample, long time) {
    for (int i = 0; i < sample.length; i++) {
        Reporter.addBeliefEntry(
            this.sim.getSimID(),
            this.getID(),
            sample[i],
            blockchain.transactionBelief(sample[i]),   // float in [0,1]
            time);
    }
}
```

`blockchain.transactionBelief(sample[i])` is a float in `[0, 1]` capturing the node's confidence that the sampled transaction is valid at `time`. Both the long-form and short-form outputs are driven by this single call.

#### Controlled by
- `Reporter#reportBeliefs(boolean)` — if `false`, the long-form file is not kept.
- `Reporter#reportBeliefsShort(boolean)` — if `false`, the short-form file is not kept.

#### Output
- `BeliefLog - <runId>.csv` (long form) — Header: `SimID, NodeID, TxID, Believes, Time`
- `BeliefLogShort - <runId>.csv` (short form) — Header: `SimID, Transaction ID, Time (ms from start), Belief`

----

### Error Entry

Records an error that signifies issues with the implementation, protocol design, or configuration choices.
#### Reporter Method
`Reporter#addErrorEntry(String errorMsg)`
#### Parameters
| Parameter  | Type   | Meaning                                         |
| ---------- | ------ | ----------------------------------------------- |
| `errorMsg` | String | The error message (may have internal structure) |
#### Called From
- Various spots in the engine and protocol modules, typically from validator helpers or exception handlers.
#### Controlled by
- None — always flushed. If any error rows were written, a notice is printed to `System.err` pointing at the file.
#### Output
- `ErrorLog - <runId>.txt`

----

### Execution Time

Records per-simulation run-time statistics. Always produced; has no toggle.
#### Reporter Method
`Reporter#addExecTimeEntry(int simID, long simTime, long sysStartTime, long sysEndTime, long numScheduled, long numProcessed)`
#### Parameters
| Parameter      | Column Name        | Type | Meaning                                              |
| -------------- | ------------------ | ---- | ---------------------------------------------------- |
| `simID`        | SimID              | int  | The simulation ID                                    |
| `simTime`      | SimTime            | long | Final simulation time (ms)                           |
| `sysStartTime` | SysStartTime       | long | Wall-clock start time (ms since epoch)               |
| `sysEndTime`   | SysEndTime         | long | Wall-clock end time (ms since epoch)                 |
| `numScheduled` | NumEventsScheduled | long | Total events scheduled during the run                |
| `numProcessed` | NumEventsProcessed | long | Total events actually processed (≤ `NumEventsScheduled`) |
#### Called From
- `Simulation#run()` — appended once at end of run.
#### Output
- `RunTime - <runId>.csv`
- Header: `SimID, SimTime, SysStartTime, SysEndTime, NumEventsScheduled, NumEventsProcessed`

----

### Configuration Snapshot

On flush, `Reporter` also dumps the full active configuration as `Config - <runId>.csv`, so every run directory is self-describing. There is no per-call reporter method for this — it is emitted once from `Reporter#flushConfig()` by iterating `Config#printPropertiesToString()`.

Header: `Key, Value`.

## Custom Reports

### Scheduled Reports

Scheduled reports are based on a set of `Event` types which, once occurred, call a designated method on some other class, chiefly the node. A pre-defined set of events and designated methods are already defined in CNSim, but custom such events and methods can be easily created. By convention the event classes are called `Event_Report_[xxx]` where `[xxx]` describes the reporting action the receiving object (e.g., a node instance) is supposed to perform.

| Event                           | Calls                                            |
| ------------------------------- | ------------------------------------------------ |
| `Event_Report_BeliefReport`     | `Node#event_PrintBeliefReport(sampleTx,simTime)` |
| `Event_Report_NodeStatusReport` | `Node#event_NodeStatusReport(simTime)`           |
| `Event_Report_StructureReport`  | `Node#event_PrintStructureReport(simTime)`       |

The Node `event_[xxx]` methods above can be used as the implementor sees fit, though likely they will be used to call `Reporter#addBeliefEntry(...)` for registering the node's belief, and methods that a *specialization* of the Reporter class defines for keeping track and saving to files node status reports and structure reports.

### Periodic and Time Advancement Reports

There are custom reports that are not triggered by a specific event but are produced potentially every time `happen(...)` of `Event` is called. These are periodic and time advancement reports.

**Time Advancement reports** are triggered from within `happen(...)`. The `Event` class loops around all nodes of the simulation and triggers their `Node#timeAdvancementReport()` method. The implementors can choose whether and how to implement the latter. Controlled by `reporter.enableTimeAdvancementReports`.

**Periodic reports** are also triggered from within `happen(...)` as above: the `Event` class loops around all nodes of the simulation and triggers their `Node#periodicReport()` method. The difference is that this happens only every `N` events where `N` is defined by the `reporter.reportingWindow` configuration parameter. So if `reporter.reportingWindow = 1000`, `Node#periodicReport()` will be called for event IDs `1000, 2000, 3000, ...`. Controlled by `reporter.enablePeriodicReports`.

## Related Configuration Parameters

### Enable/Disable Parameters

| Parameter                            | Description                                                    | Default              |
| ------------------------------------ | -------------------------------------------------------------- | -------------------- |
| `reporter.reportEvents`              | Master switch for `EventLog` output                            | None (mandatory)     |
| `reporter.reportTransactions`        | Enable the `Input` transaction log                             | None (mandatory)     |
| `reporter.reportSampleTransactionsOnly` | Restrict the transaction log to `workload.sampleTransaction` | `false` when absent  |
| `reporter.reportNodes`               | Enable the `Nodes` log                                         | None (mandatory)     |
| `reporter.reportNetEvents`           | Enable the `NetLog`                                            | None (mandatory)     |
| `reporter.reportBeliefs`             | Enable the long-form `BeliefLog`                               | None (mandatory)     |
| `reporter.reportBeliefsShort`        | Enable the short-form `BeliefLogShort`                         | `false` when absent  |
| `reporter.events.newTransactionArrival` | `Event_NewTransactionArrival` contributes to `EventLog`     | `false` when absent  |
| `reporter.events.transactionPropagation` | `Event_TransactionPropagation` contributes to `EventLog`   | `false` when absent  |
| `reporter.events.containerArrival`   | `Event_ContainerArrival` contributes to `EventLog`             | `false` when absent  |
| `reporter.events.containerValidation` | `Event_ContainerValidation` contributes to `EventLog`         | `false` when absent  |
| `reporter.events.seedUpdate`         | `Event_SeedUpdate` contributes to `EventLog`                   | `false` when absent  |
| `reporter.events.belief`             | `Event_Report_BeliefReport` contributes to `EventLog`          | `false` when absent  |
| `reporter.enablePeriodicReports`     | Enable per-node `periodicReport()` calls                       | `false` when absent  |
| `reporter.enableTimeAdvancementReports` | Enable per-node `timeAdvancementReport()` calls             | `false` when absent  |

### Belief Report Specific Parameters

| Parameter                       | Description                                                                                                                                          | Default          |
| ------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------- |
| `reporter.beliefReportInterval` | The time interval between consecutive belief report events. Used by `ReportEventFactory` to schedule reporting events.                               | None (mandatory) |
| `reporter.beliefReportOffset`   | A time offset added to the latest known event time to determine scheduling range. Used by `ReportEventFactory` to schedule reporting events. \( * \) | None (mandatory) |

\( * \)  Given that the simulation generates events during its course in addition to the initial workload, typically there will be events scheduled after the time the last transaction arrives at the system. The offset helps to ensure that these events are also captured.

### Other Parameters

| Parameter                    | Description                                                              | Default                      |
| ---------------------------- | ------------------------------------------------------------------------ | ---------------------------- |
| `reporter.reportingWindow`   | When set to `N`, `Node#periodicReport` is called every `N` events        | None (mandatory when periodic reports are enabled) |
| `sim.output.directory`       | The directory in which the per-run log directory is created              | `./log/` when absent         |
| `sim.experimentalLabel`      | String embedded in the run ID and filenames                              | `Config#getConfigLabel()` when absent |
| `workload.sampleTransaction` | A set of transactions for which belief levels are recorded: `{200, 203}` | None (required by belief reports and `reporter.reportSampleTransactionsOnly`) |
