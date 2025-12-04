# Reporting Mechanism

## Overview

### Architectural Approach

Reporting in CNSim-Engine is handled through the `Reporter` class. The `Reporter` keeps a log of the occurrences of events of different types ("event" here not necessarily equivalently to CNSim `Event` instances). To log an event or other information different parts of the simulator, primarily `Node` objects, call static methods of `Reporter` adding the information to be recorded as parameters to the corresponding call. This marks a reporting action. `Reporter` maintains this information in lists that are saved to the disc once the simulation run ends. 

CNSim supports a basic mechanism for reporting basic events (Standard Reporting) as well as a mechanism for triggering custom reports via designated events (Custom Reporting). Standard reporting pertains to events relating to the creation of various objects in the simulation, specifically transactions, nodes, network connections and events in general. These reports are important for reviewing the structure of the network and the workload of transactions after the simulation. However, some or all of them can be switched off for better performance.

Custom reporting is implemented by having simulation objects respond to specified reporting `Event` objects, possibly but not necessarily prescheduled during simulation set-up. Processing of the event (calling of its `happens()` routine) causes the class responsible for responding to it to send reporting information to the Reporter. It is up to the implementor to decide whether the class would offer a report upon requested and what this report will be. Specializations of the `Reporter` class can be utilized for custom reports. 

### Formatting and Saving Reports

Currently, event logs are appended as *comma separated* Strings in various arraylists each corresponding to a different kind of event. At the end of the simulation the arraylists are saved to CSV files on the disk following a `flush[Evt Type]` call. 

The naming convention of the event log files is TODO

The log files are saved at TODO

TODO: create TOC here


-----
## Standard Reports

We cover Standard reports first. For each we offer: (a) an overview of what events it pertains to, (b) what method to call in order to record the event, (c) the structure of the information captured. (b) where it is the method currently called from, (d) how to enable/disable event capture, (e) how to flush the events to a file.

### `Event` instance occurrences

Keeps track of all `Event` type of objects processed. 
#### Reporter Method
`Reporter#addEvent(params)`
#### Parameters
| Parameter    | Column Name | Type   | Meaning                                                                    |
| ------------ | ----------- | ------ | -------------------------------------------------------------------------- |
| simID        | SimID       | int    | The simulation ID in which the event occurs                                |
| evtID        | EventID     | long   | The ID of the event                                                        |
| simTime      | SimTime     | long   | The simulation time of the event                                           |
| sysTime      | SysTime     | long   | The system time the event was processed                                    |
| evtType      | EventType   | String | The event type (typically: `getSimpleName()` of the specializing subclass) |
| nodeInvolved | NodeID      | int    | The node in which the event is happening.                                  |
| objInvolved  | ObjectID    | long   | The object (transaction or container)                                      |
#### Called From
- `Event_ContainerArrival#happen(Simulation)`
- `Event_ContainerValidation#happen(Simulation)`
- `Event_NewTransactionArrival#happen(Simulation)`
- `Event_SeedUpdate#happen(Simulation)`
- `Event_TransactionPropagation#happen(Simulation)`
#### Controlled by
- `Reporter#reportEvents(boolean)`
	- If false the specific events will not be kept.
#### Output
- `EventLog - [label] - yyyy.mm.dd hh.mm.ss.csv`
-----
### New Transaction Arrivals

Record all new transactions arriving to the system. Output can be used as a workload for future experiments.
#### Reporter Method
`Reporter#addTx(params)`
#### Parameters
TODO as above
#### Called From
- `Event_NewTransactionArrival#happen(Simulation)`
#### Controlled by
- `Reporter#reportTransactions(boolean)`
	- If false the specific events will not be kept.
#### Output
- `Input - [label] - yyyy.mm.dd hh.mm.ss.csv`
-------
### New Node Creation

Record all new nodes added to the system. Output can be used as a fixture for future experiments.
#### Reporter Method
`Reporter#addNode(params)`
#### Parameters
TODO as above
#### Called From
- `NodeSet#closeNodes()`
	- Modeler must run the above at the end of each simulation.
	- The routine simply loops over all nodes in the set and calls the `addNode(params)`
	- Rationale: the simulation must end before all node information has been collected. 
#### Controlled by
- `Reporter#reportNodes(boolean)`
	- If false the specific events will not be kept.
#### Output
- `Nodes - [label] - yyyy.mm.dd hh.mm.ss.csv`
----
### Network Events
Record all new point-to-point links added to the system. Output can be used as a fixture for future experiments. For future, this logs continuous changes in the network throughputs.
#### Reporter Method
`Reporter#addNetEvent(params)`
#### Parameters
TODO as above
#### Called From
- `AbstractNetwork#setThroughput(int origin, int destination, float throughput)
#### Controlled by
- `Reporter#reportNetEvents(boolean)`
	- If false the specific events will not be kept.
#### Output
- `NetLog - [label] - yyyy.mm.dd hh.mm.ss.csv`
----
### Belief Entry
Records belief status of nodes to specific samples of transactions
#### Reporter Method
`Reporter#addBeliefEntry(params)`
#### Parameters
TODO as above
#### Called From
The flow of events that lead to a belief report is as follows:
- An `Event_Report_BeliefReport` object pops from the event queue.
- `Event_Report_BeliefReport#happen(Simulation)` of the above object loops over all nodes in the `NodeSet` associated with the simulation, and calls `INode#event_PrintBeliefReport`.
- Inside `Node`, `INode#event_PrintBeliefReport`, is implemented via a forwarding to abstract `Node#beliefReport(long[] sample, long time)`
- Concrete implementations of Node (e.g. `BitcoinNode`, `TangleNode`, `EthereumNode`) must arrange to call as many `Reporter#addBeliefEntry(params)` entries as the sample of transactions. 
Example inside `BitcoinNode` (TODO: revise to remove booleans):
```
public void beliefReport(long[] sample, long time) {

  for (int i = 0; i < sample.length; i++) {
	Reporter.addBeliefEntry(
		this.sim.getSimID(),
		this.getID(),
		sample[i],
		blockchain.transactionBelieved(sample[i]),
		blockchain.transactionBelief(sample[i]),
		time,
		false);
  }
}
```
In the above `blockchain.transactionBelieved(sample[i]), time)` is a boolean that specifies if the transaction with ID `sample[i]` is believed by the blockchain. A corresponding float value is offered, which is ignored by the routine.
#### Controlled by
- `Reporter#reportBeliefs(boolean)`
	- If `false` the long-form reporting will not be kept.
- `Reporter#reportBeliefsShort(boolean)`
	- If `false` the short-form reporting will not be kept.
#### Output
- `NetLog - [label] - yyyy.mm.dd hh.mm.ss.csv`
----
### Error Entry
Records an error that signifies issues with the implementation, protocol design, or configuration choices.
#### Reporter Method
`Reporter#addErrorEntry(params)`
#### Parameters
| Parameter  | Type   | Meaning                                         |
| ---------- | ------ | ----------------------------------------------- |
| `errorMsg` | String | The error message (may have internal structure) |
#### Called From
- Various spots in the implementing sources.
#### Controlled by
- None
#### Output
- `ErrorLog - [label] - yyyy.mm.dd hh.mm.ss.txt`


## Custom Reports

### Scheduled Reports

Scheduled reports are based on a set `Event` types which, once occurred, call a designated method of some other class, chiefly the node. A pre-defined set of events and designated methods are already defined in CNSim, but custom such events and methods can be easily created. By convention the event classes are called `Event_Report_[xxx]` where `[xxx]` describes the reporting action the receiving object (e.g., a node instance) is supposed to perform.

| Event                           | Calls                                            |
| ------------------------------- | ------------------------------------------------ |
| `Event_Report_BeliefReport`     | `Node#event_PrintBeliefReport(sampleTx,simTime)` |
| `Event_Report_NodeStatusReport` | `Node#event_NodeStatusReport(simTime)`           |
| `Event_Report_StructureReport`  | `Node#event_PrintStructureReport(simTime)`       |

The Node `event_[xxx]` methods above can be used as the implementor sees fit, through likely they will be used to call `Reporter#addBeliefEntry(...)` for registering the nodes belief, and methods that a *specialization* of the Reporter class defines for keeping track and saving to files node status reports and structure reports.

### Periodic and Time Advancement Reports
There are custom reports that are not relating to an event but are produced potentially every time `happen(...)` of `Event` is called. These are periodic and time advancement reports.

**Time Advancement reports** are triggered from within `happen(...)`. The `Event` class loops around all nodes of the simulation and triggers their `Node#timeAdvancementReport()` method. The implementors can choose whether and hot to implement the latter.  

**Periodic reports** are also triggered from within `happen(...)` as above: the `Event` class loops around all nodes of the simulation and triggers their `Node#periodicReport()` method. The difference is that this happens only  every `N` events where `N` is defined by the `reporter.reportingWindow` configuration parameter. So if `reporter.reportingWindow = 1000`, `Node#periodicReport()` will be called for event IDs `1000, 2000, 3000, ...`.

## Related Configuration Parameters

### Enable/Disable Parameters
| Parameter                     | Description                                                    | Default          |
| ----------------------------- | -------------------------------------------------------------- | ---------------- |
| `reporter.reportEvents`       | Set `true` to report Events, `false` otherwise                 | None (mandatory) |
| `reporter.reportTransactions` | Set `true` to report Transactions, `false` otherwise           | None (mandatory) |
| `reporter.reportNodes`        | Set `true` to report Node Events, `false` otherwise            | None (mandatory) |
| `reporter.reportNetEvents`    | Set `true` to report Network Events, `false` otherwise         | None (mandatory) |
| `reporter.reportBeliefs`      | Set `true` to report Beliefs, `false` otherwise                | None (mandatory) |
| `reporter.reportBeliefsShort` | Set `true` to report Beliefs (short option), `false` otherwise | None (mandatory) |
### Belief Report Specific  Parameters
| Parameter                       | Description                                                                                                                                          | Default          |
| ------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------- |
| `reporter.beliefReportInterval` | The time interval between consecutive belief report events. Used by `ReportEventFactory` to schedule reporting events.                               | None (mandatory) |
| `reporter.beliefReportOffset`   | A time offset added to the latest known event time to determine scheduling range. Used by `ReportEventFactory` to schedule reporting events. \( * \) | None (mandatory) |

\( * \)  Given that the simulation generates events during its course in addition to the initial workload, typically there will be events scheduled after the time the last transaction arrives at the system. The offset helps to ensure that these events are also captured.

### Other Parameters
| Parameter                    | Description                                                              | Default          |
| ---------------------------- | ------------------------------------------------------------------------ | ---------------- |
| `reporter.reportingWindow`   | When set to 'N' `Node#periodicReport` is called every `N` events         | None (mandatory) |
| `sim.output.directory`       | The directory in which the log files are to be saved.                    | None (mandatory) |
| `sim.experimentalLabel`      | Is used to construct part of the filename.                               | None (mandatory) |
| `workload.sampleTransaction` | A set of transactions for which belief levels are recorded: `{200, 203}` | TODO (Sotirios)  |

