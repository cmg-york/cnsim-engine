# Reporting Mechanism

## Overview

Reporting in CNSim-Engine is handled through the `Reporter` class. The `Reporter` keeps a log of the occurrences of events of different types ("event" here not necessarily equivalently to CNSim `Event` instances). Below for each we offer: (a) an overview of what events it pertains to, (b) what method to call in order to record the event, (c) the structure of the information captured. (b) where it is the method currently called from, (d) how to enable/disable event capture, (e) how to flush the events to a file.

Currently, event logs are appended as *comma separated* Strings in various arraylists each corresponding to a different kind of event. At the end of the simulation the arraylists are saved to CSV files on the disk following a `flush[Evt Type]` call. 

The naming convention of the event log files is TODO

The log files are saved at TODO

TODO: create TOC here

-----
### `Event` instance occurrences

Keeps track of all `Event` type of objects processed. 
#### Reporter Method
`Reporter#addEvent(params)`
#### Parameters
| Parameter    | Type   | Meaning                                                                    |
| ------------ | ------ | -------------------------------------------------------------------------- |
| simID        | int    | The simulation ID in which the event occurs                                |
| evtID        | long   | The ID of the event                                                        |
| simTime      | long   | The simulation time of the event                                           |
| sysTime      | long   | The system time the event was processed                                    |
| evtType      | String | The event type (typically: `getSimpleName()` of the specializing subclass) |
| nodeInvolved | int    | The node in which the event is happening.                                  |
| objInvolved  | long   | The object (transaction or container)                                      |
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
| Parameter                       | Description | Default          |
| ------------------------------- | ----------- | ---------------- |
| `reporter.beliefReportInterval` | TODO        | None (mandatory) |
| `reporter.beliefReportOffset`   | TODO        | None (mandatory) |
### Other Parameters
| Parameter                    | Description                                                             | Default          |
| ---------------------------- | ----------------------------------------------------------------------- | ---------------- |
| `reporter.reportingWindow`   | TODO                                                                    | None (mandatory) |
| `sim.output.directory`       | TODO                                                                    | None (mandatory) |
| `sim.experimentalLabel`      | TODO                                                                    | None (mandatory) |
| `workload.sampleTransaction` | A set of transactions for which belief levels are recorded `{200, 203}` | TODO (Sotirios)  |

