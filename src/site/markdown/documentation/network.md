# Network Topology and Throughput

## Overview

The `ca.yorku.cmg.cnsim.engine.network` package models the communication fabric that connects nodes in a simulated consensus network. CNSim deliberately abstracts away routing and physical link topology: what matters to a consensus simulation is *how long* a message of a given size takes to travel between any two nodes, not the packets it transits through. The package therefore stores an end-to-end throughput matrix and computes transmission delays on demand. A brief architectural recap is given in `overview.md`; units of measurement are documented separately in `units.md`.

The package exposes an abstract `AbstractNetwork` base class, two concrete implementations (`RandomEndToEndNetwork` and `FileBasedEndToEndNetwork`), and a `NetworkFactory` that picks between them from configuration. A single `Simulation` holds one `AbstractNetwork` (via `Simulation#setNetwork(AbstractNetwork)`), and that network's `NodeSet` is the same one the simulator iterates when dispatching events.

## The `AbstractNetwork` Base Class

`AbstractNetwork` is the protocol-neutral surface. Its state is minimal:

| Field | Type | Meaning |
| --- | --- | --- |
|`ns`|`NodeSet`|The participating nodes. Same reference as `Simulation#getNodeSet()`.|
|`Net`|`float[][]`|The end-to-end throughput matrix, indexed by node ID, in bits per second (bps).|

The matrix is sized `(net.numOfNodes + 1) × (net.numOfNodes + 1)` at construction time — node IDs are 1-based, and the row/column 0 is left unused so IDs can be used directly as indices.

Three internal constants capture the unit conversions so they do not have to be re-derived at every call site:

- `NOT_CONNECTED = -1L` — the sentinel returned (and expected by callers) when two nodes have no usable link.
- `BITS_PER_BYTE = 8f` — transaction and block sizes are measured in bytes, throughput in bits/second.
- `MS_PER_SECOND = 1000f` — simulation time is measured in milliseconds.

### Transmission Time

The central operation is `AbstractNetwork#getTransmissionTime(int origin, int destination, float size)`: it reads the end-to-end throughput from `Net[origin][destination]` and returns the transmission time in milliseconds, or `-1` if the throughput is zero (nodes are not connected). Internally it delegates to the overload `getTransmissionTime(float throughput, float size)`, which uses the formula:

```
ms = (size × 8 × 1000) / throughput
```

i.e. bytes-to-bits and seconds-to-milliseconds. Throughput below `1e-6` is treated as zero and returns `-1`. Both overloads enforce `size >= 0` and `throughput >= 0` (for the float variant) and raise `ArithmeticException` on violation.

This is the method a protocol calls whenever it schedules a propagation event (e.g., computing the arrival time of a transaction or block at a peer): the result is added to `Simulation.currTime` to produce the scheduled time of the corresponding `Event_TransactionPropagation` or `Event_ContainerArrival`.

### Throughput Access

- `getThroughput(int origin, int destination)` — reads `Net[origin][destination]`. Validates that indices are non-negative and rejects negative values found in the matrix as a runtime corruption (`RuntimeException`).
- `setThroughput(int origin, int destination, float throughput)` — writes one directed entry. Before validation, it records a network-event entry via `Reporter.addNetEvent(simID, origin, destination, throughput, Simulation.currTime)` whenever `Reporter.reportsNetEvents()` is on. This is the hook that lets `reporting.md`'s `NetLog` capture every link creation or update, including during run-time changes.
- `getAvgTroughput(int origin)` — returns the mean of the bidirectional throughputs between `origin` and every other node, i.e. `(Net[origin][i] + Net[i][origin]) / 2` averaged over all `i ≠ origin`.

Note: `setThroughput(...)` writes a *directed* entry only. Symmetric links must be established by calling the setter twice — once for each direction. `RandomEndToEndNetwork` does this explicitly; `FileBasedEndToEndNetwork` only sets the direction listed in the file, so files must list both directions if an asymmetric topology is not intended.

### Debug Printing

`printNetwork()` and `printNetwork2()` dump the matrix to standard output; the former uses a `%3.1f` format, the latter raw `println`. Both are for development only.

## Concrete Networks

Two concrete subclasses cover the two supply paths for throughput data: "generate from a sampler" and "load from a file".

### `RandomEndToEndNetwork`

`RandomEndToEndNetwork(NodeSet, Sampler)` builds the matrix by asking the sampler's network sampler for a throughput for every unordered pair `(i, j)` with `i < j`, then mirroring the result into both directions — so the topology is always symmetric. Populated entries are skipped (the loop guard is `Net[i][j] == 0`), which means re-running `createRandomNetwork()` against a partially seeded matrix only fills the holes. The number of nodes comes from `net.numOfNodes` in the configuration. There is also an empty constructor for testing.

### `FileBasedEndToEndNetwork`

`FileBasedEndToEndNetwork(NodeSet, String filename)` loads the matrix from a CSV file whose rows are `fromNodeID, toNodeID, throughput, …` (the parser actually requires exactly four comma-separated fields per row; the fourth is currently unused). The first row is optionally treated as a header. `LoadFromFile(boolean hasHeaders)` does the work; `LoadFromFile()` is a header-on shortcut. Rows with the wrong number of fields are silently skipped; numeric parse failures are logged to `System.err` but do not abort the load. IDs outside `[0, Net.length]` or beyond the `NodeSet` count raise an `Exception`.

Because each row sets exactly one directed entry, asymmetric links are representable — but symmetric topologies must include both `(from,to)` and `(to,from)` rows.

### `NetworkFactory`

`NetworkFactory#createNetwork(NodeSet, Sampler)` is the seam between configuration and the two concrete networks. The rule is simple:

- If `net.sampler.file` is set in the configuration, return a `FileBasedEndToEndNetwork` pointed at that path.
- Otherwise, return a `RandomEndToEndNetwork` driven by the provided sampler.

This is the method a protocol's `main` class calls after constructing the `NodeSet` and before handing the network to `Simulation#setNetwork(...)`.

## How the Engine Uses the Network

The network is consulted whenever the protocol needs to know how long a message takes between two nodes:

1. **Setup.** A `main` class builds a `NodeSet` and a `Sampler`, calls `NetworkFactory.createNetwork(ns, sampler)`, and attaches the result via `Simulation#setNetwork(...)`. `Simulation#getNodeSet()` afterward returns `net.getNodeSet()`.
2. **Propagation timing.** When a node that has just received or produced something needs to forward it, it calls `sim.getNetwork().getTransmissionTime(myID, peerID, payloadSize)` and schedules an `Event_TransactionPropagation` or `Event_ContainerArrival` (see `events.md`) at `Simulation.currTime + transmissionTime`. A returned `-1` means the peer is unreachable and the event should simply not be scheduled.
3. **Dynamic changes.** Throughput updates during a run flow through `setThroughput(...)`, which both mutates the matrix and logs a `NetLog` entry via `Reporter.addNetEvent(...)`. The `Reporter.reportsNetEvents()` flag gates whether the entry is kept; see `reporting.md`.
4. **End-of-run.** The network has no close/flush method of its own — its contribution to the reports is emitted eagerly at each `setThroughput(...)` call rather than at shutdown.

## Units

Throughout the package, sizes are in **bytes**, throughputs are in **bits per second**, and returned transmission times are in **milliseconds** — the three conversion constants in `AbstractNetwork` bake this into the arithmetic. See `units.md` for the full unit table used across CNSim.

## Extending the Hierarchy

Most protocols use the two built-in concrete networks as is. When a new supply path is needed — for example, a network generated from a measured Internet dataset, or one whose throughput drifts over time — the recipe is:

1. Subclass `AbstractNetwork`. Call `super(ns)` so the `Net` matrix is sized against `net.numOfNodes`.
2. Populate `Net` by calling `setThroughput(origin, destination, bps)` — this keeps the `Reporter.addNetEvent(...)` logging path intact. Avoid writing directly to `Net[i][j]` unless you also want to bypass reporting.
3. For symmetric networks, write each pair twice (the base class does not do this for you).
4. Extend `NetworkFactory#createNetwork(...)` (or replace it) so your new network is picked up from configuration.

For time-varying link throughput, the recommended pattern is to schedule an `Event` whose `happen(Simulation)` calls `setThroughput(...)` at the appropriate time — this automatically produces a `NetLog` entry at each change. A `setThroughput`-wrapping event type sits naturally alongside `Event_HashPowerChange` in the control-events family described in `events.md`.
