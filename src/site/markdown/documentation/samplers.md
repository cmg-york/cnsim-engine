# Working with Samplers

## Overview

The `ca.yorku.cmg.cnsim.engine.sampling` package is where CNSim decides the stochastic content of a simulation: how often a transaction arrives, how big it is, how much fee it pays, how much hash power each node has, what throughput each pair of nodes shares, and which seeds drive all of the above. A brief architectural recap is given in `overview.md`; this page describes the sampler hierarchy itself and how the rest of the engine consumes it.

The package is organized as four concerns in four sub-packages:

- **`interfaces`** — the abstract contracts (`ISowable`, `IMultiSowable`, `AbstractTransactionSampler`, `AbstractNodeSampler`, `AbstractNetworkSampler`).
- **`standardsamplers`** — generative implementations that draw from the parameterized distributions in `Sampler` (Poisson for arrivals, Gaussian for sizes/values, an exponential formulation for PoW mining intervals).
- **`filesamplers`** — deterministic implementations that replay values from a CSV, with optional fallback to a `standardsamplers` implementation once the file is exhausted.
- **`factories`** — factory classes that read configuration and wire the right combination of file-based and standard samplers together, scheduling `Event_SeedUpdate` events where needed.

A single `Sampler` container (in the package root) bundles one transaction sampler, one node sampler, and one network sampler and exposes the shared statistical primitives they all use. `SeedManager`, also in the package root, manages the finality-analysis seed chains described in `overview.md`.

## The `Sampler` Container

`Sampler` is the object held by `Simulation#getSampler()`. It has three fields — an `AbstractTransactionSampler`, an `AbstractNodeSampler`, and an `AbstractNetworkSampler` — accessed through `getTransactionSampler()`, `getNodeSampler()`, `getNetworkSampler()` (and their setters). The three sub-samplers are deliberately independent so that file-based and generative approaches can be mixed; a typical run uses a file-based node sampler backed by a standard transaction sampler, for example.

`Sampler` also provides the three statistical primitives the sub-samplers build on:

- `getPoissonInterval(float lambda, Random random)` — returns an exponentially distributed inter-arrival interval for a Poisson process with rate `lambda`, computed as `ln(1 - p) / -lambda` with `p` drawn from the provided `Random`.
- `getGaussianPos(float mean, float deviation, Random random)` — returns `|mean + N(0,1) × deviation|`, i.e. a folded Gaussian, guaranteed non-negative.
- `getPositiveGaussian(float mean, float deviation, Random random)` — same as above but additionally requires `mean >= 0`.

Each primitive validates its parameters with JML-style `_pre`/`_post` helpers (non-negative deviation, non-null `Random`, etc.) and raises `ArithmeticException` or `NullPointerException` on violations.

## The Sampler Interfaces

### `ISowable` and `IMultiSowable`

Two tiny interfaces capture how samplers are seeded:

- `ISowable` — one method, `setSeed(long)`. Implemented by everything that has a single underlying `Random` instance.
- `IMultiSowable` — one method, `updateSeed()`. Implemented by samplers that cycle through a pre-configured list of seeds; the call moves to the next seed in the chain.

`Event_SeedUpdate` (see `events.md`) takes an `IMultiSowable` and triggers `updateSeed()` at a scheduled time — this is the mechanism the finality-analysis machinery uses to diverge independently seeded runs from a shared initial state.

### `AbstractTransactionSampler`

Implements `ISowable`. Parameters are loaded from configuration in `LoadConfig()`:

| Field | Config property | Meaning |
| --- | --- | --- |
|`txArrivalIntervalRate`|`workload.lambda`|Poisson rate of transaction arrivals (Tx/sec).|
|`txSizeMean`, `txSizeSD`|`workload.txSizeMean`, `workload.txSizeSD`|Transaction size distribution (bytes).|
|`txValueMean`, `txValueSD`|`workload.txFeeValueMean`, `workload.txFeeValueSD`|Transaction fee distribution (local tokens).|

Abstract sampling methods subclasses must implement:

- `getNextTransactionArrivalInterval()` — inter-arrival time in ms.
- `getNextTransactionFeeValue()` — per-transaction fee.
- `getNextTransactionSize()` — per-transaction size in bytes.
- `getArrivalNode()` — node ID where the transaction first appears, or `-1` for "let the simulator pick".
- `getRandomNum(int min, int max)` — uniform integer in `[min, max]`.
- `getConflict(int id, int N, double dispersion, double likelihood)` — pick a conflicting transaction ID, used by `TransactionWorkload#updateConflicts(...)` (see `transactions.md`).
- `randomDependencies(int id, boolean mandatory, float dispersion, int countMean, float countSD)` — `BitSet` of dependency IDs, used by `TransactionWorkload#updateDependencies(...)`.
- Seed management: `updateSeed()`, `getSeedChangeTx()`, `seedUpdateEnabled()`. The transaction ID returned by `getSeedChangeTx()` is the one at which the workload flips the sampler to a new seed — the bridge between workload construction and `Transaction#makeSeedChanging()`.

All setters reject negative means and standard deviations with `ArithmeticException`. Each sampler holds its own `Random` and `randomSeed`, and `setSeed(long)` updates both.

### `AbstractNodeSampler`

Implements `IMultiSowable`. Parameters are loaded piecemeal by the factory (`NodeSamplerFactory`) rather than through a `LoadConfig()` hook. The fields cover a PoW-style node:

| Field | Meaning |
| --- | --- |
|`nodeHashPowerMean`, `nodeHashPowerSD`|Node hash power distribution (GH/s).|
|`nodeElectricPowerMean`, `nodeElectricPowerSD`|Node power consumption (Watts).|
|`nodeElectricCostMean`, `nodeElectricCostSD`|Electricity cost (currency / kWh).|
|`currentDifficulty`|PoW difficulty (search-space / success-space).|

A TODO in the source (`TODO-JIRA: De-POW-ify the Node Sampler classes`) notes that these fields presume PoW and should eventually be generalized.

Abstract sampling methods:

- `getNextMiningInterval(double hashPower)` — ms until the next validation, given hash power.
- `getNextNodeElectricPower()`, `getNextNodeHashPower()`, `getNextNodeElectricityCost()` — per-node attribute samples.
- `getNextRandomNode(int nNodes)` — uniform node ID selection.
- `updateSeed()` — implements `IMultiSowable`.

### `AbstractNetworkSampler`

Implements `ISowable`. Parameters loaded via `LoadConfig()`:

| Field | Config property | Meaning |
| --- | --- | --- |
|`netThroughputMean`|`net.throughputMean`|Mean end-to-end throughput (bps).|
|`netThroughputSD`|`net.throughputSD`|Throughput standard deviation (bps).|

One abstract method: `getNextConnectionThroughput()`, consumed by `RandomEndToEndNetwork` (see `network.md`) to fill the throughput matrix.

## Standard (Generative) Samplers

### `StandardTransactionSampler`

Draws from the distributions in `Sampler` directly.

- **Arrival intervals** — Poisson via `Sampler#getPoissonInterval(...)`, multiplied by 1000 to convert seconds to ms.
- **Fee values** — folded Gaussian via `Sampler#getGaussianPos(...)`.
- **Sizes** — folded Gaussian with a minimum of 10 bytes; if 100 tries cannot clear the minimum, the sampler aborts with a `RuntimeException` so that misconfigured `workload.txSizeMean` / `workload.txSizeSD` fail loudly.
- **Arrival node** — returns `-1`; the simulator itself picks via `NodeSet#pickRandomNode()` when it sees `-1` in `Simulation#schedule(TransactionWorkload)` (see `transactions.md`).
- **Conflicts** — two stages: a Bernoulli draw against `likelihood` (return `-1` for no conflict), then a forward-biased exponential distance controlled by `dispersion` (`0` = near, `1` = anywhere ahead). The candidate is always a larger ID — this is the invariant `TxConflictRegistry` then enforces.
- **Dependencies** — draws a count `N` from a Gaussian (with `mandatory` ensuring at least one), then chooses `N` IDs from `1..j-1` weighted toward numbers closer to `j` via a power-law key on `random.nextDouble()`.
- **Seed management** — extra fields `simID`, `initialSeed`, `currentSeed`, `seedSwitchTx`, `seedUpdateEnabled`. When `updateSeed()` fires and `Transaction.currID - 1` has passed `seedSwitchTx`, the `Random` is reseeded with `initialSeed + simID` and further updates are disabled. Configuration keys: `workload.sampler.seed`, `workload.sampler.seed.updateSeed`, `workload.sampler.seed.updateTransaction`. The `nailConfig(...)` method is the testing backdoor that bypasses configuration lookup.

### `StandardNodeSampler`

Gaussian-based node attributes, uniform random node selection.

Mining intervals use an exponential model based on an internal `Random`, not on `Sampler#getPoissonInterval`:

```
lambda = (hashPower × 1e9) / difficulty
interval_seconds = -ln(1 - random.nextDouble()) / lambda
```

`getNextMiningInterval(double)` returns the ms equivalent (rounded). An older `getNextMiningIntervalTrials(double)` / `getNextMiningIntervalSeconds(double, double)` path is still in the source for reference but the production caller uses the exponential form via `getNextMiningIntervalSeconds_alt(...)`.

Seed management is delegated to an internal `SeedManager` supplied via the three-argument constructor `StandardNodeSampler(Sampler, long[] seeds, boolean[] flags, int simID)`. `updateSeed()` advances the `SeedManager` and reseeds the `Random`. The two-argument constructor `StandardNodeSampler(Sampler)` leaves the seed manager null — `updateSeed()` on such an instance will NPE, so only use that constructor when no reseeding will be scheduled.

### `StandardNetworkSampler`

A thin wrapper: `getNextConnectionThroughput()` returns `Sampler#getGaussianPos(netThroughputMean, netThroughputSD, random)` and rejects non-positive results with an `ArithmeticException`.

## File-based Samplers

The file-based samplers replay deterministic data from a CSV, queueing values as they load and polling them on each sampling call. They all take an "alternative sampler" (typically a `Standard*Sampler`) that supplies the shortfall when the file is exhausted — so a file-based sampler is always a *file-first, sampler-fallback* object, never strictly one or the other. This is also why `setSeed(...)` / `updateSeed()` on file-based samplers simply forward to the alternative sampler.

### `FileBasedTransactionSampler`

Parses rows with five to seven fields:

1. Transaction ID (ignored during loading — the workload assigns fresh IDs).
2. Size (long).
3. Fee value (float).
4. Arrival node ID (int).
5. Arrival time in ms (long).
6. (Optional) conflicting transaction ID (int).
7. (Optional) dependency set in the form `{1;2;3}` or `-1` — parsed by the helper `parseToBitSet(String)`.

Rows with fewer than five fields are silently skipped; the header row is skipped when requested. Loaders push into queues `transactionSizes`, `transactionFeeValues`, `transactionNodeIDs`, `transactionArrivalTimes`, `conflictingTxs`, `dependencies`. `getNextTransactionArrivalInterval()` computes the interval from the *differences* between successive `transactionArrivalTimes` entries (maintaining `lastArrivalTime` so the interval remains correct).

If the file has fewer transactions than `workload.numTransactions` and no alternative sampler is defined, loading throws. If it has more, a warning is logged but loading continues.

`getConflict(id, ...)` and `randomDependencies(id, ...)` first consult the per-row file lists; if the ID is beyond the file's coverage, the calls fall through to the alternative sampler. Note that the file lists are 1-indexed through `id-1` offsets, so IDs must line up with the transaction IDs the workload assigns.

### `FileBasedNodeSampler`

Parses rows of exactly four fields: node ID (ignored), hash power, electric power, electricity cost. Rows with the wrong number of fields are silently skipped.

Samples from the three file queues one by one; empty queues fall through to the alternative sampler. `getNextMiningInterval(...)` and `getNextRandomNode(...)` always delegate — the file only carries per-node static attributes, not mining behavior. If the file has fewer rows than `net.numOfNodes`, a notice is logged but loading continues (the alternative sampler takes over). `updateSeed()` forwards to the alternative sampler's `updateSeed()` and prints an error to `System.err` if no alternative was configured.

## Factories

The factories are the seam between configuration and the sampler hierarchy. Each returns an `Abstract*Sampler` wired for a simulation, deciding file-vs-standard based on whether a path is supplied.

### `TransactionSamplerFactory`

```java
AbstractTransactionSampler getSampler(String path, Sampler outer, Simulation sim)
```

If `path != null`, returns a `FileBasedTransactionSampler(path, new StandardTransactionSampler(outer, sim.getSimID()))` — file-first, with a generative fallback carrying the simulation ID for reproducibility. Otherwise returns a bare `StandardTransactionSampler(outer, sim.getSimID())`. Factory-level configuration is minimal; the transaction sampler loads its own distribution parameters through `LoadConfig()` in its constructor.

### `NodeSamplerFactory`

The most involved of the three, because nodes participate in the finality-analysis seed machinery.

```java
AbstractNodeSampler getSampler(
    String path,
    String seedChain,
    String changeTimes,
    String updateFlags,
    Sampler sampler,
    Simulation sim)
```

Flow:

1. Parse `seedChain` (comma-separated longs) into a `long[]` of seeds — the chain the `SeedManager` will cycle through.
2. Parse `changeTimes` (comma-separated longs) into switch times and `updateFlags` (comma-separated booleans) into per-seed simID-modulation flags.
3. Validate that if switch times are given, seeds are given too, and that `updateFlags.length == seeds.length` — mismatches throw a descriptive `Exception`.
4. Instantiate the sampler. Four combinations exist, depending on whether `path` is set and whether a seed chain is given:
   - `FileBasedNodeSampler` wrapping `StandardNodeSampler(sampler, seeds, flags, simID)` — file, with reseed chain.
   - `FileBasedNodeSampler` wrapping `StandardNodeSampler(sampler)` — file, no reseed.
   - `StandardNodeSampler(sampler, seeds, flags, simID)` — generative, with reseed chain.
   - `StandardNodeSampler(sampler)` — generative, no reseed.
5. Copy the PoW/node parameters from configuration onto the sampler (`pow.hashPowerMean`, `pow.hashPowerSD`, `node.electricPowerMean`, `node.electricPowerSD`, `node.electricCostMean`, `node.electricCostSD`, `pow.difficulty`).
6. If switch times are set, schedule one `Event_SeedUpdate(nodeSampler, switchTime)` per entry via `Simulation#schedule(...)`. At run time these events pop from the queue and call `updateSeed()` on the node sampler, cycling the `SeedManager`.

The scheduling step in (6) is why the node sampler hierarchy implements `IMultiSowable`: `Event_SeedUpdate` takes an `IMultiSowable`, and the scheduled events work uniformly whether the current node sampler is `StandardNodeSampler` (cycles its own seed manager) or `FileBasedNodeSampler` (forwards to the wrapped standard sampler's seed manager).

### `NetworkSamplerFactory`

```java
AbstractNetworkSampler getNetworkSampler(Long seed, boolean seedFlag, Sampler outer, Simulation sim)
```

Always returns a `StandardNetworkSampler` — there is no file-based network sampler because end-to-end throughput tables are loaded through `FileBasedEndToEndNetwork` directly (see `network.md`). If `seed != null`, the network sampler is seeded with `seed + (seedFlag ? sim.getSimID() : 0)`, so setting `seedFlag = true` is how network sampling diverges across simulation runs in a finality-analysis batch. Finally, the factory copies `net.throughputMean` / `net.throughputSD` from configuration onto the sampler.

## `SeedManager`

`SeedManager` owns a circular seed sequence used by `StandardNodeSampler` (and any future multi-seed sampler). Its state is:

| Field | Meaning |
| --- | --- |
|`seedArray`|The base seeds, cycled in order.|
|`seedUpdateFlags`|Per-seed flag: if `true`, the active seed is offset by `simID`.|
|`currentIndex`|Pointer into the array, advanced on each `nextSeed()`.|
|`simID`|The simulation ID used for offsetting when a flag is `true`.|

`updateSeed(Random)` computes `seedArray[currentIndex] + (flag ? simID : 0)`, calls `random.setSeed(...)`, and advances `currentIndex` circularly. This is the mechanism that realizes the finality-analysis scheme from `overview.md`: all runs share the same `seedArray` and share the same "pre-switch" seeds (flags `false`), but diverge after a flagged seed is activated (`simID` is added, making each run independent).

## How the Engine Uses the Samplers

A typical setup, orchestrated by the protocol's `main` class:

1. Create an empty `Sampler`.
2. Build each sub-sampler through its factory, passing configuration paths/strings and the `Simulation` (needed to schedule `Event_SeedUpdate` events and to read `simID`).
3. Attach the sub-samplers to the `Sampler` via `setTransactionSampler(...)`, `setNodeSampler(...)`, `setNetworkSampler(...)`.
4. Hand the `Sampler` to the `Simulation`.

At run time:

- `TransactionWorkload#appendTransactions(N)` calls `transactionSampler` for each transaction's interval, size, value, and arrival node; optionally marks the one matching `getSeedChangeTx()` as seed-changing and calls `updateSeed()` immediately.
- `RandomEndToEndNetwork` calls `networkSampler.getNextConnectionThroughput()` once per unordered node pair (see `network.md`).
- `NodeSet` creation draws from `nodeSampler.getNextNodeHashPower() / getNextNodeElectricPower() / getNextNodeElectricityCost()` per node (see the relevant node sampler's consumers).
- During the run, nodes query `nodeSampler.getNextMiningInterval(hashPower)` to schedule their next validation attempt.
- When a seed-changing transaction arrives, `Event_NewTransactionArrival#happen(...)` calls `sim.getSampler().getNodeSampler().updateSeed()` — cycling the node sampler's `SeedManager` at the exact point in workload time chosen by configuration.
- Scheduled `Event_SeedUpdate` events (emitted by `NodeSamplerFactory`) call `updateSeed()` at pre-declared simulation times.

## Extending the Hierarchy

Most protocols reuse the built-in samplers verbatim. When something richer is needed:

1. **Different distribution.** Subclass `Standard*Sampler` and override the `getNext...(...)` methods. If the distribution is reusable across sampler kinds, add a primitive alongside `getPoissonInterval` / `getGaussianPos` on `Sampler` itself.
2. **Different data source.** Subclass `AbstractTransactionSampler` / `AbstractNodeSampler` / `AbstractNetworkSampler` directly and implement the queue-and-fallback pattern used by the file samplers. Take an "alternative sampler" in the constructor so callers can still get a fallback without a separate branch.
3. **New seed discipline.** Implement `IMultiSowable` and emit `Event_SeedUpdate` events from the relevant factory at construction time. If the discipline cycles a finite list of seeds, reuse `SeedManager`; otherwise build a bespoke update method.
4. **Factory integration.** Extend the appropriate factory (or introduce a new one) so the new sampler can be selected through configuration rather than hard-wired in `main`.

See `events.md` for the event-side of seed updates and `network.md` / `transactions.md` for the downstream consumers of the network and transaction samplers.
