# Configuring CNSim-Engine

## Overview

CNSim-Engine reads all runtime parameters from a Java `Properties` file loaded through the `ca.yorku.cmg.cnsim.engine.config.Config` class. Every `Config.getPropertyXxx(key)` call in the engine sources is keyed by a string defined below; every `Config.hasProperty(key)` call marks an optional key whose absence produces default behavior rather than an error.

A working example is provided at `src/main/resources/application.properties` — the tables below annotate each key with its type, whether it is mandatory, where it is consumed in the engine, and its meaning. Keys are grouped by area: simulation-wide, network, workload, node/PoW, and reporter. Protocol-specific keys (`bitcoin.\*`, `tangle.\*`) are defined and consumed in the respective protocol modules and are out of scope here.

Conventions:

* **Type** is the parser used at the call site (`getPropertyInt`, `getPropertyLong`, `getPropertyFloat`, `getPropertyDouble`, `getPropertyBoolean`, `getPropertyString`, `getOptionalPropertyBoolean`). Array-valued keys use a comma-separated `{a,b,c}` syntax parsed via `Config#parseStringToArray(String)` or `Config#parseStringToBoolean(String)`.
* **Mandatory** means the engine calls `getProperty\*` without a `hasProperty` guard — an absent key typically raises `NullPointerException` on parse. **Optional** means the engine either guards with `hasProperty` or uses `getOptionalPropertyBoolean` (which returns `false` when missing).
* **Consumed in** cites the primary source location. A few keys are read from several places; in those cases the canonical consumer is listed.

## Simulation

| Key | Type | Mandatory? | Consumed in | Meaning |
| --- | --- | --- | --- | --- |
|`sim.output.directory`|String|Yes|`Reporter#openReporter()`|Directory where log CSVs are written. Trailing slash expected (e.g. `./log/`).|
|`sim.experimentalLabel`|String|Optional|`Reporter#openReporter()`|Label embedded in every output filename. Absent → filenames carry no label.|
|`sim.terminate.atTime`|long|Yes|`SimulatorFactory#buildSimulator(...)`|Simulation time (ms) past which remaining events are discarded and `Simulation#run()` exits early.|

## Network

| Key | Type | Mandatory? | Consumed in | Meaning |
| --- | --- | --- | --- | --- |
|`net.numOfNodes`|int|Yes|`AbstractNetwork`, `RandomEndToEndNetwork`, `FileBasedNodeSampler`|Total number of nodes — determines the size of the throughput matrix and the expected row count of the nodes CSV.|
|`net.sampler.file`|String|Optional|`NetworkFactory#createNetwork`, `SimulatorFactory`|Path to an end-to-end throughput CSV. Present → `FileBasedEndToEndNetwork` is used; absent → `RandomEndToEndNetwork` is generated from the network sampler.|
|`net.sampler.seed`|long|Optional|`SimulatorFactory#buildSampler`|Base seed for the network sampler's RNG. Passed through `NetworkSamplerFactory#getNetworkSampler(...)`.|
|`net.sampler.seed.updateSeed`|boolean|Optional|`SimulatorFactory#buildSampler`|If `true`, the simulation ID is added to `net.sampler.seed` to diverge network sampling across different simulation runs.|
|`net.throughputMean`|float|Yes|`AbstractNetworkSampler#LoadConfig`, `NetworkSamplerFactory`|Mean end-to-end throughput (bps) used by `StandardNetworkSampler`.|
|`net.throughputSD`|float|Yes|`AbstractNetworkSampler#LoadConfig`, `NetworkSamplerFactory`|Standard deviation of end-to-end throughput (bps).|

See `network.md` for how these keys flow into `AbstractNetwork` and the two concrete networks.

## Workload

### Arrival and Size/Fee Distributions

| Key | Type | Mandatory? | Consumed in | Meaning |
| --- | --- | --- | --- | --- |
|`workload.numTransactions`|long|Yes|`SimulatorFactory`, `FileBasedTransactionSampler`|Number of transactions to generate (or expected from a file).|
|`workload.lambda`|float|Yes|`AbstractTransactionSampler#LoadConfig`|Poisson rate of transaction arrivals (Tx/sec). Used by `StandardTransactionSampler#getNextTransactionArrivalInterval()`.|
|`workload.txSizeMean`|float|Yes|`AbstractTransactionSampler#LoadConfig`|Mean transaction size (bytes).|
|`workload.txSizeSD`|float|Yes|`AbstractTransactionSampler#LoadConfig`|Standard deviation of transaction size (bytes).|
|`workload.txFeeValueMean`|float|Yes|`AbstractTransactionSampler#LoadConfig`|Mean transaction fee (local tokens).|
|`workload.txFeeValueSD`|float|Yes|`AbstractTransactionSampler#LoadConfig`|Standard deviation of transaction fee.|
|`workload.sampleTransaction`|String (array)|Yes (for belief reports)|`Event\_Report\_BeliefReport`, `Reporter`, `PoWNodeSet`|Transaction IDs (e.g. `{10,15,20}`) whose belief is tracked and emitted in belief reports.|

### Workload File and Seed Management

| Key | Type | Mandatory? | Consumed in | Meaning |
| --- | --- | --- | --- | --- |
|`workload.sampler.file`|String|Optional|`SimulatorFactory#buildSampler`|Path to a transaction CSV. Present → `FileBasedTransactionSampler` is used with a generative fallback; absent → `StandardTransactionSampler` only.|
|`workload.sampler.seed`|long|Optional|`StandardTransactionSampler#LoadConfig`|Initial seed for the transaction sampler. Defaults to 0 when missing.|
|`workload.sampler.seed.updateSeed`|boolean|Optional|`StandardTransactionSampler#LoadConfig`|Enables the one-shot re-seeding at `workload.sampler.seed.updateTransaction`. Defaults to `false`.|
|`workload.sampler.seed.updateTransaction`|long|Optional|`StandardTransactionSampler#LoadConfig`|Transaction ID past which the sampler re-seeds with `workload.sampler.seed + simID`. Defaults to 0 (so never re-seeding).|

### Conflicts

| Key | Type | Mandatory? | Consumed in | Meaning |
| --- | --- | --- | --- | --- |
|`workload.hasConflicts`|boolean|Optional|`SimulatorFactory#buildSampler`, `Event\_NewTransactionArrival`|Enables conflict-pair generation through the transaction sampler and richer per-Tx logging.|
|`workload.conflicts.dispersion`|double|Required when `workload.hasConflicts=true`|`SimulatorFactory#buildSampler`|Closeness parameter in `\[0,1]` for conflict-partner selection: `0` → near `id`, `1` → anywhere forward.|
|`workload.conflicts.likelihood`|double|Required when `workload.hasConflicts=true`|`SimulatorFactory#buildSampler`|Probability in `\[0,1]` that a transaction has any conflict at all.|

### Dependencies

| Key | Type | Mandatory? | Consumed in | Meaning |
| --- | --- | --- | --- | --- |
|`workload.hasDependencies`|boolean|Optional|`SimulatorFactory#buildSampler`, `Event\_NewTransactionArrival`|Enables dependency-set generation and richer per-Tx logging.|
|`workload.dependencies.dispersion`|float|Required when `workload.hasDependencies=true`|`SimulatorFactory#buildSampler`|`\[0,1]` dispersion — lower values bias dependencies closer to the dependent transaction.|
|`workload.dependencies.countMean`|int|Required when `workload.hasDependencies=true`|`SimulatorFactory#buildSampler`|Mean number of dependencies per transaction.|
|`workload.dependencies.countSD`|float|Required when `workload.hasDependencies=true`|`SimulatorFactory#buildSampler`|Standard deviation of dependency count.|
|`workload.dependencies.mandatory`|boolean|Optional|`SimulatorFactory#buildSampler`|If `true`, every transaction gets at least one dependency.|

See `transactions.md` for how `TxConflictRegistry` and `TxDependencyRegistry` consume these.

## Node and PoW

### Node Sampler

| Key | Type | Mandatory? | Consumed in | Meaning |
| --- | --- | --- | --- | --- |
|`node.sampler.file`|String|Optional|`SimulatorFactory#buildSampler`, `NodeSamplerFactory`|Path to a node characteristics CSV. Present → `FileBasedNodeSampler` wrapping `StandardNodeSampler`; absent → `StandardNodeSampler` only.|
|`node.sampler.seed`|String (array)|Optional|`SimulatorFactory#buildSampler`, `NodeSamplerFactory`|Comma-separated seed chain, e.g. `{444,222}`. Used by `SeedManager` to cycle seeds.|
|`node.sampler.seedUpdateTimes`|String (array)|Optional|`SimulatorFactory#buildSampler`, `NodeSamplerFactory`|Comma-separated simulation times (ms), e.g. `{2500}`, at which `Event\_SeedUpdate` events are scheduled.|
|`node.sampler.updateSeedFlags`|String (array)|Required when `node.sampler.seedUpdateTimes` is set|`SimulatorFactory#buildSampler`, `NodeSamplerFactory`|Comma-separated booleans, one per seed in `node.sampler.seed`. `true` → that seed is offset by `simID` when activated (enables finality-analysis divergence).|

### Node Energy and Cost

| Key | Type | Mandatory? | Consumed in | Meaning |
| --- | --- | --- | --- | --- |
|`node.electricPowerMean`|float|Yes|`NodeSamplerFactory`|Mean per-node power consumption (Watts).|
|`node.electricPowerSD`|float|Yes|`NodeSamplerFactory`|Standard deviation of per-node power consumption.|
|`node.electricCostMean`|float|Yes|`NodeSamplerFactory`|Mean electricity cost (currency/kWh).|
|`node.electricCostSD`|float|Yes|`NodeSamplerFactory`|Standard deviation of electricity cost.|

### Proof-of-Work Parameters

| Key | Type | Mandatory? | Consumed in | Meaning |
| --- | --- | --- | --- | --- |
|`pow.hashPowerMean`|float|Yes|`NodeSamplerFactory`|Mean node hash power (hashes/sec, despite the "GH/s" unit docs in some subclasses — the formula in `StandardNodeSampler` treats it as `hashPower × 1e9`).|
|`pow.hashPowerSD`|float|Yes|`NodeSamplerFactory`|Standard deviation of node hash power.|
|`pow.difficulty`|double|Yes|`NodeSamplerFactory`|PoW difficulty (search-space / success-space). Feeds the exponential mining-interval formula in `StandardNodeSampler`.|

See `samplers.md` for the full description of how these keys parameterize the node sampler and how seed updates are scheduled.

## Reporter

### Standard Report Toggles

| Key | Type | Mandatory? | Consumed in | Meaning |
| --- | --- | --- | --- | --- |
|`reporter.reportEvents`|boolean|Yes|`ConfigInitializer`|Enables `EventLog` output.|
|`reporter.reportTransactions`|boolean|Yes|`ConfigInitializer`|Enables `Input` (transaction) output.|
|`reporter.reportNodes`|boolean|Yes|`ConfigInitializer`|Enables `Nodes` output.|
|`reporter.reportNetEvents`|boolean|Yes|`ConfigInitializer`|Enables `NetLog` output.|
|`reporter.reportBeliefs`|boolean|Yes|`ConfigInitializer`|Enables long-form belief output.|
|`reporter.reportBeliefsShort`|boolean|Optional|`ConfigInitializer`|Enables short-form belief output.|
|`reporter.reportSampleTransactionsOnly`|boolean|Optional|`ConfigInitializer`|If `true`, transaction reporting is filtered down to `workload.sampleTransaction`.|

### Per-Event Type Toggles (Fine-Grained Event Log)

When `reporter.reportEvents` is on, each of these toggles controls whether a specific event subclass contributes a row. All are read through `getOptionalPropertyBoolean` (missing → `false`).

| Key | Type | Mandatory? | Consumed in | Meaning |
| --- | --- | --- | --- | --- |
|`reporter.events.newTransactionArrival`|boolean|Optional|`ConfigInitializer`|`Event\_NewTransactionArrival` contributes to the event log.|
|`reporter.events.transactionPropagation`|boolean|Optional|`ConfigInitializer`|`Event\_TransactionPropagation` contributes to the event log.|
|`reporter.events.containerArrival`|boolean|Optional|`ConfigInitializer`|`Event\_ContainerArrival` contributes to the event log.|
|`reporter.events.containerValidation`|boolean|Optional|`ConfigInitializer`|`Event\_ContainerValidation` contributes to the event log.|
|`reporter.events.seedUpdate`|boolean|Optional|`ConfigInitializer`|`Event\_SeedUpdate` contributes to the event log.|
|`reporter.events.belief`|boolean|Optional|`ConfigInitializer`|`Event\_Report\_BeliefReport` contributes to the event log.|

See `events.md` for the per-event-class behavior gated on these flags.

### Periodic and Time-Advancement Reports

| Key | Type | Mandatory? | Consumed in | Meaning |
| --- | --- | --- | --- | --- |
|`reporter.enablePeriodicReports`|boolean|Optional|`ConfigInitializer`|Enables per-node `periodicReport()` calls from inside `Event#happen(...)`.|
|`reporter.enableTimeAdvancementReports`|boolean|Optional|`ConfigInitializer`|Enables per-node `timeAdvancementReport()` calls from inside `Event#happen(...)`.|
|`reporter.reportingWindow`|long|Required when periodic reports are enabled|`Event#happen(...)`|Periodic reports fire every `N` events where `N` is this value (e.g. `100000` → every 100,000 events).|

### Belief Report Scheduling

| Key | Type | Mandatory? | Consumed in | Meaning |
| --- | --- | --- | --- | --- |
|`reporter.beliefReportInterval`|long|Yes (when belief reports are scheduled)|`SimulatorFactory`|Interval (ms) between scheduled `Event\_Report\_BeliefReport` events.|
|`reporter.beliefReportOffset`|long|Yes (when belief reports are scheduled)|`SimulatorFactory`|Offset (ms) added to `Simulation#getLatestKnownEventTime()` to extend the scheduling horizon past the last workload event.|

See `reporting.md` for how the above keys drive the output files and formats.

