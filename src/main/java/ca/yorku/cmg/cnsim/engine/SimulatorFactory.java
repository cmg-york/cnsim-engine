package ca.yorku.cmg.cnsim.engine;

import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.network.AbstractNetwork;
import ca.yorku.cmg.cnsim.engine.network.FileBasedEndToEndNetwork;
import ca.yorku.cmg.cnsim.engine.network.RandomEndToEndNetwork;
import ca.yorku.cmg.cnsim.engine.node.NodeSet;
import ca.yorku.cmg.cnsim.engine.node.PoWNodeSet;
import ca.yorku.cmg.cnsim.engine.reporter.ReportEventFactory;
import ca.yorku.cmg.cnsim.engine.sampling.Sampler;
import ca.yorku.cmg.cnsim.engine.sampling.factories.NetworkSamplerFactory;
import ca.yorku.cmg.cnsim.engine.sampling.factories.NodeSamplerFactory;
import ca.yorku.cmg.cnsim.engine.sampling.factories.TransactionSamplerFactory;
import ca.yorku.cmg.cnsim.engine.transaction.TransactionWorkload;
import ca.yorku.cmg.cnsim.engine.transaction.TxConflictRegistry;
import ca.yorku.cmg.cnsim.engine.transaction.TxDependencyRegistry;


/**
 * A factory class responsible for constructing and assembling all the main components
 * of a {@linkplain Simulation} instance. This includes samplers, node sets, networks,
 * transaction workloads, and reporting schedules.
 * <p>
 * The {@code SimulatorFactory} acts as a blueprint for simulation initialization:
 * it configures the structure and dependencies of a simulation using parameters
 * drawn from {@linkplain Config}. Subclasses define how node sets are created by
 * implementing {@linkplain #createNodeSet(Simulation)}. Subclasses can also override any other component creation methods.
 * </p>
 * <p>
 * The overall lifecycle managed by this factory is:
 * <ol>
 *     <li>Create and attach a {@linkplain Sampler} to the {@linkplain Simulation}.</li>
 *     <li>Add node, network, and transaction samplers to the sampler.</li>
 *     <li>Create a {@linkplain PoWNodeSet} using the subclass’s implementation.</li>
 *     <li>Build and attach a network.</li>
 *     <li>Create and schedule a transaction workload.</li>
 *     <li>Schedule periodic belief reports.</li>
 *     <li>Apply a hard termination time for the simulation.</li>
 * </ol>
 *
 * This class follows a <strong>template method</strong> pattern: {@linkplain #createSimulation(int)}
 * defines the high-level assembly algorithm, while subclasses provide concrete
 * details (such as how the node set is created).
 *
 * @author
 *   Sotirios Liaskos for the Conceptual Modeling Group @ York University
 */
public abstract class SimulatorFactory {

	
	
	// --------------------------------------------------------------
	// COMPONENT CONSTRUCTION METHODS
	// --------------------------------------------------------------
	
	
    /**
     * Adds and configures the node sampler for the given simulation.
     * <p>
     * The node sampler determines how nodes are selected or instantiated during
     * simulation setup, according to parameters defined in {@linkplain Config}:
     * <ul>
     *     <li>{@code node.sampler.file}</li>
     *     <li>{@code node.sampler.seed}</li>
     *     <li>{@code node.sampler.seedUpdateTimes}</li>
     *     <li>{@code node.sampler.updateSeedFlags}</li>
     * </ul>
     *
     * @param s the {@linkplain Simulation} to which the node sampler will be attached
     */
	public void addNodeSampler(Simulation s) {
		try {
			s.getSampler().setNodeSampler(
					new NodeSamplerFactory().getSampler
					(
							Config.getPropertyString("node.sampler.file"),
							Config.getPropertyString("node.sampler.seed"),
							Config.getPropertyString("node.sampler.seedUpdateTimes"),
							Config.getPropertyString("node.sampler.updateSeedFlags"),
							s.getSampler(),
							s)
					);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

    /**
     * Adds and configures the network sampler for the given simulation.
     * <p>
     * The network sampler governs how communication links or network structures
     * are sampled or generated. It reads configuration parameters such as:
     * <ul>
     *     <li>{@code net.sampler.seed}</li>
     *     <li>{@code net.sampler.seed.updateSeed}</li>
     * </ul>
     *
     * @param s the {@linkplain Simulation} to which the network sampler will be attached
     */
	public void addNetworkSampler(Simulation s) {
		s.getSampler().setNetworkSampler
		(
				new NetworkSamplerFactory().getNetworkSampler
				(
						(Config.hasProperty("net.sampler.seed") ? Config.getPropertyLong("net.sampler.seed") : null),
						(Config.hasProperty("net.sampler.seed.updateSeed") ? Config.getPropertyBoolean("net.sampler.seed.updateSeed") : null),
						s.getSampler(),s
						)
				);
	}

    /**
     * Adds and configures the transaction sampler for the given simulation.
     * <p>
     * The transaction sampler defines how workload transactions are selected or
     * constructed, based on configuration entries such as:
     * <ul>
     *     <li>{@code workload.sampler.file}</li>
     * </ul>
     *
     * @param s the {@linkplain Simulation} to which the transaction sampler will be attached
     */
	public void addTransactionSampler(Simulation s) {
		try {
			s.getSampler().setTransactionSampler
			(
					new TransactionSamplerFactory().getSampler
					(
							Config.getPropertyString("workload.sampler.file"),
							s.getSampler(),
							s
							)
					);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	/** 
    * Creates the {@linkplain NodeSet} for the given simulation.
    * <p>
    * Subclasses must implement this method to define how simulation nodes
    * are instantiated or configured.
    *
    * @param s the {@linkplain Simulation} for which the node set is created
    * @return the {@linkplain NodeSet} representing all participating nodes
    */
	public abstract NodeSet createNodeSet(Simulation s);

    /**
     * Creates and attaches the network component to the given simulation.
     * <p>
     * If {@code net.sampler.file} is defined in the configuration, a
     * {@linkplain FileBasedEndToEndNetwork} is created from that file.
     * Otherwise, a {@linkplain RandomEndToEndNetwork} is generated based on
     * the sampler.
     *
     * @param s  the simulation to which the network will be added
     * @param ns the {@linkplain NodeSet} containing all nodes participating in the network
     */
	public void addNetwork(Simulation s, NodeSet ns) {
		AbstractNetwork net = null;
		String netFilePath = Config.getPropertyString("net.sampler.file");
		if (netFilePath != null) {
			try {
				net = new FileBasedEndToEndNetwork(ns, netFilePath);
			} catch (Exception e) {
				e.printStackTrace();
			}
		} else {
			try {
				net = new RandomEndToEndNetwork(ns, s.getSampler());
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		s.setNetwork(net);
	}
	
    /**
     * Creates a transaction workload and schedules it within the simulation.
     * <p>
     * The number of transactions appended is determined by the
     * {@code workload.numTransactions} property in {@linkplain Config}.
     *
     * @param s the {@linkplain Simulation} for which to schedule the transaction workload
     */
	private void addAndScheduleTransactionWorkload(Simulation s) {
		TransactionWorkload ts = new TransactionWorkload(s.getSampler());
		try {
			ts.appendTransactions(Config.getPropertyLong("workload.numTransactions"));
		} catch (Exception e) {
			e.printStackTrace();
		}
		s.schedule(ts);
		
		//Keep also a pointer to the workload.
		s.setWorkload(ts);
	}
	
	/**
	 * Creates a conflict registry for transactions if conflicts are enabled
	 * in the configuration.
	 * <p>
	 * The conflict registry is populated based on the parameters:
	 * <ul>
	 *     <li>{@code workload.hasConflicts}</li>
	 *     <li>{@code workload.conflicts.dispersion}</li>
	 *     <li>{@code workload.conflicts.likelihood}</li>
	 * </ul>
	 *
	 * The method creates a conflict registry object based on the size of the current workload. 
	 * It populates it based on the sampler and the parameters. A reference to the registry is 
	 * given to the simulator for node access.
	 *  
	 * 
	 * @param s the {@linkplain Simulation} for which to create the conflict registry
	 */
	private void createConflictRegistry(Simulation s) {
		if (Config.hasProperty("workload.hasConflicts")) { 
			if (Config.getPropertyBoolean("workload.hasConflicts")) {
				//Get the conflict sampling calculation parameters
				double dispersion = Config.getPropertyDouble("workload.conflicts.dispersion");
				double likelihood = Config.getPropertyDouble("workload.conflicts.likelihood");
				int N = s.getWorkload().getCount();
				
				//Create the registry of the appropriate size:
				TxConflictRegistry registry = new TxConflictRegistry(N);
				
				//Update the registry with random conflicts
				s.getWorkload().updateConflicts(registry, dispersion, likelihood);
				
				//set the registry to the simulation object for use by nodes.
				s.setConflictRegistry(registry);
				
				//System.err.println("Registry says: " + registry.toString());
			}
		}
	}
	
	
	
	private void createDependencyRegistry(Simulation s) {
		if (Config.hasProperty("workload.hasDependencies")) { 
			if (Config.getPropertyBoolean("workload.hasDependencies")) {
				float dispersion = Config.getPropertyFloat("workload.dependencies.dispersion");
				int countMean = Config.getPropertyInt("workload.dependencies.countMean");
				float countSD = Config.getPropertyFloat("workload.dependencies.countSD");
				
				int N = s.getWorkload().getCount();
				
				//Create the registry of the appropriate size:
				TxDependencyRegistry registry = new TxDependencyRegistry(N);
				
				//Update the registry with random conflicts
				s.getWorkload().updateDependencies(registry, dispersion, countMean, countSD);
				
				//set the registry to the simulation object for use by nodes.
				s.setDependencyRegistry(registry);
			}
		}
	}
	
	
	/**
	 * Sets a hard termination time for the simulation based on the
	 * {@code sim.terminate.atTime} property in {@linkplain Config}.
	 *
	 * @param s the {@linkplain Simulation} for which to set the termination time
	 */
	public void setHardTerminationTime(Simulation s) {
        s.setTerminationTime(Config.getPropertyLong("sim.terminate.atTime"));
	}


    /**
     * Schedules periodic belief report events within the simulation.
     * <p>
     * Belief reports summarize internal simulation states and are scheduled
     * using {@linkplain ReportEventFactory}, with parameters:
     * <ul>
     *     <li>{@code reporter.beliefReportInterval}</li>
     *     <li>{@code reporter.beliefReportOffset}</li>
     * </ul>
     *
     * @param s the {@linkplain Simulation} for which belief reporting is configured
     */
	public void scheduleBeliefReports(Simulation s) {
        ReportEventFactory r = new ReportEventFactory();
        r.scheduleBeliefReports_Interval(Config.getPropertyLong("reporter.beliefReportInterval"), 
        		s, Config.getPropertyLong("reporter.beliefReportOffset"));
	}
	
	
	
	// --------------------------------------------------------------
	// MAIN CONSTRUCTION METHOD
	// --------------------------------------------------------------
	
	
    /**
     * Creates and fully configures a new {@linkplain Simulation} instance.
     * <p>
     * This method encapsulates the entire setup pipeline for a simulation:
     * <ol>
     *     <li>Creates the simulation object.</li>
     *     <li>Initializes and attaches a new {@linkplain Sampler}.</li>
     *     <li>Adds node, network, and transaction samplers.</li>
     *     <li>Builds the {@linkplain NodeSet} (delegated to subclass).</li>
     *     <li>Constructs and attaches a network.</li>
     *     <li>Creates and schedules the transaction workload.</li>
     *     <li>Schedules belief reporting events.</li>
     *     <li>Applies the hard termination time.</li>
     * </ol>
     *
     * @param simID a unique identifier for the simulation
     * @return a fully initialized and ready-to-run {@linkplain Simulation}
     */
	public Simulation createSimulation(int simID) {

		Simulation s = new Simulation(simID);

		// --------------------------------------------------------------
		// SAMPLER DEVELOPMENT
		// --------------------------------------------------------------

		/** Create a Sampler object, which will contain all samplers
		 * (node, network, transaction/workload).
		 * Attach it to the simulator.
		 */
		Sampler sampler = new Sampler();
		s.setSampler(sampler);

		/** Develop sampler 1: Node Sampler */
		addNodeSampler(s);

		/** Develop sampler 2: Network Sampler */
		addNetworkSampler(s);

		/** Develop sampler 3: Transaction Sampler */
		addTransactionSampler(s);

		// --------------------------------------------------------------
		// COMPONENT CONSTRUCTION
		// --------------------------------------------------------------

		/** Create the nodeset, using the node factory and the node sampler */
		NodeSet ns = createNodeSet(s);

		/** Create the network, using the network sampler and the nodeset
		 * add the node set to the network and the network to the simulator */
		addNetwork(s, ns);

		/** Create the transaction workload, using the transaction sampler
		 * add it to the simulator, and schedule the corresponding events */
		addAndScheduleTransactionWorkload(s);
		
		/** Create Conflict Registry 
		 */
		createConflictRegistry(s);

		/** Create Dependency Registry 
		 */
		createDependencyRegistry(s);
		
		/** Schedule belief reporting events */
		scheduleBeliefReports(s);
		
		/** Set the hard termination time of the simulator */
		setHardTerminationTime(s);
		
		return s;

	}
}
