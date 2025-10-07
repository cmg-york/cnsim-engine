package ca.yorku.cmg.cnsim.engine.sampling.factories;

import ca.yorku.cmg.cnsim.engine.Debug;
import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.event.Event_SeedUpdate;
import ca.yorku.cmg.cnsim.engine.sampling.Sampler;
import ca.yorku.cmg.cnsim.engine.sampling.filesamplers.FileBasedNodeSampler;
import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractNodeSampler;
import ca.yorku.cmg.cnsim.engine.sampling.standardsamplers.StandardNodeSampler;


/**
 * Factory class responsible for constructing and configuring instances of {@linkplain AbstractNodeSampler} used in simulation runs.
 * <p>
 * The {@code NodeSamplerFactory} determines whether a {@linkplain FileBasedNodeSampler file-based} or {@linkplain StandardNodeSampler standard} node sampler should be used based on the provided configuration parameters. It also supports dynamic seed switching by scheduling {@linkplain Event_SeedUpdate seed update events} during the simulation lifecycle.
 * </p>
 *
 * <p>Key responsibilities:</p>
 * <ul>
 *   <li>Selecting the sampler type (file-based or standard) based on whether a file path is provided.</li>
 *   <li>Parsing and applying initial seed chains, update flags, and switchover times from configuration strings.</li>
 *   <li>Scheduling {@linkplain Event_SeedUpdate seed update events} when time-based reseeding is configured.</li>
 * </ul>
 *
 * <p>Example usage:</p>
 * <pre>{@code
 * NodeSamplerFactory factory = new NodeSamplerFactory();
 * AbstractNodeSampler sampler = factory.getSampler(
 *         "nodes.csv",
 *         "100,200,300",
 *         "5000,10000",
 *         "true,false",
 *         outerSampler,
 *         simulation);
 * }</pre>
 *
 * @author Sotirios Liaskos for the Conceptual Modeling Group @ York University
 * @see AbstractNodeSampler
 * @see FileBasedNodeSampler
 * @see StandardNodeSampler
 * @see Event_SeedUpdate
 * @see Config
 * @see Simulation
 */
public class NodeSamplerFactory {
	
	   /**
     * Creates and configures an {@linkplain AbstractNodeSampler} instance based on the given parameters.
     * <p>
     * Depending on the supplied arguments, this method will instantiate either a {@linkplain FileBasedNodeSampler} or a {@linkplain StandardNodeSampler}. It also handles optional configuration of seed chains, update flags, and switchover events to support dynamic reseeding during simulation execution.
     * </p>
     *
     * @param path the path to a node sampling file; if {@code null}, a random sampling strategy is used
     * @param seedChain a comma-separated list of seeds to be used sequentially during simulation; may be {@code null} or empty if no seed chaining is desired
     * @param changeTimes a comma-separated list of timestamps at which the sampler should switch to the next seed; only applicable when {@code seedChain} is defined FIXME: is this simulation times or transaction ids?
     * @param updateFlags a comma-separated list of boolean flags indicating whether each seed should be modulated by simulation ID; must align with {@code changeTimes}
     * @param sampler the outer {@linkplain Sampler sampler} providing higher-level sampling context
     * @param sim the {@linkplain Simulation simulation} instance in which the sampler operates; used to obtain the simulation ID and to schedule {@linkplain Event_SeedUpdate events}
     * @return a fully configured {@linkplain AbstractNodeSampler} ready for use
     * @throws Exception if inconsistent configuration is detected (e.g., seed update times provided without seed definitions)
     */
	public AbstractNodeSampler getSampler(
			String path,
			String seedChain,
			String changeTimes,
			String updateFlags,
			Sampler sampler,
			Simulation sim
			) throws Exception {
		
		
    	AbstractNodeSampler nodeSampler;
		
        //Check requirements and initialize
		boolean hasPath = (path != null);
        boolean hasNodeSeeds = false;
        long seeds[] = null;
        boolean flags[] = null;
        
        
        // Fetch the seedchain. 
        // The seedchain is a comma-separated list of seeds to alternate between.
        if ((seedChain != null && !seedChain.isEmpty())) {
        	seeds = Config.parseStringToArray(seedChain);
        	hasNodeSeeds = true;
        }
        
        
        // Fetch the switchtimes. It is a comma-separated list of times at which to switch to the next seed in the seedchain.
        // The flags are a comma-separated list of booleans indicating whether to superimpose SimID to the seed.
        boolean hasSwitchTimes = false;  
        long switchTimes[] = null;
        if ((seedChain != null && !seedChain.isEmpty())) {
        	hasSwitchTimes = true;
        	switchTimes = Config.parseStringToArray(changeTimes);
        	flags = Config.parseStringToBoolean(updateFlags);
        }


        
        
        // ===== VALIDATION =====
        if (hasSwitchTimes) {
            if (!hasNodeSeeds) {
            	Debug.e("NodeSamplerFactory: seed switch times provided but no seeds defined. Check 'seedChain' configuration.");
                throw new Exception(
                    "NodeSamplerFactory: seed switch times provided but no seeds defined. " +
                    "Check 'seedChain' configuration."
                );
            }
            if (flags != null && flags.length != seeds.length) {
            	Debug.e("NodeSamplerFactory: number of updateFlags (" + flags.length +
					") does not match number of seeds (" + seeds.length + ").");
                throw new Exception(
                    "NodeSamplerFactory: number of updateFlags (" + flags.length +
                    ") does not match number of seeds (" + seeds.length + ")."
                );
            }
        }

         
        if (hasPath) {
        	if (hasNodeSeeds) {
        		nodeSampler = new FileBasedNodeSampler(path, new StandardNodeSampler(sampler,seeds,flags,sim.getSimID()));
        	} else {
        		nodeSampler = new FileBasedNodeSampler(path, new StandardNodeSampler(sampler));
        	}
        } else {
        	if (hasNodeSeeds) {
        		nodeSampler = new StandardNodeSampler(sampler,seeds,flags,sim.getSimID());
        	} else {
        		nodeSampler = new StandardNodeSampler(sampler);
        	}
        }
        
        //Schedule the switchover events
        //TODO-JIRA: Organize error handling and reporting
    	if (hasSwitchTimes) {
    		if (!hasNodeSeeds) {
    			throw new Exception("Error in NodeSamplerFactory: seed switch times given (" + Config.getPropertyString("node.sampler.seedUpdateTimes") +  ") but not seeds to switch around.");
    		} else {
    	        //Schedule seed change events
    	        for (int i = 0; i < switchTimes.length; i++) {
    	        	Debug.p("    Scheduling sampler with chain [...] to swich to next seed at " + switchTimes[i]);
    	            sim.schedule(new Event_SeedUpdate(nodeSampler, switchTimes[i]));
    	        }
    		}
    	}
    	
    	return(nodeSampler);
   
	}
}
