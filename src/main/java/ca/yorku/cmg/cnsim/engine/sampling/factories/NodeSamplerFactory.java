package ca.yorku.cmg.cnsim.engine.sampling.factories;

import ca.yorku.cmg.cnsim.engine.Debug;
import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.event.Event_SeedUpdate;
import ca.yorku.cmg.cnsim.engine.sampling.Sampler;
import ca.yorku.cmg.cnsim.engine.sampling.filesamplers.FileBasedNodeSampler;
import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractNodeSampler;
import ca.yorku.cmg.cnsim.engine.sampling.standardsamplers.StandardNodeSampler;

public class NodeSamplerFactory {
	
	
	public AbstractNodeSampler getSampler(
			String path,
			String seedChain,
			String changeTimes,
			String updateFlags,
			Sampler sampler,
			Simulation sim
			) throws Exception {
		
        //Check requirements
        
		boolean hasPath = (path != null);
	    	
		
        boolean hasNodeSeeds = false;
        long seeds[] = null;
        boolean flags[] = null;
        if ((seedChain != null && !seedChain.isEmpty())) {
        	seeds = Config.parseStringToArray(seedChain);
        	hasNodeSeeds = true;
        }
        
        boolean hasSwitchTimes = false;  
        long switchTimes[] = null;
        if ((seedChain != null && !seedChain.isEmpty())) {
        	hasSwitchTimes = true;
        	switchTimes = Config.parseStringToArray(changeTimes);
        	flags = Config.parseStringToBoolean(updateFlags);
        }


        //TODO: Validation code
    	
    	AbstractNodeSampler nodeSampler;
        
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
