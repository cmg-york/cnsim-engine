package ca.yorku.cmg.cnsim.engine.sampling.factories;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.sampling.Sampler;
import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractNetworkSampler;
import ca.yorku.cmg.cnsim.engine.sampling.standardsamplers.StandardNetworkSampler;

public class NetworkSamplerFactory {
	public AbstractNetworkSampler getNetworkSampler(Long seed, boolean seedFlag, Sampler outerSampler, Simulation sim) {
		AbstractNetworkSampler netSampler;
		netSampler = new StandardNetworkSampler(outerSampler);
		if (seed != null) {
			netSampler.setSeed(seed + (seedFlag ? sim.getSimID() : 0));
		}
		return(netSampler);
    }
}
