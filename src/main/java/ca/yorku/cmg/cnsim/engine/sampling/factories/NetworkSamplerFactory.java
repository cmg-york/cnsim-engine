package ca.yorku.cmg.cnsim.engine.sampling.factories;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.sampling.Sampler;
import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractNetworkSampler;
import ca.yorku.cmg.cnsim.engine.sampling.standardsamplers.StandardNetworkSampler;

/**
 * Factory class for creating instances of {@linkplain AbstractNetworkSampler}.
 * <p>
 * This class encapsulates the logic for constructing network samplers used in 
 * simulation environments. It currently returns a 
 * {@linkplain StandardNetworkSampler standard network sampler}, optionally 
 * initialized with a random seed that can be modified based on the simulation ID.
 * </p>
 * 
 * <p>Usage example:</p>
 * <pre>{@code
 * NetworkSamplerFactory factory = new NetworkSamplerFactory();
 * AbstractNetworkSampler sampler = factory.getNetworkSampler(
 *         42L, true, outerSampler, simulation);
 * }</pre>
 * 
 * @author Sotirios Liaskos for the Conceptual Modeling Group @ York University
 * @see AbstractNetworkSampler
 * @see StandardNetworkSampler
 * @see Simulation
 */
public class NetworkSamplerFactory {
	
	
	 /**
	 * Creates an {@linkplain AbstractNetworkSampler} instance.
	 * <p>
	 * This method constructs a {@linkplain StandardNetworkSampler}, optionally 
	 * initializing it with a seed that can be adjusted based on the simulation ID.
	 * </p>
	 *
	 * @param seed an optional base seed for random number generation; if {@code null}, no seed is set
	 * @param seedFlag if {@code true}, the simulation ID is added to the base seed to ensure variability across simulations
	 * @param outerSampler the outer {@linkplain Sampler sampler} that contains the sampler being created
	 * @param sim the current {@linkplain Simulation simulation} context, used to obtain the simulation ID
	 * @return an initialized {@linkplain AbstractNetworkSampler} ready for use in the simulation
	 */
	public AbstractNetworkSampler getNetworkSampler(Long seed, boolean seedFlag, Sampler outerSampler, Simulation sim) {
		AbstractNetworkSampler netSampler;
		netSampler = new StandardNetworkSampler(outerSampler);
		if (seed != null) {
			netSampler.setSeed(seed + (seedFlag ? sim.getSimID() : 0));
		}
		return(netSampler);
    }
}
