package ca.yorku.cmg.cnsim.engine.network;

import ca.yorku.cmg.cnsim.engine.Debug;
import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.node.NodeSet;
import ca.yorku.cmg.cnsim.engine.sampling.Sampler;

/**
 * Factory class for creating {@link AbstractNetwork} instances.
 * <p>
 * This class decides at runtime whether to create a file-based network
 * ({@link FileBasedEndToEndNetwork}) or a randomly generated network
 * ({@link RandomEndToEndNetwork}) based on configuration properties.
 * </p>
 * <p>
 * If the configuration property {@code net.sampler.file} is defined, a 
 * {@link FileBasedEndToEndNetwork} is created using the specified file path.
 * Otherwise, a {@link RandomEndToEndNetwork} is created using the provided {@link Sampler}.
 * </p>
 * 
 * @author Sotirios Liaskos for the Conceptual Modeling Group @ York University
 * @see AbstractNetwork
 * @see FileBasedEndToEndNetwork
 * @see RandomEndToEndNetwork
 */
public class NetworkFactory {
	
    /**
     * Creates an {@link AbstractNetwork} instance based on configuration.
     * <p>
     * This method first attempts to create a file-based network if the 
     * configuration property {@code net.sampler.file} exists. If not, 
     * it creates a random network using the provided {@link Sampler}.
     * </p>
     * 
     * @param ns      the {@link NodeSet} representing nodes in the network
     * @param sampler the {@link Sampler} used for generating random throughput values if needed
     * @return an {@link AbstractNetwork} instance (either file-based or random)
     */
	public static AbstractNetwork createNetwork(NodeSet ns, Sampler sampler) {
		
		AbstractNetwork net = null;
		
		// try to read from config file, if available
		String netFilePath = Config.getPropertyString("net.sampler.file");
		if (netFilePath != null) {
			try {
				Debug.p("Creating file-based network.");
				net = new FileBasedEndToEndNetwork(ns, netFilePath);
			} catch (Exception e) {
				e.printStackTrace();
			}
		} else {
			try {
				net = new RandomEndToEndNetwork(ns, sampler);
				Debug.p("Creating random network.");
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		return net;
	}
}
