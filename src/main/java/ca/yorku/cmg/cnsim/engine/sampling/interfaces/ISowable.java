package ca.yorku.cmg.cnsim.engine.sampling.interfaces;

/**
 * Interface for objects that can be sown with a seed for random number generation.
 * 
 * @author Sotirios Liaskos for the Conceptual Modelling Group, York University
 *
 */
public interface ISowable {
	/**
	 * Set the seed for random number generation.
	 * 
	 * @param seed The seed value.
	 */
	void setSeed(long seed);
}