package ca.yorku.cmg.cnsim.engine.sampling.interfaces;
 /**
 * Interface for objects that can update their seed for random number generation.
 * 
 * @author Sotirios Liaskos for the Conceptual Modelling Group, York University
 *
 */
public interface IMultiSowable {
	/**
	 * Update the seed for random number generation. Implementations should define how the seed is updated (e.g. based on a preset list of values).
	 */
	public void updateSeed();	
}