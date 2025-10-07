package ca.yorku.cmg.cnsim.engine.sampling;

import java.util.Arrays;
import java.util.Random;

/**
 * Manages a circular sequence of random seeds for simulations.
 * <p>
 * A {@code SeedManager} maintains:
 * <ul>
 *   <li>An array of base seeds ({@code seedArray})</li>
 *   <li>A set of update flags ({@code seedUpdateFlags}) that determine whether
 *       to offset the seed with the simulation ID</li>
 *   <li>A pointer ({@code currentIndex}) that cycles through the seeds</li>
 * </ul>
 *
 * This allows simulations to have reproducible but configurable randomness
 * across different runs, while ensuring that each simulation instance
 * (distinguished by {@code simID}) can get unique seeds if desired.
 *
 * Typical usage:
 * <pre>{@code
 * SeedManager manager = new SeedManager(
 *     new long[]{1234L, 5678L, 9012L},
 *     new boolean[]{true, false, true},
 *     42 // simulation ID
 * );
 * 
 * Random rng = new Random();
 * manager.updateSeed(rng); // seeds RNG with the next managed seed
 * }</pre>
 */
public class SeedManager {
	
	/** Array of base seeds, cycled through sequentially. */
	private long[] seedArray = null;
	
	/** Flags indicating whether to offset each seed by the simulation ID. 
	 * Ensures different seeds for different simulations */
	private boolean[] seedUpdateFlags = null;

	/** Current position in the seed array. */
	private int currentIndex = 0;
	
	/** Simulation identifier, used to offset seeds if flag in
	 * {@linkplain SeedManager#seedUpdateFlags} is set. */
	private int simID = 0;


	/*
	 * 
	 * C O N S T R U C T OR S
	 * 
	 */
		
    /** Default constructor (empty seed manager). */
	public SeedManager () {
	}

    /**
     * Constructs a SeedManager with the given seed array, flag array, and simulation ID.
     *
     * @param seedChain   the base seed array
     * @param flagArray   the update flags corresponding to each seed
     * @param sID         the simulation ID
     */
	public SeedManager (long[] seedChain, boolean[] flagArray, int sID) {
		super();
		seedArray = seedChain;
		seedUpdateFlags = flagArray;
		simID = sID;
	}


	 /**
     * Computes the next seed in the sequence.
     * <p>
     * The seed is computed as:
     * <pre>
     *   baseSeed + (flag ? simID : 0)
     * </pre>
     * where {@code baseSeed} is the current element of {@code seedArray},
     * and {@code flag} is the corresponding element in {@code seedUpdateFlags}.
     * After use, the index advances circularly.
     *
     * @return the next seed value
     */
	protected long nextSeed() {
		long newSeed = seedArray[currentIndex] + (seedUpdateFlags[currentIndex] ? simID : 0);
		currentIndex = (currentIndex + 1) % seedArray.length;
		return newSeed;
	}

    /**
     * Updates the given {@link Random} instance with the next managed seed.
     *
     * @param random the random number generator to reseed
     */
	public void updateSeed(Random random) {
		long randomSeed = nextSeed();
		random.setSeed(randomSeed);
	}
	

	/*
	 * 
	 * G E T T E R S  A N D  S E T T E R S 
	 * 
	 */
	
	public int getSimD() {
		return simID;
	}

	public void setSimD(int simD) {
		this.simID = simD;
	}
	
	public String getSeedUpdateFlag() {
		return Arrays.toString(seedUpdateFlags);
	}

	public void setSeedUpdateFlag(boolean[] seedUpdateFlag) {
		this.seedUpdateFlags = seedUpdateFlag;
	}

	protected void setSeedArray(long[] seedChain) {
		seedArray = seedChain;		
	}

	public String getSeedArray() {
		return(Arrays.toString(seedArray));
	}

}
