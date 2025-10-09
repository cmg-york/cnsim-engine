package ca.yorku.cmg.cnsim.engine.sampling.standardsamplers;

import ca.yorku.cmg.cnsim.engine.Debug;
import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.sampling.Sampler;
import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractTransactionSampler;
import ca.yorku.cmg.cnsim.engine.transaction.Transaction;


/**
 * A standard implementation of {@link AbstractTransactionSampler}.
 * <p>
 * This sampler provides transaction-level samples for simulation purposes, including:
 * <ul>
 *     <li>Transaction arrival intervals (Poisson distribution)</li>
 *     <li>Transaction fee values (Normal distribution)</li>
 *     <li>Transaction sizes (Normal distribution with lower bound)</li>
 *     <li>Random integers for generic sampling (Uniform distribution)</li>
 * </ul>
 * <p>
 * Supports optional seed updates to enable reproducible random sequences, controlled 
 * by {@code seedUpdateEnabled}, {@code seedSwitchTx}, and {@code simID}.
 * </p>
 * 
 * <p>Author: Sotirios Liaskos for the Conceptual Modeling Group @ York University</p>
 */
public class StandardTransactionSampler extends AbstractTransactionSampler {
	    
	
    /** Simulation ID for reproducible seed updates */
    private int simID;

    /** Transaction ID at which to switch seed */
    private long seedSwitchTx;

    /** Initial seed value */
    private long initialSeed;

    /** Current seed in use */
    private long currentSeed;

    /** Flag to enable/disable seed updates */
    private boolean seedUpdateEnabled = false;
    
    

    // -----------------------------------------------------------------
    // CONSTRUCTORS
    // -----------------------------------------------------------------

    
    /**
     * Constructs a StandardTransactionSampler with the specified {@linkplain Sampler}.
     * Loads configuration from {@linkplain Config}.
     *
     * @param s the Sampler instance to use for generating random samples
     */
    public StandardTransactionSampler(Sampler s) {
    	this.sampler = s;
    	LoadConfig();
    }
	    
    /**
     * Constructs a StandardTransactionSampler with the specified {@linkplain Sampler} 
     * and simulation ID.
     *
     * @param s the Sampler instance to use
     * @param simID the simulation ID for reproducible seed updates
     */
    public StandardTransactionSampler(Sampler s, int simID) {
    	this(s);
    	this.simID = simID;
    }
    
    // -----------------------------------------------------------------
    // SEED MANAGEMENT
    // -----------------------------------------------------------------

    /**
     * Updates the current seed if seed update is enabled and the transaction ID
     * has passed the configured switch point.
     */
    public void updateSeed() {
    	if ((seedUpdateEnabled) && (seedSwitchTx < Transaction.currID - 1)) {
    		currentSeed = this.initialSeed + this.simID;
    		super.random.setSeed(currentSeed);
    		seedUpdateEnabled = false;
    	}
    }

    /**
	 * Returns the current seed in use.
	 * @return the current seed value
	 */
    public long getCurrentSeed() {
    	return this.currentSeed;
    }
    
    
	@Override
	public long getSeedChangeTx() {
		return (this.seedSwitchTx);
	}
    
	@Override
	public boolean seedUpdateEnabled() {
		return (this.seedUpdateEnabled);
	}

	
	

	
	
	// -----------------------------------------------------------------
    // TRANSACTION SAMPLING
    // -----------------------------------------------------------------

    /**
     * Returns a sample of the interval until the next transaction arrives.
     * <p>
     * Uses a Poisson distribution with rate {@code txArrivalIntervalRate}.
     * Interval is returned in milliseconds.
     * </p>
     *
     * @return a sampled transaction arrival interval in milliseconds
     * @throws Exception if sampling fails
     */
	@Override
	public float getNextTransactionArrivalInterval() throws Exception {
    	updateSeed();
		return (float) sampler.getPoissonInterval(txArrivalIntervalRate,random)*1000;
	}
	
    /**
     * Returns a sample of the transaction fee.
     * <p>
     * Uses a Normal (Gaussian) distribution with mean {@code txValueMean} 
     * and standard deviation {@code txValueSD}.
     * </p>
     *
     * @return a sampled transaction fee value
     * @see AbstractTransactionSampler#getNextTransactionFeeValue()
     */
    @Override
    public float getNextTransactionFeeValue() {
        return(sampler.getGaussian(txValueMean, txValueSD, random));
    }

    /**
     * Returns a sample of the transaction size.
     * <p>
     * Uses a Normal distribution with mean {@code txSizeMean} and standard deviation {@code txSizeSD}.
     * A minimum size of 10 is enforced. If a valid sample cannot be generated within 100 tries, 
     * the program exits with an error.
     * </p>
     *
     * @return a sampled transaction size (long)
     * @throws RuntimeException 
     */
    @Override
    public long getNextTransactionSize()  {
    	long result; 
    	long minSize = 10;
    	
    	int maxTries = 100;
    	int tries = 0;
    	
    	do {
    		result = (long) sampler.getGaussian(txSizeMean, txSizeSD, random);
    		tries++;
    	} while ((result < minSize) && (tries < maxTries));
    	
    	if (tries == maxTries) {
    		Debug.e("StandardTransactionSampler: Failed to generate appropriate transaction size after " + tries + " tries. Please check workload.txSizeMean and workload.txSizeSD.");
    		throw new RuntimeException("StandardTransactionSampler: Failed to generate appropriate transaction size after " + tries + " tries. Please check workload.txSizeMean and workload.txSizeSD.");
    	}
        return(result);
    }
    
    /**
     * Returns a random integer between the given bounds (inclusive).
     * <p>
     * Uses a Uniform distribution.
     * </p>
     *
     * @param min the minimum value (inclusive)
     * @param max the maximum value (inclusive)
     * @return a random integer in [min, max]
     * @see AbstractTransactionSampler#getRandom()
     */
    @Override
    public int getRandomNum(int min, int max) {
        return(sampler.getTransactionSampler().getRandom().nextInt((max - min) + 1) + min);
    }

    
    /**
     * Loads configuration values from {@linkplain Config} for transaction sampling.
     * Initializes seed update settings and current/initial seeds.
     */
    @Override
    public void LoadConfig() {
    	super.LoadConfig();
    	this.seedUpdateEnabled = (Config.hasProperty("workload.sampler.seed.updateSeed") ? Config.getPropertyBoolean("workload.sampler.seed.updateSeed") : false);
    	this.seedSwitchTx = (Config.hasProperty("workload.sampler.seed.updateTransaction") ? Config.getPropertyLong("workload.sampler.seed.updateTransaction") : 0);
    	this.currentSeed = (Config.hasProperty("workload.sampler.seed") ? Config.getPropertyLong("workload.sampler.seed") : 0);
    	this.initialSeed = this.currentSeed;
    }

    
    
    // -----------------------------------------------------------------
    // TESING RELATED METHODS
    // -----------------------------------------------------------------

    
    
    /**
     * Sets seed-related configuration for testing purposes.
     *
     * @param initSeed initial seed value
     * @param seedUpdateEnabled whether seed updates are enabled
     * @param seedSwitchTx transaction ID at which seed should switch
     */
    public void nailConfig(long initSeed, boolean seedUpdateEnabled, long seedSwitchTx) {
    	this.seedUpdateEnabled = seedUpdateEnabled;
    	this.seedSwitchTx = seedSwitchTx;
    	this.currentSeed = initSeed;
    	this.initialSeed = this.currentSeed;
    }

}
