package ca.yorku.cmg.cnsim.engine.sampling.interfaces;

import java.util.BitSet;
import java.util.Random;

import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.sampling.Sampler;

/*
 * TODO: Complete and reformat comments  
 */

/**
 * A sampler for Transaction objects. Accepts size and value means and standard 
 * deviations and produces random samples of transactions and inter-arrival times.
 *    
 * @author Sotirios Liaskos for the Conceptual Modeling Group @ York University
 */
public abstract class AbstractTransactionSampler implements ISowable {
	
	protected Sampler sampler;
	protected Random random;
	protected long randomSeed;
	
	protected float txArrivalIntervalRate; //How often transactions arrive at the system. 
    protected float txSizeMean;
    protected float txSizeSD;
    protected float txValueMean;
    protected float txValueSD;

    
    
    /*
     * 
     * C O N S T R U C T O R S
     *  
     */
    
    protected AbstractTransactionSampler(){
   		this.random = new Random();
   		random.setSeed(randomSeed);
   		LoadConfig();
    }
    
    
	
    /*
     * 
     * S A M P LI N G   F U N C T I O N S
     *   
     */
	
	
	/**
	 * Returns the next sampled transaction interval in milliseconds.
	 * @return The next sampled transaction interval (msec).
	 * @throws Exception 
	 */
    public abstract float getNextTransactionArrivalInterval() throws Exception;
    
    /**
     * Get a sample transaction fee value.
     * @return Transaction fee value (local tokens).
     * @throws Exception 
     */
    public abstract float getNextTransactionFeeValue() throws Exception;

	/**
	 * Returns a sample of a transaction size in bytes.
	 * @return The generated transaction size in bytes.
	 * @throws Exception 
	 */
    public abstract long getNextTransactionSize() throws Exception;

    
	/** 
	 * Returns the next transaction arrival Node.
	 * <p>
	 * Pulls from the file queues; if the file is exhausted, uses the alternative sampler.
	 * </p>
	 * 
	 * @return Node ID
	 * @throws IllegalStateException if the file is exhausted and no alternative sampler is defined
	 */
	public abstract int getArrivalNode() throws IllegalStateException;
    
    
	/**
	 * Return a random number from min to max (inclusive)
	 * @param min The minimum. 
	 * @param max The maximum. 
	 * @return The random integer
	 */
    public abstract int getRandomNum(int min, int max);


    /**
     * Pick a random match for a given ID with distance bias controlled by alpha.
     * 
     * @param id    Target ID (1 .. N)
     * @param N     Total number of IDs (ignored if conflict comes predefined)
     * @param dispersion Closeness parameter [0,1]:
     *              0 -> almost always near 'id'
     *              1 -> can pick anywhere in range (near edges possible)
     *              (ignored if conflict comes predefined)
     * @param likelihood The likelihood that the transaction has a conflict.
     * @return      Chosen matching ID
     */
    public abstract int getConflict(int id, int N, double dispersion, double likelihood);



    public abstract BitSet randomDependencies(int id, boolean mandatory, float dispersion, int countMean, float countSD);

    
    /*
     * 
     * S E E D   M A N A G E M E N T  
     * 
     */
    
    /**
     * Move to the next seed on the list 
     */
    public abstract void updateSeed();
    
    /**
     * The transaction at which seed is automatically going to update 
     */
    public abstract long getSeedChangeTx();

    /**
     * Enable seed updating 
     */
    public abstract boolean seedUpdateEnabled();
	

	
    // -----------------------------------------------------------------
    // CONFIGURATION
    // -----------------------------------------------------------------

    /**
     * Loads configuration values from {@linkplain Config} for transaction sampling.
     */
    public void LoadConfig() {
        this.setTxArrivalIntervalRate(Config.getPropertyFloat("workload.lambda")); 
        this.setTxSizeMean(Config.getPropertyFloat("workload.txSizeMean"));
        this.setTxSizeSD(Config.getPropertyFloat("workload.txSizeSD"));
        this.setTxFeeValueMean(Config.getPropertyFloat("workload.txFeeValueMean"));
        this.setTxFeeValueSD(Config.getPropertyFloat("workload.txFeeValueSD"));
    }

	
    
    
    /*
     * 
     * G E T T E R S   A N D   S E T T E R S    
     * 
     */
    

	/**
	 * Returns the transaction arrival rate (in the entire system, arriving in random nodes) in transactions per second (Tx/sec) 
	 * @return Transaction arrival rate in Tx/sec
	 */
	public float getTxArrivalIntervalRate() {
        return txArrivalIntervalRate;
    }

	/**
	 * Sets the transaction arrival rate (in the entire system, arriving in random nodes) in transactions per second (Tx/sec)
	 * @param txArrivalIntervalRate Transaction arrival rate in Tx/sec
	 */
	public void setTxArrivalIntervalRate(float txArrivalIntervalRate) {
    	if(txArrivalIntervalRate < 0)
    		throw new ArithmeticException("Transaction Arrival Interval Rate < 0");
        this.txArrivalIntervalRate = txArrivalIntervalRate;
    }
	
	/**
	 * Returns the mean transaction size in bytes 
	 * @return The mean transaction size in bytes
	 */
	public float getTxSizeMean() {
        return txSizeMean;
    }

	/**
	 * Sets the mean transaction size in bytes
	 * @param txSizeMean The mean transaction size in bytes  
	 */
	public void setTxSizeMean(float txSizeMean) {
    	if(txSizeMean < 0)
    		throw new ArithmeticException("Transaction size mean < 0");
        this.txSizeMean = txSizeMean;
    }

	/**
	 * Returns the standard deviation of transaction sizes in bytes
	 * @return The standard deviation in transaction sizes in bytes
	 */
	public float getTxSizeSD() {
        return txSizeSD;
    }

	/**
	 * Sets the standard deviation of transaction sizes in bytes
	 * @param txSizeSD The standard deviation in transaction sizes in bytes
	 */
	public void setTxSizeSD(float txSizeSD) {
    	if(txSizeSD < 0)
    		throw new ArithmeticException("Transaction Size Standard Deviation < 0");
        this.txSizeSD = txSizeSD;
    }

	/**
	 * Returns the mean transaction fee value.
	 *
	 * @return The mean transaction fee value (local tokens).
	 */
	public float getTxFeeValueMean() {
        return txValueMean;
    }
	
	/**
	 * Sets the mean transaction fee value.
	 *
	 * @param txValueMean The mean transaction fee value to be set (local tokens).
	 * @throws ArithmeticException if the provided value is less than 0.
	 */
	public void setTxFeeValueMean(float txValueMean) {
    	if(txValueMean < 0)
    		throw new ArithmeticException("Transaction Value Mean < 0");
        this.txValueMean = txValueMean;
    }
	
	/**
	 * Returns the standard deviation of transaction fee value.
	 *
	 * @return The standard deviation of transaction fee value (in local tokens).
	 */
	public float getTxFeeValueSD() {
        return txValueSD;
    }
	
	/**
	 * Sets the standard deviation of transaction fee value.
	 *
	 * @param txValueSD The standard deviation of transaction fee value to be set.
	 * @throws ArithmeticException if the provided value is less than 0.
	 */
	public void setTxFeeValueSD(float txValueSD) {
    	if(txValueSD < 0)
    		throw new ArithmeticException("Transaction Value Standard Deviation < 0");
        this.txValueSD = txValueSD;
    }
	
    public Sampler getSampler() {
		return sampler;
	}

	public void setSampler(Sampler sampler) {
		this.sampler = sampler;
	}
	
	public Random getRandom() {
		return random;
	}

	public void setRandom(Random random) {
		this.random = random;
	}
	
    public void setSeed(long seed) {
    	randomSeed = seed;
    	random.setSeed(seed);
    }

	
}
