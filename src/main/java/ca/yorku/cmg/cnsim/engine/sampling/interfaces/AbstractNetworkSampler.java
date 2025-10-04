package ca.yorku.cmg.cnsim.engine.sampling.interfaces;

import java.util.Random;

import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.sampling.Sampler;


/**
 * Abstract base class for network throughput sampling in a simulation environment.
 * <p>
 * Provides a framework for generating random samples of network throughput between nodes,
 * based on configurable mean and standard deviation. Concrete implementations must provide
 * a method to sample the next connection throughput.
 * <p>
 * Uses {@linkplain Random} for random number generation and {@linkplain Sampler} for statistical sampling.
 * 
 * @author Sotirios Liaskos
 * @see Sampler
 * @see ISowable
 */
public abstract class AbstractNetworkSampler implements ISowable {
	
    /** Sampler used for generating statistical samples */
    protected Sampler sampler;

    /** Random number generator */
    protected Random random = new Random();

    /** Seed used to initialize the random generator */
    protected long randomSeed;

    /** Mean network throughput in bits per second (bps) */
    protected float netThroughputMean;

    /** Standard deviation of network throughput in bits per second (bps) */
    protected float netThroughputSD;   

    
    // -----------------------------------------------------------------
    // CONSTRUCTORS
    // -----------------------------------------------------------------

    /**
     * Default constructor.
     * <p>
     * Loads configuration values from {@linkplain Config}.
     * </p>
     */
    public AbstractNetworkSampler() {
    	LoadConfig();
    }
    
     
    /**
     * Constructs an {@linkplain AbstractNetworkSampler} with specified mean and standard deviation.
     *
     * @param netThroughputMean The mean network throughput (bps)
     * @param netThroughputSD   The standard deviation of network throughput (bps)
     * @param sampler           The {@linkplain Sampler} to use for generating random samples
     * @throws ArithmeticException if any of the provided values are less than 0
     */
    public AbstractNetworkSampler(float netThroughputMean, 
    		float netThroughputSD,
    		Sampler sampler) {

        if(netThroughputMean < 0)
    		throw new ArithmeticException("Network Throughput Mean < 0");
        this.netThroughputMean = netThroughputMean;
        if(netThroughputSD < 0)
    		throw new ArithmeticException("Network Throughput Standard Deviation < 0");
        this.netThroughputSD = netThroughputSD;

    }
    
    

    
    
    // -----------------------------------------------------------------
    // SAMPLING ROUTINES
    // -----------------------------------------------------------------

    /**
     * Returns a sampled network throughput for an arbitrary node-to-node connection.
     * <p>
     * Concrete subclasses must implement this method using the configured mean and
     * standard deviation.
     * </p>
     *
     * @return the throughput value in bits per second (bps)
     */
    public abstract float getNextConnectionThroughput();
    
    

    // -----------------------------------------------------------------
    // GETTERS AND SETTERS
    // -----------------------------------------------------------------

    /**
     * Returns the mean node-to-node throughput in bits per second (bps).
     *
     * @return the mean throughput of an arbitrary node-to-node connection
     */
	public float getNetThroughputMean() {
        return netThroughputMean;
    }

    /**
     * Sets the mean node-to-node throughput in bits per second (bps).
     *
     * @param netThroughputMean The mean throughput to set
     * @throws ArithmeticException if the provided value is less than 0
     */
	public void setNetThroughputMean(float netThroughputMean) {
    	if(netThroughputMean < 0)
    		throw new ArithmeticException("Network Throughput Mean < 0");
        this.netThroughputMean = netThroughputMean;
    }

    /**
     * Returns the standard deviation of node-to-node throughput in bits per second (bps).
     *
     * @return the standard deviation of an arbitrary node-to-node connection
     */
	public float getNetThroughputSD() {
        return netThroughputSD;
    }

    /**
     * Sets the standard deviation of node-to-node throughput in bits per second (bps).
     *
     * @param netThroughputSD The standard deviation to set
     * @throws ArithmeticException if the provided value is less than 0
     */
	public void setNetThroughputSD(float netThroughputSD) {
    	if(netThroughputSD < 0)
    		throw new ArithmeticException("Network Throughput Standard Deviation < 0");
        this.netThroughputSD = netThroughputSD;
    }

    

    /**
     * Returns the {@linkplain Sampler} used for statistical sampling primitives.
     *
     * @return the sampler instance
     */
	public Sampler getSampler() {
		return sampler;
	}

    /**
     * Sets the {@linkplain Sampler} used for statistical sampling primitives.
     *
     * @param sampler the sampler instance
     */
	public void setSampler(Sampler sampler) {
		this.sampler = sampler;
	}

    /**
     * Returns the {@linkplain Random} number generator used by this sampler.
     *
     * @return the random number generator
     */
	public Random getRandom() {
		return random;
	}

	/**
    * Sets the {@linkplain Random} number generator for this sampler.
    *
    * @param random the random number generator to set
    */
	public void setRandom(Random random) {
		this.random = random;
	}
	
    /**
     * Sets the seed for the random number generator.
     *
     * @param seed the seed value to use
     */
    @Override
	public void setSeed(long seed) {
    	randomSeed = seed;
    	random.setSeed(seed);
    }
    
    
    /**
    * Loads network configuration from {@linkplain Config}.
    * <p>
    * Sets {@code netThroughputMean} and {@code netThroughputSD} from configuration properties:
    * <ul>
    *     <li>{@code net.throughputMean}</li>
    *     <li>{@code net.throughputSD}</li>
    * </ul>
    */
    public void LoadConfig() {
        this.setNetThroughputMean(Config.getPropertyFloat("net.throughputMean"));
        this.setNetThroughputSD(Config.getPropertyFloat("net.throughputSD"));
    }
    
}
