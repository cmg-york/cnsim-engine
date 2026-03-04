package ca.yorku.cmg.cnsim.engine.sampling;

import java.util.Random;

import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractNetworkSampler;
import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractNodeSampler;
import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractTransactionSampler;

/*
 * TODO: Complete and reformat comments.
 */

/**
 * Acts as a container of different kinds of Samplers and offers some basic
 * sampling methods. There are three different kinds of Samplers accessed through
 * this: a transaction sampler, a node sampler and a network sampler.
 * 
 * @author Sotirios Liaskos for the Conceptual Modeling Group @ York University
 * @see AbstractTransactionSampler
 * @see AbstractNodeSampler
 * @see AbstractNetworkSampler
 * @since 0.1
 */
public class Sampler {
	// ================================
	// FIELDS
	// ================================
	/** The transaction sampler for generating transaction workloads. */
	AbstractTransactionSampler transactionSampler;

	/** The node sampler for generating node configurations. */
	AbstractNodeSampler nodeSampler;

	/** The network sampler for generating network topologies. */
	AbstractNetworkSampler networkSampler;

	// ================================
	// MAIN PUBLIC METHODS
	// ================================

	/*
	 * B A S E L I N E   S A M P L I N G   R O U T I N E S  
	 */

	/**
     * Calculates a random interval following the Poisson distribution.
	 *
	 * <p><b>JML Contract:</b></p>
	 * <pre>{@code
	 *   //@ requires lambda >= 0;
	 *   //@ requires random != null;
	 *   //@ ensures \result >= 0;
	 * }</pre>
	 *
     * @param lambda The parameter of the Poisson distribution (lambda greater or equal to 0). To be used for arrival rates.
	 * @param random the {@linkplain Random} number generator to use
     * @return The random interval following the Poisson distribution
	 * @throws ArithmeticException if {@code lambda < 0}
	 * @throws NullPointerException if {@code random} is null
     */
    public double getPoissonInterval(float lambda, Random random) {
		getPoissonInterval_pre(lambda, random);

		double p = random.nextDouble();
		while (p == 0.0){
			p = random.nextDouble();
		}
		double result = Math.log(1 - p) / (-lambda);

		getPoissonInterval_post(result);

        return result;
    }
    
    
    /**
     * Generates a random value following the Gaussian distribution (normal distribution), 
     * truncated to ensure it is positive.
     *
	 * <p><b>JML Contract:</b></p>
	 * <pre>{@code
	 *   //@ requires deviation >= 0;
	 *   //@ requires random != null;
	 *   //@ ensures \result > 0;
	 * }</pre>
	 *
     * @param mean  The mean value of the distribution.
     * @param deviation The standard deviation of the distribution (deviation greater or equal to 0).
	 * @param random The {@linkplain Random} number generator to use
	 * @return The generated random value following the Gaussian distribution.
	 * @throws ArithmeticException if {@code deviation < 0}
	 * @throws NullPointerException if {@code random} is null
     */
    public float getGaussian(float mean, float deviation, Random random) {
		getGaussian_pre(mean, deviation, random);

    	float gaussianValue = mean + (float) random.nextGaussian() * deviation;
    	while(gaussianValue <= 0) {
    		gaussianValue = mean + (float) random.nextGaussian() * deviation;
    	}

		getGaussian_post(gaussianValue);
    	return gaussianValue;
    }

    
	// ================================
	// SETTERS AND GETTERS
	// ================================

	/**
	 * Returns the transaction sampler.
	 *
	 * <p><b>JML Contract:</b></p>
	 * <pre>{@code
	 *   //@ ensures \result == this.transactionSampler;
	 * }</pre>
	 *
	 * @return the {@linkplain AbstractTransactionSampler} instance
	 */
	public AbstractTransactionSampler getTransactionSampler() {
		return transactionSampler;
	}


	/**
	 * Sets the transaction sampler.
	 *
	 * <p><b>JML Contract:</b></p>
	 * <pre>{@code
	 *   //@ ensures this.transactionSampler == txSampler;
	 * }</pre>
	 *
	 * @param txSampler the {@linkplain AbstractTransactionSampler} to set
	 */
	public void setTransactionSampler(AbstractTransactionSampler txSampler) {
		this.transactionSampler = txSampler;
	}

	
	/**
	 * Returns the node sampler.
	 *
	 * <p><b>JML Contract:</b></p>
	 * <pre>{@code
	 *   //@ ensures \result == this.nodeSampler;
	 * }</pre>
	 *
	 * @return the {@linkplain AbstractNodeSampler} instance
	 */
	public AbstractNodeSampler getNodeSampler() {
		return nodeSampler;
	}

	/**
	 * Sets the node sampler.
	 *
	 * <p><b>JML Contract:</b></p>
	 * <pre>{@code
	 *   //@ ensures this.nodeSampler == nodeSampler;
	 * }</pre>
	 *
	 * @param nodeSampler the {@linkplain AbstractNodeSampler} to set
	 */
	public void setNodeSampler(AbstractNodeSampler nodeSampler) {
		this.nodeSampler = nodeSampler;
	}

	/**
	 * Returns the network sampler.
	 *
	 * <p><b>JML Contract:</b></p>
	 * <pre>{@code
	 *   //@ ensures \result == this.networkSampler;
	 * }</pre>
	 *
	 * @return the {@linkplain AbstractNetworkSampler} instance
	 */
	public AbstractNetworkSampler getNetworkSampler() {
		return networkSampler;
	}

	/**
	 * Sets the network sampler.
	 *
	 * <p><b>JML Contract:</b></p>
	 * <pre>{@code
	 *   //@ ensures this.networkSampler == netSampler;
	 * }</pre>
	 *
	 * @param netSampler the {@linkplain AbstractNetworkSampler} to set
	 */
	public void setNetworkSampler(AbstractNetworkSampler netSampler) {
		this.networkSampler = netSampler;
	}
    
	// ================================
	// VALIDATOR METHODS
	// ================================

	private static void requirePostcondition(boolean condition, String message) {
		if (!condition) {
			throw new IllegalStateException(message);
		}
	}

	private void getPoissonInterval_pre(float lambda, Random random) {
		if (lambda < 0) {
			throw new ArithmeticException("lambda < 0");
		}
		if (random == null) {
			throw new NullPointerException("random cannot be null");
		}
	}

	private void getPoissonInterval_post(double result) {
		requirePostcondition(
			result >= 0,
			"Postcondition violated: result must be non-negative"
		);
	}

	private void getGaussian_pre(float mean, float deviation, Random random) {
		if (deviation < 0) {
			throw new ArithmeticException("Standard deviation < 0");
		}
		if (random == null) {
			throw new NullPointerException("random cannot be null");
		}
	}

	private void getGaussian_post(float result) {
		requirePostcondition(
			result > 0,
			"Postcondition violated: result must be positive"
		);
	}
}
