package ca.yorku.cmg.cnsim.engine.sampling.standardsamplers;

import java.util.Random;

import ca.yorku.cmg.cnsim.engine.sampling.Sampler;
import ca.yorku.cmg.cnsim.engine.sampling.SeedManager;
import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractNodeSampler;

/**
 * A standard implementation of the {@linkplain AbstractNodeSampler}.
 * Uses Normal distribution for node properties and Uniform 
 * distribution for random node selection.
 * 
 * TODO-JIRA: De-POW-ify the Node Sampler classes in Engine.
 * - Both this and the parent refer to PoW-style nodes. They must be renamed and more generic Node classes
 * need to be introduced. 
 * 
 * 
 * @author Sotirios Liaskos for the Conceptual Modeling Group @ York University
 *
 */
public class StandardNodeSampler extends AbstractNodeSampler {

	SeedManager seedManager;
	Random random;
	int simID;




	// -----------------------------------------------------------------
	// CONSTRUCTORS
	// -----------------------------------------------------------------

	/**
	 * Constructs a StandardNodeSampler using the specified {@linkplain Sampler}.
	 * Initializes a new {@linkplain Random} generator.
	 *
	 * @param s the Sampler to use for Gaussian sampling
	 */
	public StandardNodeSampler(Sampler s) {
		this.sampler = s;
		random = new Random();
	}


	/**
	 * Constructs a StandardNodeSampler using the specified {@linkplain Sampler} 
	 * and seed management configuration.
	 *
	 * @param s the Sampler to use for Gaussian sampling
	 * @param seedArray array of seeds for reproducible random sequences
	 * @param flagArray flags indicating whether each seed should be updated
	 * @param sim the simulation ID for seed updates
	 * @see SeedManager
	 * 
	 */
	public StandardNodeSampler(Sampler s, long[] seedArray, boolean[] flagArray, int sim) {
		this(s);
		seedManager = new SeedManager(seedArray,flagArray,sim);
		seedManager.updateSeed(random);
	}



	// -----------------------------------------------------------------
	// MINING INTERVAL SAMPLING
	// -----------------------------------------------------------------

	/**
	 * Returns a sample of the mining interval in milliseconds for a node with
	 * the specified hash power and current difficulty.
	 *
	 * @param hashPower the node's hash power in Giga-hashes/second
	 * @return a sampled mining interval in milliseconds
	 * @throws ArithmeticException if {@code hashPower} is less than 0
	 * @see AbstractNodeSampler#getNextMiningInterval(double)
	 */
	@Override
	public long getNextMiningInterval(double hashPower) {

		if(hashPower < 0)
			throw new ArithmeticException("hashPower < 0");
		long inter = Math.round(getNextMiningIntervalMiliSeconds(hashPower, currentDifficulty));
		return((long) inter);
	}

	/**
	 * Get a random sample of the number of trials needed to successfully validate.
	 * Sampling formula is: Math.log(1-Math.random())/Math.log1p(- 1.0/difficulty))
	 * @param difficulty The difficulty under which the number of trials is generated. 
	 * @return A number of trials needed for validation.
	 * @throws ArithmeticException if {@code difficulty} is less than 0
	 */
	public double getNextMiningIntervalTrials(double difficulty) {
		if(difficulty < 0)
			throw new ArithmeticException("difficulty < 0");
		//return ((double) (Math.log(1-Math.random())/Math.log1p(- 1.0/difficulty)));
		return ((double) (Math.log(1-random.nextDouble())/Math.log1p(- 1.0/difficulty)));
	}


	/**
	 * Returns a sample of the mining interval in seconds for a node with
	 * the specified hash power and difficulty.
	 *
	 * @param hashPower the node's hash power in Giga-hashes/second
	 * @param difficulty the PoW difficulty
	 * @return a sampled mining interval in seconds
	 * @throws ArithmeticException if {@code hashPower} is less than 0
	 */
	private double getNextMiningIntervalSeconds(double hashPower, double difficulty) {
		if (hashPower < 0)
			throw new ArithmeticException("hashPower < 0");
		double tris = getNextMiningIntervalTrials(difficulty);
		return((double) tris / (hashPower*1e9));
	}

	/**
	 * Returns a sample of the mining interval in seconds for a node with
	 * the specified hash power and difficulty.
	 * 
	 * This implementation is based on exponential distribution 
	 *
	 * @param hashPower the node's hash power in Giga-hashes/second
	 * @param difficulty the PoW difficulty
	 * @return a sampled mining interval in seconds
	 * @throws ArithmeticException if {@code hashPower} is less than 0
	 */
	public double getNextMiningIntervalSeconds_alt(double hashrate,double difficulty) {
	    if (difficulty <= 0 || hashrate <= 0)
	        throw new ArithmeticException("invalid parameters");

	    double truehashrate = hashrate * 1e9; 
	    double lambda = truehashrate / difficulty;   // successes per second
	    return -Math.log(1 - random.nextDouble()) / lambda;
	}
	
	
	/**
	 * Returns a sample of the mining interval in milliseconds for a node with
	 * the specified hash power and difficulty.
	 *
	 * @param hashPower the node's hash power in Giga-hashes/second
	 * @param difficulty the PoW difficulty
	 * @return a sampled mining interval in milliseconds
	 * @see	StandardNodeSampler#getNextMiningIntervalSeconds(double, double)
	 */
	public double getNextMiningIntervalMiliSeconds(double hashPower, double difficulty) {
		double secs = getNextMiningIntervalSeconds_alt(hashPower,difficulty);
		return((double) secs*1000);
	}




	// -----------------------------------------------------------------
	// NODE PROPERTY SAMPLING
	// -----------------------------------------------------------------

	/**
	 * Returns a random sample of the node's electric power (Watts) using
	 * a Normal distribution defined by {@link #nodeElectricPowerMean} and {@link #nodeElectricPowerSD}.
	 *
	 * @return a sampled electric power value (Watts)
	 * @see AbstractNodeSampler#getNextNodeElectricPower() 
	 */
	@Override
	public float getNextNodeElectricPower() {
		return (sampler.getGaussian(nodeElectricPowerMean, nodeElectricPowerSD, getRandom()));
	}

	/**
	 * Returns a random sample of the node's hash power (hashes/second) using
	 * a Normal distribution defined by {@linkplain #nodeHashPowerMean} and {@linkplain #nodeHashPowerSD}.
	 *
	 * @return a sampled hash power value (hashes/second)
	 * @see AbstractNodeSampler#getNextNodeHashPower()
	 */
	@Override
	public float getNextNodeHashPower() {
		return (sampler.getGaussian(nodeHashPowerMean, nodeHashPowerSD, getRandom()));
	}

	/**
	 * Returns a random sample of the node's electricity cost (currency/kWh) using
	 * a Normal distribution defined by {@linkplain #nodeElectricCostMean} and {@linkplain #nodeElectricCostSD}.
	 *
	 * @return a sampled electricity cost
	 * @see AbstractNodeSampler#getNextNodeElectricityCost()
	 */
	@Override
	public float getNextNodeElectricityCost() {
		return (sampler.getGaussian(nodeElectricCostMean, nodeElectricCostSD, getRandom()));
	}


	/**
	 * Returns a randomly selected node ID from the range [0, nNodes).
	 * <p>
	 * Selection is uniform.
	 * </p>
	 *
	 * @param nNodes the total number of nodes
	 * @return a randomly selected node ID
	 * @throws ArithmeticException if {@code nNodes} is less than 1
	 * @see AbstractNodeSampler#getNextRandomNode(int)
	 */
	@Override
	public int getNextRandomNode(int nNodes) {
		return(getRandom().nextInt(nNodes));
	}




	// -----------------------------------------------------------------
	// GETTERS AND SETTERS
	// -----------------------------------------------------------------

	public Random getRandom() {
		return random;
	}

	public void setRandom(Random random) {
		this.random = random;
	}

	public SeedManager getSeedManager() {
		return seedManager;
	}

	public void updateSeed() {
		seedManager.updateSeed(random);
	}

}
