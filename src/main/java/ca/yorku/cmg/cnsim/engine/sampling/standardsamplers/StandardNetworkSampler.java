package ca.yorku.cmg.cnsim.engine.sampling.standardsamplers;

import ca.yorku.cmg.cnsim.engine.sampling.Sampler;
import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractNetworkSampler;

public class StandardNetworkSampler extends AbstractNetworkSampler {

    public StandardNetworkSampler(Sampler s) {
    	this.sampler = s;
    }
	
	
    /**
     * See parent. Use Normal distribution.
     */
    @Override
    public float getNextConnectionThroughput() {
    	float result = sampler.getGaussianPos(netThroughputMean, netThroughputSD, random);
    	if (result <= 0) {
    		throw new ArithmeticException("getGaussianPos gives " + result + " with mean " + netThroughputMean + " and sd " + netThroughputSD);
    	}
        return (result);
    }


}
