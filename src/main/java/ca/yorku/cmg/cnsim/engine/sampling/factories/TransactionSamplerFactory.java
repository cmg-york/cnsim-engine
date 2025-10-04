package ca.yorku.cmg.cnsim.engine.sampling.factories;

import ca.yorku.cmg.cnsim.engine.Debug;
import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.sampling.Sampler;
import ca.yorku.cmg.cnsim.engine.sampling.filesamplers.FileBasedTransactionSampler;
import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractTransactionSampler;
import ca.yorku.cmg.cnsim.engine.sampling.standardsamplers.StandardTransactionSampler;

public class TransactionSamplerFactory {
	
	public AbstractTransactionSampler getSampler(String path, 
			Sampler outerSampler, Simulation sim) throws Exception {

		if (path != null) {
			Debug.p("    Creating file-based workload sampler");
			return(new FileBasedTransactionSampler(path, new StandardTransactionSampler(outerSampler, sim.getSimID())));
		} else {
			Debug.p("    Creating random workload sampler");
				return(new StandardTransactionSampler(outerSampler, sim.getSimID()));
		}
	}
}
