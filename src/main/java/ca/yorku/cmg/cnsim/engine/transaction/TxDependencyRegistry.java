package ca.yorku.cmg.cnsim.engine.transaction;

import java.util.BitSet;
import java.util.Collection;
import java.util.List;

	public final class TxDependencyRegistry {

	    private final int size;
	    private final BitSet[] deps;  // deps[j] contains dependencies for j

	    public TxDependencyRegistry(long size) {
	    	if (size > Integer.MAX_VALUE) {
	            throw new IllegalArgumentException("TxDependencyRegistry: maximum size (" + size +  " ) cannot exceed maximum integer.");
	        }
	        this.size = (int) size;
	        this.deps = new BitSet[this.size + 1];
	        for (int j = 0; j <= this.size; j++) {
	            deps[j] = new BitSet();
	        }
	    }

	    // Add a dependency: j depends on i
	    public void addDependency(int j, int i) {
	        if (i >= j) {
	            throw new IllegalArgumentException("Dependency must be < j");
	        }
	        deps[j].set(i);
	    }

		public void addDependencies(int id, BitSet dependencies) {
			if (id < 0 || id >= deps.length) throw new IndexOutOfBoundsException("id=" + id);
			deps[id] = dependencies;
		}
	    
	    // Convert any given set of satisfied numbers into a BitSet once
	    public BitSet toBitSet(Collection<Integer> satisfied) {
	        BitSet bs = new BitSet();
	        for (int x : satisfied) {
	            bs.set(x);
	        }
	        return bs;
	    }
	    
	    // Convert any given set of satisfied numbers into a BitSet once
	    public BitSet toBitSet(List<Transaction> satisfied) {
	        BitSet bs = new BitSet();
	        for (Transaction x : satisfied) {
	            bs.set((int) x.getID());
	        }
	        return bs;
	    }
	    
	    // Check whether ALL dependencies of j are contained in 'satisfiedBits'
	    public boolean dependenciesMet(int j, BitSet satisfiedBits) {
	        BitSet req = deps[j];
	        // (req AND NOT satisfiedBits) must be empty
	        BitSet tmp = (BitSet) req.clone();
	        tmp.andNot(satisfiedBits);
	        return tmp.isEmpty();
	    }

	    // Even faster if you can afford a reusable temp BitSet per thread:
	    public boolean dependenciesMetFast(int j, BitSet satisfiedBits, BitSet scratch) {
	        scratch.clear();
	        scratch.or(deps[j]);
	        scratch.andNot(satisfiedBits);
	        return scratch.isEmpty();
	    }
	    
	    public String toString(int txID) {
	        if (txID < 1 || txID >= deps.length) {
	            throw new IllegalArgumentException("txID must be between " + 1 + " and " + (deps.length - 1) + ". Was:" + txID);
	        }
	        
	        if ((deps[txID] == null) || deps[txID].isEmpty()) {
	            return "-1"; 
	        }


	        BitSet bs = deps[txID];

	        // Convert stream of set bits to comma-separated string
	        String content = bs.stream()
	                           .boxed()
	                           .map(String::valueOf)
	                           .reduce((a, b) -> a + ";" + b)
	                           .orElse("");

	        return "{" + content + "}";
	    }
	    
}
