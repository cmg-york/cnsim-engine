package ca.yorku.cmg.cnsim.engine.reporter;

import java.util.Objects;

public class BeliefEntry {
	   private final int simID;
	   private final long txID;
	   private final long time;

	   public BeliefEntry(int simID, long txID, long time) {
	       this.simID = simID;
	       this.txID = txID;
	       this.time = time;
	   }
	   
	   // Important: equals and hashCode so it works in HashMap
	    @Override
	    public boolean equals(Object o) {
	        if (this == o) return true;
	        if (!(o instanceof BeliefEntry)) return false;
	        BeliefEntry triple = (BeliefEntry) o;
	        return simID == triple.simID && txID == triple.txID && time == triple.time;
	    }

	    @Override
	    public int hashCode() {
	        return Objects.hash(this.simID, this.txID, this.time);
	    }

	    @Override
	    public String toString() {
	        return "(" + this.simID + ", " + this.txID + ", " + this.time + ")";
	    }

		public int getSimID() {
			return simID;
		}

		public long getTxID() {
			return txID;
		}

		public long getTime() {
			return time;
		}
	       
}