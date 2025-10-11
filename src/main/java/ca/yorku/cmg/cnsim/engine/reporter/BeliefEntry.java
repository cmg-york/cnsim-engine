package ca.yorku.cmg.cnsim.engine.reporter;

import java.util.Objects;


/**
 * Represents a unique belief entry of a node regarding a transaction in a simulation.
 * <p>
 * Each {@code BeliefEntry} object encapsulates:
 * <ul>
 *   <li>{@code simID} – the simulation identifier.</li>
 *   <li>{@code txID} – the transaction identifier.</li>
 *   <li>{@code time} – the simulation time (in milliseconds) at which the belief was recorded.</li>
 * </ul>
 * </p>
 * 
 * <p>
 * Instances of this class are immutable; all fields are {@code final} and set during construction.
 * This immutability ensures that the object can be safely used as a key in hash-based collections
 * such as {@linkplain java.util.HashMap} or {@linkplain java.util.HashSet}.
 * </p>
 * 
 * <p>
 * The {@link #equals(Object)} and {@link #hashCode()} methods are overridden to provide
 * value-based equality, meaning two {@code BeliefEntry} objects are considered equal if
 * they have the same {@code simID}, {@code txID}, and {@code time}.
 * </p>
 * 
 * <p>
 * The {@link #toString()} method produces a human-readable representation in the format:
 * <pre>
 * (simID, txID, time)
 * </pre>
 * </p>
 * 
 * @see Reporter
 * @see BeliefEntryCounter
 * @author
 *   Sotirios Liaskos for the Conceptual Modeling Group @ York University
 */
public class BeliefEntry {
	
    /** The simulation ID associated with this belief entry. */
    private final int simID;

    /** The transaction ID associated with this belief entry. */
    private final long txID;

    /** The simulation time (in milliseconds) at which the belief is recorded. */
    private final long time;

    
    // -----------------------------------------------------------------
    // CONSTRUCTOR
    // -----------------------------------------------------------------
    
    
    /**
     * Constructs a new {@code BeliefEntry} with the specified simulation ID, transaction ID, and time.
     *
     * @param simID the simulation identifier
     * @param txID the transaction identifier
     * @param time the simulation time (milliseconds) at which the belief was recorded
     */
	   public BeliefEntry(int simID, long txID, long time) {
	       this.simID = simID;
	       this.txID = txID;
	       this.time = time;
	   }
	   
	   
	   
	    /**
	     * Indicates whether some other object is "equal to" this one.
	     * <p>
	     * Two {@code BeliefEntry} objects are equal if and only if they have the same
	     * {@code simID}, {@code txID}, and {@code time}.
	     * </p>
	     *
	     * @param o the reference object with which to compare
	     * @return {@code true} if this object is equal to the given object, {@code false} otherwise
	     */
	    @Override
	    public boolean equals(Object o) {
	        if (this == o) return true;
	        if (!(o instanceof BeliefEntry)) return false;
	        BeliefEntry triple = (BeliefEntry) o;
	        return simID == triple.simID && txID == triple.txID && time == triple.time;
	    }

	    
	    // -----------------------------------------------------------------
	    // OVERRIDEN METHODS
	    // -----------------------------------------------------------------
	    
	    
	    @Override
	    public int hashCode() {
	        return Objects.hash(this.simID, this.txID, this.time);
	    }

	    @Override
	    public String toString() {
	        return "(" + this.simID + ", " + this.txID + ", " + this.time + ")";
	    }

	    
	    
	    
	    // -----------------------------------------------------------------
	    // GETTERS
	    // -----------------------------------------------------------------
	    
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