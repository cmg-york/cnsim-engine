package ca.yorku.cmg.cnsim.engine.transaction;

import java.util.Arrays;

public class TxConflictRegistry {

    private final long[] match;   // 1-indexed
    private final int size;

    /**
     * Creates a registry for conflicts between IDs 1..size.
     */
    public TxConflictRegistry(long size) {
        if (size < 1) {
            throw new IllegalArgumentException(
                "TxConflictRegistry: size must be >= 1, got " + size
            );
        }
        if (size > Integer.MAX_VALUE) {
            throw new IllegalArgumentException(
                "TxConflictRegistry: maximum size exceeded: " + size
            );
        }

        this.size = (int) size;

        // Allocate 1..N (index 0 unused)
        match = new long[this.size + 1];
        Arrays.fill(match, -2L); // -2 means "uninitialized"
    }

    public void neutralize() {
    	Arrays.fill(match, -1L); // -1 means no conflict
    }
    
    /**
     * Gets the partner of ID 'id'.
     * Returns -1 if unmatched.
     */
    public long getMatch(int id) {
        validateId(id);
        return match[id];
    }

    /**
     * Creates a conflict pair (a <-> b).
     * Overwrites previous matches if any.
     */
    public void setMatch(int a, int b) {
        validateId(a);
        validateId(b);
        if (a == b) {
            throw new IllegalArgumentException("Cannot match an ID with itself: " + a);
        }

        // Remove existing relationships
        noMatch(a);
        noMatch(b);

        match[a] = b;
        match[b] = a;
    }

    /**
     * Removes any match for the given ID.
     */
    public void noMatch(int id) {
        validateId(id);
        long partner = match[id];
        if (partner > 0) { // only remove if partner is a valid ID
            match[(int) partner] = -1;
        }
        match[id] = -1;
    }
    
    

    public boolean uninitialized(int id) {
    	return(match[id] == -2);
    }
    
    private void validateId(int id) {
        if (id < 1 || id > size) {
            throw new IllegalArgumentException(
                "ID must be between 1 and " + size + ", got " + id
            );
        }
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("[");

        for (int i = 1; i < match.length; i++) {
            if (i > 1) {
                sb.append(", ");
            }
            sb.append("(")
              .append(i)
              .append(" <-> ")
              .append(match[i])
              .append(")");
        }

        sb.append("]");
        return sb.toString();
    }
}
