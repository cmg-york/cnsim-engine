package ca.yorku.cmg.cnsim.engine.transaction;

import java.util.Arrays;

public class TxConflictRegistry {


    // ================================
    // CONSTANTS
    // ================================

    private final long[] match;   // 1-indexed
    private final int size;




    // ================================
    // CONSTRUCTOR
    // ================================

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




    // ================================
    // MAIN PUBLIC METHODS
    // ================================

    /**
     * Replaces all elements in {@code match} with -1.
     * 
     * <p><b>JML Contract:</b></p>
     * <pre>
     *      //@ ensures all elements in {@code match} equals to -1.
     * </pre>
     * 
     */
    public void neutralize() {
    	Arrays.fill(match, -1L); // -1 means no conflict
        neutralize_post();
    }
    
    /**
     * Removes any match for the given ID.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *      //@ requires {@code id} to be valid;
     * </pre>
     * 
     * @param id the ID to remove the match from.
     * @throws IllegalArgumentException if {@code id} is not valid. (precondition violated)
     */
    public void noMatch(int id) {
        validateId(id);
        long partner = match[id];
        if (partner > 0) { // only remove if partner is a valid ID
            match[(int) partner] = -1;
        }
        match[id] = -1;

        noMatch_post(id);
    }

    /**
     * Checks if an id is unitialized
     * 
     * <p><b>JML Contract:</b></p>
     * <pre>
     *      //@ requires {@code id} to be valid;
     * </pre>
     * 
     * @param id the ID to check if unitialized or not
     * @return true if {@code id} is unitialized ({@code match[id] == -2}) and false otherwise
     * @throws IllegalArgumentException if {@code id} is not valid. (precondition violated)
    */
    public boolean uninitialized(int id) {
        validateId(id);
    	return(match[id] == -2);
    }
    




    // ================================
    // SETTERS AND GETTERS
    // ================================


    /**
     * Gets the partner of ID {@code id}
     * 
     * <p><b>JML Contract:</b></p>
     * <pre>
     *      //@ requires {@code id} to be valid;
     * </pre>
     * 
     * @param id the ID to get the partner of
     * @return the partner ID, -1 if unmatched, -2 if unitialized
     * @throws IllegalArgumentException if {@code id} is not valid. (precondition violated)
     */
    public long getMatch(int id) {
        validateId(id);
        return match[id];
    }

    /**
     * Creates a conflict pair {@code (a <-> b)}.
     * Overwrites previous matches if any.
     * 
     * <p><b>JML Contract:</b></p>
     * <pre>
     *      //@ requires {@code a} to be valid;
     *      //@ requires {@code b} to be valid;
     *      //@ requires {@code (a != b)};
     *      //@ ensures {@code match[a] = b};
     *      //@ ensures {@code match[b] = a};
     * </pre>
     * 
     * @param a the first ID of the conflict pair
     * @param b the second ID of the conflict pair
     * @throws IllegalArgumentException if {@code a} is not valid (precondition violated)
     * @throws IllegalArgumentException if {@code b} is not valid (precondition violated)
     * @throws IllegalArgumentException if {@code a == b} (precondition violated)
     * 
     */
    public void setMatch(int a, int b) {
        setMatch_pre(a, b);

        // Remove existing relationships
        noMatch(a);
        noMatch(b);

        match[a] = b;
        match[b] = a;

        setMatch_post(a, b);
    }




    // ================================
    // HELPER METHODS
    // ================================

    // Private helper method to check if a given {@code id} is valid or not.
    private void validateId(int id) {
        if (id < 1 || id > size) {
            throw new IllegalArgumentException(
                "ID must be between 1 and " + size + ", got " + id
            );
        }
    }







    // ================================
    // DEBUG/PRINT/TOSTRING METHODS
    // ================================

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


    // =============================
    // VALIDATOR METHODS 
    // =============================

    // Private helper method to check postcondition for {@linkplain neutralize}.
    private static void neutralize_post() {
        for (long id : match) {
            assert id == -1L : "Postcondition violated: All elements in match must equal -1";
        }
    }

    // Private helper method to check postcondition for {@linkplain noMatch}.
    private static void noMatch_post(int id) {
        long partner = match[id];
        assert match[id] == -1 : "Postcondition violated: match[id] must equal -1.";
        assert match[(int) partner] == -1 : "Postcondition violated: match[partner] must equal -1."
    }

    // Private helper method to check precondition for {@linkplain setMatch}.
    private static void setMatch_pre(int a, int b) {
        validateId(a);
        validateId(b);
        if (a == b) {
            throw new IllegalArgumentException("Cannot match an ID with itself: " + a);
        }
    }

    // Private helper method to check postcondition for {@linkplain setMatch}.
    private static void setMatch_post(int a, int b) {
        assert match[a] == b : "Postcondition violated: match[a] must equal b.";
        assert match[b] == a : "Postcondition violated: match[b] must equal a.";
    }

    