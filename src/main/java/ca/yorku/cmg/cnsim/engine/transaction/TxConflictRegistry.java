package ca.yorku.cmg.cnsim.engine.transaction;

import java.util.Arrays;

public class TxConflictRegistry {


// --------------------------------
// FIELDS
// --------------------------------
    private final int[] match;   // 1-indexed
    private final int size;




// --------------------------------
// CONSTRUCTOR
// --------------------------------
    /**
     * Creates a registry for conflicts between IDs 1..size.
     */
    public TxConflictRegistry(int size) {
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
        match = new int[this.size + 1];
        Arrays.fill(match, -2); // -2 means "uninitialized"
    }




// --------------------------------
// GETTERS
// --------------------------------
   /**
     * Gets the partner of ID 'id'.
     * Returns -1 if unmatched, -2 if uninitialized.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires 1 <= id <= size;
     *   //@ ensures \result == match[id];
     * </pre>
     *
     * @param id the transaction ID to query
     * @return the matching transaction ID, -1 if unmatched, or -2 if uninitialized
     * @throws IllegalArgumentException if id is out of range [1..size]
     */
    public int getMatch(int id) {
        validateId(id);
        return match[id];
    }


// --------------------------------
// MAIN PUBLIC METHODS
// --------------------------------


    /**
     * Neutralizes all conflicts by setting all matches to -1.
     * After calling this method, all IDs will be unmatched.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ ensures (\forall int i; 1 <= i <= size; getMatch(i) == -1);
     * </pre>
     */
    public void neutralize() {
    	Arrays.fill(match, -1); // -1 means no conflict
        neutralize_post();
    }
    


    /**
     * Checks if the given ID is uninitialized.
     * An uninitialized ID has a match value of -2.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires 1 <= id <= size;
     *   //@ ensures \result == (match[id] == -2);
     * </pre>
     *
     * @param id the transaction ID to check
     * @return true if the ID is uninitialized, false otherwise
     */
    public boolean uninitialized(int id) {
    	return(match[id] == -2);
    }




/**
 * Creates a conflict pair between two transaction IDs.
 * Both IDs will reference each other as conflicts.
 * Overwrites previous matches if any.
 *
 * <p><b>JML Contract:</b></p>
 * <pre>
 *   //@ requires 1 <= a <= size;
 *   //@ requires 1 <= b <= size;
 *   //@ requires a != b;
 *   //@ ensures getMatch(a) == b;
 *   //@ ensures getMatch(b) == a;
 * </pre>
 *
 * @param a first transaction ID
 * @param b second transaction ID
 * @throws IllegalArgumentException if a or b is out of range [1..size]
 * @throws IllegalArgumentException if a equals b
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




    /**
     * Removes any match for the given ID.
     * If the ID has a partner, that partner's match is also cleared.
     * After this operation, the ID will have a match value of -1.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires 1 <= id <= size;
     *   //@ ensures getMatch(id) == -1;
     *   //@ ensures (\old(getMatch(id)) > 0) ==>
     *   //@         getMatch((int)\old(getMatch(id))) == -1;
     * </pre>
     *
     * @param id the transaction ID to clear
     * @throws IllegalArgumentException if id is out of range [1..size]
     */
    public void noMatch(int id) {
        validateId(id);
        int partner = match[id];
        if (partner > 0) { // only remove if partner is a valid ID
            match[(int) partner] = -1;
        }
        match[id] = -1;
        noMatch_post(id, partner);
    }
    
    

    
// --------------------------------
// TOSTRING METHOD
// --------------------------------

    /**
     * Returns a string representation of the conflict registry.
     * The format is [(1 <-> match1), (2 <-> match2), ...].
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ ensures \result != null;
     * </pre>
     *
     * @return a string showing all ID-match pairs
     */
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
    
// --------------------------------
// VALIDATION/HELPER METHODS
// --------------------------------


    /**
     * Validates that the given ID is within the valid range [1..size].
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures 1 <= id && id <= size;
     *   //@ signals_only IllegalArgumentException;
     *   //@ signals (IllegalArgumentException e) id < 1 || id > size;
     * </pre>
     *
     * @param id the transaction ID to validate
     * @throws IllegalArgumentException if id is out of range [1..size]
     */
    private void validateId(int id) {
        if (id < 1 || id > size) {
            throw new IllegalArgumentException(
                "ID must be between 1 and " + size + ", got " + id
            );
        }
    }

      // Private helper method to check postcondition for {@linkplain neutralize}.
    private void neutralize_post() {
        for (long id : match) {
            assert id == -1L : "Postcondition violated: All elements in match must equal -1";
        }
    }

    // Private helper method to check postcondition for {@linkplain noMatch}.
    private void noMatch_post(int id, int old_partner) {
        assert match[id] == -1 : "Postcondition violated: match[id] must equal -1.";

        if (old_partner > 0) {
            assert match[(int) old_partner] == -1 : "Postcondition violated: match[partner] must equal -1.";
        }
    }

    // Private helper method to check precondition for {@linkplain setMatch}.
    private void setMatch_pre(int a, int b) {
        validateId(a);
        validateId(b);
        if (a == b) {
            throw new IllegalArgumentException("Cannot match an ID with itself: " + a);
        }
    }

    // Private helper method to check postcondition for {@linkplain setMatch}.
    private void setMatch_post(int a, int b) {
        assert match[a] == b : "Postcondition violated: match[a] must equal b.";
        assert match[b] == a : "Postcondition violated: match[b] must equal a.";
    }
}


