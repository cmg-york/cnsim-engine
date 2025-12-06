package ca.yorku.cmg.cnsim.engine.transaction;

import java.util.Arrays;

public class TxConflictRegistry {
    private final long[] match;

    public TxConflictRegistry(long size) {
        if (size < 1) {
            throw new IllegalArgumentException(
                "TxConflictRegistry: size must be between 1 and " + Integer.MAX_VALUE +
                ", but got " + size
            );
        }
        if (size > Integer.MAX_VALUE) {
            throw new IllegalArgumentException(
                "TxConflictRegistry: maximum size exceeded: " + size +
                " (max allowed is " + Integer.MAX_VALUE + ")"
            );
        }

        match = new long[(int) size + 1];
        Arrays.fill(match, -1L); // initialize with "no match"
    }
	
	// set match
	public void setMatch(int a, int b) {
	    match[a] = b;
	    match[b] = a;
	}

	// get match
	public long getMatch(int id) {
	    return match[id];   // returns -1 if no match
	}
	
}
