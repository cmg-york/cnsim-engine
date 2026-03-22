package ca.yorku.cmg.cnsim.engine.transaction;

import java.util.BitSet;
import java.util.Collection;
import java.util.List;

import ca.yorku.cmg.cnsim.engine.Debug;

/**
 * Tracks transaction dependencies for simulation purposes.
 *
 * <p>
 * The {@code TxDependencyRegistry} maintains dependencies between transactions, where transaction
 * {@code j} can depend on one or more earlier transactions {@code i} (where {@code i < j}).
 * Dependencies are stored using {@linkplain BitSet} arrays for compact representation and efficient
 * dependency checking operations. Transaction IDs are expected to be in the range {@code [1, size]},
 * where {@code size} is specified at construction time.
 * </p>
 *
 * <p>
 * The registry provides methods for adding individual dependencies, setting all dependencies for a
 * transaction at once, checking whether all dependencies of a transaction are satisfied, and
 * converting collections of satisfied transactions to BitSets for efficient set operations.
 * </p>
 *
 * @author Sotirios Liaskos for the Conceptual Modeling Group @ York University
 * @see BitSet
 * @see Transaction
 * @since 0.1
 */
public final class TxDependencyRegistry {
	// ================================
    // FIELDS
    // ================================

	/** Max number of transactions this registry can track. */
	private final int size;

	/** Array of BitSets where {@code deps[j]} contains transaction IDs that {@code j} depends on. */
	private final BitSet[] deps;  // deps[j] contains dependencies for j

	// ================================
	// CONSTRUCTORS
	// ================================

	/**
     * Creates a transaction dependency registry with the specified size.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>{@code
	 *   //@ requires 0 < size && size < Integer.MAX_VALUE;
     *   //@ ensures this.size == (int) size;
     *   //@ ensures this.deps.length == this.size + 1;
     * }</pre>
     *
     * @param size the max number of transactions this registry will track
     * @throws IllegalArgumentException if {@code size >= Integer.MAX_VALUE || size <= 0} (precondition violated)
     */
	public TxDependencyRegistry(long size) {
		TxDependencyRegistry_pre(size);

		this.size = (int) size;
		this.deps = new BitSet[this.size + 1];
		for (int j = 0; j <= this.size; j++) {
			deps[j] = new BitSet();
		}

		TxDependencyRegistry_post(this, size);
	}

	// ================================
	// MAIN PUBLIC METHODS
	// ================================

	 /**
     * Adds a dependency indicating that transaction {@code j} depends on transaction {@code i}.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>{@code
     *   //@ requires i < j;
     *   //@ requires j >= 1 && j < deps.length;
     *   //@ requires i >= 1;
     *   //@ ensures deps[j].get(i) == true;
     * }</pre>
     *
     * @param j the transaction ID that has the dependency
     * @param i the transaction ID that {@code j} depends on
	 * @throws IndexOutOfBoundsException if {@code j < 1 || j > size} (precondition violated)
     * @throws IllegalArgumentException if {@code i < 1 || i >= j} (precondition violated)
     */
	public void addDependency(int j, int i) {
		addDependency_pre(j, i);

		deps[j].set(i);

		addDependency_post(this, j, i);
	}

	/**
     * Sets all dependencies for a transaction by replacing its dependency {@linkplain BitSet}.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>{@code
     *   //@ requires id >= 1 && id < deps.length;
     *   //@ ensures deps[id] == dependencies;
     * }</pre>
     *
     * @param id the transaction ID
     * @param dependencies the {@linkplain BitSet} representing all dependencies for this transaction
     * @throws IndexOutOfBoundsException if {@code id < 1} or {@code id >= deps.length} (precondition violated)
     */
	public void addDependencies(int id, BitSet dependencies) {
        addDependencies_pre(id);

		deps[id] = dependencies;

		addDependencies_post(this, id, dependencies);
	}

	/**
     * Converts a collection of satisfied transaction IDs into a {@linkplain BitSet}.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>{@code
     *   //@ requires satisfied != null;
     *   //@ ensures \result != null;
     *   //@ ensures (\forall int x; satisfied.contains(x); \result.get(x));
     * }</pre>
     *
     * @param satisfied a collection of satisfied transaction IDs
     * @return a {@linkplain BitSet} with bits set for each ID in {@code satisfied}
     * @throws NullPointerException if {@code satisfied} is null
     */
	public BitSet toBitSet(Collection<Integer> satisfied) {
		toBitSet_Collection_pre(satisfied);

		BitSet bs = new BitSet();
		for (int x : satisfied) {
			bs.set(x);
		}

		toBitSet_Collection_post(satisfied, bs);
		return bs;
	}

	 /**
     * Converts a list of satisfied {@linkplain Transaction} objects into a {@linkplain BitSet}.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>{@code
     *   //@ requires satisfied != null;
     *   //@ ensures \result != null;
     *   //@ ensures (\forall Transaction tx; satisfied.contains(tx); \result.get((int) tx.getID()));
     * }</pre>
     *
     * @param satisfied a list of satisfied {@linkplain Transaction} objects
     * @return a {@linkplain BitSet} with bits set for each transaction ID in {@code satisfied}
     * @throws NullPointerException if {@code satisfied} is null or contains null elements (precondition violated)
     */
	public BitSet toBitSet(List<Transaction> satisfied) {
		toBitSet_Transaction_pre(satisfied);

		BitSet bs = new BitSet();
		for (Transaction x : satisfied) {
			bs.set((int) x.getID());
		}

		toBitSet_Transaction_post(satisfied, bs);
		return bs;
	}

	/**
     * Checks whether all dependencies of transaction {@code j} are satisfied (contained in {@code satisfiedBits}).
     *
     * <p><b>JML Contract:</b></p>
     * <pre>{@code
     *   //@ requires j >= 1 && j < deps.length;
     *   //@ requires satisfiedBits != null;
     *   //@ ensures \result == (\forall int i; deps[j].get(i); satisfiedBits.get(i));
     * }</pre>
     *
     * @param j the transaction ID to check
     * @param satisfiedBits a {@linkplain BitSet} representing all satisfied transaction IDs
     * @return {@code true} if all dependencies of {@code j} are satisfied; {@code false} otherwise
     * @throws NullPointerException if {@code satisfiedBits} is null (precondition violated)
     * @throws IndexOutOfBoundsException if {@code j < 1} or {@code j >= deps.length} (precondition violated)
     */
	public boolean dependenciesMet(int j, BitSet satisfiedBits) {
		dependenciesMet_pre(j, satisfiedBits);

		BitSet req = deps[j];
		// (req AND NOT satisfiedBits) must be empty
		BitSet tmp = (BitSet) req.clone();
		tmp.andNot(satisfiedBits);
		boolean result = tmp.isEmpty();
		return result;
	}

	/**
     * Checks whether all dependencies of transaction {@code j} are satisfied, using a reusable scratch BitSet.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>{@code
     *   //@ requires j >= 1 && j < deps.length;
     *   //@ requires satisfiedBits != null;
     *   //@ requires scratch != null;
     *   //@ ensures \result == (deps[j] == null || (\forall int i; deps[j].get(i); satisfiedBits.get(i)));
     * }</pre>
     *
     * @param j the transaction ID to check
     * @param satisfiedBits a {@linkplain BitSet} representing all satisfied transaction IDs
     * @param scratch a reusable {@linkplain BitSet} for temporary calculations (will be modified)
     * @return {@code true} if all dependencies of {@code j} are satisfied or if {@code deps[j]} is {@code null};
     *         {@code false} otherwise
     * @throws NullPointerException if {@code satisfiedBits} is null (precondition violated)
     * @throws NullPointerException if {@code scratch} is null (precondition violated)
     * @throws IndexOutOfBoundsException if {@code j < 1} or {@code j >= deps.length} (precondition violated)
     */
	public boolean dependenciesMetFast(int j, BitSet satisfiedBits, BitSet scratch) {
		dependenciesMetFast_pre(j, satisfiedBits, scratch);

		boolean result;
		if (deps[j] != null) {
			scratch.clear();
			scratch.or(deps[j]);
			scratch.andNot(satisfiedBits);
			result = scratch.isEmpty();
		} else {
			result = true;
		}
		return result;
	}


	// ================================
    // DEBUG/PRINT/TOSTRING METHODS
    // ================================

	/**
     * Returns a string representation of the dependencies of the given transaction.
     *
     * @param txID the transaction ID whose dependencies should be printed
     * @return {@code "-1"} if there are no dependencies; otherwise a semicolon-separated set like {@code "{1;2}"}
     * @throws IndexOutOfBoundsException if {@code txID < 1} or {@code txID >= deps.length}
     */
	public String toString(int txID) {
		if (txID < 1 || txID >= deps.length) {
			throw new IndexOutOfBoundsException("txID must be between " + 1 + " and " + (deps.length - 1) + ". Was:" + txID);
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

	// =============================
	// VALIDATOR METHODS
	// =============================

	private static void requirePostcondition(boolean condition, String message) {
		if (!condition) {
			throw new IllegalStateException(message);
		}
	}

	private void TxDependencyRegistry_pre(long size) {
		if (size <= 0) {
			throw new IllegalArgumentException(
				"TxDependencyRegistry: size must be positive, was: " + size
			);
		}
		if (size >= Integer.MAX_VALUE) {
			throw new IllegalArgumentException(
				"TxDependencyRegistry: maximum size (" + size +
				") cannot be at least maximum integer."
			);
		}
	}

    private void TxDependencyRegistry_post(TxDependencyRegistry registry, long size) {
		requirePostcondition(
			registry.size == (int) size,
			"Postcondition violated: size must equal constructor parameter size"
		);
		requirePostcondition(
			registry.deps.length == registry.size + 1,
			"Postcondition violated: deps array length must be size + 1"
		);
    }

	private void addDependency_pre(int j, int i) {
		if (j < 1 || j > size) {
			throw new IndexOutOfBoundsException(
				"j must be in range [1, " + size + "], but was: " + j
			);
		}
		if (i < 1) {
			throw new IllegalArgumentException("Dependency i must be >= 1, was: " + i);
		}
		if (i >= j) {
			throw new IllegalArgumentException("Dependency i must be < j, but i=" + i + " and j=" + j);
		}
	}

	private void addDependency_post(TxDependencyRegistry registry, int j, int i) {
		requirePostcondition(
			registry.deps[j].get(i),
			"Postcondition violated: deps[" + j + "].get(" + i + ") must be true"
		);
	}

	private void addDependencies_pre(int id) {
		if (id < 1 || id >= deps.length) {
			throw new IndexOutOfBoundsException(
				"id must be in range [1, " + (deps.length - 1) + "], but was: " + id
			);
		}
	}

	private void addDependencies_post(TxDependencyRegistry registry, int id, BitSet dependencies) {
		requirePostcondition(
			registry.deps[id] == dependencies,
			"Postcondition violated: deps[" + id + "] must equal provided dependencies"
		);
    }

	private void toBitSet_Collection_pre(Collection<Integer> satisfied) {
        if (satisfied == null) {
            throw new NullPointerException("satisfied collection cannot be null");
        }
    }

    private void toBitSet_Collection_post(Collection<Integer> satisfied, BitSet result) {
		requirePostcondition(result != null, "Postcondition violated: result must not be null");
        for (int x : satisfied) {
			requirePostcondition(
				result.get(x),
				"Postcondition violated: result must contain " + x
			);
        }
    }

    private void toBitSet_Transaction_pre(List<Transaction> satisfied) {
        if (satisfied == null) {
            throw new NullPointerException("satisfied list cannot be null");
        }
    }

    private void toBitSet_Transaction_post(List<Transaction> satisfied, BitSet result) {
		requirePostcondition(result != null, "Postcondition violated: result must not be null");
        for (Transaction tx : satisfied) {
            int id = (int) tx.getID();
			requirePostcondition(
				result.get(id),
				"Postcondition violated: result must contain transaction ID " + id
			);
        }
    }

	 private void dependenciesMet_pre(int j, BitSet satisfiedBits) {
        if (satisfiedBits == null) {
            throw new NullPointerException("satisfiedBits cannot be null");
        }
		if (j < 1 || j >= deps.length) {
			throw new IndexOutOfBoundsException(
				"id must be in range [1, " + (deps.length - 1) + "], but was: " + j
			);
		}
    }

    private void dependenciesMetFast_pre(int j, BitSet satisfiedBits, BitSet scratch) {
        if (satisfiedBits == null) {
            throw new NullPointerException("satisfiedBits cannot be null");
        }
        if (scratch == null) {
            throw new NullPointerException("scratch BitSet cannot be null");
        }

		if (j < 1 || j >= deps.length) {
			throw new IndexOutOfBoundsException(
				"id must be in range [1, " + (deps.length - 1) + "], but was: " + j
			);
		}
    }
}