package ca.yorku.cmg.cnsim.engine.transaction;

import java.util.Comparator;

public class TxValueComparator implements Comparator<Transaction>{

	/**
	 * Compares the value of Transaction t1 to Transaction t2.
	 * Returns 1 if value of t1 > t2; 0 if t1 == t2; or -1 if t1 < t2.
	 *
	 * <p><b>JML Contract:</b></p>
	 * <pre>
	 *     //@ requires t1 != null;
	 *     //@ requires t2 != null;
	 * </pre>
	 * @param t1 the first Transaction to be compared.
	 * @param t2 the second Transaction to be compared.
	 * @return 1 if value of t1 > t2; 0 if t1 == t2; or -1 if t1 < t2</>
	 */
	@Override
	public int compare(Transaction t1, Transaction t2) {
		compare_pre(t1, t2);

		if(t1.getValue() > t2.getValue())
			return 1;
		else if (t1.getValue() == t2.getValue())
			return 0;
		else
			return -1;
	}

	// Private helper method to check precondition for {@linkplain compare}
	private void compare_pre(Transaction t1, Transaction t2) {
		if (t1 == null || t2 == null) {
			throw new NullPointerException("Input Transaction objects can not be null");
		}
	}
}
