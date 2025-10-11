package ca.yorku.cmg.cnsim.engine.reporter;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;


/**
 * Maintains a count of {@linkplain BeliefEntry} occurrences for a simulation.
 * <p>
 * Each {@code BeliefEntryCounter} keeps track of how many times each belief entry
 * (identified by simulation ID, transaction ID, and simulation time) has been recorded.
 * This is useful for producing summarized belief reports.
 * </p>
 * 
 * <p>
 * Internally, this class uses a {@linkplain HashMap} with {@linkplain BeliefEntry} as keys
 * and {@linkplain Integer} as values. The {@link #increment(int, long, long)} method
 * updates the count of a specific belief entry, while {@link #getCount(int, long, long)}
 * retrieves the current count. The {@link #getEntries()} method returns a sorted list
 * of all entries in the format:
 * <pre>
 * simID, txID, time, count
 * </pre>
 * sorted first by {@code simID}, then {@code txID}, then {@code time}.
 * </p>
 * 
 * <p>
 * This class is intended to be used by {@linkplain Reporter} for reporting short belief logs.
 * </p>
 * @see Reporter
 * @see BeliefEntry
 * @author
 *   Sotirios Liaskos for the Conceptual Modeling Group @ York University
 */
public class BeliefEntryCounter {
	
    /** Internal map storing each BeliefEntry and its count. */
    private final Map<BeliefEntry, Integer> counts = new HashMap<>();

    /**
     * Increments the count of the belief entry specified by the simulation ID,
     * transaction ID, and simulation time. If the entry does not exist yet, it is added with count 1.
     *
     * @param simID the simulation ID
     * @param txID the transaction ID
     * @param time the simulation time at which the belief is recorded
     */
    public void increment(int simID, long txID, long time) {
    	BeliefEntry key = new BeliefEntry(simID, txID, time);
        counts.put(key, counts.getOrDefault(key, 0) + 1);
    }

    /**
     * Returns the current count of a belief entry identified by simulation ID,
     * transaction ID, and simulation time.
     *
     * @param simID the simulation ID
     * @param txID the transaction ID
     * @param time the simulation time at which the belief was recorded
     * @return the number of times this belief entry has been recorded, or 0 if not recorded
     */
    public int getCount(int simID, long txID, long time) {
        return counts.getOrDefault(new BeliefEntry(simID, txID, time), 0);
    }

    /**
     * Returns all belief entries with their counts as a list of strings.
     * <p>
     * Each string is in the format:
     * <pre>
     * simID, txID, time, count
     * </pre>
     * Entries are sorted by {@code simID}, then {@code txID}, then {@code time}.
     * </p>
     *
     * @return an {@linkplain ArrayList} of strings representing all belief entries and their counts
     */
    public ArrayList<String> getEntries() {
        return (ArrayList<String>) counts.entrySet().stream()
            .sorted(Comparator
                .comparing((Map.Entry<BeliefEntry, Integer> e) -> e.getKey().getSimID())
                .thenComparing(e -> e.getKey().getTxID())
                .thenComparing(e -> e.getKey().getTime())
            )
            .map(e -> e.getKey().getSimID() + ", " +
                      e.getKey().getTxID() + ", " +
                      e.getKey().getTime() + ", " +
                      e.getValue())
            .collect(Collectors.toList());
    }

}
