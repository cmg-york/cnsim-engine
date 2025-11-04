package ca.yorku.cmg.cnsim.engine.reporter;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Maintains average values for {@linkplain BeliefEntry} occurrences for generating
 * short belief reporting.  
 * 
 * Specifically when nodes are asked to report their beliefs on a sample of transactions
 * they register their degree of belief (e.g. 1 or 0) by simply calling {@linkplain BeliefEntryCounter#add(int, long, long, float)} in which for a given Simulation ID, Transaction ID, and Simulation Time a value is provided. The class maintains a running average for each unique BeliefEntry. 
 * 
 * This aleviates the need to store all individual belief values for each node and aggregating 
 * a large belief file as activating the (long) belief reporting feature does.
 * 
 *  
 * @author Sotirios Liaskos for the Conceptual Modeling Group, York University
 * 
 */
public class BeliefEntryCounter {

    /** Internal map storing each BeliefEntry and its running average + count. */
    private final Map<BeliefEntry, AvgTracker> values = new HashMap<>();

    /**
     * Adds a value for the belief entry specified by simulation ID,
     * transaction ID, and simulation time. Updates the running average.
     *
     * @param simID the simulation ID
     * @param txID the transaction ID
     * @param time the simulation time at which the belief is recorded
     * @param value the new value to incorporate
     */
    public void add(int simID, long txID, long time, float value) {
        BeliefEntry key = new BeliefEntry(simID, txID, time);
        values.compute(key, (k, tracker) -> {
            if (tracker == null) tracker = new AvgTracker();
            tracker.add(value);
            return tracker;
        });
    }

    /**
     * Returns the current average value of a belief entry.
     *
     * @param simID the simulation ID
     * @param txID the transaction ID
     * @param time the simulation time
     * @return the average of all added values, or 0 if none
     */
    public float getAverage(int simID, long txID, long time) {
        AvgTracker tracker = values.get(new BeliefEntry(simID, txID, time));
        return tracker != null ? tracker.getAverage() : 0f;
    }

    /**
     * Returns all belief entries with their averages as a list of strings.
     * Format: simID, txID, time, average
     */
    public ArrayList<String> getEntries() {
        return (ArrayList<String>) values.entrySet().stream()
            .sorted(Comparator
                .comparing((Map.Entry<BeliefEntry, AvgTracker> e) -> e.getKey().getSimID())
                .thenComparing(e -> e.getKey().getTxID())
                .thenComparing(e -> e.getKey().getTime())
            )
            .map(e -> e.getKey().getSimID() + ", " +
                      e.getKey().getTxID() + ", " +
                      e.getKey().getTime() + ", " +
                      e.getValue().getAverage())
            .collect(Collectors.toList());
    }

    /** Helper class to track running average using incremental formula. */
    private static class AvgTracker {
        private float average = 0f;
        private int count = 0;

        void add(float value) {
            average += (value - average) / (count + 1); // incremental formula
            count++;
        }

        float getAverage() {
            return average;
        }
    }
}
