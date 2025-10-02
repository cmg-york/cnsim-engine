package ca.yorku.cmg.cnsim.engine.reporter;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;

public class BeliefEntryCounter {
    private final Map<BeliefEntry, Integer> counts = new HashMap<>();

    public void increment(int simID, long txID, long time) {
    	BeliefEntry key = new BeliefEntry(simID, txID, time);
        counts.put(key, counts.getOrDefault(key, 0) + 1);
    }

    public int getCount(int simID, long txID, long time) {
        return counts.getOrDefault(new BeliefEntry(simID, txID, time), 0);
    }

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
