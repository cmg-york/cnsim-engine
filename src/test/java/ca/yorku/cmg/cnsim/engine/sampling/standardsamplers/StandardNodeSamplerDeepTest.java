package ca.yorku.cmg.cnsim.engine.sampling.standardsamplers;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;

import java.util.ArrayList;
import java.util.List;

import java.nio.file.Files;
import java.nio.file.Path;

import java.util.Comparator;

import ca.yorku.cmg.cnsim.engine.config.ConfigInitializer;
import ca.yorku.cmg.cnsim.engine.sampling.Sampler;

class StandardNodeSamplerDeepTest {

    private StandardNodeSampler sampler;

    private record MiningEvent(long time, String miner) {}

    @BeforeEach
    void setUp() throws Exception {
        String[] args = {"-c", "src/test/resources/application.properties"};
        ConfigInitializer.initialize(args);
        sampler = new StandardNodeSampler(new Sampler(), new long[]{123}, new boolean[]{false}, 1);
    }

    @Test
    void deepTestStandardNodeSampler() throws Exception {

        List<MiningEvent> events = new ArrayList<>();

        // generate good miner timestamps
        long goodTime = 0;
        for (int i = 0; i < 10000; i++) {
            goodTime += sampler.getNextMiningInterval(70);
            events.add(new MiningEvent(goodTime, "GOOD"));
        }
        // generate bad miner timestamps
        long badTime= 0;
        for (int i = 0; i < 10000; i++) {
            badTime += sampler.getNextMiningInterval(30);
            events.add(new MiningEvent(badTime, "BAD"));
        }

        // sort all events
        events.sort(Comparator.comparingLong(MiningEvent::time));
        // traverse and update confirmations/advantage
        int confirmations = 0;
        int advantage = 0;

        List<String> lines = new ArrayList<>();
        lines.add("time,miner,confirmations,advantage");

        for (MiningEvent e : events) {

            if (e.miner().equals("GOOD")) {
                confirmations++;
                advantage--;
            } else {
                advantage++;
            }
            lines.add(e.time() + "," + e.miner() + "," + confirmations + "," + advantage);
        }   
        // write CSV
        Path output = Path.of("target/node-sampler-deep-test.csv");
        Files.write(output, lines);
    }
}
