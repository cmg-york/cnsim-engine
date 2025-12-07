package ca.yorku.cmg.cnsim.engine;

import static org.junit.jupiter.api.Assertions.*;

import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

import ca.yorku.cmg.cnsim.engine.transaction.Transaction;
import ca.yorku.cmg.cnsim.engine.config.ConfigInitializer;
import ca.yorku.cmg.cnsim.engine.sampling.Sampler;
import ca.yorku.cmg.cnsim.engine.sampling.standardsamplers.StandardTransactionSampler;

class StandardTransactionSamplerTest {
	private StandardTransactionSampler s;
	private Sampler s0;
	private long initSeed = 123;
	private boolean flag = false;
	private long switchTx = 100;
	private int simID = 5;
	
	@BeforeEach
	void setUp() throws Exception {
		String[] args = {"-c", "src/test/resources/application.properties"};
		//String[] args = {"-c", "application.properties"};
        try{
            ConfigInitializer.initialize(args);
        } catch (IOException e){
            e.printStackTrace();
            System.exit(1);
        }
		s0 = new Sampler();

		s = new StandardTransactionSampler(s0, simID);
		
		s.nailConfig(123, false, 15);
	}

	@Test
	void testGetNextTransactionArrivalInterval() throws Exception {
		float lambda = 4; //Tx/sec
		
		/**
		 * 4 Transactions per second means 1 (sec)/4 = 0.25 seconds interval.
		 * Hence 250 msec.
		 */
		
		float interv = 0;
		float rounds;
		for (rounds=1;rounds<=1000;rounds++) {
			s.setTxArrivalIntervalRate(lambda);
			interv += s.getNextTransactionArrivalInterval();
		}
		//System.out.println("Average interval:" + ((float) interv)/((float) rounds));
		assertEquals(250,((float) interv)/((float) rounds),50);
	}

	
	@Test
	void testGetNextTransactionArrivalIntervalSeed_1() throws Exception {
		float lambda = 4; //Tx/sec
		float rounds;
		
		s = new StandardTransactionSampler(s0, simID);
		
		initSeed = 123;
		flag = true;
		switchTx = 15;

		s.nailConfig(initSeed, flag, switchTx);
	
		for (rounds=1;rounds<=30;rounds++) {
			s.setTxArrivalIntervalRate(lambda);
			Transaction.getNextTxID();
			s.getNextTransactionArrivalInterval();
			//System.err.println("Tx just created: " + rounds + ", seed:" + s.getCurrentSeed());
			if (rounds < (switchTx)) {
				assertEquals(this.initSeed,s.getCurrentSeed(), "where rounds =" + rounds + " and switchTx = " + switchTx);
			}
			
			if (rounds == (switchTx)) {
				assertEquals(this.initSeed,s.getCurrentSeed(), "where rounds =" + rounds + " and switchTx = " + switchTx);
			} 
			
			if (rounds > (switchTx)) {
				assertEquals(this.initSeed + this.simID,s.getCurrentSeed(), "where rounds =" + rounds + " and switchTx = " + switchTx);
			} 
			

		}
		
	}

	/*
	 * 
	 * getConflict Tests
	 * 
	 */
	
	

    @Test
    void testInvalidAlpha() {
        assertThrows(IllegalArgumentException.class, () -> s.getConflict(1, 10, -0.1, 0.5));
        assertThrows(IllegalArgumentException.class, () -> s.getConflict(1, 10, 1.1, 0.5));
    }

    @Test
    void testInvalidId() {
        assertThrows(IllegalArgumentException.class, () -> s.getConflict(0, 10, 0.5, 0.5));
        assertThrows(IllegalArgumentException.class, () -> s.getConflict(11, 10, 0.5, 0.5));
    }

    @Test
    void testSingleIDThrowsException() {
        assertThrows(IllegalArgumentException.class, () -> s.getConflict(1, 1, 0.5, 0.5));
    }

    @Test
    void testResultWithinBounds() {
        int N = 100;
        int id = 50;
        double alpha = 0.5;
        double likelihood = 1.0;

        for (int i = 0; i < 1000; i++) {
            int result = s.getConflict(id, N, alpha, likelihood);
            assertTrue(result == -1 || (result >= 1 && result <= N), 
                "Result should be -1 or within [1, N], was " + result);
        }
    }

    @Test
    void testAlphaZeroProducesMostlyNearWithFrequencies() {
        int N = 100;
        int id = 50;
        double alpha = 0.0;
        double likelihood = 1.0;
        int trials = 1000;

        Map<Integer, Integer> frequencies = new HashMap<>();
        s.setSeed(18);

        for (int i = 0; i < trials; i++) {
            int result = s.getConflict(id, N, alpha, likelihood);
            if (result != -1) {
                frequencies.put(result, frequencies.getOrDefault(result, 0) + 1);
            }
        }

        // Check that all results are “near” the target ID (±10)
        for (int r : frequencies.keySet()) {
            assertTrue(Math.abs(r - id) <= 10, "Alpha=0 should produce near id, got " + r);
        }
    }

    @Test
    void testAlphaOneProducesFullRangeWithFrequencies() {
        int N = 100;
        int id = 50;
        double alpha = 1.0;
        double likelihood = 1.0;
        int trials = 10000;

        Map<Integer, Integer> frequencies = new HashMap<>();

        for (int i = 0; i < trials; i++) {
            int result = s.getConflict(id, N, alpha, likelihood);
            if (result != -1) {
                frequencies.put(result, frequencies.getOrDefault(result, 0) + 1);
            }
        }

        // Check that low and high IDs are reached (forward-only)
        boolean lowFound = frequencies.keySet().stream().anyMatch(v -> v <= id + 5);
        boolean highFound = frequencies.keySet().stream().anyMatch(v -> v > N - 10);

        assertTrue(lowFound, "Alpha=1 should reach near the start IDs (forward-only)");
        assertTrue(highFound, "Alpha=1 should reach high IDs");
    }
    
	@Test
	@Tag("exclude")
	void testGetNextTransactionFeeValue() {
		fail("Not yet implemented");
	}

	@Test
	@Tag("exclude")
	void testGetNextTransactionSize() {
		fail("Not yet implemented");
	}

}
