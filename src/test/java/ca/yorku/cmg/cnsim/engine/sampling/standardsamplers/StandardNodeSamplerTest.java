package ca.yorku.cmg.cnsim.engine.sampling.standardsamplers;

import static org.junit.jupiter.api.Assertions.*;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import ca.yorku.cmg.cnsim.engine.sampling.Sampler;
import ca.yorku.cmg.cnsim.engine.testutils.TestTutorial;

//@Disabled
class StandardNodeSamplerTest {

	private StandardNodeSampler4Test s;
	@BeforeEach
	void setUp() throws Exception {
		this.s = new StandardNodeSampler4Test(new Sampler());
	}

	@AfterEach
	void tearDown() throws Exception {
		this.s = new StandardNodeSampler4Test(new Sampler());
	}

	@Disabled
	@Test
	void testGetNextMiningIntervalSeconds_alt() {
		double difficulty = 4.3933890848757156E23;
		double power_honest = 7E10;
		double power_malicious = 3E10;
		int minConfirmations = 5;
		int totalExperiments = 10000;
		int honest_wins = 0;
		int malicious_wins = 0;

		// Track per-experiment outcomes (1 = malicious win, 0 = honest win)
		int[] outcomes = new int[totalExperiments];

		// Perform experiments
		for (int exp = 0; exp < totalExperiments; exp++) {

			// Create 10000 samples of the malicious miner
			List<double[]> events = new ArrayList<>();
			double maliciousTime = 0;
			for (int i = 0; i < 10000; i++) {
				maliciousTime += s.getNextMiningIntervalSeconds_alt(power_malicious, difficulty);
				events.add(new double[]{maliciousTime, 1}); // 1 = malicious
			}
			double endTime = maliciousTime;

			// Create honest samples until cumulative time >= endTime
			double honestTime = 0;
			while (honestTime < endTime) {
				honestTime += s.getNextMiningIntervalSeconds_alt(power_honest, difficulty);
				events.add(new double[]{honestTime, 0}); // 0 = honest
			}

			// Sort combined list by timestamp
			events.sort(Comparator.comparingDouble(a -> a[0]));

			// Traverse and determine winner
			int confirmations = 0;
			int advantage = 0;
			boolean maliciousWon = false;
			for (double[] event : events) {
				if (event[1] == 0) { // honest
					confirmations++;
					advantage--;
				} else { // malicious
					advantage++;
				}
				if (advantage >= 1 && confirmations >= minConfirmations) {
					malicious_wins++;
					maliciousWon = true;
					outcomes[exp] = 1;
					break;
				}
			}
			if (!maliciousWon) {
				honest_wins++;
				outcomes[exp] = 0;
			}
		}

		// Compute mean and standard deviation
		double mean = (double) malicious_wins / totalExperiments;
		double sumSqDiff = 0;
		for (int i = 0; i < totalExperiments; i++) {
			double diff = outcomes[i] - mean;
			sumSqDiff += diff * diff;
		}
		double stdDev = Math.sqrt(sumSqDiff / totalExperiments);
		double stdErr = stdDev / Math.sqrt(totalExperiments);

		// Print results
		System.err.println("=== Original Simulation - Strict (q=" + power_malicious/(power_malicious+power_honest) + ", z=" + minConfirmations + ", horizon=10000 blocks) ===");
		System.err.println("Honest Wins:" + honest_wins + ", Malicious Wins:" + malicious_wins);
		System.err.println("Attack success rate:" + String.format("%.4f", mean));
		System.err.println("Std deviation:" + String.format("%.4f", stdDev));
		System.err.println("Std error:" + String.format("%.4f", stdErr));
		System.err.println("95% CI: [" + String.format("%.4f", mean - 1.96 * stdErr) + ", " + String.format("%.4f", mean + 1.96 * stdErr) + "]");

	}

	@Test
	void doubleSpendAttackTest() {

		double[] values = {0.06, 0.1, 0.2, 0.3, 0.4};
		double delta = 0.05;

		try {
			TestTutorial.start("BlockArrivalRatesValidation.md");
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		for (double q : values) {
			for (int z = 1; z <= 6; z++) {
				TestTutorial.step("## q = " + q + ", z = " + z);
				
				TestTutorial.code(hiddenChainAttackSim(
						z,
						q,
						4.3933890848757156E23,
						1E11,
						1000,
						1000,
						nakamotoAnalyticalOneBehind(q, z),
						delta
						)  + "\n");
			}
		}
		TestTutorial.close();
	}
	
		
	
	/**
	 * Pure Monte Carlo simulation of double-spend attack (no analytical catch-up).
	 *
	 * After the honest chain reaches z confirmations, both miners continue racing
	 * until either:
	 *   - The attacker catches up (attacker blocks >= honest blocks) → attacker wins
	 *   - A horizon of additional blocks is reached without catch-up → honest wins
	 *
	 * The horizon parameter controls how many additional honest blocks we simulate
	 * after z confirmations. A larger horizon is more accurate but slower.
	 */
	private String hiddenChainAttackSim(
			int minConfirmations,
			double q,
			double difficulty,
			double totalPower,
			int N,
			int horizon,
			double theoretical,
			double delta
			) {

		int honest_wins = 0;
		int malicious_wins = 0;
		
		double power_honest = totalPower*(1-q);
		double power_malicious = totalPower*q;
		int totalExperiments = N;
		
		
		// Track per-experiment outcomes (1 = malicious win, 0 = honest win)
		int[] outcomes = new int[totalExperiments];

		for (int exp = 0; exp < totalExperiments; exp++) {

			// Simulate both miners as interleaved Poisson processes
			// using a merged event stream
			double honestTime = 0;
			double maliciousTime = 0;
			double nextHonest = s.getNextMiningIntervalSeconds_alt(power_honest, difficulty);
			double nextMalicious = s.getNextMiningIntervalSeconds_alt(power_malicious, difficulty);

			//int honestBlocks = 0;
			int honestBlocks = 1;
			int attackerBlocks = 0;
			boolean attackerWon = false;

			// Phase 1: Race until z honest confirmations
			while (honestBlocks < minConfirmations) {
				if (honestTime + nextHonest <= maliciousTime + nextMalicious) {
					honestTime += nextHonest;
					honestBlocks++;
					nextHonest = s.getNextMiningIntervalSeconds_alt(power_honest, difficulty);
				} else {
					maliciousTime += nextMalicious;
					attackerBlocks++;
					nextMalicious = s.getNextMiningIntervalSeconds_alt(power_malicious, difficulty);
				}
			}

			// Check if attacker already caught up at z
			if (attackerBlocks > honestBlocks) {
				attackerWon = true;
			}

			// Phase 2: Continue racing up to horizon additional honest blocks
			if (!attackerWon) {
				int additionalHonest = 0;
				while (additionalHonest < horizon) {
					if (honestTime + nextHonest <= maliciousTime + nextMalicious) {
						honestTime += nextHonest;
						honestBlocks++;
						additionalHonest++;
						nextHonest = s.getNextMiningIntervalSeconds_alt(power_honest, difficulty);
					} else {
						maliciousTime += nextMalicious;
						attackerBlocks++;
						nextMalicious = s.getNextMiningIntervalSeconds_alt(power_malicious, difficulty);
					}

					if (attackerBlocks > honestBlocks) {
						attackerWon = true;
						break;
					}
				}
			}

			if (attackerWon) {
				malicious_wins++;
				outcomes[exp] = 1;
			} else {
				honest_wins++;
				outcomes[exp] = 0;
			}
		}

		// Compute mean and standard deviation
		double mean = (double) malicious_wins / totalExperiments;
		double sumSqDiff = 0;
		for (int i = 0; i < totalExperiments; i++) {
			double diff = outcomes[i] - mean;
			sumSqDiff += diff * diff;
		}
		double stdDev = Math.sqrt(sumSqDiff / totalExperiments);
		double stdErr = stdDev / Math.sqrt(totalExperiments);
		
		String tostResult = tostEquivalenceTest(mean, theoretical, stdErr, totalExperiments, delta);

		return String.format("Analytical: %.4f, Empirical: %.4f [%.4f, %.4f], [%s]",
				theoretical, mean, mean - 1.96 * stdErr, mean + 1.96 * stdErr, tostResult);
	}

	
	
	
	/**
	 * Computes the Rosenfeld double-spend attack probability analytically
	 * under strict overtaking (attacker must be strictly ahead, ties don't count).
	 *
	 * Modified Rosenfeld formula (z confirmations):
	 *   P_sim  = P(k > z)  = 1 − Σ_{k=0}^{z} Poisson(k, λ)     — attacker already strictly ahead at z
	 *   P_tail = Σ_{k=0}^{z} Poisson(k, λ) × (q/p)^(z−k+1)     — catch-up to strictly ahead from deficit
	 *   P_total = P_sim + P_tail
	 *
	 * The +1 in the exponent accounts for the attacker needing to surpass (not just match)
	 * the honest chain.
	 *
	 * where λ = z × q/p
	 * @return 
	 *
	 * @see <a href="https://arxiv.org/abs/1402.2009">Rosenfeld, Analysis of Hashrate-Based Double Spending</a>
	 */
	private double nakamotoAnalytical(double q, int z) {
		double p = 1.0 - q;
		double lambda = (double) z * q / p;
		double ratio = q / p; // < 1 when q < 0.5

		// Poisson PMF terms
		double[] poisson = new double[z + 1];
		for (int k = 0; k <= z; k++) {
			poisson[k] = Math.exp(-lambda) * Math.pow(lambda, k) / factorial(k);
		}

		// P_sim = 1 - CDF(z, lambda) = P(Poisson > z), i.e. attacker already strictly ahead.
		// NO DIFFERENCE FROM ROSENFELD: this term is identical in both versions.
		// Rosenfeld also uses P(k > z) here — the attacker must have mined more than
		// z blocks by the time z confirmations arrive. The k = z case (tie) is handled
		// by P_tail with deficit = 0.
		double cdf = 0;
		for (int k = 0; k <= z; k++) {
			cdf += poisson[k];
		}
		double pSim = 1.0 - cdf;

		// P_tail (strict): attacker must surpass, so deficit is (z - k + 1)
		// DIFFERENCE FROM ROSENFELD: exponent is (z - k + 1) instead of (z - k).
		// To revert to original Rosenfeld (ties count as attacker wins),
		// change the exponent below from (z - k + 1) to (z - k).
		double pTail = 0;
		for (int k = 0; k <= z; k++) {
			pTail += poisson[k] * Math.pow(ratio, z - k + 1);
			//pTail += poisson[k] * Math.pow(ratio, z - k);
		}

		// P_total = P_sim + P_tail
		double pTotal = pSim + pTail;

		return (pTotal);
		
	}

	
	private double nakamotoAnalyticalOneBehind(double q, int z) {
	    double p = 1.0 - q;
	    double lambda = (double) z * q / p;
	    double ratio = q / p;

	    // Poisson PMF terms — need up to z+1 now
	    double[] poisson = new double[z + 2];
	    for (int k = 0; k <= z + 1; k++) {
	        poisson[k] = Math.exp(-lambda) * Math.pow(lambda, k) / factorial(k);
	    }

	    // P_sim: attacker already strictly ahead despite starting 1 behind
	    // Needs k > z+1, so CDF sums to z+1
	    double cdf = 0;
	    for (int k = 0; k <= z + 1; k++) {
	        cdf += poisson[k];
	    }
	    double pSim = 1.0 - cdf;

	    // P_tail: deficit is now (z - k + 2) instead of (z - k + 1)
	    double pTail = 0;
	    for (int k = 0; k <= z + 1; k++) {
	        pTail += poisson[k] * Math.pow(ratio, z - k + 2);
	    }

	    double pTotal = pSim + pTail;
	    return pTotal;
	}
	
	
	/** 
	 * 
	 * 
	 * 
	 * H E L P E R S 
	 * 
	 * 
	 * 
	 */
	
	
	
	
	private static double factorial(int n) {
		double f = 1.0;
		for (int i = 2; i <= n; i++) f *= i;
		return f;
	}

	/**
	 * Performs a TOST (Two One-Sided Tests) equivalence test using normal approximation.
	 *
	 * Tests H0: |empiricalMean - theoretical| >= delta
	 * vs    H1: |empiricalMean - theoretical| < delta
	 *
	 * Uses z-test (normal approximation) appropriate for large N.
	 *
	 * @param empiricalMean  the observed sample mean
	 * @param theoretical    the theoretical (expected) value
	 * @param stdErr         the standard error of the mean
	 * @param N              sample size
	 * @param delta          the equivalence margin
	 * @return "TOST PASS" or "TOST FAIL" with t-statistics
	 */
	private String tostEquivalenceTest(double empiricalMean, double theoretical, double stdErr, int N, double delta) {
		double zCrit = 1.645; // one-sided alpha = 0.05

		// Test 1: H0: mean <= theoretical - delta (reject => mean > lower bound)
		double t1 = (empiricalMean - (theoretical - delta)) / stdErr;

		// Test 2: H0: mean >= theoretical + delta (reject => mean < upper bound)
		double t2 = (empiricalMean - (theoretical + delta)) / stdErr;

		if (t1 > zCrit && t2 < -zCrit) {
			return "TOST PASS (t1=" + String.format("%.3f", t1) + ", t2=" + String.format("%.3f", t2) + ")";
		} else {
			return "TOST FAIL (t1=" + String.format("%.3f", t1) + ", t2=" + String.format("%.3f", t2) + ")";
		}
	}

	
	
	
	
	/** 
	 * 
	 * 
	 * 
	 * D E P R E C A T E D
	 * 
	 * 
	 * 
	 */
	
	
	
	/**
	 * Monte Carlo simulation of double-spend attack.
	 *
	 * For each experiment:
	 *   1. Generate z honest block intervals to determine when z confirmations arrive.
	 *   2. Count how many attacker blocks were mined by that time.
	 *   3. If attacker already has >= z blocks, immediate win.
	 *   4. Otherwise, apply gambler's ruin catch-up probability: (q/p)^deficit.
	 *
	 * Reports mean attack success rate with standard deviation, standard error,
	 * and 95% confidence interval.
	 * @return 
	 */
	private String doubleSpendAttack(
			int minConfirmations,
			double q,
			double difficulty,
			double totalPower,
			int N
			) {
		/*
		double difficulty = 4.3933890848757156E23;
		double power_honest = 7E10;
		double power_malicious = 3E10;
		int minConfirmations = 5;
		int totalExperiments = 10000;
		int honest_wins = 0;
		int malicious_wins = 0;
		double q = power_malicious / (power_honest + power_malicious);
		double p = 1.0 - q;
		//double q = power_malicious / (power_honest + power_malicious);
		//double p = 1.0 - q;

		*/
		
		int honest_wins = 0;
		int malicious_wins = 0;
		
		double power_honest = totalPower*(1-q);
		double power_malicious = totalPower*q;
		int totalExperiments = N;
		double p = 1 - q;
		
		
		// Track per-experiment outcomes (1 = malicious win, 0 = honest win)
		int[] outcomes = new int[totalExperiments];

		for (int exp = 0; exp < totalExperiments; exp++) {

			// Generate z honest block intervals to find when z-th confirmation arrives
			double honestTime = 0;
			for (int i = 0; i < minConfirmations; i++) {
				honestTime += s.getNextMiningIntervalSeconds_alt(power_honest, difficulty);
			}
			double zTime = honestTime;

			// Count how many attacker blocks were mined by zTime
			int attackerBlocks = 0;
			double maliciousTime = 0;
			while (true) {
				maliciousTime += s.getNextMiningIntervalSeconds_alt(power_malicious, difficulty);
				if (maliciousTime > zTime) break;
				attackerBlocks++;
			}

			if (attackerBlocks >= minConfirmations) {
				// Attacker already has at least z blocks — immediate win
				malicious_wins++;
				outcomes[exp] = 1;
			} else {
				// Attacker is behind by (z - attackerBlocks); apply gambler's ruin
				int deficit = minConfirmations - attackerBlocks;
				double catchUpProb = Math.pow(q / p, deficit);
				if (Math.random() < catchUpProb) {
					malicious_wins++;
					outcomes[exp] = 1;
				} else {
					honest_wins++;
					outcomes[exp] = 0;
				}
			}
		}

		// Compute mean and standard deviation
		double mean = (double) malicious_wins / totalExperiments;
		double sumSqDiff = 0;
		for (int i = 0; i < totalExperiments; i++) {
			double diff = outcomes[i] - mean;
			sumSqDiff += diff * diff;
		}
		double stdDev = Math.sqrt(sumSqDiff / totalExperiments);
		double stdErr = stdDev / Math.sqrt(totalExperiments);

		// Print results
		/*System.err.println("=== Rosenfeld Simulation (q=" + q + ", z=" + minConfirmations + ") ===");
		System.err.println("Honest Wins:" + honest_wins + ", Malicious Wins:" + malicious_wins);
		System.err.println("Attack success rate:" + String.format("%.4f", mean));
		System.err.println("Std deviation:" + String.format("%.4f", stdDev));
		System.err.println("Std error:" + String.format("%.4f", stdErr));
		System.err.println("95% CI: [" + String.format("%.4f", mean - 1.96 * stdErr) + ", " + String.format("%.4f", mean + 1.96 * stdErr) + "]");
		*/
		
		return(String.format("%.4f", mean) + "[" + String.format("%.4f", mean - 1.96 * stdErr) + ", " + String.format("%.4f", mean + 1.96 * stdErr) + "]");
	}
	
}
