package ca.yorku.cmg.cnsim.engine.sampling.standardsamplers;

import static org.junit.jupiter.api.Assertions.*;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import ca.yorku.cmg.cnsim.engine.sampling.Sampler;

@Disabled
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

	/**
	 * Rosenfeld-aligned Monte Carlo simulation of double-spend attack.
	 *
	 * For each experiment:
	 *   1. Generate z honest block intervals to determine when z confirmations arrive.
	 *   2. Count how many attacker blocks were mined by that time.
	 *   3. If attacker already has >= z blocks, immediate win.
	 *   4. Otherwise, apply gambler's ruin catch-up probability: (q/p)^deficit.
	 *
	 * Reports mean attack success rate with standard deviation, standard error,
	 * and 95% confidence interval.
	 */
	@Test
	void testRosenfeldSimulation() {
		double difficulty = 4.3933890848757156E23;
		double power_honest = 7E10;
		double power_malicious = 3E10;
		int minConfirmations = 5;
		int totalExperiments = 10000;
		int honest_wins = 0;
		int malicious_wins = 0;
		double q = power_malicious / (power_honest + power_malicious);
		double p = 1.0 - q;

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
		System.err.println("=== Rosenfeld Simulation (q=" + q + ", z=" + minConfirmations + ") ===");
		System.err.println("Honest Wins:" + honest_wins + ", Malicious Wins:" + malicious_wins);
		System.err.println("Attack success rate:" + String.format("%.4f", mean));
		System.err.println("Std deviation:" + String.format("%.4f", stdDev));
		System.err.println("Std error:" + String.format("%.4f", stdErr));
		System.err.println("95% CI: [" + String.format("%.4f", mean - 1.96 * stdErr) + ", " + String.format("%.4f", mean + 1.96 * stdErr) + "]");
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
	@Test
	void testPureSimulation() {
		double difficulty = 4.3933890848757156E23;
		double power_honest = 7E10;
		double power_malicious = 3E10;
		int minConfirmations = 5;
		int horizon = 10000; // additional blocks to simulate after z confirmations
		int totalExperiments = 10000;
		int honest_wins = 0;
		int malicious_wins = 0;

		// Track per-experiment outcomes (1 = malicious win, 0 = honest win)
		int[] outcomes = new int[totalExperiments];

		for (int exp = 0; exp < totalExperiments; exp++) {

			// Simulate both miners as interleaved Poisson processes
			// using a merged event stream
			double honestTime = 0;
			double maliciousTime = 0;
			double nextHonest = s.getNextMiningIntervalSeconds_alt(power_honest, difficulty);
			double nextMalicious = s.getNextMiningIntervalSeconds_alt(power_malicious, difficulty);

			int honestBlocks = 0;
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

		// Print results
		double q = power_malicious / (power_honest + power_malicious);
		System.err.println("=== Pure Simulation (q=" + q + ", z=" + minConfirmations + ", horizon=" + horizon + ") ===");
		System.err.println("Honest Wins:" + honest_wins + ", Malicious Wins:" + malicious_wins);
		System.err.println("Attack success rate:" + String.format("%.4f", mean));
		System.err.println("Std deviation:" + String.format("%.4f", stdDev));
		System.err.println("Std error:" + String.format("%.4f", stdErr));
		System.err.println("95% CI: [" + String.format("%.4f", mean - 1.96 * stdErr) + ", " + String.format("%.4f", mean + 1.96 * stdErr) + "]");
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
	 *
	 * @see <a href="https://arxiv.org/abs/1402.2009">Rosenfeld, Analysis of Hashrate-Based Double Spending</a>
	 */
	@Test
	void testNakamotoAnalytical() {
		double q = 0.2;
		double p = 1.0 - q;
		int z = 3;
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

		System.err.println("=== Rosenfeld Analytical - Strict (q=" + q + ", z=" + z + ") ===");
		System.err.println("lambda (expected attacker blocks at z confirmations): " + lambda);
		System.err.println("P_sim  (attacker already strictly ahead at z): " + String.format("%.6f", pSim));
		System.err.println("P_tail (catch-up to strictly ahead):           " + String.format("%.6f", pTail));
		System.err.println("P_total (strict attack probability):           " + String.format("%.6f", pTotal));
	}

	private static double factorial(int n) {
		double f = 1.0;
		for (int i = 2; i <= n; i++) f *= i;
		return f;
	}

}
