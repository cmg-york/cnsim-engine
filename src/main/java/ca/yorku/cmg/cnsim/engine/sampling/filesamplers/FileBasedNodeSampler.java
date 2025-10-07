package ca.yorku.cmg.cnsim.engine.sampling.filesamplers;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.LinkedList;
import java.util.Queue;

import ca.yorku.cmg.cnsim.engine.Debug;
import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractNodeSampler;

/**
 * Node sampler that reads node characteristics from a CSV file.
 * <p>
 * The CSV file is expected to contain the following columns:
 * <ol>
 *   <li>Node ID (ignored)</li>
 *   <li>Node hash power (float)</li>
 *   <li>Node electric power (float, Watts)</li>
 *   <li>Node electricity cost (float, currency per kWh)</li>
 * </ol>
 * Optionally, the first line can be a header, which will be skipped.
 * <p>
 * If the file does not contain enough nodes according to the configuration
 * property {@code net.numOfNodes}, additional node samples are drawn from
 * an optional {@linkplain AbstractNodeSampler} passed as the alternative sampler.
 * 
 * @author Sotirios Liaskos
 * @see AbstractNodeSampler
 */
public class FileBasedNodeSampler extends AbstractNodeSampler {

	/** Optional alternative node sampler for additional nodes if the file is too short */
	private AbstractNodeSampler alternativeSampler = null;

	/** Path to the CSV file containing node data */
	private String nodesFilePath;

	/** Queue of node electric power samples (Watts) read from the file */
	private Queue<Float> nodeElectricPowers = new LinkedList<>();

	/** Queue of node hash power samples (hashes/sec) read from the file */
	private Queue<Float> nodeHashPowers = new LinkedList<>();

	/** Queue of node electricity cost samples (currency per kWh) read from the file */
	private Queue<Float> nodeElectricityCosts = new LinkedList<>();

	/** Number of nodes required according to configuration */
	private int requiredNodeLines = Config.getPropertyInt("net.numOfNodes");



	// -----------------------------------------------------------------
	// CONSTRUCTORS
	// -----------------------------------------------------------------

	/**
	 * Creates a {@linkplain FileBasedNodeSampler} that reads node data from a file.
	 * 
	 * @param nodesFilePath Path to the CSV file containing node data
	 * @param nodeSampler   Alternative {@linkplain AbstractNodeSampler} for additional nodes if file specifies fewer nodes than required as per configuration
	 */
	public FileBasedNodeSampler(String nodesFilePath, AbstractNodeSampler nodeSampler) {
		this.nodesFilePath = nodesFilePath;
		this.alternativeSampler = nodeSampler;
		loadNodeConfig();
	}

	// -----------------------------------------------------------------
	// FILE LOADING
	// -----------------------------------------------------------------

	/**
	 * Loads node data from the file, assuming the first line is a header.
	 */
	public void loadNodeConfig() {
		loadNodeConfig(true);
	}

	/**
	 * Loads node data from the file, optionally skipping the first line if it is a header.
	 * 
	 * @param hasHeaders True if the first line is a header
	 */
	public void loadNodeConfig(boolean hasHeaders) {
		int lineCount = 0;
		try (BufferedReader br = new BufferedReader(new FileReader(nodesFilePath))) {
			String line;
			while ((line = br.readLine()) != null) {
				lineCount++;
				String[] values = line.split(",");
				if (values.length != 4) {
					continue; // Skip lines that don't have exactly 4 values
				}
				if (hasHeaders && lineCount == 1) {
					continue; // Skip first line
				}
				try {
					nodeHashPowers.add(Float.parseFloat(values[1].trim()));
					nodeElectricPowers.add(Float.parseFloat(values[2].trim()));
					nodeElectricityCosts.add(Float.parseFloat(values[3].trim()));
				} catch (NumberFormatException e) {
					Debug.e(this,"loadNodeConfig: Error parsing node line: " + line);
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		if (hasHeaders) lineCount--;
		if (lineCount < requiredNodeLines) {
			Debug.p(1, this, "The nodes file does not contain enough lines as per configuration file. Required: " + requiredNodeLines + ", Found: " + lineCount + ". Additional nodes to be drawn from alternative sampler.");
		} else if (lineCount > requiredNodeLines) {
			Debug.w(this,"Warning: Nodes file contains more lines than required nodes as per configuration file. Required: " + requiredNodeLines + ", Found: " + lineCount);
		}
	}


	// -----------------------------------------------------------------
	// SAMPLING ROUTINES
	// -----------------------------------------------------------------

	/**
	 * Returns the mining interval for a node with the given hash power.
	 * <p>
	 * Delegates to the alternative sampler.
	 * </p>
	 * @see AbstractNodeSampler#getNextMiningInterval(double)
	 */
	@Override
	public long getNextMiningInterval(double hashPower) {
		return alternativeSampler.getNextMiningInterval(hashPower);
	}

	/**
	 * Returns the next node electric power sample (Watts) from the file,
	 * or from the alternative sampler if the file queue is empty.
	 * @see AbstractNodeSampler#getNextNodeElectricPower()
	 */
	@Override
	public float getNextNodeElectricPower() {
		if (!nodeElectricPowers.isEmpty()) {
			return (nodeElectricPowers.poll());
		} else {
			return (alternativeSampler.getNextNodeElectricPower());
		}
	}


	/**
	 * Returns the next node hash power sample from the file,
	 * or from the alternative sampler if the file queue is empty.
	 * @see AbstractNodeSampler#getNextNodeHashPower()
	 */
	@Override
	public float getNextNodeHashPower() {
		if (!nodeHashPowers.isEmpty()) {
			return (nodeHashPowers.poll());
		} else {
			return (alternativeSampler.getNextNodeHashPower());
		}
	}

	/**
	 * Returns the next node electricity cost sample (currency per kWh) from the file,
	 * or from the alternative sampler if the file queue is empty.
	 * @see AbstractNodeSampler#getNextNodeElectricityCost()
	 */
	@Override
	public float getNextNodeElectricityCost() {
		if (!nodeElectricityCosts.isEmpty()) {
			return (nodeElectricityCosts.poll());
		} else {
			return (alternativeSampler.getNextNodeElectricityCost());
		}
	}

	/**
	 * Returns a random node index.
	 * <p>
	 * Delegates to the alternative sampler.
	 * </p>
	 * @see AbstractNodeSampler#getNextRandomNode(int)
	 */
	@Override
	public int getNextRandomNode(int nNodes) {
		return (alternativeSampler.getNextRandomNode(nNodes));
	}


	// -----------------------------------------------------------------
	// SEED MANAGEMENT
	// -----------------------------------------------------------------

	/**
	 * Updates the seed of the alternative sampler.
	 * <p>
	 * Prints an error if the alternative sampler is not defined.
	 * </p>
	 */
	public void updateSeed() {
		if (alternativeSampler != null) {
			alternativeSampler.updateSeed();
		} else {
			System.err.print("Error in update seed: alternativeSampler not defined.");
		}
	}



}
