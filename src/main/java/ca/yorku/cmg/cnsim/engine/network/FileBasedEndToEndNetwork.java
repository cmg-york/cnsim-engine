package ca.yorku.cmg.cnsim.engine.network;


import ca.yorku.cmg.cnsim.engine.Debug;
import ca.yorku.cmg.cnsim.engine.node.NodeSet;
import ca.yorku.cmg.cnsim.engine.node.PoWNodeSet;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;


/**
 * Represents a network where end-to-end throughput is loaded from a CSV file.  
 * For each pair of nodes, a throughput value indicates the number of bits that can travel 
 * from one node to the other in the unit of time (ignoring routing). This network is 
 * typically an abstraction produced by applying all-possible-shortest-paths algorithms to the true 
 * structure and throughput of a network. It is agnostic to the actual physical structure 
 * or individual link throughputs.
 * <p>
 * The CSV file should contain rows describing the connections between nodes in the format:
 * <pre>
 * fromNodeID,toNodeID,throughput
 * </pre>
 * Optionally, the first line can contain headers.
 * <p>
 * This class extends {@link AbstractNetwork} and initializes the network matrix
 * based on the provided {@link NodeSet} and the data read from the file.
 * </p>
 * 
 * @author Sotirios Liaskos for the Conceptual Modeling Group @ York University
 * @see AbstractNetwork
 */
public class FileBasedEndToEndNetwork extends AbstractNetwork {

	 /** Path to the CSV file describing the network throughput */
	private String networkFilePath;
	
	
    /**
     * Constructs a FileBasedEndToEndNetwork from a NodeSet and a CSV file.
     * The network throughput matrix is initialized based on the file contents.
     * 
     * @param ns the NodeSet representing the nodes in the network
     * @param filename the path to the CSV file containing throughput data
     * @throws Exception if the NodeSet exceeds the maximum allowed nodes, or if file parsing fails
     */
    public FileBasedEndToEndNetwork(NodeSet ns, String filename) throws Exception {
        super(ns);
        networkFilePath = filename;
        try {
			LoadFromFile();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
    }
    
    /**
     * Empty constructor for testing purposes.
     * The network will not be initialized until {@link #LoadFromFile()} is called.
     */
    public FileBasedEndToEndNetwork(){
    }

    /**
     * Loads the network throughput matrix from the CSV file.
     * Assumes the first line is a header.
     * 
     * @throws Exception if there is a problem reading the file or parsing the values
     */
    public void LoadFromFile() throws Exception {
    	LoadFromFile(true);
    }
    
    /**
     * Loads the network throughput matrix from the CSV file.
     * 
     * @param hasHeaders true if the first line of the CSV file contains headers and should be skipped
     * @throws Exception if there is a problem reading the file, parsing values, or invalid node IDs
     */
    public void LoadFromFile(boolean hasHeaders) throws Exception {
    	int lineCount = 0;
        //read the file from file path
        try(BufferedReader br = new BufferedReader(new FileReader(networkFilePath))) {
            String line;
            while ((line = br.readLine()) != null) {
            	lineCount++;
                String[] values = line.split(",");
                if (values.length != 4) {
                    continue; // Skip lines that don't have exactly 3 values
                }
				if (hasHeaders && lineCount == 1) {
					continue; // Skip first line
				}
                try {
                    int from = Integer.parseInt(values[0].trim());
                    int to = Integer.parseInt(values[1].trim());
                    float throughput = Float.parseFloat(values[2].trim());
                    //Debug.p(line);
                    if (from < 0 || from > Net.length || to < 0 || to > Net.length) {
                        throw new Exception("Invalid node ID in throughput (out of max ranger) line: " + line);
                    }
                    //check the number of nodes and put data based on that
                    if (from > ns.getNodeSetCount() || to > ns.getNodeSetCount()) {
                        throw new Exception("Invalid node ID in throughput line (ID not in nodeset): " + line);
                    }
                    this.setThroughput(from, to, throughput);
                } catch (NumberFormatException e) {
                    System.err.println("Error parsing throughput line: " + line);
                }
            }

        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}