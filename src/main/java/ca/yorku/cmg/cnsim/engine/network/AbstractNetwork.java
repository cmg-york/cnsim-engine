package ca.yorku.cmg.cnsim.engine.network;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.node.NodeSet;
import ca.yorku.cmg.cnsim.engine.reporter.Reporter;

/**
 * Represents a generic network structure in a simulation.
 * <p>
 * This class maintains a reference to a {@link NodeSet} object representing the participating nodes
 * and stores point-to-point throughput values between nodes in a 2D {@code float} array {@code Net}.
 * Propagation times can be computed for messages of a given size. See
 * <a href="../documentation/units.html">documentation/units</a> for the units of measurement of throughput and propagation times.
 * </p>
 * 
 * @author Sotirios Liaskos
 * @version 1.0
 */
public abstract class AbstractNetwork {
	
    /** The set of nodes in the network */
	protected NodeSet ns;

    /** The network throughput matrix in bits per second (bps) */
	public float[][] Net;

	
	// -----------------------------------------------------------------
	// CONSTRUCTORS
	// -----------------------------------------------------------------

	
    /**
     * Empty constructor for testing purposes.
     * Initializes an empty network object.
     */
	public AbstractNetwork() {
	}
	
    /**
     * Constructs a network using the specified {@link NodeSet}.
     * Initializes the throughput matrix with dimensions based on {@code sim.maxNodes}.
     * 
     * @param ns the NodeSet representing the nodes of the network
     * @throws Exception if the number of nodes exceeds the maximum allowed in configuration
     */
	public AbstractNetwork(NodeSet ns) throws Exception {
        int maxNodes = Config.getPropertyInt("sim.maxNodes");
		if (maxNodes < ns.getNodeSetCount()) {
			throw new Exception("Node count exceed maximum allowed number of nodes.");
		}
		Net = new float [maxNodes + 1][maxNodes + 1];
        this.ns = ns;
	}
	

	// -----------------------------------------------------------------
	// PROPAGATION TIME CALCULATIONS
	// -----------------------------------------------------------------

	
   /**
    * Calculates the propagation time of a message of given size between two nodes.
    * 
    * @param origin      the ID of the origin node
    * @param destination the ID of the destination node
    * @param size        the size of the message in bytes
    * @return the propagation time in <b>milliseconds</b>, or -1 if the nodes are not connected
    * @throws ArithmeticException if {@code size < 0}
    * @see #getPropagationTime(float, float)
    * @see <a href="../documentation/units.html">documentation/units</a>
    */
	public long getPropagationTime(int origin, int destination, float size) {
		if(size < 0)
			throw new ArithmeticException("Size < 0");
		float bps = getThroughput(origin, destination);
		return (getPropagationTime(bps, size));
	}

	
    /**
     * Calculates the propagation time for a message of a given size over a channel with specified throughput.
     * 
     * @param throughput the channel throughput in bits per second (bps)
     * @param size       the size of the message in bytes
     * @return the propagation time in <b>milliseconds</b>, or -1 if throughput is 0
     * @throws ArithmeticException if {@code size < 0} or {@code throughput < 0}
     * @see <a href="../documentation/units.html">documentation/units</a>
     */
	public long getPropagationTime(float throughput, float size) {
		if(size < 0)
			throw new ArithmeticException("Size < 0");
		if(throughput < 0)
			throw new ArithmeticException("Throughput < 0");

	    if(throughput == 0)
	        return (-1);
	    else
		    /* Multiply by 8 because Size is in terms of bytes but throughput is in terms of bits. Multiply by 1000 because throughput is measured in bits/second but expected output is in terms of milliseconds. */
	    	return(Math.round((size * 8 * 1000)/throughput));
	}
	
	
	
	
	// -----------------------------------------------------------------
	// GETTERS AND SETTERS
	// -----------------------------------------------------------------

	
    /**
     * Returns the throughput between two nodes.
     * 
     * @param origin      the ID of the origin node
     * @param destination the ID of the destination node
     * @return the throughput in bits per second (bps)
     * @throws ArithmeticException if {@code origin < 0} or {@code destination < 0}
     */
	public float getThroughput(int origin, int destination) {
		if(origin < 0)
			throw new ArithmeticException("Origin < 0");
		if(destination < 0)
			throw new ArithmeticException("Destination < 0");
		return Net[origin][destination];
	}

    /**
     * Sets the throughput between two nodes.
     * Records the event in the reporter.
     * 
     * @param origin      the ID of the origin node
     * @param destination the ID of the destination node
     * @param throughput  the throughput in bits per second (bps)
     * @throws ArithmeticException if {@code origin < 0}, {@code destination < 0}, or {@code throughput < 0}
     */
	public void setThroughput(int origin, int destination, float throughput) {
		if (Reporter.reportsNetEvents()) {
			Reporter.addNetEvent(Simulation.currentSimulationID, origin, destination, throughput, Simulation.currTime);
		}
		if(origin < 0)
			throw new ArithmeticException("Origin < 0");
		if(destination < 0)
			throw new ArithmeticException("Destination < 0");
		if(throughput < 0)
			throw new ArithmeticException("Throughput < 0");
		Net[origin][destination] = throughput;
	}

	
    /**
     * Calculates the average throughput for a given origin node with all other nodes in the network.
     * 
     * @param origin the ID of the origin node
     * @return the average throughput for the origin node in bits per second (bps)
     */
	public float getAvgTroughput(int origin) {
		float sum=0;
		int i=1, count = 0;
		
		for (i=1; i <= Config.getPropertyInt("net.numOfNodes"); i++) {
	        if(i!=origin)
	        {
	            sum += (Net[origin][i] + Net[i][origin]);
	            count += 2;
	        }
	    }
	    return (sum/count);
	}
	
	
    /**
     * Returns the {@link NodeSet} used to construct this network.
     * 
     * @return the NodeSet representing the nodes in this network
     */
	public NodeSet getNodeSet() {
		return ns;
	}


	/**
     * Prints the network throughput matrix to standard output.
     * Each element represents the throughput between two nodes.
     */
	public void printNetwork() {
		for (float[] x : Net) {
		   for (float y : x) {
		        System.out.printf("%3.1f ", y);
		   }
		   System.out.println();
		}
	}
	
	
    /**
     * Alternate implementation of network printing.
     * Prints the throughput matrix as plain numbers separated by spaces.
     */
	public void printNetwork2() {
		for (int i = 0; i < Net.length; i++) {
			for (int j = 0; j < Net[i].length; j++) {
				System.out.print(Net[i][j] + " ");
			}
			System.out.println();
		}
	}
	
}