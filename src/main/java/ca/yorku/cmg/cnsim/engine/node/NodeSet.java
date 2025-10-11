package ca.yorku.cmg.cnsim.engine.node;

import java.util.ArrayList;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.reporter.Reporter;

/**
 * Represents a collection of {@linkplain INode} objects participating in a network simulation.
 * <p>
 * A {@code NodeSet} maintains references to all nodes created by an {@linkplain AbstractNodeFactory},
 * tracks aggregate metrics, and provides mechanisms for
 * random and direct node selection. It also supports bulk node creation and reporting.
 * </p>
 *
 * <p>Typical usage:</p>
 * TODO: check the bitcoin case 
 *
 * @author  Sotirios Liaskos for the Conceptual Modeling Group @ York University
 * @see AbstractNodeFactory
 * @see INode
 * @see Simulation
 */
public class NodeSet {

    /** The list of nodes participating in this network. */
	protected ArrayList<INode> nodes;
	
	/** The factory used to create new nodes. */
	protected AbstractNodeFactory nodeFactory;
	
  	/** If there is a malicious node, this points to it. Otherwise, it is null. */
	private INode maliciousNode = null;
	
	/** The total hash power of all honest nodes in the NodeSet. */
	private float totalHonestHP;



	// -----------------------------------------------------------------
	// CONSTRUCTORS
	// -----------------------------------------------------------------
	
	
    /**
     * Constructs a new {@code NodeSet} using the provided {@linkplain AbstractNodeFactory}.
     *
     * @param nf the node factory used to create new nodes
     */
	public NodeSet(AbstractNodeFactory nf) {
        nodes = new ArrayList<>();
        nodeFactory = nf;
	}
	
	
	

	// -----------------------------------------------------------------
	// SETTERS AND GETTERS
	// -----------------------------------------------------------------
	
	
    /**
     * Sets the {@linkplain AbstractNodeFactory} used to create new nodes.
     *
     * @param nf the node factory
     */
	public void setNodeFactory(AbstractNodeFactory nf) {
		this.nodeFactory = nf;
	}

	

    /**
     * Adds a single node to the {@code NodeSet} using the configured factory.
     *
     * @throws Exception if an error occurs while creating or initializing the node
     */
	public void addNode() throws Exception {
        INode o = nodeFactory.createNewNode();
        nodes.add(o);
        this.totalHonestHP += o.getHashPower();
	}
	
    /**
     * Adds multiple nodes to this {@code NodeSet}, by repeatedly calling {@linkplain #addNode()}.
     *
     * @param num the number of nodes to add
     * @throws ArithmeticException if {@code num < 0}
     */
	public void addNodes(int num) {
	    if(num < 0)
	        throw new ArithmeticException("num < 0");
	    for (int i = 1; i<=num; i++){
	        try {
				addNode();
			} catch (Exception e) {e.printStackTrace();}
	    }
	}

	
	
	/**
	 * TODO: Refactor to avoid direct access to the underlying list.
     * Returns the underlying list of nodes.
     * @return the {@linkplain ArrayList} of {@linkplain INode} objects
     */
	public ArrayList<INode> getNodes() {
	    return nodes;
	}
	
	

	// -----------------------------------------------------------------
	// NODE INFORMATION
	// -----------------------------------------------------------------
	
	
	
    /**
     * Returns the number of nodes in this {@code NodeSet}.
     *
     * @return the node count
     */
	public int getNodeSetCount() {
	    return (nodes.size());
	}
	

    /**
     * Returns the total honest hash power (sum of hash powers of all honest nodes).
     *
     * @return total honest hash power
     */
	public float getTotalHonestHP() {
		return totalHonestHP;
	}

	

	// -----------------------------------------------------------------
	// NODE SELECTION
	// -----------------------------------------------------------------
	
	
	
	   /**
     * Selects and returns a random node from this {@code NodeSet}.
     * <p>
     * Randomness is determined by the {@linkplain ca.yorku.cmg.cnsim.engine.sampling.Sampler}
     * provided by the associated {@linkplain AbstractNodeFactory}.
     * </p>
     *
     * @return a randomly selected node
     */
	public INode pickRandomNode() {
	    return (nodes.get(nodeFactory.getSampler().getNodeSampler().getNextRandomNode(nodes.size())));
	}

    /**
     * Returns a specific node by its index (ID) within this {@code NodeSet}.
     *
     * @param nodeID the index or ID of the node
     * @return the corresponding {@linkplain INode}
     * @throws IndexOutOfBoundsException if {@code nodeID} is invalid
     */
	public INode pickSpecificNode(int nodeID) {
	    return (nodes.get(nodeID));
	}
	
    /**
     * Performs cleanup and final reporting for all nodes in this {@code NodeSet}.
     * <p>
     * This typically occurs at the end of a simulation run. Each node is closed
     * and its statistics are recorded using {@linkplain Reporter#addNode(int, int, float, float, float, float)}.
     * </p>
     */
	public void closeNodes() {
		for (INode n:this.getNodes()) {
			n.close(n);
			Reporter.addNode(Simulation.currentSimulationID, n.getID(), n.getHashPower(), n.getElectricPower(), n.getElectricityCost(), n.getTotalCycles());
		}
	}
	
	
	// -----------------------------------------------------------------
	// DEBUGGING AND PRINTING
	// -----------------------------------------------------------------
	
    /**
     * Returns a formatted string containing details for all nodes in this {@code NodeSet}.
     * FIXME: it is not clear if this is H/s or GH/s
     * <p>The output includes:</p>
     * <ul>
     *   <li>Node ID</li>
     *   <li>Hash power (H/sec)</li>
     *   <li>Whether malicious</li>
     * </ul>
     *
     * @return a formatted string representation of all nodes
     */
	public String debugPrintNodeSet() {
	    String s = "";
	    for(int i = 0; i< nodes.size();i++){
	        s = s + "Node ID:" + nodes.get(i).getID() + 
	                "\t Hashpower: " + nodes.get(i).getHashPower() + " (H/sec)" +
	                "\t Malicious?: " + (nodes.get(i) == maliciousNode) +
	                "\n";
	    }
	    return (s);
	}


	
    /**
     * Generates a CSV-style representation of the node set, where each line
     * corresponds to a node and contains:
     * <ul>
     *   <li>Node ID</li>
     *   <li>Electric power</li>
     *   <li>Hash power</li>
     *   <li>Electricity cost</li>
     *   <li>Cost per GH</li>
     *   <li>Average connectedness</li>
     *   <li>Total cycles</li>
     * </ul>
     *
     * @return an array of strings, each describing one node
     */
	public String[] printNodeSet() {
	    String s[] = new String[nodes.size()];
	    for(int i = 0; i< nodes.size();i++){
	    	// 6 items
	        s[i] = nodes.get(i).getID() + "," + 
	        		+ nodes.get(i).getElectricPower() + ","
	        		+ nodes.get(i).getHashPower() + ","
	        		+ nodes.get(i).getElectricityCost() + "," 
	        		+ nodes.get(i).getCostPerGH() + ","
	        		+ nodes.get(i).getAverageConnectedness() + ","
	        		+ nodes.get(i).getTotalCycles();
	    }
	    return (s);
	}

}