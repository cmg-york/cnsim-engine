package ca.yorku.cmg.cnsim.engine.node;

import java.util.ArrayList;

public abstract class NodeSet {

	/** The list of nodes participating in this network. */
	protected ArrayList<INode> nodes;
	/** The factory used to create new nodes. */
	protected AbstractNodeFactory nodeFactory;
	/** If there is a malicious node, this points to it. Otherwise, it is null. */
	private INode maliciousNode = null;

	
	
	// ---------------------------------------------
	// Node Addition Methods
	// ---------------------------------------------

	/**
	 * Adds a single node to the {@code NodeSet} using the configured factory.
	 *
	 * @throws Exception if an error occurs while creating or initializing the node
	 */
	public abstract void addNode() throws Exception;

	
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


	
	// ---------------------------------------------
	// Node Closing Methods
	// ---------------------------------------------
	
	
	/**
	 * Performs cleanup and final reporting for all nodes in this {@code NodeSet}.
	 * <p>
	 * This typically occurs at the end of a simulation run. Each node is closed
	 * and its statistics are recorded using {@linkplain Reporter#addNode(int, int, float, float, float, float)}.
	 * </p>
	 */
	public abstract void closeNodes();
	
	// ---------------------------------------------
	// Node Picking Methods
	// ---------------------------------------------
	
	
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
	 * @return the corresponding {@linkplain IMiner}
	 * @throws IndexOutOfBoundsException if {@code nodeID} is invalid
	 */
	public INode pickSpecificNode(int nodeID) {
	    return (nodes.get(nodeID));
	}

	
	// ---------------------------------------------
	// Misc Getters and Setters
	// ---------------------------------------------
	
	/**
	 * Returns the underlying list of nodes.
	 * @return the {@linkplain ArrayList} of {@linkplain INode} objects
	 */
	public ArrayList<INode> getNodes() {
	    return nodes;
	}

	/**
	 * Returns the number of nodes in this {@code NodeSet}.
	 *
	 * @return the node count
	 */
	public int getNodeSetCount() {
	    return (nodes.size());
	}

	
 	/**
	 * Returns the malicious node, if one exists.
	 *
	 * @return the malicious {@linkplain INode}, or {@code null} if none exists
	 */	
	public INode getMalicious() {
		return (maliciousNode);
	}
	
	
	/**
	 * Sets the {@linkplain AbstractNodeFactory} used to create new nodes.
	 *
	 * @param nf the node factory
	 */
	public void setNodeFactory(AbstractNodeFactory nf) {
		this.nodeFactory = nf;
	}
	
	
	// ---------------------------------------------
	// Debug and Print Methods
	// ---------------------------------------------
	
	/**
	 * Returns a formatted string containing details for all nodes in this {@code NodeSet}.
	 * @return a formatted string representation of all nodes
	 */
	public abstract String debugPrintNodeSet();
	
	
	
	/**
	 * Generates a CSV-style representation of the node set, where each line
	 * corresponds to a node and contains its properties separated by commas.
	 * @return an array of strings, each describing one node
	 */
	public abstract String[] printNodeSet();



	
	
}