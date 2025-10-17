package ca.yorku.cmg.cnsim.engine.node;

import java.util.ArrayList;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.reporter.Reporter;

/**
 * Represents a collection of {@linkplain IMiner} objects participating in a network simulation.
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
 * @see IMiner
 * @see Simulation
 */
public class PoWNodeSet extends NodeSet {

	/** The total hash power of all honest nodes in the NodeSet. */
	float totalHonestHP;



	// -----------------------------------------------------------------
	// CONSTRUCTORS
	// -----------------------------------------------------------------


	/**
	 * Constructs a new {@code NodeSet} using the provided {@linkplain AbstractNodeFactory}.
	 *
	 * @param nf the node factory used to create new nodes
	 */
	public PoWNodeSet(AbstractNodeFactory nf) {
		super();
		nodes = new ArrayList<>();
		nodeFactory = nf;
	}


	// ---------------------------------------------
	// Node Addition Methods
	// ---------------------------------------------

	/**
	 * Adds a single node to the {@code NodeSet} using the configured factory.
	 *
	 * @throws Exception if an error occurs while creating or initializing the node
	 */
	@Override
	public void addNode() throws Exception {
		INode n = nodeFactory.createNewNode();
		if (n instanceof IMiner) {
			IMiner o = (IMiner) n;
			nodes.add(o);
			totalHonestHP += o.getHashPower();
		} else {
			throw new IllegalStateException("PoWNodeSet: Node created is not an IMiner instance.");
		}
	}



	// -----------------------------------------------------------------
	// CLOSING
	// -----------------------------------------------------------------


	/**
	 * Performs cleanup and final reporting for all nodes in this {@code NodeSet}.
	 * <p>
	 * This typically occurs at the end of a simulation run. Each node is closed
	 * and its statistics are recorded using {@linkplain Reporter#addNode(int, int, float, float, float, float)}.
	 * </p>
	 */
	@Override
	public void closeNodes() {
		for (INode n: getNodes()) {
			if (n instanceof IMiner) {
				n.close(n);
				IMiner miner = (IMiner) n;
				if (Reporter.reportsNodeEvents()) {
					Reporter.addNode(Simulation.currentSimulationID, miner.getID(), miner.getHashPower(), miner.getElectricPower(), miner.getElectricityCost(), miner.getTotalCycles());
				}				
			} else {
				throw new IllegalStateException("Node in PoWNodeSet is not an IMiner instance.");
			}

		}
	}


	// -----------------------------------------------------------------
	// Other
	// -----------------------------------------------------------------

	/**
	 * Returns the total honest hash power (sum of hash powers of all honest nodes).
	 *
	 * @return total honest hash power
	 */
	public float getTotalHonestHP() {
		return totalHonestHP;
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

			if (nodes.get(i) instanceof IMiner) {
				IMiner n = (IMiner) nodes.get(i);
				s = s + "Node ID:" + n.getID() + 
						"\t Hashpower: " + n.getHashPower() + " (H/sec)" +
						"\t Malicious?: " + (n == getMalicious()) +
						"\n";
			} else {
				throw new IllegalStateException("Node in PoWNodeSet is not an IMiner instance.");
			}
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
		for(int i = 0; i< nodes.size();i++) {
			if (nodes.get(i) instanceof IMiner) {
				IMiner n = (IMiner) nodes.get(i);

				s[i] = n.getID() + "," + 
						+ n.getElectricPower() + ","
						+ n.getHashPower() + ","
						+ n.getElectricityCost() + "," 
						+ n.getCostPerGH() + ","
						+ n.getAverageConnectedness() + ","
						+ n.getTotalCycles();
			} else {
				throw new IllegalStateException("Node in PoWNodeSet is not an IMiner instance");
			}
		}
		return (s);
	}
}