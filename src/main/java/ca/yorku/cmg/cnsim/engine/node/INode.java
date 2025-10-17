package ca.yorku.cmg.cnsim.engine.node;

import ca.yorku.cmg.cnsim.engine.IStructure;
import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.transaction.ITxContainer;
import ca.yorku.cmg.cnsim.engine.transaction.Transaction;

public interface INode {

	/**
	 * Returns the ID of the node.
	 *
	 * @return the unique node ID
	 */
	int getID();

	/**
	 * Returns the structure associated with this node.
	 *
	 * @return the structure (blockchain, DAG, etc.)
	 */
	IStructure getStructure();

	/**
	 * Returns the average connectedness of the node with other nodes.
	 *
	 * @return the average throughput with other nodes
	 */
	float getAverageConnectedness();

	/**
	 * Sets the simulation object for this node.
	 *
	 * @param sim the simulation instance
	 */
	void setSimulation(Simulation sim);

	/**
	 * Sets the behavior type of the node.
	 *
	 * @param behaviorName description of the behavior type as a string (e.g., "honest", "selfish", "malicious")
	 */
	void setBehavior(String behaviorName);

	/**
	 * Returns the current behavior type of the node.
	 *
	 * @return behavior type as a string
	 */
	String getBehavior();

	/**
	 * Generates a time advancement report.
	 * <p>The method is called every time a new event is processed.</p>
	 * <p>To be used sparingly, due to computational implications.</p>
	 */
	void timeAdvancementReport();

	/**
	 * Generates a periodic report.
	 * <p>The method is called at user-defined time intervals.</p>
	 */
	void periodicReport();

	/**
	 * Generates a transaction belief report.
	 * <p>
	 * Called by the simulation environment to report the node's belief 
	 * on a set of transactions.
	 * </p>
	 *
	 * @param sample list of transaction IDs to report on
	 * @param time   timestamp of the report
	 */
	void beliefReport(long[] sample, long time);

	/**
	 * Generates a node status report.
	 * <p>
	 * Reports the node's status (e.g., active, token balance, power usage).
	 * </p>
	 */
	void nodeStatusReport();

	/**
	 * Generates a structure report.
	 * <p>
	 * Reports the node's current structure (blockchain, DAG, etc.).
	 * </p>
	 */
	void structureReport();

	/**
	 * To be called when the node object is not closing though end of simulation or other termination condition. 
	 *
	 * @param n The {@linkplain IMiner} implementing object to close.
	 */
	void close(INode n);

	/**
	* Event: Node receives a client transaction, i.e. a transaction outside the system.
	*
	* @param t The client transaction received by the node.
	* @param time The timestamp of the event.
	*/
	void event_NodeReceivesClientTransaction(Transaction t, long time);

	/**
	 * Event: Node receives a propagated transaction, i.e., from another node.
	 *
	 * @param trans The propagated transaction received by the node.
	 * @param time The timestamp of the event.
	 */
	void event_NodeReceivesPropagatedTransaction(Transaction trans, long time);

	/**
	 * Event: Node receives a propagated container; e.g., block of transactions.
	 *
	 * @param t The propagated container received by the node.
	 */
	void event_NodeReceivesPropagatedContainer(ITxContainer t);

	/**
	 * Event: Node completes validation of a container.
	 *
	 * @param t The container for which validation is completed.
	 * @param time The timestamp of the event.
	 */
	void event_NodeCompletesValidation(ITxContainer t, long time);

	/**
	 * Event: Node receives a request to print a periodic report
	 *
	 * @param time The timestamp of the event.
	 */
	void event_PrintPeriodicReport(long time);

	/**
	 * Event: Node receives a request to print a belief report
	 *
	 * @param sample The transactions for which the belief report is to be produced.
	 * @param time The timestamp of the event.
	 */
	void event_PrintBeliefReport(long[] sample, long time);

	/**
	 * Event: Node receives a request to print a structure
	 *
	 * @param time The timestamp of the event.
	 */
	void event_PrintStructureReport(long time);

	/**
	 * Event: Node receives a request to print a self status report
	 *
	 * @param time The timestamp of the event.
	 */
	void event_NodeStatusReport(long time);

}