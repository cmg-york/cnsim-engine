package ca.yorku.cmg.cnsim.engine.node;

import ca.yorku.cmg.cnsim.engine.IStructure;
import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.transaction.ITxContainer;
import ca.yorku.cmg.cnsim.engine.transaction.Transaction;

/**
 * Represents a network node within the simulation.
 * <p>
 * Each node has an associated structure (e.g., blockchain or DAG), 
 * a set of behavioral characteristics, and can report events for monitoring.
 * The interface defines methods for node properties,  
 * reporting, and event handling.
 * </p>
 * 
 * @author Sotirios
 */
public interface INode {
	
	
	// -----------------------------------------------------------------
	// GETTERS AND SETTERS
	// -----------------------------------------------------------------
	
    /**
     * Returns the ID of the node.
     *
     * @return the unique node ID
     */
	public int getID();
	
    /**
     * Returns the structure associated with this node.
     *
     * @return the structure (blockchain, DAG, etc.)
     */
	public IStructure getStructure(); 
	
    /**
     * Sets the total hash power of the node in Gigahashes per second (GH/s).
     *
     * @param hashPower the hash power in GH/s
     */
    public void setHashPower(float hashPower);

    /**
     * Returns the total hash power of the node in Gigahashes per second (GH/s).
     *
     * @return hash power in GH/s
     */
    public float getHashPower();

    /**
     * Sets the cost of electricity in tokens per kilowatt-hour (tokens/kWh).
     *
     * @param electricityCost the cost of electricity
     */
    public void setElectricityCost(float electricityCost);
    
    /**
     * Returns the cost of electricity in tokens per kilowatt-hour (tokens/kWh).
     *
     * @return the electricity cost
     */
    public float getElectricityCost();
    
    /**
     * Returns the cost in conventional currency tokens in tokens/GH. Calculation is as follows: 
     * [ [electrictiyCost ($/kWh) * electricPower (W) / 1000 (W/kW)] /  [3600 (s/h) * hashPower (GH/s)]] = 
     * [ [electrictiyCost ($/kWh) * electricPowerinkW (kW)] /  [3600 (s/h) * hashPower (GH/s)]] =
     * [ [electrictiyCostPerHour ($/h)] /  [hashesPerHour (GH/h)]] =
     * Tokens per billions of hashes ($/GH)
     * @return Cost in conventional currency tokens in tokens/GH.
     */
    public double getCostPerGH();
    
    
    /**
     * Returns the electric power of the node in Watts.
     *
     * @return electric power in Watts
     */
    public float getElectricPower();
    

    /**
     * Sets the electric power of the node in Watts.
     *
     * @param power the electric power in Watts
     */
    public void setElectricPower(float power);
    
    
    /**
     * Returns the average connectedness of the node with other nodes.
     *
     * @return the average throughput with other nodes
     */
	public float getAverageConnectedness();
    

    /**
     * Sets the simulation object for this node.
     *
     * @param sim the simulation instance
     */
    public void setSimulation(Simulation sim);
    
    
    /**
     * Sets the behavior type of the node.
     *
     * @param behaviorName description of the behavior type as a string (e.g., "honest", "selfish", "malicious")
     */
    public void setBehavior(String behaviorName);
    
    
    /**
     * Returns the current behavior type of the node.
     *
     * @return behavior type as a string
     */
    public String getBehavior();
    
    
	// -----------------------------------------------------------------
	// REPORTING HOOKS
	// -----------------------------------------------------------------
	
    
    /**
     * Generates a time advancement report.
     * <p>The method is called every time a new event is processed.</p>
     * <p>To be used sparingly, due to computational implications.</p>
     */
	public void timeAdvancementReport();
	
    /**
     * Generates a periodic report.
     * <p>The method is called at user-defined time intervals.</p>
     */
	public void periodicReport();
	
	
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
	public void beliefReport(long[] sample, long time);
	
    /**
     * Generates a node status report.
     * <p>
     * Reports the node's status (e.g., active, token balance, power usage).
     * </p>
     */
	public void nodeStatusReport();
	
	
    /**
     * Generates a structure report.
     * <p>
     * Reports the node's current structure (blockchain, DAG, etc.).
     * </p>
     */
	public void structureReport();
	
	
	// -----------------------------------------------------------------
	// MISC ROUTINES
	// -----------------------------------------------------------------
	
	
    /**
     * Returns the total PoW cycles the node has expended
     * TODO: Unit of measure?
     * @return The total PoW cycles of the node has expended.
     */
    public double getTotalCycles();
	
	
	/**
	 * To be called when the node object is not closing though end of simulation or other termination condition. 
	 *
	 * @param n The {@linkplain INode} implementing object to close.
	 */
	public void close(INode n);
    
	
	
	
	
	// -----------------------------------------------------------------
	// EVENT HANDLERS / BEHAVIORS
	// -----------------------------------------------------------------
	
	
	
	/**
	* Event: Node receives a client transaction, i.e. a transaction outside the system.
	*
	* @param t The client transaction received by the node.
	* @param time The timestamp of the event.
	*/
    public void event_NodeReceivesClientTransaction(Transaction t, long time);

    /**
     * Event: Node receives a propagated transaction, i.e., from another node.
     *
     * @param trans The propagated transaction received by the node.
     * @param time The timestamp of the event.
     */
	public void event_NodeReceivesPropagatedTransaction(Transaction trans, long time);
    
	/**
	 * Event: Node receives a propagated container; e.g., block of transactions.
	 *
	 * @param t The propagated container received by the node.
	 */
	public void event_NodeReceivesPropagatedContainer(ITxContainer t);
    
	/**
	 * Event: Node completes validation of a container.
	 *
	 * @param t The container for which validation is completed.
	 * @param time The timestamp of the event.
	 */
    public void event_NodeCompletesValidation(ITxContainer t, long time);
    
    
	/**
	 * Event: Node receives a request to print a periodic report
	 *
	 * @param time The timestamp of the event.
	 */
    public void event_PrintPeriodicReport(long time);

    
	/**
	 * Event: Node receives a request to print a belief report
	 *
	 * @param sample The transactions for which the belief report is to be produced.
	 * @param time The timestamp of the event.
	 */
    public void event_PrintBeliefReport(long[] sample,long time);
    
	/**
	 * Event: Node receives a request to print a structure
	 *
	 * @param time The timestamp of the event.
	 */
    public void event_PrintStructureReport(long time);
        
    
	/**
	 * Event: Node receives a request to print a self status report
	 *
	 * @param time The timestamp of the event.
	 */
    public void event_NodeStatusReport(long time);
    
    
}
