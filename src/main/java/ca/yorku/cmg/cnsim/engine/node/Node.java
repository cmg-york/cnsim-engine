package ca.yorku.cmg.cnsim.engine.node;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.event.Event;
import ca.yorku.cmg.cnsim.engine.event.Event_ContainerArrival;
import ca.yorku.cmg.cnsim.engine.event.Event_ContainerValidation;
import ca.yorku.cmg.cnsim.engine.event.Event_TransactionPropagation;
import ca.yorku.cmg.cnsim.engine.reporter.Reporter;
import ca.yorku.cmg.cnsim.engine.transaction.ITxContainer;
import ca.yorku.cmg.cnsim.engine.transaction.Transaction;
import ca.yorku.cmg.cnsim.engine.transaction.TransactionGroup;

import java.util.ArrayList;

/**
 * Abstract class representing a node in a blockchain network.
 * 
 * @author Sotirios Liaskos for the Conceptual Modeling Group @ York University
 * 
 */
public abstract class Node implements INode {

	private static int currID = 1;
	protected int ID;
	
	protected Simulation sim;
	
	protected float hashPower;
	protected float electricPower;
	protected float electricityCost;
	protected double totalCycles = 0;
	protected double prospectiveMiningCycles = 0;
	
	protected String behaviorType;
	protected TransactionGroup pool;
	protected Event nextValidationEvent;
	
	private boolean isMining = false;
	

	
	// 
	//   C O N S T R U C T O R
	//
	public Node(Simulation sim) {
		super();
        this.sim = sim;
        pool = new TransactionGroup();
        //setNetwork(sim.getNetwork());
        ID = getNextNodeID();
	}

	
	
	//
	// I D   M A N A G E M E N T
	//
	@Deprecated
	public void ______________________ID() {} 
	

	


	// -----------------------------------------------------------------
	// A C T I O N S
	// -----------------------------------------------------------------

	
	
	// -----------------------------------------------------------------
	// MINING MANAGEMENT
	// -----------------------------------------------------------------
		

	
	/**
	 * Starts mining with the specified expected mining interval. 
	 * The interval may be based on when the next validation event takes place.  
	 * @param interval The mining interval (in seconds).
	 */
	public void startMining(double interval) {
		prospectiveMiningCycles = interval*this.getHashPower();
		isMining = true;
	}

	/**
	 * Starts mining without specifying an expected mining interval.
	 */
	public void startMining() {
		isMining = true;
	}
	
	
	/**
	 * Checks if the node is currently mining.
	 * @return true if the node is mining, false otherwise.
	 */
	public boolean isMining() {
	    return isMining;
	}


	/**
	 * Stops mining
	 */
	public void stopMining() {
		isMining = false;
	}

	
	
	// -----------------------------------------------------------------
	// POOL MANAGEMENT
	// -----------------------------------------------------------------
	
	
	/**
	 * Adds a new transaction to the pool of unprocessed transactions
	 * @param t The Transaction to be added.
	 */
	public void addTransactionToPool(Transaction t) {
		getPool().addTransaction(t);
	}
	
	/**
	 * Removes the transactions included in transaction container from the pool.
	 * @param removeThese The transaction container whose transactions are to be removed.
	 */
	public void removeFromPool(ITxContainer removeThese) {
		if ( (!pool.getTransactions().isEmpty()) && (!removeThese.getTransactions().isEmpty()) )
			pool.getTransactions().removeAll(removeThese.getTransactions());
	}

	public void removeFromPool(Transaction removeThis) {
		if ( (!pool.getTransactions().isEmpty()) && (removeThis != null) )
			pool.getTransactions().remove(removeThis);
	}

	public void removeFromPool(int removeThis) {
		if ( (!pool.getTransactions().isEmpty()) && (removeThis >= 0) )
			//pool.getTransactions().remove(removeThis);
			pool.removeTransaction(removeThis);
	}

	
	
	// -----------------------------------------------------------------
	// PROPAGATION ACTIONS
	// -----------------------------------------------------------------
	
	/**
	 * Propagates the specified transaction container to other nodes in the simulation.
	 * TODO: All time references should be on a global time parameter. 
	 * @param txc The transaction container to be propagated.
	 * @param time The current simulation time.
	 */
	public void propagateContainer(ITxContainer txc, long time) {
	    NodeSet nodes = sim.getNodeSet();
	    ArrayList<INode> ns_list = nodes.getNodes();
	    for (INode n : ns_list) {
	        if (!n.equals(this)){
	            long inter = sim.getNetwork().getPropagationTime(this.getID(), n.getID(), txc.getSize());
	            Event_ContainerArrival e = new Event_ContainerArrival(txc, n, time + inter);
	            sim.schedule(e);
	        }
	    }
	}
	
	/**
	 * 
	 * Propagates the specified transaction to other nodes in the simulation.
	 * @param t The transaction to be propagated.
	 * @param time The current time in the simulation.
	 */
	public void propagateTransaction(Transaction t, long time) {
	    NodeSet nodes = sim.getNodeSet();
	    ArrayList<INode> ns_list = nodes.getNodes();
	    for (INode n : ns_list) {
	        if (!n.equals(this)){
	            long inter = sim.getNetwork().getPropagationTime(this.getID(), n.getID(), t.getSize());
	            if (inter<0) {
	            	String error = "Error in 'propagateTransaction' Negative interval between " + this.getID() + " and " + n.getID() + " for size " + t.getSize() + " of transaction " + t.getID() +  " interval is " + inter;
	            	Reporter.addErrorEntry(error);
	            	System.err.println(error);
	            	assert(inter > 0);
	            }

	            //TODO: do something more elaborate perhaps
	            inter+= Config.getPropertyInt("net.propagationTime");
	            
	            Event_TransactionPropagation e = new Event_TransactionPropagation(t, n, time + inter);
	            sim.schedule(e);
	        }
	    }
	}

	// -----------------------------------------------------------------
	// CYCLE COUNTING AND COST CALCULATIONS
	// -----------------------------------------------------------------
	
	/**
	 * Adds the specified number of cycles to the total cycles of the node.
	 * @param c The number of cycles to be added. 
	 */
	public void addCycles(double c) {
		totalCycles += c;
	}
	
	/**
	 * See ({@linkplain INode#getTotalCycles()}
	 */
	@Override
	public double getTotalCycles() {
		return totalCycles;
	}
	
	/**
	 * See {@linkplain INode#getCostPerGH()}
	 */
	@Override
	public double getCostPerGH() {
		//[ [electrictiyCost ($/kWh) * electricPower (W) / 1000 (W/kW)] /  [3600 (s/h) * hashPower (GH/s)]]
		return ( (electricityCost * electricPower / 1000) / (3600 * hashPower) );
	}


	
	// -----------------------------------------------------------------
	// GETTERS AND SETTERS
	// -----------------------------------------------------------------

	
	//
	// ID MANAGEMENT
	//
	/**
	 * Gets the next available ID for a node and increments the counter.
	 * @return The next available ID for a node.
	 */
	public static int getNextNodeID() {
	    return(currID++);
	}


	/**
	 * Resets the next available ID to 1. To be used for moving to the next experiment.
	 */
	public static void resetCurrID() {
	    currID = 1;
	}
		
	/**
	 * Gets the ID of the node.
	 * @return The ID of the node.
	 */
	public int getID() {
	    return ID;
	}

	//
	// R E F E R E N C E S
	//
	/**
	 * Gets the simulation associated with the node.
	 * @param s The simulation associated with the node.
	 */
	@Override
	public void setSimulation(Simulation s) {
		sim = (Simulation) s;
	}
	
	/**
	 * Gets the simulation associated with the node.
	 * @return The Simulation object associated with the node.
	 */
	public Simulation getSim() {
	    return sim;
	}

	/**
	 * Gets the transaction pool of the node.
	 * @return The transaction pool of the node.
	 */
	public TransactionGroup getPool() {
	    return pool;
	}


	//
	// SIMPLE SET/GET
	//
	/**
	 * See ({@linkplain INode} interface.
	 */
	@Override
	public void setHashPower(float hashpower) {
		if(hashpower < 0 )
			throw new ArithmeticException("Hash Power < 0");
	    this.hashPower = hashpower;
	}

	/**
	 * See ({@linkplain INode} interface.
	 */
	@Override
	public float getHashPower() {
	    return hashPower;
	}
	
	/**
	 * See ({@linkplain INode} interface.
	 */
	@Override
	public void setElectricityCost(float electricityCost) {
		if(electricityCost < 0 )
			throw new ArithmeticException("Electricity Cost < 0");
	    this.electricityCost = electricityCost;
	}

	/**
	 * See ({@linkplain INode} interface.
	 */
	@Override
	public float getElectricityCost() {
	    return electricityCost;
	}

	/**
	 * See ({@linkplain INode} interface.
	 */
	@Override
	public String getBehavior() {
	    return behaviorType;
	}

	/**
	 * See ({@linkplain INode} interface.
	 */
	@Override
	public void setBehavior(String type) {
	    this.behaviorType = type;
	}

	/**
	 * See ({@linkplain INode} interface.
	 */
	@Override
	public float getAverageConnectedness() {
		return(sim.getNetwork().getAvgTroughput(getID()));
	}


	/**
	 * See {@linkplain INode#getElectricPower()}
	 */
	@Override
	public float getElectricPower() {
		return this.electricPower;
	}

	
	/**
	 * See {@linkplain INode#setElectricPower(float)}
	 */
	@Override
	public void setElectricPower(float power) {
		this.electricPower = power;
		
	}
	
	

	
	
	// -----------------------------------------------------------------
	// VALIDATION EVENT CREATION AND MANAGEMENT
	// -----------------------------------------------------------------
	
	
    /**
     * Returns the next validation event associated with this node. Useful for removing the event when necessary.
     * @return The next validation Event.
     */
    public Event getNextValidationEvent() {
    	return this.nextValidationEvent;
    }
    
    /**
     * Deletes the next validation event associated with this node.
     * TODO: how does this affect cycle counting statistics?
     */
    public void resetNextValidationEvent() {
    	this.nextValidationEvent = null;
    }
	
	/**
	 * Schedules a validation event for the specified transaction container at the given time.
	 * @param txc The transaction container to be validated.
	 * @param time The simulation time when the scheduling occurs. The even will be scheduled at `time + mining interval`. 
	 * @return The scheduled mining interval in seconds.
	 */
	public long scheduleValidationEvent(ITxContainer txc, long time) {
		long h = sim.getSampler().getNodeSampler().getNextMiningInterval(getHashPower());
	    Event_ContainerValidation e = new Event_ContainerValidation(txc, this, time + h);
	    this.nextValidationEvent = e;
	    sim.schedule(e);
	    return (h);
	}
    
	
	
	// -----------------------------------------------------------------
	// EVENT HANDLERS / BEHAVIORS
	// -----------------------------------------------------------------
	
	
	
	/**
	 * See {@linkplain INode#event_NodeCompletesValidation(ITxContainer, long)}
	 * TODO: prospectiveMiningCycles must be removed from here, they are inaccurate, in cases of cancellation.
	 */
	@Override
	public void event_NodeCompletesValidation(ITxContainer t, long time) {
		addCycles(prospectiveMiningCycles);
		prospectiveMiningCycles = 0;
	}

	/**
	 * See {@linkplain INode#event_NodeReceivesPropagatedTransaction(Transaction, long)}
	 */
	@Override
	public void event_NodeReceivesPropagatedTransaction(Transaction t, long time) {
	}


	/**
	 * See {@linkplain INode#event_PrintPeriodicReport(long)}
	 */
	@Override
	public void event_PrintPeriodicReport(long time) {
		this.periodicReport();
	}



	/**
	 * See {@linkplain INode#event_PrintBeliefReport(long[], long)}
	 */
	@Override
	public void event_PrintBeliefReport(long[] sample, long time) {
		this.beliefReport(sample, time);
		
	}

	/**
	 * See {@linkplain INode#event_PrintStructureReport(long)}
	 */
	@Override
	public void event_PrintStructureReport(long time) {
		this.structureReport();
	}


	/**
	 * See {@linkplain INode#event_PrintStructureReport(long)}
	 */
	@Override
	public void event_NodeStatusReport(long time) {
		this.nodeStatusReport();
	}
	
	
}