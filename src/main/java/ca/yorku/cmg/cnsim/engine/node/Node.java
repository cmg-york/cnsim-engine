package ca.yorku.cmg.cnsim.engine.node;

import java.util.ArrayList;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.event.Event;
import ca.yorku.cmg.cnsim.engine.event.Event_ContainerArrival;
import ca.yorku.cmg.cnsim.engine.event.Event_TransactionPropagation;
import ca.yorku.cmg.cnsim.engine.transaction.ITxContainer;
import ca.yorku.cmg.cnsim.engine.transaction.Transaction;
import ca.yorku.cmg.cnsim.engine.transaction.TransactionGroup;

/**
 * Abstract class representing a node in a blockchain network.
 * 
 * @author Sotirios Liaskos for the Conceptual Modeling Group @ York University
 * 
 */
public abstract class Node implements INode {

	protected static int currID = 1;
	protected int ID;
	
	protected Simulation sim;
	
	protected TransactionGroup pool;
	protected Event nextValidationEvent;
	
	protected long networkInterfaceBusyUntil = -1;
	

	

	
	// 
	//   C O N S T R U C T O R
	//
	public Node(Simulation sim) {
		super();
        this.sim = sim;
        pool = new TransactionGroup();
        ID = getNextNodeID();
	}

	// 
	//   For testing only
	//
	public Node() {
		super();
        pool = new TransactionGroup();
        ID = getNextNodeID();
	}


	// -----------------------------------------------------------------
	// A C T I O N S
	// -----------------------------------------------------------------
	
	
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
	 * Computes the end time of the next transmission starting at or after the given
	 * current time, taking into account the time until which the network interface
	 * is already busy.
	 *
	 * <p>If the interface is free at {@code currTime}, meaning either it has never
	 * been used (busy time = -1) or its busy-until time is earlier than
	 * {@code currTime}, then the next transmission begins immediately at
	 * {@code currTime} and ends at {@code currTime + transDuration}.
	 *
	 * <p>If the interface is still busy at {@code currTime}, the next transmission
	 * begins only after {@code networkInterfaceBusyUntil}, and ends at
	 * {@code networkInterfaceBusyUntil + transDuration}.
	 *
	 * @param currTime       the current simulation time (must be ≥ 0)
	 * @param transDuration  the duration of the transmission (must be ≥ 0)
	 * @return the time at which the next transmission will end
	 */
	 /*@ 
	   @ requires currTime >= 0;
	   @ requires transDuration >= 0;
	   @
	   @ // Case 1: interface free or never used
	   @ ensures (networkInterfaceBusyUntil == -1 
	   @          || networkInterfaceBusyUntil < currTime)
	   @        ==> \result == currTime + transDuration;
	   @
	   @ // Case 2: interface busy past currTime
	   @ ensures (networkInterfaceBusyUntil != -1
	   @          && networkInterfaceBusyUntil >= currTime)
	   @        ==> \result == networkInterfaceBusyUntil + transDuration;
	   @
	   @ // Result is always at least currTime
	   @ ensures \result >= currTime;
	   @
	   @ // Does not modify object state
	   @ assignable \nothing;
	   @*/
	public long getNextTransmissionEndTime(long currTime, long transDuration) {
		long returnTime;

		if (currTime < 0 || transDuration < 0) {
			throw new RuntimeException("Both arguments must be non-negative.");
		}
		
		if ((networkInterfaceBusyUntil == -1) || (networkInterfaceBusyUntil < currTime )) {
			//Uninitalized or last transmission ended in the past.
			returnTime = currTime + transDuration;
		} else { 
			//Last transmission ends at networkInterfaceBusyUntil
			returnTime = networkInterfaceBusyUntil + transDuration;
		}
		
		if (returnTime < currTime) {
			throw new RuntimeException("Next scheduled time is less than the current time.");
		}
		
		return(returnTime);
	}

	/**
	 * Sets the time until which the network interface is considered busy.
	 *
	 * <p>A value of -1 may be used to indicate that the interface has never been
	 * used or is currently idle with no pending transmissions.
	 *
	 * @param latestBusyUntil the simulation time at which the interface will become free again
	 */
	 /*@
	   @ // Allow any non-negative busy-until time
	   @ requires latestBusyUntil >= 0;
	   @
	   @ // State update: the field must equal the argument afterward
	   @ ensures networkInterfaceBusyUntil == latestBusyUntil;
	   @
	   @ // Only this field is modified
	   @ assignable networkInterfaceBusyUntil;
	   @*/
	public void setNetworkInterfaceBusyUntil(long latestBusyUntil) {
		networkInterfaceBusyUntil  = latestBusyUntil;
	}
	
	/**
	 * Propagates the specified transaction container to other nodes in the simulation.
	 * TODO: All time references should be on a global time parameter. 
	 * @param txc The transaction container to be propagated.
	 * @param time The current simulation time.
	 */
	public void broadcastContainer(ITxContainer txc, long time) {
	    NodeSet nodes = sim.getNodeSet();
	    ArrayList<INode> ns_list = nodes.getNodes();
	    for (INode n : ns_list) {
	        if (!n.equals(this)){
	            long inter = sim.getNetwork().getTransmissionTime(this.getID(), n.getID(), txc.getSize());
	            long scheduleTime = getNextTransmissionEndTime(time, inter);
	            Event_ContainerArrival e = new Event_ContainerArrival(txc, n, scheduleTime);
	            sim.schedule(e);
	            setNetworkInterfaceBusyUntil(scheduleTime);
	        }
	    }
	}
	
	/**
	 * 
	 * Propagates the specified transaction to other nodes in the simulation.
	 * @param t The transaction to be propagated.
	 * @param time The current time in the simulation.
	 */
	public void broadcastTransaction(Transaction t, long time) {
	    NodeSet nodes = sim.getNodeSet();
	    ArrayList<INode> ns_list = nodes.getNodes();
	    for (INode n : ns_list) {
	        if (!n.equals(this)){
	            long inter = sim.getNetwork().getTransmissionTime(this.getID(), n.getID(), t.getSize());
	            
	            if (inter<0) {
	            	String error = "Error in 'propagateTransaction' Negative interval between " + this.getID() + " and " + n.getID() + " for size " + t.getSize() + " of transaction " + t.getID() +  " interval is " + inter;
	            	throw new RuntimeException(error);
	            }

	            //TODO: do something more elaborate perhaps
	            //inter += Config.getPropertyInt("net.propagationTime");
	            
	            long scheduleTime = getNextTransmissionEndTime(time, inter);
	            Event_TransactionPropagation e = new Event_TransactionPropagation(t, n, scheduleTime);
	            sim.schedule(e);
	            setNetworkInterfaceBusyUntil(scheduleTime);
	        }
	    }
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


	/**
	 * See ({@linkplain IMiner} interface.
	 */
	@Override
	public float getAverageConnectedness() {
		return(sim.getNetwork().getAvgTroughput(getID()));
	}


	
	// -----------------------------------------------------------------
	// EVENT HANDLERS / BEHAVIORS
	// -----------------------------------------------------------------
		
	/**
	 * {@inheritDoc}
	 */
	@Override
	public abstract void event_NodeCompletesValidation(ITxContainer t, long time);

	/**
	 * {@inheritDoc}
	 */
	@Override
	public abstract void event_NodeReceivesPropagatedTransaction(Transaction t, long time);

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void event_PrintPeriodicReport(long time) {
		this.periodicReport();
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void event_PrintBeliefReport(long[] sample, long time) {
		this.beliefReport(sample, time);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void event_PrintStructureReport(long time) {
		this.structureReport();
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void event_NodeStatusReport(long time) {
		this.nodeStatusReport();
	}
}