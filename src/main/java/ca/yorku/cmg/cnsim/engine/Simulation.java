package ca.yorku.cmg.cnsim.engine;


import ca.yorku.cmg.cnsim.engine.event.Event;
import ca.yorku.cmg.cnsim.engine.event.EventTimeComparator;
import ca.yorku.cmg.cnsim.engine.event.Event_NewTransactionArrival;
import ca.yorku.cmg.cnsim.engine.network.AbstractNetwork;
import ca.yorku.cmg.cnsim.engine.node.NodeSet;
import ca.yorku.cmg.cnsim.engine.reporter.Reporter;
import ca.yorku.cmg.cnsim.engine.sampling.Sampler;
import ca.yorku.cmg.cnsim.engine.transaction.Transaction;
import ca.yorku.cmg.cnsim.engine.transaction.TransactionWorkload;
import ca.yorku.cmg.cnsim.engine.transaction.TxConflictRegistry;

import java.util.PriorityQueue;


/*
 * TODO: Complete and reformat the comments.
 */

/**
 * The central class of any simulation
 *  
 * @author Sotirios Liaskos for the Conceptual Modeling Group @ York University
 * 
 */
public class Simulation {

	public static long currTime; //Current simulation time
	public static long sysStartTime; //Real start time of the simulation
	public static long sysEndTime; //Real end time of the simulation
	public static int currentSimulationID = 1; //The ID of the current simulation

	private int simID; //The ID of this simulation

	private final EventTimeComparator comp = new EventTimeComparator();
	
	//The main Events Queue
	protected PriorityQueue<Event> queue = new PriorityQueue<>(comp);
	
	//The network relating to the simulator
	private AbstractNetwork net;

	protected Sampler sampler;
	
	private TxConflictRegistry conflictRegistry;
	
	private TransactionWorkload workload;

	public int totalqueuedTransactions = 0;
	private long latestKnownEventTime = 0;

	//Externally set termination time
	private long terminationTime = 0;
	
	//Event statistics
	private long numEventsScheduled = 0;
	private long numEventsProcessed = 0;

	
	
	/* 
	 * 
	 *  C O N S T R U C T O R S
	 * 
	 */
	
	
	public Simulation(int simID) {
		this.simID = simID;
		currentSimulationID = simID;
	}

	
	public Simulation(Sampler a, int simID) {
		this(simID);
	    this.sampler = a;
	}
	
	

	/*
	 * 
	 * S T A T I S T I C S 
	 * 
	 */
	
	
	public String getStatistics() {
		String s;
		s = "    Total Simulation Time: " + currTime + " (ms)\n";
		s = s + "    Total Real Time: " + (sysEndTime - sysStartTime) + " (ms)\n";
		s = s + "    Speed-up factor: " + currTime/(sysEndTime - sysStartTime) + "\n";
		s = s + "    Total Events Scheduled: " + numEventsScheduled + "\n";
		s = s + "    Total Events Processed: " + numEventsProcessed + "\n";
		return(s);
	}
	

	
	
	/*
	 * 
	 *  E V E N T   S C H E D U L I N G   R O U T I NE S
	 * 
	 */
	
	

	/**
	 * Schedules an event by adding it to the queue.
	 *
	 * @param e The Event object to be scheduled.
	 */
	public void schedule(Event e) {
		if (e.getTime() > this.latestKnownEventTime) {
			this.latestKnownEventTime = e.getTime();
		}
		numEventsScheduled++;
	    queue.add(e);
	}

	
	/**
	 * TODO: this needs to be moved to the TransactionWorkload class. Propose a refactoring.
	 * 
	 * Schedules a set of transactions given in the form of a TransactionWorkload object by adding them to the events queue.
	 * For each transaction in the TransactionSet, an Event_NewTransactionArrival event is created and scheduled.
	 * If the transaction's nodeID is -1, a random node from the network's NodeSet is selected.
	 * Otherwise, the transaction is assigned to the specific node with the given nodeID.
	 *
	 * @param ts The TransactionWorkload object containing the set of transactions to be scheduled.
	 */
	public void schedule(TransactionWorkload ts) {
        Event_NewTransactionArrival e;
		for (Transaction t : ts.getTransactions()) {
			if (t.getNodeID() == -1) {
				e = new Event_NewTransactionArrival(t, this.net.getNodeSet().pickRandomNode(), t.getCreationTime());
			} else {
				e = new Event_NewTransactionArrival(t, this.net.getNodeSet().pickSpecificNode(t.getNodeID()), t.getCreationTime());
			}
	        this.schedule(e);
		}
		this.totalqueuedTransactions += ts.getCount();
	}

	
	
	/**
	 * 
	 *  M A I N   S I M U L A T I O N   L O O P
	 * 
	 */

	
	/**
	 * Runs the main loop of the simulation.
	 * The method continuously processes events from the queue until it is empty.
	 * For each event in the queue, the method performs the following steps:
	 * 1. Retrieves the next event from the front of the queue by using the `poll` method, which also removes it from the queue.
	 * 2. Updates the current global simulation time to match the time of the retrieved event.
	 * 3. Calls the `happen` method on the event object, passing the current object (`this`) as an argument to handle the event.
	 */
	
	public void run() {
	    //MainLoop
		sysStartTime = System.currentTimeMillis();
	    Event e;
	    while (!queue.isEmpty()){
	        e = queue.poll(); //it removes the last element of the queue
	        numEventsProcessed++;
            Simulation.currTime = e.getTime();
            if (Simulation.currTime > this.terminationTime) {
            	System.out.println("\n\n    Sim #" + this.getSimID() + ": reached termination time. Ignoring remaining queue and exiting.");
            	break;
            }
            e.happen(this);
	    }
		sysEndTime = System.currentTimeMillis();
		
		Reporter.addExecTimeEntry(this.simID, currTime, sysStartTime, sysEndTime, numEventsScheduled, numEventsProcessed);
		
	}
	
	
	public void closeNodes() {
		getNodeSet().closeNodes();
	}
	
	
	/*
	 * 
	 * G E T T E R S   A N D  S E T T E R S
	 * 
	 */
	
	
	public long getLatestKnownEventTime() {
		return latestKnownEventTime;
	}

	public long getNumEventsScheduled() {
		return numEventsScheduled;
	}
	
	public long getNumEventsProcessed() {
		return numEventsProcessed;
	}

	public void setTerminationTime(long terminationTime) {
		this.terminationTime = terminationTime;
	}

		
	public int getSimID() {
		return (simID);
	}


	/**
	 * Retrieves the network associated with this Simulation object.
	 *
	 * @return The AbstractNetwork object representing the network.
	 */
	public AbstractNetwork getNetwork() {
	    return net;
	}

	
	/**
	 * Sets the network associated with this Simulation object.
	 *
	 * @param net The AbstractNetwork object to be set as the network.
	 */
	public void setNetwork(AbstractNetwork net) {
	    this.net = net;
	}

	
	/**
	 * Retrieves the Sampler object associated with this Simulation object.
	 *
	 * @return The Sampler object representing the sampler.
	 */
	public Sampler getSampler() {
	    return sampler;
	}

	
	/**
	 * Sets the Sampler associated with this object.
	 *
	 * @param sampler The Sampler object to be set as the sampler.
	 */
	public void setSampler(Sampler sampler) {
	    this.sampler = sampler;
	}
	
	
	/**
	 * Retrieves the NodeSet (set of participating nodes) from the associated Network object.
	 *
	 * @return The NodeSet object representing the set of nodes in the network.
	 */
	public NodeSet getNodeSet() {
	    return(this.net.getNodeSet());
	}


	public PriorityQueue<Event> getQueue() {
		return queue;
	}
	
	
	public TxConflictRegistry getConflictRegistry() {
		return conflictRegistry;
	}


	public void setConflictRegistry(TxConflictRegistry conflictRegistry) {
		this.conflictRegistry = conflictRegistry;
	}

	public TransactionWorkload getWorkload() {
		return workload;
	}

	public void setWorkload(TransactionWorkload workload) {
		this.workload = workload;
	}
	
	
}







