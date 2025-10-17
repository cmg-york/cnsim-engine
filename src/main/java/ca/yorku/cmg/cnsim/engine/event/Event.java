package ca.yorku.cmg.cnsim.engine.event;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.node.IMiner;
import ca.yorku.cmg.cnsim.engine.node.INode;
import ca.yorku.cmg.cnsim.engine.transaction.ITxContainer;
import ca.yorku.cmg.cnsim.engine.transaction.Transaction;

/**
 * Represents a single discrete occurrence within the event-driven simulation.
 * <p>
 * An {@code Event} encapsulates the notion of something happening at a particular
 * simulation time. Subclasses specialize this class to define concrete simulation
 * actions (for example, container arrivals, transaction propagation, etc.).
 * </p>
 *
 * <p>Each event maintains a unique identifier, a simulation time, and an optional
 * flag indicating whether it should be ignored (useful for disregarding future events).</p>
 *
 * @author 
 *     Sotirios Liaskos for the Conceptual Modeling Group @ York University
 */
public class Event {
	
	/** A global counter for assigning unique event IDs. */
	public static long currID = 1;

	/** The ID of the current event object. */
	public long evtID = 1;
	
	/** If true, the event will be ignored when processed. Useful for disregarding future events. */
	protected boolean ignore = false;
	
	/** The simulation time at which the event occurs. */
    private long time;

    
	// -----------------------------------------------------------------
    // ID MANAGEMENT
    // -----------------------------------------------------------------
    
    
    /**
     * Retrieves the next unique event identifier.
     *
     * @return The next available event ID.
     */
	public static long getNextEventID() {
		return(currID++);
	}
	

    /**
     * Returns the unique identifier of this event instance.
     * IDs are assigned at the time the event is processed.
     *
     * @return The event ID.
     */
	public long getEvtID() {
		return evtID;
	}
	
	
	// -----------------------------------------------------------------
	// SETTERS AND GETTERS
	// -----------------------------------------------------------------
	
    /**
     * Sets the time of occurrence for this event.
     *
     * @param time The simulation time (must be non-negative).
     * @throws ArithmeticException if {@code time < 0}.
     */
    public void setTime(long time) {
    	if(time < 0)
    		throw new ArithmeticException("Time < 0");
        this.time = time;
    }

    /**
     * Returns the simulation time at which this event occurs.
     *
     * @return The event's simulation time.
     */
    public long getTime() {
        return time;
    }
    
    
	// -----------------------------------------------------------------
	// EVENT IGNORING
	// -----------------------------------------------------------------
    
    /**
     * Indicates whether this event should be ignored by the simulator.
     * Useful for canceling future events or suppressing redundant actions.
     *
     * @return {@code true} if the event should be ignored; {@code false} otherwise.
     */
    public boolean ignoreEvt() {
    	return ignore;
    }
    
    
    /**
     * Sets whether this event should be ignored.
     *
     * @param ignoreEvt {@code true} to ignore the event, {@code false} otherwise.
     */
    public void ignoreEvt(boolean ignoreEvt) {
    	ignore = ignoreEvt;
    }
    
    
    
    /**
     * Executes the event in the context of a simulation.
     * <p>
     * This base implementation:
     * <ul>
     *   <li>Assigns a unique event ID.</li>
     *   <li>Triggers periodic reporting on all nodes based on the
     *       configured reporting window (see {@linkplain Config}).</li>
     *   <li>Triggers a time advancement report on each {@linkplain IMiner}.</li>
     * </ul>
     * Subclasses typically override this method to implement specific behaviors. Howver, Subclasses must call {@code super.happen(sim)} to allow the base functionality to execute.
     * TODO: introduce template method pattern to enforce calling super.happen(sim)
     * @param sim The active {@linkplain Simulation} instance.
     */
    public void happen(Simulation sim){
    	evtID = getNextEventID();
 
    	// Every little while ask node if it wants to print any period reports.
    	if ((currID % Config.getPropertyLong("reporter.reportingWindow")) == 0) {
    		for (INode n : sim.getNodeSet().getNodes()) {
    			n.periodicReport();
    		}
    	}

    	// Ask node if it wants to print Node report.
		for (INode n : sim.getNodeSet().getNodes()) {
			n.timeAdvancementReport();
		}
    	
    }
   
	// -----------------------------------------------------------------
	// DEBUGGING AND PRINTING
	// -----------------------------------------------------------------
    
    
    /**
     * Prints a debug message describing the event and its associated transaction.
     * This is intended for development and tracing only.
	 * TODO: remove the parameters and make it specific on the event data.
     *
     * @param msg   A message prefix to display.
     * @param tx    The relevant {@linkplain Transaction} instance.
     * @param n     The relevant {@linkplain IMiner} instance.
     * @param tim   The simulation time.
     * @param delay The delay (in milliseconds) before continuing execution.
     */
	public void debugPrint(String msg, Transaction tx, INode n, long tim, long delay) {
		System.out.println(msg + tx.getID() + " node " + n.getID() + " time " + tim);
		try {
			Thread.sleep(delay);
		} catch (InterruptedException e) {e.printStackTrace();}
	}

	
    /**
     * Prints a debug message describing the event and its associated transaction container.
     * This is intended for development and tracing only.
     *
     * @param msg   A message prefix to display.
     * @param txc   The relevant {@linkplain ITxContainer} instance.
     * @param n     The relevant {@linkplain IMiner} instance.
     * @param tim   The simulation time.
     * @param delay The delay (in milliseconds) before continuing execution.
     */
	public void debugPrint(String msg, ITxContainer txc, INode n, long tim, long delay) {
		System.out.println(msg + txc.printIDs(",") + " node " + n.getID() + " time " + tim);
		try {
			Thread.sleep(500);
		} catch (InterruptedException e) {e.printStackTrace();}
	}

}
