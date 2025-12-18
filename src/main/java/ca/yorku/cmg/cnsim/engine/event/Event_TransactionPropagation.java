package ca.yorku.cmg.cnsim.engine.event;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.node.IMiner;
import ca.yorku.cmg.cnsim.engine.node.INode;
import ca.yorku.cmg.cnsim.engine.reporter.Reporter;
import ca.yorku.cmg.cnsim.engine.transaction.Transaction;

/**
 * Represents an event for the propagation of a transaction within the simulation.
 * <p>
 * When this event occurs, a specific {@linkplain IMiner node} receives a
 * propagated {@linkplain Transaction transaction} from another node (not from a client). 
 * The event triggers the node's transaction propagation logic and logs the event using
 * {@linkplain Reporter}.
 * </p>
 *
 * <p>
 * This class extends {@linkplain Event} and implements the {@linkplain #happen(Simulation)}
 * method to define the behavior specific to transaction propagation events.
 * </p>
 * 
 * @author 
 *   Sotirios Liaskos for the Conceptual Modeling Group @ York University
 *
 * @see Event
 * @see INode#event_NodeReceivesPropagatedTransaction(Transaction, long)
 * @see Reporter
 * @see Transaction
 */
public class Event_TransactionPropagation extends Event {
	
    /** The transaction being propagated. */
    private Transaction trans;

    /** The node receiving the propagated transaction. */
    private INode node;

    
    /**
     * Constructs a new {@code Event_TransactionPropagation}.
     *
     * @param t     the {@linkplain Transaction transaction} being propagated
     * @param n     the {@linkplain IMiner node} receiving the transaction
     * @param time  the simulation time at which the event occurs
     */
    public Event_TransactionPropagation(Transaction t, INode n, long time){
    	super();
        this.node = n;
        this.trans = t;
        super.setTime(time);
    }

    /**
     * Executes the transaction propagation event in the simulation.
     * <p>
     * This method first calls {@linkplain Event#happen(Simulation)} to perform
     * shared event bookkeeping (such as ID assignment and periodic reporting). 
     * Then it invokes {@linkplain INode#event_NodeReceivesPropagatedTransaction(Transaction, long)}
     * on the associated node and logs the event using {@linkplain Reporter#addEvent}.
     * </p>
     *
     * @param sim the {@linkplain Simulation simulation} instance in which the event occurs
     * @see INode#event_NodeReceivesPropagatedTransaction(Transaction, long)
     */
    @Override
    public void happen(Simulation sim) {
        super.happen(sim);
        node.event_NodeReceivesPropagatedTransaction(trans, getTime());
        if (Reporter.reportsEvents()) {
	        Reporter.addEvent(
	        		sim.getSimID(),
	        		getEvtID(), 
	        		getTime(), 
	        		System.currentTimeMillis() - Simulation.sysStartTime, 
	        		this.getClass().getSimpleName(), 
	        		node.getID(), 
	        		trans.getID(),
	        		"");
        }
    }

}
