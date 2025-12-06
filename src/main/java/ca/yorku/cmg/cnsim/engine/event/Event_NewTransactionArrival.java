package ca.yorku.cmg.cnsim.engine.event;

import ca.yorku.cmg.cnsim.engine.ProgressBar;
import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.node.INode;
import ca.yorku.cmg.cnsim.engine.reporter.Reporter;
import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractNodeSampler;
import ca.yorku.cmg.cnsim.engine.transaction.Transaction;


/**
 * Represents an event corresponding to the arrival of a new external (client) transaction 
 * at a node within the simulation. 
 * <p>
 * When this event occurs, the associated node receives a new transaction 
 * from a client, the event and transaction are recorded by the {@linkplain Reporter}, 
 * and progress tracking is updated via the {@linkplain ProgressBar}.
 * </p>
 *
 * @author Sotirios Liaskos
 * @see INode#event_NodeReceivesClientTransaction(Transaction, long)
 * @see Reporter
 * @see ProgressBar
 */
public class Event_NewTransactionArrival extends Event {
	
	/** The new transaction arriving at the node. */
    private Transaction transaction;
    
    /** The node where the transaction arrives. */
    private INode node;
    
    /** 
     * Tracks the total number of queued transactions across all events. 
     */
    public static int totalqueuedTransactions = 0;
    
    /**
     * Constructs a new {@code Event_NewTransactionArrival}.
     *
     * @param tx    the new transaction that arrives.
     * @param n     the node where the transaction arrives.
     * @param time  the simulation time at which the event occurs.
     */
    public Event_NewTransactionArrival(Transaction tx, INode n, long time) {
    	super();
        this.node = n;
        this.transaction = tx;
        super.setTime(time);
    }



    /**
     * Executes the event logic for a new transaction arrival.
     * <p>
     * This method notifies the node of the transaction reception, 
     * logs the event and transaction to the reporter, and updates 
     * the progress bar. If the transaction is marked as seed-changing, 
     * the node sampler seeds are also updated.
     * </p>
     *
     * @param sim the simulation instance in which the event occurs.
     * @see INode#event_NodeReceivesClientTransaction(Transaction, long)
     * @see AbstractNodeSampler#updateSeed()
     */
    @Override
    public void happen(Simulation sim) {
        super.happen(sim);
        node.event_NodeReceivesClientTransaction(transaction, getTime());
        
        
        if (Reporter.reportsEvents()) {
	        Reporter.addEvent(
	        		sim.getSimID(),
	        		getEvtID(), 
	        		getTime(), 
	        		System.currentTimeMillis() - Simulation.sysStartTime, 
	        		this.getClass().getSimpleName(), 
	        		node.getID(), 
	        		transaction.getID());
        }
        
        if (Reporter.reportsTransactions()) {
        	if (transaction.getID() > Integer.MAX_VALUE) {
	        	Reporter.addTx(
	            		sim.getSimID(),
	            		transaction.getID(), 
	            		transaction.getSize(), 
	            		transaction.getValue(),
	            		getTime());        		
        	} else {
	        	Reporter.addTx(
	            		sim.getSimID(),
	            		transaction.getID(), 
	            		transaction.getSize(), 
	            		transaction.getValue(),
	            		getTime(),
	            		(int) sim.getConflictRegistry().getMatch((int) transaction.getID()));
        	}
		}
        
        ProgressBar.printProgress((int) transaction.getID(),sim.totalqueuedTransactions,4);

        // If the transaction has been marked (at TransactionWorkload) as seed changing.
        // update the node seeds. (Transaction Sampler seeds have been updated at workload creation).
        if (transaction.isSeedChanging()) {
        	sim.getSampler().getNodeSampler().updateSeed();
        }
        
    }
}
