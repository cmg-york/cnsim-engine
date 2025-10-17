package ca.yorku.cmg.cnsim.engine.event;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.node.INode;
import ca.yorku.cmg.cnsim.engine.reporter.Reporter;
import ca.yorku.cmg.cnsim.engine.transaction.ITxContainer;

/**
 * Represents a simulation event where a node validates a container, such as a block.
 * <p>
 * This event occurs when a specific {@linkplain INode node} completes the validation
 * of a {@linkplain ITxContainer container}. Upon execution, the node's validation
 * logic is invoked, and a corresponding event record is added to the
 * {@linkplain Reporter Reporter}.
 * </p>
 *
 * <p>
 * If the event has been marked as ignored (via
 * {@linkplain #ignoreEvt(boolean)}), the event does not trigger validation
 * and is instead logged as <code>_Abandoned</code> in the event report.
 * </p>
 *
 * @author
 *   Sotirios Liaskos for the Conceptual Modeling Group @ York University
 *
 * @see Event
 * @see ITxContainer
 * @see INode
 * @see INode#event_NodeCompletesValidation(ITxContainer, long)
 * @see Reporter
 */
public class Event_ContainerValidation extends Event {
	
	 /** The container being validated. */
    private ITxContainer container;
    
    /** The node performing the validation. */
    private INode node;

    
    /**
     * Constructs a new {@code Event_ContainerValidation}.
     *
     * @param txc   the {@linkplain ITxContainer container} to validate
     * @param n     the {@linkplain INode node} performing the validation
     * @param time  the simulation time at which this event occurs
     */
    public Event_ContainerValidation(ITxContainer txc, INode n, long time){
    	super();
        this.node = n;
        this.container = txc;
        super.setTime(time);
    }

    /**
     * Executes the event within the given {@linkplain Simulation simulation} context.
     * <p>
     * This method first calls {@linkplain Event#happen(Simulation)} to perform
     * shared event bookkeeping (including ID assignment and periodic reporting).
     * It then invokes {@linkplain INode#event_NodeCompletesValidation(ITxContainer, long)}
     * on the associated node, unless the event has been marked as ignored.
     * Finally, the event outcome is logged using {@linkplain Reporter#addEvent}.
     * </p>
     *
     * @param sim the {@linkplain Simulation simulation} instance in which the event occurs
     */
    @Override
    public void happen(Simulation sim) {
        super.happen(sim);
        String status = "";
        if (!super.ignoreEvt()) {
        	node.event_NodeCompletesValidation(container, getTime());
        } else {
        	status = "_Abandonded";
        }

        if (Reporter.reportsEvents()) {
            Reporter.addEvent(
            		sim.getSimID(),
            		getEvtID(), 
            		getTime(), 
            		System.currentTimeMillis() - Simulation.sysStartTime, 
            		this.getClass().getSimpleName() + status, 
            		node.getID(), 
            		container.getID());
        }
    }

}
