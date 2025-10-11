package ca.yorku.cmg.cnsim.engine.event;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.node.INode;
import ca.yorku.cmg.cnsim.engine.reporter.Reporter;
import ca.yorku.cmg.cnsim.engine.transaction.ITxContainer;

/**
 * Represents an event that signifies the arrival of a propagated transaction container
 * (e.g., a validated block) at a particular node within the simulation network.
 * <p>
 * This event models the network propagation of containers between nodes.
 * When triggered, it invokes {@linkplain INode#event_NodeReceivesPropagatedContainer(ITxContainer)}
 * on the receiving node, simulating that the node has received a new container from peers.
 * </p>
 *
 * <p>Additionally, this event logs its occurrence through the {@linkplain Reporter} system,
 * allowing detailed analysis of timing and node-to-node communication.</p>
 *
 * <p>Example:</p>
 * TODO: add this example from bitcoin
 *
 * @author
 *   Sotirios Liaskos for the Conceptual Modeling Group @ York University
 * @see INode
 * @see INode#event_NodeReceivesPropagatedContainer(ITxContainer)
 * @see ITxContainer
 * @see Simulation
 * @see Reporter
 */
public class Event_ContainerArrival extends Event {  
	
	/** The transaction container (e.g., block) being propagated. */
    private ITxContainer container;
    
    /** The node at which this container arrives. */
    private INode node;

    
    /**
     * Constructs a new {@code Event_ContainerArrival} representing the arrival
     * of a specific {@linkplain ITxContainer} at a given {@linkplain INode}.
     *
     * @param txc  the container (block or transaction group) that has arrived
     * @param n    the node receiving the container
     * @param time the simulation time at which this event occurs
     */
    public Event_ContainerArrival(ITxContainer txc, INode n, long time){
    	super();
        this.node = n;
        this.container = txc;
        super.setTime(time);
    }
    


    /**
     * Executes the event’s behavior within the given simulation context.
     * <p>
     * This method triggers the receiving node’s reaction to the arrival of the
     * container and logs the event via {@linkplain Reporter}. The event is timestamped
     * both with simulation time and system wall-clock time.
     * </p>
     *
     * @param sim the active {@linkplain Simulation} instance
     * @see INode#event_NodeReceivesPropagatedContainer(ITxContainer)
     *
     * <p><b>Note:</b> Currently, all container arrival events are automatically logged.
     * Future revisions may make this conditional based on configuration
     * parameters (see TODO comment in implementation).</p>
     */
    @Override
    public void happen(Simulation sim) {
        super.happen(sim);
        node.event_NodeReceivesPropagatedContainer(container);
        //TODO: this should be conditional on some configuration parameter
        //TODO: how this reports to the parent reporting
        Reporter.addEvent(
        		sim.getSimID(),
        		this.getEvtID(), 
        		this.getTime(), 
        		System.currentTimeMillis() - Simulation.sysStartTime, 
        		this.getClass().getSimpleName(), 
        		node.getID(), 
        		container.getID());
    }

}
