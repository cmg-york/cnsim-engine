package ca.yorku.cmg.cnsim.engine.event;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.node.INode;

/**
 * Represents a periodic reporting event in the simulation.
 * <p>
 * This abstract event triggers all nodes in the simulation to generate
 * their periodic reports at the event's scheduled simulation time.
 * It extends {@linkplain Event} and overrides {@linkplain #happen(Simulation)}
 * to call each node's {@linkplain INode#event_PrintPeriodicReport(long)}
 * method.
 * </p>
 * 
 * <p>
 * Subclasses may define additional behavior, but the periodic report logic
 * is always executed by this base class.
 * </p>
 * 
 * @author 
 *   Sotirios Liaskos for the Conceptual Modeling Group @ York University
 *
 * @see Event
 * @see INode#event_PrintPeriodicReport(long)
 */
public abstract class Event_Report_PeriodicReport extends Event {
	
    /**
     * Executes the periodic report event.
     * <p>
     * This method first calls {@linkplain Event#happen(Simulation)} to perform
     * shared bookkeeping, then iterates over all nodes in the simulation,
     * invoking {@linkplain INode#event_PrintPeriodicReport(long)} for each node.
     * </p>
     *
     * @param sim the {@linkplain Simulation simulation} instance in which the event occurs
     * @see INode#event_PrintPeriodicReport(long)
     */
    public void happen(Simulation sim){
    	super.happen(sim);
		for (INode n : sim.getNodeSet().getNodes()) {
			n.event_PrintPeriodicReport(this.getTime());
		}
    }
}
