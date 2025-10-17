package ca.yorku.cmg.cnsim.engine.event;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.node.IMiner;
import ca.yorku.cmg.cnsim.engine.node.INode;

/**
 * Represents an event that triggers a structure report for all nodes in the simulation.
 * <p>
 * This event extends {@linkplain Event} and overrides {@linkplain #happen(Simulation)}
 * to call {@linkplain INode#event_PrintStructureReport(long)} on every node in the simulation.
 * The report captures the current structure of each node at the scheduled simulation time.
 * </p>
 * 
 * <p>
 * Subclasses may extend this behavior, but the structure reporting is always executed.
 * </p>
 * 
 * @author 
 *   Sotirios Liaskos for the Conceptual Modeling Group @ York University
 *
 * @see Event
 * @see INode#event_PrintStructureReport(long)
 */
public class Event_Report_StructureReport extends Event {
	
	/**
	 * Executes the structure report event.
	 * <p>
	 * This method first calls {@linkplain Event#happen(Simulation)} to perform
	 * shared event bookkeeping, and then iterates over all nodes in the simulation,
	 * invoking {@linkplain INode#event_PrintStructureReport(long)} for each node.
	 * </p>
	 *
	 * @param sim the {@linkplain Simulation simulation} instance in which the event occurs
	 * @see INode#event_PrintStructureReport(long)
	 */
	public void happen(Simulation sim){
    	super.happen(sim);
		for (INode n : sim.getNodeSet().getNodes()) {
			n.event_PrintStructureReport(this.getTime());
		}
    }
}
