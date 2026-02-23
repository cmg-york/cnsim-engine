package ca.yorku.cmg.cnsim.engine.event;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.node.INode;
import ca.yorku.cmg.cnsim.engine.reporter.Reporter;

/**
 * Represents an event that triggers a belief report for all nodes in the simulation, relative to a set of sample transactions, defined in the configuration.
 * <p>
 * This event extends {@linkplain Event} and overrides {@linkplain #happen(Simulation)}
 * to call {@linkplain INode#event_PrintBeliefReport(long[] , long)} on every node in the simulation.
 * The report captures the current beliefs of each node at the scheduled simulation time.
 * </p>
 * 
 * <p>
 * Subclasses may extend this behavior, but the belief reporting is always executed.
 * </p>
 * 
 * @author 
 *   Sotirios Liaskos for the Conceptual Modeling Group @ York University
 *
 * @see Event
 * @see INode#event_PrintBeliefReport(long[], long)
 */
public class Event_Report_BeliefReport extends Event {
	
	/** The sample transactions for the belief report. */
	private long[] sampleTx;
	
	/**
	 * Constructs a new {@code Event_Report_BeliefReport}. The sample transactions are read from the configuration property {@code workload.sampleTransaction}.
	 *
	 * @param time  the simulation time at which the event occurs
	 */
	public Event_Report_BeliefReport(long time){
		super.setTime(time);
		this.sampleTx = Config.parseStringToArray(Config.getPropertyString("workload.sampleTransaction"));
	}
	
	/**
	 * Executes the belief report event.
	 * <p>
	 * This method first calls {@linkplain Event#happen(Simulation)} to perform
	 * shared event bookkeeping, and then iterates over all nodes in the simulation,
	 * invoking {@linkplain INode#event_PrintBeliefReport(long[], long)} for each node with the sample transactions.
	 * </p>
	 *
	 * @param sim the {@linkplain Simulation simulation} instance in which the event occurs
	 * @see INode#event_PrintBeliefReport(long[], long)
	 */
	public void happen(Simulation sim){
    	super.happen(sim);
		for (INode n : sim.getNodeSet().getNodes()) {
			n.event_PrintBeliefReport(sampleTx,this.getTime());
		}
        if (Reporter.reportsEvents() && Reporter.reportsBeliefEvents()) {
	        Reporter.addEvent(
	        		sim.getSimID(),
	        		getEvtID(), 
	        		getTime(), 
	        		System.currentTimeMillis() - Simulation.sysStartTime, 
	        		this.getClass().getSimpleName(), 
	        		-1, 
	        		-1,
	        		"");
        }
    }
}
