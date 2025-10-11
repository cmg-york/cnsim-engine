package ca.yorku.cmg.cnsim.engine.reporter;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.event.Event_Report_BeliefReport;


/**
 * Factory class for scheduling periodic {@linkplain Event_Report_BeliefReport} events
 * in a {@linkplain Simulation}. To be used during, e.g., simulation setup.
 * <p>
 * Provides methods to schedule belief reporting either at fixed time intervals or based
 * on a specified number of reports over the simulation duration.
 * </p>
 * 
 * <p>
 * The scheduled events can then be executed by the simulation to collect and report
 * the beliefs of nodes at the specified times.
 * </p>
 * 
 * @author
 *   Sotirios Liaskos for the Conceptual Modeling Group @ York University
 */
public class ReportEventFactory {
	
	/**
	 * Schedules {@linkplain Event_Report_BeliefReport} events at fixed intervals
	 * throughout the simulation duration, adjusted by an offset.
	 * <p>
	 * Events are scheduled starting from the specified interval up to the latest
	 * known event time in the simulation plus the offset.
	 * </p>
	 *
	 * @param interval  the time interval between consecutive belief report events
	 * @param sim       the {@linkplain Simulation simulation} instance where events are scheduled
	 * @param offset    a time offset added to the latest known event time to determine scheduling range
	 */
	public void scheduleBeliefReports_Interval(long interval, Simulation sim, long offset) {
		long t, max;
		t = interval;
		max = sim.getLatestKnownEventTime() + offset;
		while (t <= max) {
			sim.schedule(new Event_Report_BeliefReport(t));
			t += interval;
		}
	}
	
	/**
	 * Schedules a specified number of {@linkplain Event_Report_BeliefReport} events
	 * evenly distributed over the simulation duration, adjusted by an offset.
	 * <p>
	 * The interval between events is calculated based on the total duration
	 * (latest known event time plus offset) divided by the desired count of events.
	 * </p>
	 *
	 * @param count   the total number of belief report events to schedule
	 * @param sim     the {@linkplain Simulation simulation} instance where events are scheduled
	 * @param offset  a time offset added to the latest known event time to determine scheduling range
	 */
	public void scheduleBeliefReports_Count(long count, Simulation sim, long offset) {
		long interval = (sim.getLatestKnownEventTime() + offset)/count;
		scheduleBeliefReports_Interval(interval, sim, offset);
	}
	
}
