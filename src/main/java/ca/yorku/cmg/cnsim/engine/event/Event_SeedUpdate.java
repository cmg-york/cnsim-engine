package ca.yorku.cmg.cnsim.engine.event;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.reporter.Reporter;
import ca.yorku.cmg.cnsim.engine.sampling.interfaces.IMultiSowable;

 /**
 * Represents an event for updating the random seed of a multi-sowable sampler within the simulation.
 * <p>
 * When this event occurs, the associated {@linkplain IMultiSowable sampler} updates its random seed.
 * The event also logs the occurrence using {@linkplain Reporter}.
 * </p>
 *
 * <p>
 * This class extends {@linkplain Event} and implements the {@linkplain #happen(Simulation)}
 * method to define the behavior specific to seed update events.
 * </p>
 * 
 * @author 
 *   Sotirios Liaskos for the Conceptual Modeling Group @ York University
 *
 * @see Event
 * @see IMultiSowable
 * @see IMultiSowable#updateSeed()
 * @see Reporter
 */
public class Event_SeedUpdate extends Event {
	
	/** The multi-sowable sampler whose seed is to be updated. */
	IMultiSowable sampler;
	
	/** The new random seed value (if needed for reference). */
	long randomSeed;
	
    /**
	 * Constructs a new {@code Event_SeedUpdate}.
	 *
	 * @param sampler the {@linkplain IMultiSowable sampler} whose seed will be updated
	 * @param time    the simulation time at which the event occurs
	 */
    public Event_SeedUpdate(IMultiSowable sampler, long time){
    	super();
    	this.sampler = sampler;
    	super.setTime(time);
    }
    

	/**
	 * Executes the seed update event in the simulation.
	 * <p>
	 * This method first calls {@linkplain Event#happen(Simulation)} to perform
	 * shared event bookkeeping (such as ID assignment and periodic reporting). 
	 * Then it invokes {@linkplain IMultiSowable#updateSeed()} on the associated sampler
	 * and logs the event using {@linkplain Reporter#addEvent}.
	 * </p>
	 *
	 * @param sim the current {@linkplain Simulation simulation} context
	 * @see IMultiSowable#updateSeed()
	 */
    @Override
    public void happen(Simulation sim) {
        super.happen(sim);
        sampler.updateSeed();
        if (Reporter.reportsEvents()) {
	        Reporter.addEvent(
	        		sim.getSimID(),
	        		this.getEvtID(), 
	        		this.getTime(), 
	        		System.currentTimeMillis() - Simulation.sysStartTime, 
	        		this.getClass().getSimpleName(), 
	        		-1, 
	        		-1);
        }
    }
}
