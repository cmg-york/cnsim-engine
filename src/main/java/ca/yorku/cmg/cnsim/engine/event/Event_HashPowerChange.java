package ca.yorku.cmg.cnsim.engine.event;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.node.IMiner;
import ca.yorku.cmg.cnsim.engine.node.INode;
import ca.yorku.cmg.cnsim.engine.reporter.Reporter;

/**
 * Represents an event that changes the hashpower of a node in the simulation.
 * <p>
 * When this event occurs, the associated node's hashpower is updated to the
 * new specified value. This allows for dynamic changes in mining power during
 * the simulation, such as simulating hardware upgrades, network changes, or
 * other events that affect a node's computational capacity.
 * </p>
 * <p>
 * The event can be scheduled at any simulation time to change a node's hashpower
 * at that point in the simulation timeline.
 * </p>
 *
 * @author Amirreza Radjou for the Conceptual Modeling Group @ York University
 * @see IMiner#setHashPower(float)
 * @see IMiner#getHashPower()
 * @see Reporter
 */
public class Event_HashPowerChange extends Event {
	
	/** The node whose hashpower will be changed. */
	private IMiner node;
	
	/** The new hashpower value to set (in Gigahashes per second). */
	private float newHashPower;
	
	/** The previous hashpower value (for reporting purposes). */
	private float oldHashPower;
	
	/**
	 * Constructs a new {@code Event_HashPowerChange}.
	 *
	 * @param node the node whose hashpower will be changed (must implement {@link IMiner})
	 * @param newHashPower the new hashpower value in Gigahashes per second (GH/s)
	 * @param time the simulation time at which the event occurs
	 * @throws IllegalArgumentException if the node is not an instance of {@link IMiner} or if newHashPower is negative
	 */
	public Event_HashPowerChange(INode node, float newHashPower, long time) {
		super();
		if (!(node instanceof IMiner)) {
			throw new IllegalArgumentException("Node must implement IMiner interface to change hashpower");
		}
		if (newHashPower < 0) {
			throw new IllegalArgumentException("Hash power cannot be negative: " + newHashPower);
		}
		this.node = (IMiner) node;
		this.newHashPower = newHashPower;
		this.oldHashPower = this.node.getHashPower();
		super.setTime(time);
	}
	
	/**
	 * Executes the event logic for changing a node's hashpower.
	 * <p>
	 * This method updates the node's hashpower to the new value and logs
	 * the event to the reporter if event reporting is enabled.
	 * </p>
	 *
	 * @param sim the simulation instance in which the event occurs
	 * @see IMiner#setHashPower(float)
	 */
	@Override
	public void happen(Simulation sim) {
		super.happen(sim);
		
		// Update the node's hashpower
		node.setHashPower(newHashPower);
		
		// Report the event if reporting is enabled
		if (Reporter.reportsEvents()) {
			Reporter.addEvent(
				sim.getSimID(),
				getEvtID(),
				getTime(),
				System.currentTimeMillis() - Simulation.sysStartTime,
				this.getClass().getSimpleName(),
				node.getID(),
				-1L, // No specific transaction or container involved
				//TODO: Add some description here
				""
			);
		}
	}
	
	/**
	 * Returns the node whose hashpower is being changed.
	 *
	 * @return the node instance
	 */
	public IMiner getNode() {
		return node;
	}
	
	/**
	 * Returns the new hashpower value that will be set.
	 *
	 * @return the new hashpower in GH/s
	 */
	public float getNewHashPower() {
		return newHashPower;
	}
	
	/**
	 * Returns the previous hashpower value (before the change).
	 *
	 * @return the old hashpower in GH/s
	 */
	public float getOldHashPower() {
		return oldHashPower;
	}
}

