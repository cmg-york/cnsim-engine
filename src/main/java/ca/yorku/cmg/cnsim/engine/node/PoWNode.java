package ca.yorku.cmg.cnsim.engine.node;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.event.Event;
import ca.yorku.cmg.cnsim.engine.event.Event_ContainerArrival;
import ca.yorku.cmg.cnsim.engine.event.Event_ContainerValidation;
import ca.yorku.cmg.cnsim.engine.event.Event_TransactionPropagation;
import ca.yorku.cmg.cnsim.engine.reporter.Reporter;
import ca.yorku.cmg.cnsim.engine.transaction.ITxContainer;
import ca.yorku.cmg.cnsim.engine.transaction.Transaction;
import ca.yorku.cmg.cnsim.engine.transaction.TransactionGroup;

import java.util.ArrayList;

/**
 * Abstract class representing a node in a blockchain network.
 * 
 * @author Sotirios Liaskos for the Conceptual Modeling Group @ York University
 * 
 */
public abstract class PoWNode extends Node {

	private float hashPower;
	private float electricPower;
	private float electricityCost;
	private double totalCycles = 0;
	private double prospectiveMiningCycles = 0;
	private boolean isMining = false;
	

	
	// -----------------------------------------------------------------
	// CONSTRUCTOR
	// -----------------------------------------------------------------

	public PoWNode(Simulation sim) {
		super(sim);
	}

	
	

	// -----------------------------------------------------------------
	// A C T I O N S
	// -----------------------------------------------------------------

	
	
	// -----------------------------------------------------------------
	// MINING MANAGEMENT
	// -----------------------------------------------------------------
		
	/**
	 * Starts mining with the specified expected mining interval. 
	 * The interval may be based on when the next validation event takes place.  
	 * @param interval The mining interval (in seconds).
	 */
	public void startMining(double interval) {
		setProspectiveMiningCycles(interval*this.getHashPower());
		isMining = true;
	}

	/**
	 * Starts mining without specifying an expected mining interval.
	 */
	public void startMining() {
		isMining = true;
	}
	
	
	/**
	 * Checks if the node is currently mining.
	 * @return true if the node is mining, false otherwise.
	 */
	public boolean isMining() {
	    return isMining;
	}


	/**
	 * Stops mining
	 */
	public void stopMining() {
		isMining = false;
	}


	// -----------------------------------------------------------------
	// CYCLE COUNTING AND COST CALCULATIONS
	// -----------------------------------------------------------------
	
	/**
	 * Adds the specified number of cycles to the total cycles of the node.
	 * @param c The number of cycles to be added. 
	 */
	public void addCycles(double c) {
		totalCycles += c;
	}
	
	/**
	 * @return the prospectiveMiningCycles
	 */
	public double getProspectiveMiningCycles() {
		return prospectiveMiningCycles;
	}




	/**
	 * @param prospectiveMiningCycles the prospectiveMiningCycles to set
	 */
	public void setProspectiveMiningCycles(double prospectiveMiningCycles) {
		this.prospectiveMiningCycles = prospectiveMiningCycles;
	}




	/**
	 * {@inheritDoc}
	 */
	@Override
	public double getTotalCycles() {
		return totalCycles;
	}
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public double getCostPerGH() {
		//[ [electrictiyCost ($/kWh) * electricPower (W) / 1000 (W/kW)] /  [3600 (s/h) * hashPower (GH/s)]]
		return ( (electricityCost * electricPower / 1000) / (3600 * hashPower) );
	}


	
	// -----------------------------------------------------------------
	// GETTERS AND SETTERS
	// -----------------------------------------------------------------

	//
	// SIMPLE SET/GET
	//
	/**
	 * {@inheritDoc}
	 */
	@Override
	public void setHashPower(float hashpower) {
		if(hashpower < 0 )
			throw new ArithmeticException("Hash Power < 0");
	    this.hashPower = hashpower;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public float getHashPower() {
	    return hashPower;
	}
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public void setElectricityCost(float electricityCost) {
		if(electricityCost < 0 )
			throw new ArithmeticException("Electricity Cost < 0");
	    this.electricityCost = electricityCost;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public float getElectricityCost() {
	    return electricityCost;
	}


	/**
	 * {@inheritDoc}
	 */
	@Override
	public float getElectricPower() {
		return this.electricPower;
	}

	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public void setElectricPower(float power) {
		this.electricPower = power;
		
	}
	
	

	
	
	// -----------------------------------------------------------------
	// VALIDATION EVENT CREATION AND MANAGEMENT
	// -----------------------------------------------------------------
	
	
    /**
     * Returns the next validation event associated with this node. Useful for removing the event when necessary.
     * @return The next validation Event.
     */
    public Event getNextValidationEvent() {
    	return this.nextValidationEvent;
    }
    
    /**
     * Deletes the next validation event associated with this node.
     * TODO: how does this affect cycle counting statistics?
     */
    public void resetNextValidationEvent() {
    	this.nextValidationEvent = null;
    }
	
	/**
	 * Schedules a validation event for the specified transaction container at the given time.
	 * @param txc The transaction container to be validated.
	 * @param time The simulation time when the scheduling occurs. The even will be scheduled at `time + mining interval`. 
	 * @return The scheduled mining interval in seconds.
	 */
	public long scheduleValidationEvent(ITxContainer txc, long time) {
		long h = sim.getSampler().getNodeSampler().getNextMiningInterval(getHashPower());
	    Event_ContainerValidation e = new Event_ContainerValidation(txc, this, time + h);
	    this.nextValidationEvent = e;
	    sim.schedule(e);
	    return (h);
	}
    
	
	
	// -----------------------------------------------------------------
	// EVENT HANDLERS / BEHAVIORS
	// -----------------------------------------------------------------
	
	
	
	/**
	 * {@inheritDoc}
	 * TODO: prospectiveMiningCycles must be removed from here, they are inaccurate, in cases of cancellation.
	 */
	@Override
	public void event_NodeCompletesValidation(ITxContainer t, long time) {
		addCycles(getProspectiveMiningCycles());
		setProspectiveMiningCycles(0);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void event_NodeReceivesPropagatedTransaction(Transaction t, long time) {
	}


	/**
	 * {@inheritDoc}
	 */
	@Override
	public void event_PrintPeriodicReport(long time) {
		this.periodicReport();
	}



	/**
	 * {@inheritDoc}
	 */
	@Override
	public void event_PrintBeliefReport(long[] sample, long time) {
		this.beliefReport(sample, time);
		
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void event_PrintStructureReport(long time) {
		this.structureReport();
	}


	/**
	 * {@inheritDoc}
	 */
	@Override
	public void event_NodeStatusReport(long time) {
		this.nodeStatusReport();
	}
	
	
}