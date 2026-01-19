package ca.yorku.cmg.cnsim.engine.transaction;

/**
 * Represents a transaction in the CNSim simulation engine.
 * <p>
 * A transaction encapsulates core properties including
 * a unique identifier, creation time, monetary value, and size in bytes. Each transaction
 * may optionally be associated with a specific node where it first appears in the network.
 * </p>
 * <p>
 * This class provides static ID management for generating unique transaction identifiers
 * across the simulation and supports tracking whether a transaction causes seed changes
 * in the consensus protocol.
 * </p>
 *
 * @author CNSim Development Team
 * @version 1.0
 */
public class Transaction {

	// ================================
	// CONSTANTS
	// ================================
	
	public static int currID = 1;
	protected int nodeID = -1;

	// ================================
	// FIELDS
	// ================================
	
	protected long ID;
	protected float size;
	protected float value;
	protected long creationTime;
	protected boolean seedChanging;

	// ================================
	// CONSTRUCTORS
	// ================================

	/**
	 * Marks this transaction as one that causes seed changes in the consensus protocol.
	 * <p>
	 * Seed-changing transactions have special significance in consensus algorithms
	 * as they may affect the randomness or selection process for validators.
	 * </p>
	 */
	public void makeSeedChanging() {
		this.seedChanging = true;
	}

	/**
	 * Checks whether this transaction causes seed changes in the consensus protocol.
	 *
	 * @return {@code true} if this transaction causes seed changes, {@code false} otherwise
	 */
	public boolean isSeedChanging() {
		return(this.seedChanging);
	}
	
	/**
	 * Constructor
	 * @param ID The ID of the transaction.
	 * @param time The time the transaction is created.
	 * @param value The value of the transaction in local currency.
	 * @param size The size of the transaction in bytes.
	 */
	public Transaction(long ID, long time, float value, float size) {
	    if(time < 0)
	    	throw new ArithmeticException("Trying to create new transaction with Time < 0");
	    creationTime = time;
	    this.ID = ID;
	    if(value < 0)
	    	throw new ArithmeticException("Trying to create new transaction with Value < 0");
	    this.value = value;
	    if(size < 0)
	    	throw new ArithmeticException("Trying to create new transaction with Size < 0");
	    this.size = size;
    }
	
	/**
	 * Constructor
	 * @param ID The ID of the transaction.
	 * @param time The time the transaction is created.
	 * @param value The value of the transaction in local currency.
	 * @param size The size of the transaction in bytes.
	 * @param nodeID The ID of the node where the transaction is supposed to show up (-1 if no node is defined yet). If undefined, please use constructor that omits this parameter.
	 */
	public Transaction(long ID, long time, float value, float size, int nodeID) {
	    if(time < 0)
	    	throw new ArithmeticException("Trying to create new transaction with Time < 0");
	    creationTime = time;
	    this.ID = ID;
	    if(value < 0)
	    	throw new ArithmeticException("Trying to create new transaction with Value < 0");
	    this.value = value;
	    if(size < 0)
	    	throw new ArithmeticException("Trying to create new transaction with Size < 0");
	    this.size = size;
	    //if(nodeID < 1)
	    //	throw new ArithmeticException("NodeID must be a positive integer");
	    this.nodeID = nodeID;
	}
		
	/**
	 * Constructor. ID, time, value and size must be initialized with setters.
	 */
	public Transaction() {
		super();
	}
	
	/**
	 * Constructor for given ID. Time, value and size must be initialized with setters.
	 * @param id The ID of the transaction.
	 */
	public Transaction(long id) {
		super();
		this.setID(id);
	}
	
	// ================================
	// SETTERS AND GETTERS
	// ================================
	
	/**
	 * Gets the next available ID number to assign to the transaction.
	 * @return The next transaction ID number.
	 */
	public static int getNextTxID() {
	    return(currID++);
	}
	
	
	/**
	 * Resets the next available ID to 1. To be used for moving to the next experiment.
	 */
	public static void resetCurrID() {
	    currID = 1;
	}
		
	
	/**
	 * Gets the simulation time the transaction was created.
	 * @return The simulation time the transaction was created.
	 */
	public long getCreationTime() {
	    return creationTime;
	}

	/**
	 * Gets the value of the transaction in the native currency.
	 * @return The value of the transaction in the native currency.
	 */
	public float getValue() {
	    return value;
	}

	/**
	 * Sets the value of the transaction in the native currency.
	 * @param value The value of the transaction in the native currency.
	 */
	public void setValue(float value) {
		if(value < 0)
			throw new ArithmeticException("Value < 0");
	    this.value = value;
	}

	/**
	 * Sets the size of the transaction in bytes.
	 * @param size The size of the transaction in bytes.
	 */
	public void setSize(float size) {
	    if(size < 0)
			throw new ArithmeticException("Size < 0");
	    this.size = size;
	}

	/**
	 * Gets the size of the transaction.
	 * @return The size of the transaction in bytes.
	 */
	public float getSize() {
	    return (size);
	}

	/**
	 * Sets the unique ID of the transaction.
	 * @param ID The ID of the transaction.
	 */
	public void setID(long ID) {
	    this.ID = ID;
	}

	/**
	 * Gets the unique ID of the transaction.
	 * @return The unique ID of the transaction.
	 */
	public long getID() {
	   return(ID);
	}


	/**
	 * Gets the ID of the node where the transaction first arrives.
	 * @return The ID of the node where the transaction first arrives. -1 if unspecified.
	 */
	public int getNodeID() {
		return nodeID;
	}

	/**
	 * Sets the ID of the node where the transaction first appears.
	 * @param nodeID The ID of the node where the transaction first appears.
	 */
	public void setNodeID(int nodeID) {
		this.nodeID = nodeID;
	}

	
}