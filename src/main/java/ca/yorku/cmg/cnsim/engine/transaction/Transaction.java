package ca.yorku.cmg.cnsim.engine.transaction;

/**
 * Represents a transaction used in the CNSim engine.
 *
 * <p>
 * A {@code Transaction} encapsulates a transaction identifier, its creation time (simulation time),
 * its value in native currency, and its size in bytes. A transaction may also record the id of the
 * node where it first appears. The no argument constructor supports two-phase initialization,
 * where fields are later set through setters.
 * </p>
 *
 * @author Shafaat
 */
public class Transaction {

    // ================================
    // CONSTANTS
    // ================================

    /** Next transaction ID number */
    public static int currID = 1;

    // ================================
    // FIELDS
    // ================================

    /** Unique id of transaction. */
    protected long ID;

    /** Size of the transaction in bytes */
    protected float size;

    /** Value of the transaction in native currency */
    protected float value;

    /** Simulation time when transaction was created */
    protected long creationTime;

    /** Id of node where transaction first comes; {@code -1} if unspecified. */
    protected int nodeID = -1;

    /** Whether this transaction changes the simulation seed. */
    protected boolean seedChanging;

    // ================================
    // CONSTRUCTORS
    // ================================

    /**
     * Creates a transaction with fields initialized
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires time >= 0;
     *   //@ requires value >= 0;
     *   //@ requires size >= 0;
     *   //@ ensures this.ID == ID;
     *   //@ ensures this.creationTime == time;
     *   //@ ensures this.value == value;
     *   //@ ensures this.size == size;
     * </pre>
     *
     * @param ID the ID of the transaction
     * @param time the simulation time the transaction is created
     * @param value the value of the transaction in local currency
     * @param size the size of the transaction in bytes
     * @throws ArithmeticException if {@code time < 0} (precondition violated)
     * @throws ArithmeticException if {@code value < 0} (precondition violated)
     * @throws ArithmeticException if {@code size < 0} (precondition violated)
     */
    public Transaction(long ID, long time, float value, float size) {
        Transaction_pre(time, value, size);
        this.creationTime = time;
        this.ID = ID;
        this.value = value;
        this.size = size;
        Transaction_post(this, ID, time, value, size);
    }

    /**
     * Creates a transaction with all mandatory fields initialized plus a node id.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires time >= 0;
     *   //@ requires value >= 0;
     *   //@ requires size >= 0;
     *   //@ ensures this.ID == ID;
     *   //@ ensures this.creationTime == time;
     *   //@ ensures this.value == value;
     *   //@ ensures this.size == size;
     *   //@ ensures this.nodeID == nodeID;
     * </pre>
     *
     * @param ID the ID of the transaction
     * @param time the simulation time the transaction is created
     * @param value the value of the transaction in local currency
     * @param size the size of the transaction in bytes
     * @param nodeID the ID of the node where the transaction is supposed to show up
     *     ({@code -1} if no node is defined yet)
     * @throws ArithmeticException if {@code time < 0} (precondition violated)
     * @throws ArithmeticException if {@code value < 0} (precondition violated)
     * @throws ArithmeticException if {@code size < 0} (precondition violated)
     */
    public Transaction(long ID, long time, float value, float size, int nodeID) {
        Transaction_pre(time, value, size); //did not include arithmetic exception for nodes here as if it below 1 then exception called however we default to -1

        this.creationTime = time;
        this.ID = ID;
        this.value = value;
        this.size = size;
        this.nodeID = nodeID;

        TransactionWithNode_post(this, ID, time, value, size, nodeID);
    }

    /**
     * Creates an empty transaction.
     *
     * <p>
     * ID, time, value and size must be initialized with setters.
     * </p>
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures true;
     * </pre>
     */
    public Transaction() {
        super();
    }

    /**
     * Creates an empty transaction with a given ID.
     *
     * <p>
     * Time, value and size must be initialized with setters.
     * </p>
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures this.ID == id;
     * </pre>
     *
     * @param id the id of the transaction
     */
    public Transaction(long id) {
        super();
        this.setID(id);
    }

    // ================================
    // MAIN PUBLIC METHODS
    // ================================

    /**
     * Marks this transaction as seed-changing.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures this.seedChanging == true;
     * </pre>
     */
    public void makeSeedChanging() {
        makeSeedChanging_pre();

        this.seedChanging = true;

        makeSeedChanging_post(this);
    }

    /**
     * Indicates whether this transaction is seed-changing.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures \result == this.seedChanging;
     * </pre>
     *
     * @return {@code true} if this transaction is seed-changing; {@code false} otherwise
     */
    public boolean isSeedChanging() {
        isSeedChanging_pre();

        boolean result = this.seedChanging;

        isSeedChanging_post(this, result);
        return result;
    }

    /**
     * Gets the next available ID number to assign to a transaction.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures \result == \old(currID);
     *   //@ ensures currID == \old(currID) + 1;
     * </pre>
     *
     * @return the next transaction ID number
     */
    public static int getNextTxID() {
        getNextTxID_pre();

        int oldCurrId = currID;
        int result = currID++;

        getNextTxID_post(oldCurrId, result);
        return result;
    }


    /**
     * Resets the next available ID to 1.
     *
     * <p>
     * To be used for moving to the next experiment.
     * </p>
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures currID == 1;
     * </pre>
     */
    public static void resetCurrID() {
        resetCurrID_pre();

        currID = 1;

        resetCurrID_post();
    }

    // ================================
    // SETTERS AND GETTERS
    // ================================

    /**
     * Returns the simulation time the transaction was created.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures \result == this.creationTime;
     * </pre>
     *
     * @return the simulation time the transaction was created
     */
    public long getCreationTime() {
        getCreationTime_pre();

        long result = creationTime;

        getCreationTime_post(this, result);
        return result;
    }

    /**
     * Returns the value of the transaction in the native currency.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures \result == this.value;
     * </pre>
     *
     * @return the value of the transaction in the native currency
     */
    public float getValue() {
        getValue_pre();

        float result = value;

        getValue_post(this, result);
        return result;
    }

    /**
     * Sets the value of the transaction in the native currency.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires value >= 0;
     *   //@ ensures this.value == value;
     * </pre>
     *
     * @param value the value of the transaction in the native currency
     * @throws ArithmeticException if {@code value < 0} (precondition violated)
     */


    public void setValue(float value) {
        setValue_pre(value);

        this.value = value;

        setValue_post(this, value);
    }

    /**
     * Sets the size of the transaction in bytes.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires size >= 0;
     *   //@ ensures this.size == size;
     * </pre>
     *
     * @param size the size of the transaction in bytes
     * @throws ArithmeticException if {@code size < 0} (precondition violated)
     */
    public void setSize(float size) {
        setSize_pre(size);

        this.size = size;

        setSize_post(this, size);
    }

    /**
     * Gets the size of the transaction.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures \result == this.size;
     * </pre>
     *
     * @return the size of the transaction in bytes
     */
    public float getSize() {
        getSize_pre();

        float result = size;

        getSize_post(this, result);
        return result;
    }

    /**
     * Sets the unique ID of the transaction.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures this.ID == ID;
     * </pre>
     *
     * @param ID the ID of the transaction
     */
    public void setID(long ID) {
        setID_pre(ID);

        this.ID = ID;

        setID_post(this, ID);
    }

    /**
     * Gets the unique ID of the transaction.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures \result == this.ID;
     * </pre>
     *
     * @return the unique ID of the transaction
     */
    public long getID() {
        getID_pre();

        long result = ID;

        getID_post(this, result);
        return result;
    }

    /**
     * Returns the id of the node where the transaction first arrives.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures \result == this.nodeID;
     * </pre>
     *
     * @return the id of the node where the transaction first arrives; {@code -1} if unspecified
     */
    public int getNodeID() {
        getNodeID_pre();

        int result = nodeID;

        getNodeID_post(this, result);
        return result;
    }

    /**
     * Sets the id of the node where the transaction first appears.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures this.nodeID == nodeID;
     * </pre>
     *
     * @param nodeID the id of the node where the transaction first appears
     */
    public void setNodeID(int nodeID) {
        setNodeID_pre(nodeID);

        this.nodeID = nodeID;

        setNodeID_post(this, nodeID);
    }

    // ================================
    // VALIDATOR METHODS
    // ================================

    private static void Transaction_pre(long time, float value, float size) {
        if (time < 0) {
            throw new ArithmeticException("Trying to create new transaction with Time < 0");
        }
        if (value < 0) {
            throw new ArithmeticException("Trying to create new transaction with Value < 0");
        }
        if (size < 0) {
            throw new ArithmeticException("Trying to create new transaction with Size < 0");
        }
    }

    private static void Transaction_post(Transaction tx, long ID, long time, float value, float size) {
        assert tx.creationTime == time : "Postcondition violated: creationTime must equal time";
        assert tx.ID == ID : "Postcondition violated: ID must equal constructor parameter ID";
        assert tx.value == value : "Postcondition violated: value must equal constructor parameter value";
        assert tx.size == size : "Postcondition violated: size must equal constructor parameter size";
    }

    private static void TransactionWithNode_post(Transaction tx, long ID, long time, float value, float size, int nodeID) {
        Transaction_post(tx, ID, time, value, size);
        assert tx.nodeID == nodeID : "Postcondition violated: nodeID must equal constructor parameter nodeID";
    }

    private static void makeSeedChanging_pre() {
        // no preconditions
    }

    private static void makeSeedChanging_post(Transaction tx) {
        assert tx.seedChanging : "Postcondition violated: seedChanging must be true";
    }

    private static void isSeedChanging_pre() {
        // no preconditions
    }

    private static void isSeedChanging_post(Transaction tx, boolean result) {
        assert result == tx.seedChanging : "Postcondition violated: result must equal seedChanging";
    }

    private static void getNextTxID_pre() {
        // no preconditions
    }

    private static void getNextTxID_post(int oldCurrId, int result) {
        assert result == oldCurrId : "Postcondition violated: result must equal old currID";
        assert currID == oldCurrId + 1 : "Postcondition violated: currID must increment by 1";
    }

    private static void resetCurrID_pre() {
        // no preconditions
    }

    private static void resetCurrID_post() {
        assert currID == 1 : "Postcondition violated: currID must equal 1";
    }

    private static void getCreationTime_pre() {
        // no preconditions
    }

    private static void getCreationTime_post(Transaction tx, long result) {
        assert result == tx.creationTime : "Postcondition violated: result must equal creationTime";
    }

    private static void getValue_pre() {
        // no preconditions
    }

    private static void getValue_post(Transaction tx, float result) {
        assert result == tx.value : "Postcondition violated: result must equal value";
    }

    private static void setValue_pre(float value) {
        if (value < 0) {
            throw new ArithmeticException("Value < 0");
        }
    }

    private static void setValue_post(Transaction tx, float value) {
        assert tx.value == value : "Postcondition violated: value must equal parameter value";
    }

    private static void setSize_pre(float size) {
        if (size < 0) {
            throw new ArithmeticException("Size < 0");
        }
    }

    private static void setSize_post(Transaction tx, float size) {
        assert tx.size == size : "Postcondition violated: size must equal parameter size";
    }

    private static void getSize_pre() {
        // no preconditions
    }

    private static void getSize_post(Transaction tx, float result) {
        assert result == tx.size : "Postcondition violated: result must equal size";
    }

    private static void setID_pre(long ID) {
        // no preconditions
    }

    private static void setID_post(Transaction tx, long ID) {
        assert tx.ID == ID : "Postcondition violated: ID must equal parameter ID";
    }

    private static void getID_pre() {
        // no preconditions
    }

    private static void getID_post(Transaction tx, long result) {
        assert result == tx.ID : "Postcondition violated: result must equal ID";
    }

    private static void getNodeID_pre() {
        // no preconditions
    }

    private static void getNodeID_post(Transaction tx, int result) {
        assert result == tx.nodeID : "Postcondition violated: result must equal nodeID";
    }

    private static void setNodeID_pre(int nodeID) {
        // no preconditions (note: {@code -1} is for unspecified)
    }

    private static void setNodeID_post(Transaction tx, int nodeID) {
        assert tx.nodeID == nodeID : "Postcondition violated: nodeID must equal parameter nodeID";
    }
}
