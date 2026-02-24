package ca.yorku.cmg.cnsim.engine.network;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.node.NodeSet;
import ca.yorku.cmg.cnsim.engine.reporter.Reporter;

/**
 * Represents a generic network structure in a simulation.
 * <p>
 * Maintains a reference to a {@linkplain NodeSet} representing participating nodes and stores
 * point-to-point throughput values between nodes in a 2D {@code float} array {@code Net}.
 * Transmission times can be computed for messages of a given size.
 * See {@code documentation/units} for the units of measurement of throughput and transmission times.
 * </p>
 *
 * @author CMT
 * @version 1.0
 */
public abstract class AbstractNetwork {

    // ================================
    // CONSTANTS
    // ================================

    /** Return value for not-connected / no-throughput links. */
    private static final long NOT_CONNECTED = -1L;

    /** Byte-to-bit conversion factor. */
    private static final float BITS_PER_BYTE = 8f;

    /** Seconds-to-milliseconds conversion factor. */
    private static final float MS_PER_SECOND = 1000f;

    // ================================
    // FIELDS
    // ================================

    /** The set of nodes in the network. */
    protected NodeSet ns;

    /** The network throughput matrix in bits per second (bps). */
    public float[][] Net;

    // ================================
    // CONSTRUCTORS
    // ================================

    /**
     * Empty constructor for testing purposes.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures true;
     * </pre>
     */
    public AbstractNetwork() {
        super();
    }

    /**
     * Constructs a network using the specified {@linkplain NodeSet}.
     * Initializes the throughput matrix with dimensions based on {@code net.numOfNodes}.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires ns != null;
     *   //@ ensures this.ns == ns;
     *   //@ ensures this.Net != null;
     * </pre>
     *
     * @param ns the NodeSet representing the nodes of the network
     * @throws Exception if the number of nodes exceeds the maximum allowed in configuration
     * @throws NullPointerException if {@code ns == null} (precondition violated)
     */
    public AbstractNetwork(NodeSet ns) throws Exception {
        AbstractNetwork_pre(ns);

        int maxNodes = Config.getPropertyInt("net.numOfNodes");
        Net = new float[maxNodes + 1][maxNodes + 1];
        this.ns = ns;

        AbstractNetwork_post(this, ns);
    }

    // ================================
    // MAIN PUBLIC METHODS
    // ================================

    /**
     * Calculates the transmission time of a message of given size between two nodes.
     *
     * <p>
     * If the nodes are not connected (throughput is 0), returns {@code -1}.
     * </p>
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires size >= 0;
     *   //@ ensures \result == -1 || \result >= 0;
     * </pre>
     *
     * @param origin the ID of the origin node
     * @param destination the ID of the destination node
     * @param size the size of the message in bytes
     * @return the transmission time in <b>milliseconds</b>, or {@code -1} if the nodes are not connected
     * @throws ArithmeticException if {@code size < 0} (precondition violated)
     * @see #getTransmissionTime(float, float)
     * @see <a href="../documentation/units.html">documentation/units</a>
     */
    public long getTransmissionTime(int origin, int destination, float size) {
        getTransmissionTimeByNodes_pre(size);

        float bps = getThroughput(origin, destination);
        long result = getTransmissionTime(bps, size);

        getTransmissionTimeByNodes_post(result);
        return result;
    }

    /**
     * Calculates the transmission time for a message of a given size over a channel with specified throughput.
     *
     * <p>
     * Multiply by 8 because {@code size} is in bytes but throughput is in bits/second.
     * Multiply by 1000 because throughput is bits/second but output is milliseconds.
     * </p>
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires size >= 0;
     *   //@ requires throughput >= 0;
     *   //@ ensures (throughput == 0) ==> (\result == -1);
     *   //@ ensures (throughput > 0) ==> (\result >= 0);
     * </pre>
     *
     * @param throughput the channel throughput in bits per second (bps)
     * @param size the size of the message in bytes
     * @return the transmission time in <b>milliseconds</b>, or {@code -1} if throughput is 0
     * @throws ArithmeticException if {@code size < 0} or {@code throughput < 0} (precondition violated)
     * @see <a href="../documentation/units.html">documentation/units</a>
     */
    public long getTransmissionTime(float throughput, float size) {
        getTransmissionTimeByThroughput_pre(throughput, size);

        long result;
        if (throughput == 0) {
            result = NOT_CONNECTED;
        } else {
            float ms = (size * BITS_PER_BYTE * MS_PER_SECOND) / throughput;
            result = Math.round(ms);
        }

        getTransmissionTimeByThroughput_post(throughput, result);
        return result;
    }

    // ================================
    // SETTERS AND GETTERS
    // ================================

    /**
     * Returns the throughput between two nodes.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires origin >= 0;
     *   //@ requires destination >= 0;
     *   //@ ensures \result == this.Net[origin][destination];
     * </pre>
     *
     * @param origin the ID of the origin node
     * @param destination the ID of the destination node
     * @return the throughput in bits per second (bps)
     * @throws ArithmeticException if {@code origin < 0} or {@code destination < 0} (precondition violated)
     */
    public float getThroughput(int origin, int destination) {
        getThroughput_pre(origin, destination);

        float result = Net[origin][destination];

        getThroughput_post(this, origin, destination, result);
        return result;
    }

    /**
     * Sets the throughput between two nodes.
     * <p>
     * Records the event in the reporter (if enabled).
     * </p>
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires origin >= 0;
     *   //@ requires destination >= 0;
     *   //@ requires throughput >= 0;
     *   //@ ensures this.Net[origin][destination] == throughput;
     * </pre>
     *
     * @param origin the ID of the origin node
     * @param destination the ID of the destination node
     * @param throughput the throughput in bits per second (bps)
     * @throws ArithmeticException if {@code origin < 0}, {@code destination < 0}, or {@code throughput < 0}
     *     (precondition violated)
     */
    public void setThroughput(int origin, int destination, float throughput) {
        // Preserve original behavior: report attempt before validation.
        if (Reporter.reportsNetEvents()) {
            Reporter.addNetEvent(Simulation.currentSimulationID, origin, destination, throughput, Simulation.currTime);
        }

        setThroughput_pre(origin, destination, throughput);

        Net[origin][destination] = throughput;

        setThroughput_post(this, origin, destination, throughput);
    }

    /**
     * Calculates the average throughput for a given origin node with all other nodes in the network.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures \result == \result; // (total function; see implementation)
     * </pre>
     *
     * @param origin the ID of the origin node
     * @return the average throughput for the origin node in bits per second (bps)
     */
    public float getAvgTroughput(int origin) {
        float sum = 0;
        int count = 0;

        for (int i = 1; i <= Config.getPropertyInt("net.numOfNodes"); i++) {
            if (i != origin) {
                sum += (Net[origin][i] + Net[i][origin]);
                count += 2;
            }
        }

        float result = sum / count;

        getAvgTroughput_post(result);
        return result;
    }

    /**
     * Returns the {@linkplain NodeSet} used to construct this network.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires true;
     *   //@ ensures \result == this.ns;
     * </pre>
     *
     * @return the NodeSet representing the nodes in this network
     */
    public NodeSet getNodeSet() {

        NodeSet result = ns;

        getNodeSet_post(this, result);
        return result;
    }

    // ================================
    // DEBUG/PRINT/TOSTRING METHODS
    // ================================

    /**
     * Prints the network throughput matrix to standard output.
     * Each element represents the throughput between two nodes.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires this.Net != null;
     *   //@ ensures true;
     * </pre>
     *
     * @throws NullPointerException if {@code Net == null} (precondition violated)
     */
    public void printNetwork() {
        printNetwork_pre();

        for (float[] x : Net) {
            for (float y : x) {
                System.out.printf("%3.1f ", y);
            }
            System.out.println();
        }
    }

    /**
     * Alternate implementation of network printing.
     * Prints the throughput matrix as plain numbers separated by spaces.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires this.Net != null;
     *   //@ ensures true;
     * </pre>
     *
     * @throws NullPointerException if {@code Net == null} (precondition violated)
     */
    public void printNetwork2() {
        printNetwork2_pre();

        for (int i = 0; i < Net.length; i++) {
            for (int j = 0; j < Net[i].length; j++) {
                System.out.print(Net[i][j] + " ");
            }
            System.out.println();
        }
    }

    // ================================
    // VALIDATOR METHODS
    // ================================

    private static void AbstractNetwork_pre(NodeSet ns) {
        if (ns == null) {
            throw new NullPointerException("Precondition violated: ns must not be null");
        }
    }

    private static void AbstractNetwork_post(AbstractNetwork net, NodeSet ns) {
        assert net.ns == ns : "Postcondition violated: ns must be stored";
        assert net.Net != null : "Postcondition violated: Net must be initialized";
    }

    private static void getTransmissionTimeByNodes_pre(float size) {
        if (size < 0) {
            throw new ArithmeticException("Size < 0");
        }
    }

    private static void getTransmissionTimeByNodes_post(long result) {
        assert result == NOT_CONNECTED || result >= 0
                : "Postcondition violated: result must be -1 or non-negative";
    }

    private static void getTransmissionTimeByThroughput_pre(float throughput, float size) {
        if (size < 0) {
            throw new ArithmeticException("Size < 0");
        }
        if (throughput < 0) {
            throw new ArithmeticException("Throughput < 0");
        }
    }

    private static void getTransmissionTimeByThroughput_post(float throughput, long result) {
        if (throughput == 0) {
            assert result == NOT_CONNECTED : "Postcondition violated: throughput==0 must return -1";
        } else {
            assert result >= 0 : "Postcondition violated: throughput>0 must return non-negative time";
        }
    }

    private static void getThroughput_pre(int origin, int destination) {
        if (origin < 0) {
            throw new ArithmeticException("Origin < 0");
        }
        if (destination < 0) {
            throw new ArithmeticException("Destination < 0");
        }
    }

    private static void getThroughput_post(
            AbstractNetwork net,
            int origin,
            int destination,
            float result
    ) {
        assert result == net.Net[origin][destination]
                : "Postcondition violated: result must equal Net[origin][destination]";
    }

    private static void setThroughput_pre(int origin, int destination, float throughput) {
        if (origin < 0) {
            throw new ArithmeticException("Origin < 0");
        }
        if (destination < 0) {
            throw new ArithmeticException("Destination < 0");
        }
        if (throughput < 0) {
            throw new ArithmeticException("Throughput < 0");
        }
    }

    private static void setThroughput_post(
            AbstractNetwork net,
            int origin,
            int destination,
            float throughput
    ) {
        assert net.Net[origin][destination] == throughput
                : "Postcondition violated: Net[origin][destination] must equal throughput";
    }

    private static void getAvgTroughput_post(float result) {
        assert !Float.isNaN(result) : "Postcondition violated: average throughput must not be NaN";
    }


    private static void getNodeSet_post(AbstractNetwork net, NodeSet result) {
        assert result == net.ns : "Postcondition violated: result must equal ns";
    }

    private void printNetwork_pre() {
        if (Net == null) {
            throw new NullPointerException("Precondition violated: Net must not be null");
        }
    }

    private void printNetwork2_pre() {
        if (Net == null) {
            throw new NullPointerException("Precondition violated: Net must not be null");
        }
    }
}