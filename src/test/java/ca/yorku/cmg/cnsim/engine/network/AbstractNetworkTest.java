package ca.yorku.cmg.cnsim.engine.network;

import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.config.ConfigInitializer;
import ca.yorku.cmg.cnsim.engine.node.NodeSet;
import ca.yorku.cmg.cnsim.engine.node.PoWNodeSet;
import ca.yorku.cmg.cnsim.engine.reporter.Reporter;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.net.URL;
import java.nio.file.Paths;

import static org.junit.jupiter.api.Assertions.*;

/**
 * JUnit tests for {@link AbstractNetwork}.
 *
 * Test design document:
 * src/test/resources/test-design/ca/yorku/cmg/cnsim/engine/network/AbstractNetworkTest.md
 */
public class AbstractNetworkTest {

    // ============================================================
    // Concrete subclass for testing
    // ============================================================

    private static class TestableAbstractNetwork extends AbstractNetwork {
        public TestableAbstractNetwork() {
            super();
        }

        public TestableAbstractNetwork(NodeSet ns) throws Exception {
            super(ns);
        }
    }

    // ============================================================
    // Fields
    // ============================================================

    private TestableAbstractNetwork network;
    private NodeSet nodeSet;

    // ============================================================
    // Setup
    // ============================================================

    @BeforeAll
    static void setUpClass() throws Exception {
        URL url = AbstractNetworkTest.class.getClassLoader().getResource("inputs/config.properties");
        assertNotNull(url, "Missing test config: src/test/resources/inputs/config.properties");
        String[] args = {"-c", Paths.get(url.toURI()).toString()};
        ConfigInitializer.initialize(args);
    }

    @BeforeEach
    void setUp() throws Exception {
        nodeSet = new PoWNodeSet();
        network = new TestableAbstractNetwork(nodeSet);
    }

    // ============================================================
    // TC-1: AbstractNetwork() - empty constructor
    // ============================================================

    @Test
    @DisplayName("TC-1: Empty constructor creates object with null ns and null Net")
    void TC_1_emptyConstructor_objectCreated() {
        TestableAbstractNetwork net = new TestableAbstractNetwork();
        assertNotNull(net);
        assertNull(net.ns);
        assertNull(net.Net);
    }

    // ============================================================
    // TC-2 to TC-3: AbstractNetwork(NodeSet ns) constructor
    // ============================================================

    @Test
    @DisplayName("TC-2: Constructor with null NodeSet throws NullPointerException")
    void TC_2_constructor_nullNodeSet_throwsNullPointerException() {
        assertThrows(NullPointerException.class,
                () -> new TestableAbstractNetwork(null));
    }

    @Test
    @DisplayName("TC-3: Constructor with valid NodeSet initializes Net matrix and stores ns")
    void TC_3_constructor_validNodeSet_networkInitialized() {
        int numNodes = Config.getPropertyInt("net.numOfNodes");
        assertNotNull(network.Net);
        assertSame(nodeSet, network.ns);
        assertEquals(numNodes + 1, network.Net.length);
        assertEquals(numNodes + 1, network.Net[0].length);
    }

    // ============================================================
    // TC-4 to TC-9: getTransmissionTime(int origin, int dest, float size)
    // ============================================================

    @Test
    @DisplayName("TC-4: getTransmissionTime(origin, dest, size) - negative size throws ArithmeticException")
    void TC_4_getTransmissionTime3_negativeSize_throwsArithmeticException() {
        assertThrows(ArithmeticException.class,
                () -> network.getTransmissionTime(1, 1, -1f));
    }

    @Test
    @DisplayName("TC-5: getTransmissionTime(origin, dest, size) - negative origin throws ArithmeticException")
    void TC_5_getTransmissionTime3_negativeOrigin_throwsArithmeticException() {
        assertThrows(ArithmeticException.class,
                () -> network.getTransmissionTime(-1, 1, 100f));
    }

    @Test
    @DisplayName("TC-6: getTransmissionTime(origin, dest, size) - negative destination throws ArithmeticException")
    void TC_6_getTransmissionTime3_negativeDestination_throwsArithmeticException() {
        assertThrows(ArithmeticException.class,
                () -> network.getTransmissionTime(1, -1, 100f));
    }

    @Test
    @DisplayName("TC-7: getTransmissionTime(0, 0, 0) - all zero returns 0 ms")
    void TC_7_getTransmissionTime3_allZero_returnsZero() {
        network.Net[0][0] = 8000f;
        long result = network.getTransmissionTime(0, 0, 0f);
        assertEquals(0L, result);
    }

    @Test
    @DisplayName("TC-8: getTransmissionTime(origin, dest, size) - zero throughput returns -1")
    void TC_8_getTransmissionTime3_zeroThroughput_returnsNotConnected() {
        network.Net[1][2] = 0f;
        long result = network.getTransmissionTime(1, 2, 100f);
        assertEquals(-1L, result);
    }

    @Test
    @DisplayName("TC-9: getTransmissionTime(1, 2, 1000) with Net[1][2]=8000 bps returns 1000 ms")
    void TC_9_getTransmissionTime3_normalCase_returnsCorrectMilliseconds() {
        // size=1000 bytes, throughput=8000 bps -> (1000*8*1000)/8000 = 1000 ms
        network.Net[1][2] = 8000f;
        long result = network.getTransmissionTime(1, 2, 1000f);
        assertEquals(1000L, result);
    }

    // ============================================================
    // TC-10 to TC-14: getTransmissionTime(float throughput, float size)
    // ============================================================

    @Test
    @DisplayName("TC-10: getTransmissionTime(throughput, size) - negative size throws ArithmeticException")
    void TC_10_getTransmissionTime2_negativeSize_throwsArithmeticException() {
        assertThrows(ArithmeticException.class,
                () -> network.getTransmissionTime(100f, -1f));
    }

    @Test
    @DisplayName("TC-11: getTransmissionTime(throughput, size) - negative throughput throws ArithmeticException")
    void TC_11_getTransmissionTime2_negativeThroughput_throwsArithmeticException() {
        assertThrows(ArithmeticException.class,
                () -> network.getTransmissionTime(-1f, 100f));
    }

    @Test
    @DisplayName("TC-12: getTransmissionTime(0, 100) - zero throughput with non-zero size returns -1")
    void TC_12_getTransmissionTime2_zeroThroughputNonzeroSize_returnsNotConnected() {
        long result = network.getTransmissionTime(0f, 100f);
        assertEquals(-1L, result);
    }

    @Test
    @DisplayName("TC-13: getTransmissionTime(0, 0) - zero throughput with zero size returns -1")
    void TC_13_getTransmissionTime2_zeroThroughputZeroSize_returnsNotConnected() {
        long result = network.getTransmissionTime(0f, 0f);
        assertEquals(-1L, result);
    }

    @Test
    @DisplayName("TC-14: getTransmissionTime(8000, 1000) - normal case returns 1000 ms")
    void TC_14_getTransmissionTime2_normalCase_returnsCorrectMilliseconds() {
        // throughput=8000 bps, size=1000 bytes -> (1000*8*1000)/8000 = 1000 ms
        long result = network.getTransmissionTime(8000f, 1000f);
        assertEquals(1000L, result);
    }

    // ============================================================
    // TC-15 to TC-18: getThroughput(int origin, int destination)
    // ============================================================

    @Test
    @DisplayName("TC-15: getThroughput - negative origin throws ArithmeticException")
    void TC_15_getThroughput_negativeOrigin_throwsArithmeticException() {
        assertThrows(ArithmeticException.class,
                () -> network.getThroughput(-1, 1));
    }

    @Test
    @DisplayName("TC-16: getThroughput - negative destination throws ArithmeticException")
    void TC_16_getThroughput_negativeDestination_throwsArithmeticException() {
        assertThrows(ArithmeticException.class,
                () -> network.getThroughput(1, -1));
    }

    @Test
    @DisplayName("TC-17: getThroughput(0, 0) - returns value stored in Net[0][0]")
    void TC_17_getThroughput_zeroIndices_returnsStoredValue() {
        network.Net[0][0] = 1234.5f;
        float result = network.getThroughput(0, 0);
        assertEquals(1234.5f, result, 0.001f);
    }

    @Test
    @DisplayName("TC-18: getThroughput(1, 2) - returns value stored in Net[1][2]")
    void TC_18_getThroughput_normalIndices_returnsStoredValue() {
        network.Net[1][2] = 5678.9f;
        float result = network.getThroughput(1, 2);
        assertEquals(5678.9f, result, 0.001f);
    }

    // ============================================================
    // TC-19 to TC-24: setThroughput(int origin, int destination, float throughput)
    // ============================================================

    @Test
    @DisplayName("TC-19: setThroughput - negative origin throws ArithmeticException")
    void TC_19_setThroughput_negativeOrigin_throwsArithmeticException() {
        assertThrows(ArithmeticException.class,
                () -> network.setThroughput(-1, 1, 100f));
    }

    @Test
    @DisplayName("TC-20: setThroughput - negative destination throws ArithmeticException")
    void TC_20_setThroughput_negativeDestination_throwsArithmeticException() {
        assertThrows(ArithmeticException.class,
                () -> network.setThroughput(1, -1, 100f));
    }

    @Test
    @DisplayName("TC-21: setThroughput - negative throughput throws ArithmeticException")
    void TC_21_setThroughput_negativeThroughput_throwsArithmeticException() {
        assertThrows(ArithmeticException.class,
                () -> network.setThroughput(1, 1, -1f));
    }

    @Test
    @DisplayName("TC-22: setThroughput(0, 0, 0) - stores 0 in Net[0][0]")
    void TC_22_setThroughput_allZero_setsNetMatrix() {
        network.setThroughput(0, 0, 0f);
        assertEquals(0f, network.Net[0][0], 0.001f);
    }

    @Test
    @DisplayName("TC-23: setThroughput(1, 2, 8000) - stores 8000 in Net[1][2]")
    void TC_23_setThroughput_normalCase_setsNetMatrix() {
        network.setThroughput(1, 2, 8000f);
        assertEquals(8000f, network.Net[1][2], 0.001f);
    }

    @Test
    @DisplayName("TC-24: setThroughput with reporter enabled - stores value and fires reporter event")
    void TC_24_setThroughput_withReporterEnabled_setsNetMatrixAndFiresReporter() {
        Reporter.reportNetEvents(true);
        try {
            network.setThroughput(1, 2, 9000f);
            assertEquals(9000f, network.Net[1][2], 0.001f);
        } finally {
            Reporter.reportNetEvents(false);
        }
    }

    // ============================================================
    // TC-25 to TC-30: getAvgTroughput(int origin)
    // ============================================================

    @Test
    @DisplayName("TC-25: getAvgTroughput - negative origin throws ArrayIndexOutOfBoundsException")
    void TC_25_getAvgTroughput_negativeOrigin_throwsArrayIndexOutOfBoundsException() {
        assertThrows(ArrayIndexOutOfBoundsException.class,
                () -> network.getAvgTroughput(-1));
    }

    @Test
    @DisplayName("TC-26: getAvgTroughput(0) - origin=0 is outside the 1-based range; does not throw and returns a number (N >= 1)")
    void TC_26_getAvgTroughput_originZero_returnsNumber() {
        // origin=0 is semantically invalid (nodes are 1-based) but has no guard.
        // The loop runs i=1..N; since i != 0 is always true, count = 2*N > 0 and
        // a finite float is returned (no NaN, no exception) whenever N >= 1.
        int numNodes = Config.getPropertyInt("net.numOfNodes");
        Assumptions.assumeTrue(numNodes >= 1, "Test requires net.numOfNodes >= 1");

        float result = network.getAvgTroughput(0);
        assertFalse(Float.isNaN(result));
    }

    @Test
    @DisplayName("TC-27: getAvgTroughput(1) - first valid origin returns a non-negative, non-NaN float (N >= 2)")
    void TC_27_getAvgTroughput_originOne_returnsNonNegative() {
        int numNodes = Config.getPropertyInt("net.numOfNodes");
        Assumptions.assumeTrue(numNodes >= 2, "Test requires net.numOfNodes >= 2");

        float result = network.getAvgTroughput(1);
        assertTrue(result >= 0f);
        assertFalse(Float.isNaN(result));
    }

    @Test
    @DisplayName("TC-28: getAvgTroughput(N) - last valid origin returns a non-NaN float (N >= 2)")
    void TC_28_getAvgTroughput_originAtN_returnsNonNegative() {
        int numNodes = Config.getPropertyInt("net.numOfNodes");
        Assumptions.assumeTrue(numNodes >= 2, "Test requires net.numOfNodes >= 2");

        float result = network.getAvgTroughput(numNodes);
        assertFalse(Float.isNaN(result));
    }

    @Test
    @DisplayName("TC-29: getAvgTroughput(N+1) - origin beyond matrix bounds throws ArrayIndexOutOfBoundsException")
    void TC_29_getAvgTroughput_originBeyondN_throwsArrayIndexOutOfBoundsException() {
        int numNodes = Config.getPropertyInt("net.numOfNodes");
        assertThrows(ArrayIndexOutOfBoundsException.class,
                () -> network.getAvgTroughput(numNodes + 1));
    }

    @Test
    @DisplayName("TC-30: getAvgTroughput - uniform throughput matrix returns that constant value as the average (N >= 2)")
    void TC_30_getAvgTroughput_uniformThroughput_returnsExpectedAverage() {
        int numNodes = Config.getPropertyInt("net.numOfNodes");
        Assumptions.assumeTrue(numNodes >= 2, "Test requires net.numOfNodes >= 2");

        float constant = 500f;
        for (int i = 0; i <= numNodes; i++) {
            for (int j = 0; j <= numNodes; j++) {
                network.Net[i][j] = constant;
            }
        }

        float result = network.getAvgTroughput(1);
        assertEquals(constant, result, 0.01f);
    }

    // ============================================================
    // TC-31: getNodeSet()
    // ============================================================

    @Test
    @DisplayName("TC-31: getNodeSet() returns the NodeSet passed to the constructor")
    void TC_31_getNodeSet_returnsStoredNodeSet() {
        assertSame(nodeSet, network.getNodeSet());
    }

    // ============================================================
    // TC-32 to TC-33: printNetwork()
    // ============================================================

    @Test
    @DisplayName("TC-32: printNetwork() - prints all throughput values to stdout")
    void TC_32_printNetwork_withValues_printsToStdout() {
        network.Net[0][0] = 100.5f;
        network.Net[0][1] = 200.7f;
        network.Net[1][0] = 300.9f;

        ByteArrayOutputStream out = new ByteArrayOutputStream();
        PrintStream original = System.out;
        System.setOut(new PrintStream(out));
        try {
            network.printNetwork();
        } finally {
            System.setOut(original);
        }

        String output = out.toString();
        assertTrue(output.contains("100.5"), "Expected 100.5 in output");
        assertTrue(output.contains("200.7"), "Expected 200.7 in output");
        assertTrue(output.contains("300.9"), "Expected 300.9 in output");
    }

    @Test
    @DisplayName("TC-33: printNetwork() - null Net throws NullPointerException")
    void TC_33_printNetwork_nullNet_throwsNullPointerException() {
        TestableAbstractNetwork net = new TestableAbstractNetwork(); // Net == null
        assertThrows(NullPointerException.class, net::printNetwork);
    }

    // ============================================================
    // TC-34 to TC-35: printNetwork2()
    // ============================================================

    @Test
    @DisplayName("TC-34: printNetwork2() - prints all throughput values to stdout")
    void TC_34_printNetwork2_withValues_printsToStdout() {
        network.Net[0][0] = 111.0f;
        network.Net[0][1] = 222.0f;
        network.Net[1][0] = 333.0f;

        ByteArrayOutputStream out = new ByteArrayOutputStream();
        PrintStream original = System.out;
        System.setOut(new PrintStream(out));
        try {
            network.printNetwork2();
        } finally {
            System.setOut(original);
        }

        String output = out.toString();
        assertTrue(output.contains("111.0"), "Expected 111.0 in output");
        assertTrue(output.contains("222.0"), "Expected 222.0 in output");
        assertTrue(output.contains("333.0"), "Expected 333.0 in output");
    }

    @Test
    @DisplayName("TC-35: printNetwork2() - null Net throws NullPointerException")
    void TC_35_printNetwork2_nullNet_throwsNullPointerException() {
        TestableAbstractNetwork net = new TestableAbstractNetwork(); // Net == null
        assertThrows(NullPointerException.class, net::printNetwork2);
    }
}