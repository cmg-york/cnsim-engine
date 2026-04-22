package ca.yorku.cmg.cnsim.engine.transaction;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * JUnit tests for {@link Transaction}.
 * <p>
 * Test design document: src/test/resources/test-design/ca/yorku/cmg/cnsim/engine/transaction/TransactionTest.md
 * </p>
 */
public class TransactionTest {

    @BeforeEach
    public void setUp() {
        // Reset the static ID counter before each test to ensure test isolation
        Transaction.resetCurrID();
    }

    // ================================
    // TC-1 to TC-5: Constructor(long ID, long time, float value, float size)
    // ================================

    /**
     * TC-1: 4-param constructor with all zero boundary values.
     * Satisfies: P1, P3, P5, B1, B3, B5, CD1
     */
    @Test
    public void testConstructor4Param_allZeroBoundaryValues() {
        Transaction tx = new Transaction(1L, 0L, 0f, 0f);

        assertEquals(1L, tx.getID());
        assertEquals(0L, tx.getCreationTime());
        assertEquals(0f, tx.getValue(), 0.001f);
        assertEquals(0f, tx.getSize(), 0.001f);
    }

    /**
     * TC-2: 4-param constructor with typical valid values.
     * Satisfies: G1, CD1
     */
    @Test
    public void testConstructor4Param_typicalValidValues() {
        Transaction tx = new Transaction(1L, 100L, 50f, 200f);

        assertEquals(1L, tx.getID());
        assertEquals(100L, tx.getCreationTime());
        assertEquals(50f, tx.getValue(), 0.001f);
        assertEquals(200f, tx.getSize(), 0.001f);
    }

    /**
     * TC-3: 4-param constructor with negative time throws ArithmeticException.
     * Satisfies: P2, B7, CD2
     */
    @Test
    public void testConstructor4Param_negativeTimeThrowsException() {
        assertThrows(ArithmeticException.class, () -> new Transaction(1L, -1L, 50f, 200f));
    }

    /**
     * TC-4: 4-param constructor with negative value throws ArithmeticException.
     * Satisfies: P4, B8, CD3
     */
    @Test
    public void testConstructor4Param_negativeValueThrowsException() {
        assertThrows(ArithmeticException.class, () -> new Transaction(1L, 100L, -1f, 200f));
    }

    /**
     * TC-5: 4-param constructor with negative size throws ArithmeticException.
     * Satisfies: P6, B9, CD4
     */
    @Test
    public void testConstructor4Param_negativeSizeThrowsException() {
        assertThrows(ArithmeticException.class, () -> new Transaction(1L, 100L, 50f, -1f));
    }

    // ================================
    // TC-6 to TC-10: Constructor(long ID, long time, float value, float size, int nodeID)
    // ================================

    /**
     * TC-6: 5-param constructor with valid nodeID.
     * Satisfies: P9
     */
    @Test
    public void testConstructor5Param_validNodeID() {
        Transaction tx = new Transaction(1L, 100L, 50f, 200f, 5);

        assertEquals(1L, tx.getID());
        assertEquals(100L, tx.getCreationTime());
        assertEquals(50f, tx.getValue(), 0.001f);
        assertEquals(200f, tx.getSize(), 0.001f);
        assertEquals(5, tx.getNodeID());
    }

    /**
     * TC-7: 5-param constructor with nodeID=-1 (unspecified).
     * Satisfies: P8
     */
    @Test
    public void testConstructor5Param_nodeIDMinusOne() {
        Transaction tx = new Transaction(1L, 100L, 50f, 200f, -1);

        assertEquals(-1, tx.getNodeID());
    }

    /**
     * TC-8: 5-param constructor with negative time throws ArithmeticException.
     * Satisfies: P2
     */
    @Test
    public void testConstructor5Param_negativeTimeThrowsException() {
        assertThrows(ArithmeticException.class, () -> new Transaction(1L, -1L, 50f, 200f, 5));
    }

    /**
     * TC-9: 5-param constructor with negative value throws ArithmeticException.
     * Satisfies: P4
     */
    @Test
    public void testConstructor5Param_negativeValueThrowsException() {
        assertThrows(ArithmeticException.class, () -> new Transaction(1L, 100L, -1f, 200f, 5));
    }

    /**
     * TC-10: 5-param constructor with negative size throws ArithmeticException.
     * Satisfies: P6
     */
    @Test
    public void testConstructor5Param_negativeSizeThrowsException() {
        assertThrows(ArithmeticException.class, () -> new Transaction(1L, 100L, 50f, -1f, 5));
    }

    // ================================
    // TC-11: Constructor()
    // ================================

    /**
     * TC-11: Default constructor creates object with default values.
     */
    @Test
    public void testDefaultConstructor() {
        Transaction tx = new Transaction();

        assertEquals(0L, tx.getID());
        assertEquals(0L, tx.getCreationTime());
        assertEquals(0f, tx.getValue(), 0.001f);
        assertEquals(0f, tx.getSize(), 0.001f);
        assertEquals(-1, tx.getNodeID());
        assertFalse(tx.isSeedChanging());
    }

    // ================================
    // TC-12 to TC-13: Constructor(long id)
    // ================================

    /**
     * TC-12: Single-param constructor sets ID correctly.
     */
    @Test
    public void testConstructorSingleParam_setsID() {
        Transaction tx = new Transaction(42L);

        assertEquals(42L, tx.getID());
    }

    /**
     * TC-13: Single-param constructor with ID=0.
     */
    @Test
    public void testConstructorSingleParam_zeroID() {
        Transaction tx = new Transaction(0L);

        assertEquals(0L, tx.getID());
    }

    // ================================
    // TC-14 to TC-15: makeSeedChanging() and isSeedChanging()
    // ================================

    /**
     * TC-14: isSeedChanging() returns false initially.
     * Satisfies: P11
     */
    @Test
    public void testIsSeedChanging_initiallyFalse() {
        Transaction tx = new Transaction(1L, 100L, 50f, 200f);

        assertFalse(tx.isSeedChanging());
    }

    /**
     * TC-15: makeSeedChanging() sets flag to true.
     * Satisfies: P12
     */
    @Test
    public void testMakeSeedChanging_setsFlagToTrue() {
        Transaction tx = new Transaction(1L, 100L, 50f, 200f);

        tx.makeSeedChanging();

        assertTrue(tx.isSeedChanging());
    }

    // ================================
    // TC-16 to TC-18: getNextTxID() and resetCurrID()
    // ================================

    /**
     * TC-16: After @BeforeEach reset, getNextTxID() returns 1.
     * Satisfies: P13, P15
     */
    @Test
    public void testGetNextTxID_returnsOneAfterReset() {
        int id = Transaction.getNextTxID();

        assertEquals(1, id);
    }

    /**
     * TC-17: getNextTxID() increments and returns sequential IDs.
     * Satisfies: P14
     */
    @Test
    public void testGetNextTxID_incrementsSequentially() {
        int first = Transaction.getNextTxID();
        int second = Transaction.getNextTxID();

        assertEquals(1, first);
        assertEquals(2, second);
    }

    /**
     * TC-18: resetCurrID() resets counter back to 1.
     * Satisfies: P14, P15
     */
    @Test
    public void testResetCurrID_resetsCounterToOne() {
        Transaction.getNextTxID();
        Transaction.getNextTxID();
        Transaction.resetCurrID();
        int id = Transaction.getNextTxID();

        assertEquals(1, id);
    }

    // ================================
    // TC-19 to TC-21: setValue(float value)
    // ================================

    /**
     * TC-19: setValue() with positive value.
     * Satisfies: P16
     */
    @Test
    public void testSetValue_positiveValue() {
        Transaction tx = new Transaction();
        tx.setValue(100f);

        assertEquals(100f, tx.getValue(), 0.001f);
    }

    /**
     * TC-20: setValue() with zero.
     * Satisfies: B10
     */
    @Test
    public void testSetValue_zero() {
        Transaction tx = new Transaction();
        tx.setValue(0f);

        assertEquals(0f, tx.getValue(), 0.001f);
    }

    /**
     * TC-21: setValue() with negative throws ArithmeticException.
     * Satisfies: P17, B11
     */
    @Test
    public void testSetValue_negativeThrowsException() {
        Transaction tx = new Transaction();

        assertThrows(ArithmeticException.class, () -> tx.setValue(-1f));
    }

    // ================================
    // TC-22 to TC-24: setSize(float size)
    // ================================

    /**
     * TC-22: setSize() with positive size.
     * Satisfies: P18
     */
    @Test
    public void testSetSize_positiveSize() {
        Transaction tx = new Transaction();
        tx.setSize(500f);

        assertEquals(500f, tx.getSize(), 0.001f);
    }

    /**
     * TC-23: setSize() with zero.
     * Satisfies: B12
     */
    @Test
    public void testSetSize_zero() {
        Transaction tx = new Transaction();
        tx.setSize(0f);

        assertEquals(0f, tx.getSize(), 0.001f);
    }

    /**
     * TC-24: setSize() with negative throws ArithmeticException.
     * Satisfies: P19, B13
     */
    @Test
    public void testSetSize_negativeThrowsException() {
        Transaction tx = new Transaction();

        assertThrows(ArithmeticException.class, () -> tx.setSize(-1f));
    }

    // ================================
    // TC-25 to TC-26: setID(long ID) and getID()
    // ================================

    /**
     * TC-25: setID() and getID() with valid ID.
     */
    @Test
    public void testSetIDAndGetID_validID() {
        Transaction tx = new Transaction();
        tx.setID(999L);

        assertEquals(999L, tx.getID());
    }

    /**
     * TC-26: setID() and getID() with zero.
     */
    @Test
    public void testSetIDAndGetID_zero() {
        Transaction tx = new Transaction();
        tx.setID(0L);

        assertEquals(0L, tx.getID());
    }

    // ================================
    // TC-27 to TC-29: setNodeID(int nodeID) and getNodeID()
    // ================================

    /**
     * TC-27: setNodeID() and getNodeID() with positive value.
     */
    @Test
    public void testSetNodeIDAndGetNodeID_positiveValue() {
        Transaction tx = new Transaction();
        tx.setNodeID(10);

        assertEquals(10, tx.getNodeID());
    }

    /**
     * TC-28: setNodeID() and getNodeID() with -1 (default unspecified).
     */
    @Test
    public void testSetNodeIDAndGetNodeID_minusOne() {
        Transaction tx = new Transaction();
        tx.setNodeID(-1);

        assertEquals(-1, tx.getNodeID());
    }

    /**
     * TC-29: setNodeID() and getNodeID() with zero.
     */
    @Test
    public void testSetNodeIDAndGetNodeID_zero() {
        Transaction tx = new Transaction();
        tx.setNodeID(0);

        assertEquals(0, tx.getNodeID());
    }

    // ================================
    // TC-30: getCreationTime()
    // ================================

    /**
     * TC-30: getCreationTime() returns correct value from constructor.
     */
    @Test
    public void testGetCreationTime_returnsCorrectValue() {
        Transaction tx = new Transaction(1L, 1000L, 50f, 200f);

        assertEquals(1000L, tx.getCreationTime());
    }

    // ================================
    // TC-31: getValue() and getSize()
    // ================================

    /**
     * TC-31: getValue() and getSize() return correct values from constructor.
     */
    @Test
    public void testGetValueAndGetSize_returnCorrectValues() {
        Transaction tx = new Transaction(1L, 100L, 322f, 500f);

        assertEquals(322f, tx.getValue(), 0.001f);
        assertEquals(500f, tx.getSize(), 0.001f);
    }
}
