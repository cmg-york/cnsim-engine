package ca.yorku.cmg.cnsim.engine.transaction;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * JUnit tests for {@link Transaction}.
 *
 * Test design document:
 * src/test/resources/test-design/ca/yorku/cmg/cnsim/engine/transaction/TransactionTest.md
 */
public class TransactionTest {

    @BeforeEach
    void setUp() {
        // Reset global static ID before each test.
        Transaction.resetCurrID();
    }

    // ============================================================
    // Constructor tests (TC-1 - TC-8)
    // ============================================================

    @Test
    void TC_1_constructor_throws_when_time_negative() {
        assertThrows(ArithmeticException.class,
                () -> new Transaction(1L, -1L, 1.0f, 1.0f));
    }

    @Test
    void TC_2_constructor_throws_when_value_negative() {
        assertThrows(ArithmeticException.class,
                () -> new Transaction(1L, 0L, -1.0f, 1.0f));
    }

    @Test
    void TC_3_constructor_throws_when_size_negative() {
        assertThrows(ArithmeticException.class,
                () -> new Transaction(1L, 0L, 1.0f, -1.0f));
    }

    @Test
    void TC_4_constructor_all_zero_creates_valid_object() {
        Transaction tx = new Transaction(7L, 0L, 0.0f, 0.0f);

        assertEquals(0L, tx.getCreationTime());
        assertEquals(7L, tx.getID());
        assertEquals(0.0f, tx.getValue());
        assertEquals(0.0f, tx.getSize());
    }

    @Test
    void TC_5_constructor_positive_values_creates_valid_object() {
        Transaction tx = new Transaction(9L, 1L, 0.01f, 0.01f);

        assertEquals(1L, tx.getCreationTime());
        assertEquals(9L, tx.getID());
        assertEquals(0.01f, tx.getValue(), 0.000001f);
        assertEquals(0.01f, tx.getSize(), 0.000001f);
    }

    @Test
    void TC_6_constructor_with_nodeID_minus_one_creates_tx_with_nodeID_minus_one() {
        Transaction tx = new Transaction(1L, 0L, 1.0f, 1.0f, -1);
        assertEquals(-1, tx.getNodeID());
    }

    @Test
    void TC_7_constructor_with_nodeID_zero_creates_tx_with_nodeID_zero() {
        Transaction tx = new Transaction(1L, 0L, 1.0f, 1.0f, 0);
        assertEquals(0, tx.getNodeID());
    }

    @Test
    void TC_8_constructor_with_nodeID_one_creates_tx_with_nodeID_one() {
        Transaction tx = new Transaction(1L, 0L, 1.0f, 1.0f, 1);
        assertEquals(1, tx.getNodeID());
    }

    // ============================================================
    // Setter/getter tests (TC-9 ... TC-14)
    // ============================================================

    @Test
    void TC_9_setValue_throws_when_negative() {
        Transaction tx = new Transaction();
        assertThrows(ArithmeticException.class, () -> tx.setValue(-1.0f));
    }

    @Test
    void TC_10_setValue_sets_zero() {
        Transaction tx = new Transaction();
        tx.setValue(0.0f);
        assertEquals(0.0f, tx.getValue());
    }

    @Test
    void TC_11_setSize_throws_when_negative() {
        Transaction tx = new Transaction();
        assertThrows(ArithmeticException.class, () -> tx.setSize(-1.0f));
    }

    @Test
    void TC_12_setSize_sets_zero() {
        Transaction tx = new Transaction();
        tx.setSize(0.0f);
        assertEquals(0.0f, tx.getSize());
    }

    @Test
    void TC_13_setID_then_getID_returns_same_value() {
        Transaction tx = new Transaction();
        tx.setID(123L);
        assertEquals(123L, tx.getID());
    }

    @Test
    void TC_14_setNodeID_then_getNodeID_returns_same_value() {
        Transaction tx = new Transaction();
        tx.setNodeID(5);
        assertEquals(5, tx.getNodeID());
    }

    // ============================================================
    // Seed flag behavior (TC-15 ... TC-16)
    // ============================================================

    @Test
    void TC_15_new_tx_isSeedChanging_defaults_false() {
        Transaction tx = new Transaction();
        assertFalse(tx.isSeedChanging());
    }

    @Test
    void TC_16_makeSeedChanging_sets_flag_true() {
        Transaction tx = new Transaction();
        tx.makeSeedChanging();
        assertTrue(tx.isSeedChanging());
    }

    // ============================================================
    // Static currID behavior (TC-17 ... TC-18)
    // ============================================================

    @Test
    void TC_17_reset_then_getNextTxID_returns_1_then_2_and_currID_ends_at_3() {
        Transaction.resetCurrID();

        int first = Transaction.getNextTxID();
        int second = Transaction.getNextTxID();

        assertEquals(1, first);
        assertEquals(2, second);
        assertEquals(3, Transaction.currID);
    }

    @Test
    void TC_18_getNextTxID_increments_from_known_state() {
        Transaction.resetCurrID();
        assertEquals(1, Transaction.getNextTxID()); // currID becomes 2
        assertEquals(2, Transaction.getNextTxID()); // currID becomes 3
        assertEquals(3, Transaction.currID);
    }
}