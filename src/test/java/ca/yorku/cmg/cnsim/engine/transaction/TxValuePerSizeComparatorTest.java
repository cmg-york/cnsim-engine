package ca.yorku.cmg.cnsim.engine.transaction;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test suite for TxValuePerSizeComparator.
 *
 * Test design: src/test/resources/test-design/ca/yorku/cmg/cnsim/engine/transaction/TxValuePerSizeComparator.md
 */
public class TxValuePerSizeComparatorTest {
    private Transaction t1;
    private Transaction t2;
    private TxValuePerSizeComparator comparator;

    @BeforeEach
    void setUp() {
        t1 = new Transaction(5, 123, 150, 33);
        t2 = new Transaction(6, 124, 300, 85);
        comparator = new TxValuePerSizeComparator();
    }

    @Test
    @DisplayName("Comparing t1=null with t2=valid")
    void testCompare_TC1() {
        Transaction t = null;
        NullPointerException ex = assertThrows(NullPointerException.class, () -> {
            comparator.compare(t, t2);
        });

        assertTrue(ex.getMessage().contains("Input Transaction objects can not be null"));
    }

    @Test
    @DisplayName("Comparing t1=valid with t2=null")
    void testCompare_TC2() {
        Transaction t = null;
        NullPointerException ex = assertThrows(NullPointerException.class, () -> {
            comparator.compare(t1, t);
        });

        assertTrue(ex.getMessage().contains("Input Transaction objects can not be null"));
    }

    @Test
    @DisplayName("Comparing t1 < t2 should return 1")
    void testCompare_TC3() {

        // t1 value per size = 5; 10/2 = 5
        t1.setValue(10);
        t1.setSize(2);
        // t2 value per size = 10; 10/1 = 5
        t2.setValue(10);
        t2.setSize(1);

        assertEquals(1, comparator.compare(t1, t2));

    }

    @Test
    @DisplayName("Comparing t1 > t2 should return -1")
    void testCompare_TC4() {

        // t1 value per size = 10; 10/1 = 10
        t1.setValue(10);
        t1.setSize(1);
        // t2 value per size = 5; 10/2 = 5
        t2.setValue(10);
        t2.setSize(2);

        assertEquals(-1, comparator.compare(t1, t2));

    }

    @Test
    @DisplayName("Comparing t1 == t2 should return 0")
    void testCompare_TC5() {
        t1.setValue(100);
        t1.setSize(10);
        t2.setValue(50);
        t2.setSize(5);

        assertEquals(0, comparator.compare(t1, t2));

    }

    @Test
    @DisplayName("Comparing antisymmetry unequal: compare(t1,t2) == -compare(t2,t1)")
    void testCompare_TC6() {
        int outcome = -1 * comparator.compare(t2, t1);
        assertEquals(outcome, comparator.compare(t1, t2));

    }

    @Test
    @DisplayName("Comparing antisymmetry equal: if compare(t1,t2)=0, compare(t1,t2)==compare(t2,t1)==0")
    void testCompare_TC7() {
        t1.setValue(100);
        t1.setSize(10);
        t2.setValue(50);
        t2.setSize(5);

        int outcome = comparator.compare(t2, t1);
        assertEquals(outcome, comparator.compare(t1, t2));
    }

    @Test
    @DisplayName("Comparing transitivity: if t1 < t2, and t2 < t3, then t1 < t3")
    void testCompare_TC8() {
        t1.setValue(10);
        t1.setSize(3);
        t2.setValue(10);
        t2.setSize(2);
        Transaction t3 = new Transaction(456, 188, 10, 1);

        int compareT1_T2 = comparator.compare(t1, t2);
        int compareT2_T3 = comparator.compare(t2, t3);

        assertEquals(1, compareT1_T2);
        assertEquals(1, compareT2_T3);
        assertEquals(1, comparator.compare(t1, t3));

    }

    @Test
    @DisplayName("Comparing valid inputs, t1=infinity")
    void testCompare_TC9_TC10() {
        t1.setSize(0);
        assertEquals(-1, comparator.compare(t1, t2));
    }

    @Test
    @DisplayName("Comparing NaN vs finite")
    void testCompare_TC11() {
        t1.setValue(0); t1.setSize(0);

        assertEquals(-1, comparator.compare(t1, t2));
    }

    @Test
    @DisplayName("Comparing NaN vs NaN")
    void testCompare_TC12() {
        t1.setValue(0.0f); t1.setSize(0.0f);
        t2.setValue(0.0f); t2.setSize(0.0f);

        assertEquals(0, comparator.compare(t1, t2));
    }
}
