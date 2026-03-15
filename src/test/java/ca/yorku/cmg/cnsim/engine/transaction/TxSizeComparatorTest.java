package ca.yorku.cmg.cnsim.engine.transaction;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test suite for TxSizeComparator.
 *
 * Test design: src/test/resources/test-design/ca/yorku/cmg/cnsim/engine/transaction/TxSizeComparator.md
 */
public class TxSizeComparatorTest {
    private Transaction t1;
    private Transaction t2;
    private TxSizeComparator comparator;

    @BeforeEach
    void setUp() {
        t1 = new Transaction(5, 123, 150, 33);
        t2 = new Transaction(6, 124, 300, 85);
        comparator = new TxSizeComparator();
    }

    @Test
    @DisplayName("Comparing t1=null with t2=valid")
    void testCompare_TC1() {
        t1 = null;
        NullPointerException ex = assertThrows(NullPointerException.class, () -> {
            comparator.compare(t1, t2);
        });

        assertTrue(ex.getMessage().contains("Input Transaction objects can not be null"));
    }

    @Test
    @DisplayName("Comparing t1=valid with t2=null")
    void testCompare_TC2() {
        t2 = null;
        NullPointerException ex = assertThrows(NullPointerException.class, () -> {
            comparator.compare(t1, t2);
        });

        assertTrue(ex.getMessage().contains("Input Transaction objects can not be null"));
    }

    @Test
    @DisplayName("Comparing t1=100 with t2=200")
    void testCompare_TC3() {
        t1.setSize(100);
        t2.setSize(200);
        assertEquals(-1, comparator.compare(t1, t2));
    }

    @Test
    @DisplayName("Comparing t1=200 with t2=100")
    void testCompare_TC4() {
        t1.setSize(200);
        t2.setSize(100);
        assertEquals(1, comparator.compare(t1, t2));
    }

    @Test
    @DisplayName("Comparing equal sizes: t1=100 with t2=100")
    void testCompare_TC5() {
        t1.setSize(100);
        t2.setSize(100);
        assertEquals(0, comparator.compare(t1, t2));
    }

    @Test
    @DisplayName("Comparing antisymmetry unequal: compare(t1,t2) == -compare(t2,t1)")
    void testCompare_TC6() {
        t1.setSize(200);
        t2.setSize(100);

        int outcome = -1 * comparator.compare(t2, t1);
        assertEquals(outcome, comparator.compare(t1, t2));
    }

    @Test
    @DisplayName("Comparing antisymmetry equal: t1=t2, compare(t1,t2) == compare(t2,t1) == 0")
    void testCompare_TC7() {
        t1.setSize(100);
        t2.setSize(100);

        int outcome = comparator.compare(t2, t1);
        assertEquals(outcome, comparator.compare(t1, t2));
        assertEquals(0, outcome);
    }

    @Test
    @DisplayName("Comparing transitivity consistent ordering: if t1 < t2 and t2 < t3, then t1 < t3")
    void testCompare_TC8() {
        t1.setSize(100);
        t2.setSize(200);
        Transaction t3 = new Transaction(9, 456, 25, 300);

        assertEquals(-1, comparator.compare(t1, t2));
        assertEquals(-1, comparator.compare(t2, t3));
        assertEquals(-1, comparator.compare(t1, t3));
    }

    @Test
    @DisplayName("Comparing boundary size with valid input: t1=0, t2=positive")
    void testCompare_TC9_1() {
        t1.setSize(0);
        assertEquals(-1, comparator.compare(t1, t2));

    }

    @Test
    @DisplayName("Comparing boundary size with valid input: t1=positive, t2=0")
    void testCompare_TC9_2() {
        t2.setSize(0);
        assertEquals(1, comparator.compare(t1, t2));
    }

    @Test
    @DisplayName("Comparing boundary size with valid input: t1=MAX_VALUE, t2=0")
    void testCompare_TC10_1() {
        t1.setSize(Float.MAX_VALUE);
        assertEquals(1, comparator.compare(t1, t2));
    }

    @Test
    @DisplayName("Comparing boundary size with valid input: t1=positive, t2=MAX_VALUE")
    void testCompare_TC10_2() {
        t2.setSize(Float.MAX_VALUE);
        assertEquals(-1, comparator.compare(t1, t2));
    }
}