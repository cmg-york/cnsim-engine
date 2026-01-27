package ca.yorku.cmg.cnsim.engine.transaction;

import static org.junit.jupiter.api.Assertions.*;
import org.junit.jupiter.api.Test;

class txConflictRegistryTest {

    @Test
    void testConstructorValidSize_TC1() {
        int size = 1;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        for (int i = 1; i <= size; i++) {
            assertEquals(-2, registry.getMatch(i), "Initially all matches should be -2");
        }
    }

//    @Test
//    void testConstructorValidSize_TC2() {
//        int size = Integer.MAX_VALUE;
//        TxConflictRegistry registry = new TxConflictRegistry(size);
//
//        assertTrue(registry.uninitialized(size - 1), "Initially match[size-1] should be valid and unitialized");
//    }

//    @Test
//    void testConstructorValidSize_TC3() {
//        int size = Integer.MAX_VALUE - 1;
//        TxConflictRegistry registry = new TxConflictRegistry(size);
//
//        assertTrue(registry.uninitialized(size - 1), "Initially match[size-1] should be valid and unitialized");
//    }

//    @Test
//    void testConstructorInvalidSizeTooLarge_TC4() {
//        long size = (long) Integer.MAX_VALUE + 1;
//        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
//            new TxConflictRegistry(size);
//        });
//        assertTrue(ex.getMessage().contains("maximum size exceeded"));
//    }

    @Test
    void testConstructorInvalidSizeZero_TC5() {
        int size = 0;
        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            new TxConflictRegistry(size);
        });
        assertTrue(ex.getMessage().contains("size must be >= 1, got "));
    }

    @Test
    void testConstructorValidSize_TC6() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        for (int i = 1; i <= size; i++) {
            assertEquals(-2, registry.getMatch(i), "Initially all matches should be -2");
        }
    }

    @Test
    void testNeutralizeUninitialized_TC1() {
        TxConflictRegistry registry = new TxConflictRegistry(10);
        registry.neutralize();

        for (int i = 1; i <= 10; i++) {
            assertEquals(-1, registry.getMatch(i), "All elements should equal -1 after neutralize");
        }
    }

    @Test
    void testNeutralizeNeutralized_TC2() {
        // match[i] = -1 for all i is the same as neutralizing after neutralizing.
        TxConflictRegistry registry = new TxConflictRegistry(100);
        registry.neutralize();
        registry.neutralize();

        for (int i = 1; i <= 100; i++) {
            assertEquals(-1, registry.getMatch(i), "All elements should equal -1 after neutralize");
        }
    }

    @Test
    void testNeutralizeAfterSetMatch_TC3() {
        TxConflictRegistry registry = new TxConflictRegistry(10);

        for (int i = 1; i <= 10; i++) {
            if (i == 5) continue;
            registry.setMatch(i, 5);
        }

        registry.neutralize();
        for (int i = 1; i <= 10; i++) {
            assertEquals(-1, registry.getMatch(i), "All elements should equal -1 after neutralize");
        }
    }

    @Test
    void testNoMatchValidateId_TC1() {
        int id = 1, size = 2;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        registry.noMatch(id);
        assertEquals(-1, registry.getMatch(id), "match["+id+"] should equal to -1");
    }

    @Test
    void testNoMatchInvalidId_TC2() {
        int id = 0, size = 2;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.noMatch(id);
        });
        assertTrue(ex.getMessage().contains("ID must be between 1 and "));
    }

    @Test
    void testNoMatchInvalidId_TC3() {
        int id = 10, size = 9;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.noMatch(id);
        });
        assertTrue(ex.getMessage().contains("ID must be between 1 and "));
    }

    @Test
    void testNoMatchValidateId_TC4() {
        int id = 10, size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        registry.noMatch(id);
        assertEquals(-1, registry.getMatch(id), "match["+id+"] should equal to -1");
    }

    @Test
    void testNoMatchValidateId_TC5() {
        int id = 9, size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        registry.noMatch(id);
        assertEquals(-1, registry.getMatch(id), "match["+id+"] should equal to -1");
    }

    @Test
    void testNoMatchValidateId_TC6() {
        int id = 5, size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        registry.noMatch(id);
        assertEquals(-1, registry.getMatch(id), "match["+id+"] should equal to -1");
    }

    @Test
    void testNoMatchValidateId_TC7() {
        int id = 5, size = 10, partner = 7;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(partner, id);

        registry.noMatch(id);
        assertEquals(-1, registry.getMatch(partner), "match["+id+"] should equal to -1");
    }

    @Test
    void testUninitializedValidateId_TC1() {
        int id = 1, size = 2;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        assertTrue(registry.uninitialized(id), "match["+id+"] should be uninitialized (equal to -2)");
    }

    @Test
    void testUninitializedInvalidId_TC2() {
        int id = 0, size = 2;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.uninitialized(id);
        });
        assertTrue(ex.getMessage().contains("ID must be between 1 and "));
    }

    @Test
    void testUninitializedInvalidId_TC3() {
        int id = 10, size = 9;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.uninitialized(id);
        });
        assertTrue(ex.getMessage().contains("ID must be between 1 and "));
    }

    @Test
    void testUninitializedValidateId_TC4() {
        int id = 10, size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        assertTrue(registry.uninitialized(id), "match["+id+"] should be uninitialized (equal to -2)");
    }

    @Test
    void testUninitializedValidateId_TC5() {
        int id = 9, size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        assertTrue(registry.uninitialized(id), "match["+id+"] should be uninitialized (equal to -2)");
    }

    @Test
    void testUninitializedValidateId_TC6() {
        int id = 5, size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        assertTrue(registry.uninitialized(id), "match["+id+"] should be uninitialized (equal to -2)");
    }

    @Test
    void testUninitializedFalse_TC7() {
        int id = 5, size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(5, 6);
        assertFalse(registry.uninitialized(id), "match["+id+"] should not be equal to -2");
    }

    @Test
    void testGetMatchValidateId_TC1() {
        int id = 1, size = 2, res = 2;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(id, res);
        assertEquals(res, registry.getMatch(id), "match["+id+"] should equal to " + res);
    }

    @Test
    void testGetMatchInvalidId_TC2() {
        int id = 0, size = 2;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.getMatch(id);
        });
        assertTrue(ex.getMessage().contains("ID must be between 1 and "));
    }

    @Test
    void testGetMatchInvalidId_TC3() {
        int id = 10, size = 9;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.getMatch(id);
        });
        assertTrue(ex.getMessage().contains("ID must be between 1 and "));
    }

    @Test
    void testGetMatchValidateId_TC4() {
        int id = 10, size = 10, res=2;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(id, res);
        assertEquals(res, registry.getMatch(id), "match["+id+"] should equal to " + res);
    }

    @Test
    void testGetMatchValidateId_TC5() {
        int id = 9, size = 10, res = 2;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(id, res);

        assertEquals(res, registry.getMatch(id), "match["+id+"] should equal to " + res);
    }

    @Test
    void testGetMatchValidateId_TC6() {
        int id = 5, size = 10, res = 2;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(id, res);

        assertEquals(res, registry.getMatch(id), "match["+id+"] should equal to " + res);
    }

    @Test
    void testSetMatchValidateIdA_TC1() {
        int a = 1, b = 2, size = 2;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(a, b);
        assertEquals(b, registry.getMatch(a), "match["+a+"] should equal to " + b + " after setMatch(a,b)");
    }

    @Test
    void testSetMatchInvalidIdA_TC2() {
        int a = 0, b = 1, size = 2;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.setMatch(a, b);
        });
        assertTrue(ex.getMessage().contains("ID must be between 1 and "));
    }

    @Test
    void testSetMatchInvalidIdA_TC3() {
        int a = 10, b = 2, size = 9;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.setMatch(a, b);
        });
        assertTrue(ex.getMessage().contains("ID must be between 1 and "));
    }

    @Test
    void testSetMatchValidateIdB_TC4() {
        int a = 2, b = 1, size = 2;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(b, a);
        assertEquals(a, registry.getMatch(b), "match["+b+"] should equal to " + a + " after setMatch(b,a)");
    }

    @Test
    void testSetMatchInvalidIdB_TC5() {
        int a = 1, b = 0, size = 2;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.setMatch(b, a);
        });
        assertTrue(ex.getMessage().contains("ID must be between 1 and "));
    }

    @Test
    void testSetMatchInvalidIdB_TC6() {
        int a = 2, b = 10, size = 9;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.setMatch(b, a);
        });
        assertTrue(ex.getMessage().contains("ID must be between 1 and "));
    }

    @Test
    void testSetMatchInvalidAEqualsB_TC7() {
        int a = 2, b = 2, size = 5;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.setMatch(a, b);
        });
        assertTrue(ex.getMessage().contains("Cannot match an ID with itself:"));
    }

    @Test
    void testSetMatchG1_TC8() {
        int a = 9, b = 10, size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(a,b);
        assertEquals(b, registry.getMatch(a),"match["+a+"] should equal to " + b + " after setMatch(a,b)");
        assertEquals(a, registry.getMatch(b),"match["+b+"] should equal to " + a + " after setMatch(a,b)");
    }

    @Test
    void testSetMatchG2_TC9() {
        int a = 1, b = 5, size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(a,b);
        assertEquals(b, registry.getMatch(a),"match["+a+"] should equal to " + b + " after setMatch(a,b)");
        assertEquals(a, registry.getMatch(b),"match["+b+"] should equal to " + a + " after setMatch(a,b)");
    }

    @Test
    void testSetAndGetMatch() {
        TxConflictRegistry registry = new TxConflictRegistry(5);
        assertEquals(-2, registry.getMatch(1));
        assertEquals(-2, registry.getMatch(2));

        registry.setMatch(1, 2);
        assertEquals(2, registry.getMatch(1));
        assertEquals(1, registry.getMatch(2));

        // Other indices remain unmatched
        assertEquals(-2, registry.getMatch(4));
    }

    @Test
    void testMultipleMatches() {
        TxConflictRegistry registry = new TxConflictRegistry(10);
        registry.setMatch(1, 4);
        registry.setMatch(3, 2);

        assertEquals(3, registry.getMatch(2));
        assertEquals(2, registry.getMatch(3));
        assertEquals(4, registry.getMatch(1));
        assertEquals(1, registry.getMatch(4));
    }

}
