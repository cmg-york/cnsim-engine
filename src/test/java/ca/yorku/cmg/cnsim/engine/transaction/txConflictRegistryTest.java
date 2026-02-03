package ca.yorku.cmg.cnsim.engine.transaction;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;


/**
 * Test suite for TxConflictRegistry.
 *
 * Test design: src/test/resources/test-design/Transaction/TxConflictRegistryTest.md
 */

class TxConflictRegistryTest {


// --------------------------------
// CONSTRUCTOR TESTS
// --------------------------------

    @Test
    @DisplayName("Constructor with size=1 should create registry with all IDs initialized to -2")
    void testConstructor_MinimumValidSize_TCC1() {
        TxConflictRegistry registry = new TxConflictRegistry(1);
        for (int i = 1; i <= 1; i++) {
            assertEquals(-2, registry.getMatch(i));
        }
    }

    @Test
    @DisplayName("Constructor with size=Integer.MAX_VALUE should throw NegativeArraySizeException")
    void testConstructor_MaximumValidSize_TCC2() {
        // Note: Integer.MAX_VALUE+1 overflows to negative, causing NegativeArraySizeException
        // when the constructor tries to allocate match = new long[size + 1]
        assertThrows(NegativeArraySizeException.class, () -> {
            new TxConflictRegistry(Integer.MAX_VALUE);
        });
    }

    @Test
    @DisplayName("Constructor with size=0 should throw IllegalArgumentException")
    void testConstructorInvalidSizeZero_TCC3() {
        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            new TxConflictRegistry(0);
        });
        assertTrue(ex.getMessage().contains("size must be >= 1, got "));
    }

    @Test
    @DisplayName("Constructor with size=-1 should throw IllegalArgumentException")
    void testConstructorInvalidSizeLessThanZero_TCC4() {
        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            new TxConflictRegistry(-1);
        });
        assertTrue(ex.getMessage().contains("size must be >= 1, got "));
    }

    @Test
    @DisplayName("Constructor with size=Integer.MAX_VALUE+1 should overflow to the MIN_VALUE (a negative number); should throw IllegalArgumentException")
    void testConstructorInvalidSizeTooLarge_TCC5() {
        int tooLarge = Integer.MAX_VALUE + 1;
        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            new TxConflictRegistry(tooLarge);
        });
        // Note: Integer.MAX_VALUE + 1 overflows to Integer.MIN_VALUE (negative)
        // so the constructor catches it with "size must be >= 1" check
        assertTrue(ex.getMessage().contains("size must be >= 1"));
    }


// --------------------------------
// SIMPLE HELPER METHOD TESTS
// --------------------------------

//getMatch(int id)

    @Test
    @DisplayName("getMatch on uninitialized ID should return -2")
    void testGetMatch_UninitializedID_TCGM1() { 
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        long result = registry.getMatch(1);

        assertEquals(-2L, result);
    }

    @Test
    @DisplayName("getMatch on matched ID should return partner ID")
    void testGetMatch_matchedID_TCGM2() { 
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(1,3);

        long result = registry.getMatch(1);


        assertEquals(3, result);
    }

    @Test
    @DisplayName("getMatch on neutralized ID should return -1")
    void testGetMatch_neutralizedID_TCGM3() { 
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(1,3);
        registry.neutralize();

        long result = registry.getMatch(1);

        assertEquals(-1, result);
    }

    @Test
    @DisplayName("getMatch on id = 0 should throw IllegalArgumentException ")
    void testGetMatch_InvalidSizeZero_TCGM4() { 
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.getMatch(0);
        });

        assertTrue(ex.getMessage().contains("ID must be between 1 and"));
    }

    @Test
    @DisplayName("getMatch on id = size + 1 should throw IllegalArgumentException ")
    void testGetMatch_InvalidSizeAboveMaximum_TCGM5() { 
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.getMatch(size + 1);
        });

        assertTrue(ex.getMessage().contains("ID must be between 1 and"));
    }

//uninitialized(int id)

    @Test
    @DisplayName("uninitialized on new registry should return true")
    void testUninitialized_NewRegistry_TCUT1() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        boolean result = registry.uninitialized(1);

        assertTrue(result);
    }

    @Test
    @DisplayName("uninitialized after setMatch should return false")
    void testUninitialized_AfterSetMatch_TCUT2() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(size, size - 1);

        boolean result = registry.uninitialized(size);

        assertFalse(result);
    }

    @Test
    @DisplayName("uninitialized after neutralize should return false")
    void testUninitialized_AfterNeutralize_TCUT3() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.neutralize();

        boolean result = registry.uninitialized(1);

        assertFalse(result);
    }

    @Test
    @DisplayName("uninitialized with id=0 should return value at index 0 (conceptually unused)")
    void testUninitialized_InvalidIDZero_TCUT4() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        // Note: uninitialized() does not validate IDs, it just accesses match[id]
        // Since the array has size+1 elements (0..size), index 0 is technically accessible
        // but conceptually unused (IDs are 1-indexed)
        boolean result = registry.uninitialized(0);
        assertTrue(result, "Index 0 should be -2 (uninitialized)");
    }

    @Test
    @DisplayName("uninitialized with id=size+1 should throw ArrayIndexOutOfBoundsException")
    void testUninitialized_InvalidIDAboveSize_TCUT5() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        assertThrows(ArrayIndexOutOfBoundsException.class, () -> {
            registry.uninitialized(size + 1);
        });
    }



// --------------------------------
// MAIN METHOD TESTS
// --------------------------------

//setMatch(int a, int b)
    @Test
    @DisplayName("setMatch on a = 1 and b = 1 should throw IllegalArgumentException ")
    void testsetMatch_InvalidSizeAboveMaximum_TCSM1() { 
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.setMatch(1, 1);
        });

        assertTrue(ex.getMessage().contains("Cannot match an ID with itself"));
    }

    @Test
    @DisplayName("setMatch on minimu values a = 1 and b = 2 should create bidirectional match between the two IDs ")
    void testsetMatch_MinimumValidIDsCreateMatch_TCSM2() { 
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        registry.setMatch(1, 2);

        assertEquals(2, registry.getMatch(1), "ID 1 should match to ID 2");
        assertEquals(1, registry.getMatch(2), "ID 2 should match to ID 1");

        // Other indices remain unmatched
        assertEquals(-2, registry.getMatch(4));
    }

    @Test
    @DisplayName("setMatch on maximum values a = size and b = size - 1 should create bidirectional match between the two IDs ")
    void testsetMatch_MaximumValueValidIDsCreateMatch_TCSM3() { 
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        registry.setMatch(size, size - 1);

        assertEquals(size - 1, registry.getMatch(size), "ID size should match to ID size - 1");
        assertEquals(size, registry.getMatch(size - 1), "ID size - 1 should match to ID size");

        // Other indices remain unmatched
        assertEquals(-2, registry.getMatch(4));
    }

    @Test
    @DisplayName("setMatch on boundary values a = 1 and b = size should create bidirectional match between the two IDs ")
    void testsetMatch_BoundaryValueValidIDsCreateMatch_TCSM4() { 
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        registry.setMatch(1, size);

        assertEquals(size, registry.getMatch(1), "ID 1 should match to ID size");
        assertEquals(1, registry.getMatch(size), "ID size should match to ID 1");

        // Other indices remain unmatched
        assertEquals(-2, registry.getMatch(4));
    }

    @Test
    @DisplayName("setMatch with a=0 should throw IllegalArgumentException")
    void testsetMatch_InvalidIDBelowRange_TCSM5() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.setMatch(0, 2);
        });

        assertTrue(ex.getMessage().contains("ID must be between 1 and"));
    }

    @Test
    @DisplayName("setMatch with a=size+1 should throw IllegalArgumentException")
    void testsetMatch_InvalidIDAboveRange_TCSM6() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.setMatch(size + 1, 2);
        });

        assertTrue(ex.getMessage().contains("ID must be between 1 and"));
    }

    @Test
    @DisplayName("setMatch with b=0 should throw IllegalArgumentException")
    void testsetMatch_InvalidIDBBelowRange_TCSM7() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.setMatch(2, 0);
        });

        assertTrue(ex.getMessage().contains("ID must be between 1 and"));
    }

    @Test
    @DisplayName("setMatch with b=size+1 should throw IllegalArgumentException")
    void testsetMatch_InvalidIDBAboveRange_TCSM8() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.setMatch(2, size + 1);
        });

        assertTrue(ex.getMessage().contains("ID must be between 1 and"));
    }

    @Test
    @DisplayName("setMatch twice on same ID should update match and clear old partner")
    void testsetMatch_OverwriteExistingMatch_TCSM9() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(1, 2);

        registry.setMatch(1, 3);

        assertEquals(3, registry.getMatch(1), "ID 1 should now match to ID 3");
        assertEquals(-1, registry.getMatch(2), "ID 2 should be unmatched");
        assertEquals(1, registry.getMatch(3), "ID 3 should match to ID 1");
    }

    @Test
    @DisplayName("setMatch on ID that is already a partner should update both matches")
    void testsetMatch_OverwritePartnerMatch_TCSM10() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(1, 2);

        registry.setMatch(3, 2);

        assertEquals(3, registry.getMatch(2), "ID 2 should now match to ID 3");
        assertEquals(-1, registry.getMatch(1), "ID 1 should be unmatched");
        assertEquals(2, registry.getMatch(3), "ID 3 should match to ID 2");
    }


//noMatch(int id)

    @Test
    @DisplayName("noMatch with id=0 should throw IllegalArgumentException")
    void testNoMatch_InvalidIDZero_TCNM1() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.noMatch(0);
        });

        assertTrue(ex.getMessage().contains("ID must be between 1 and"));
    }

    @Test
    @DisplayName("noMatch with id=size+1 should throw IllegalArgumentException")
    void testNoMatch_InvalidIDAboveSize_TCNM2() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.noMatch(size + 1);
        });

        assertTrue(ex.getMessage().contains("ID must be between 1 and"));
    }

    @Test
    @DisplayName("noMatch on ID with match should clear both ID and partner")
    void testNoMatch_IDWithMatch_ClearsBoth_TCNM3() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(1, 2);

        registry.noMatch(1);

        assertEquals(-1, registry.getMatch(1), "ID 1 should be -1");
        assertEquals(-1, registry.getMatch(2), "ID 2 (partner) should also be -1");
    }

    @Test
    @DisplayName("noMatch on ID with match at boundary should clear both ID and partner")
    void testNoMatch_BoundaryIDWithMatch_ClearsBoth_TCNM4() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(3, size);

        registry.noMatch(size);

        assertEquals(-1, registry.getMatch(3), "ID 3 (partner) should be -1");
        assertEquals(-1, registry.getMatch(size), "ID size should be -1");
    }

    @Test
    @DisplayName("noMatch on already neutralized ID should keep it at -1")
    void testNoMatch_AlreadyNeutralized_StaysNegativeOne_TCNM5() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.neutralize();

        registry.noMatch(1);

        assertEquals(-1, registry.getMatch(1), "ID 1 should remain -1");
    }

    @Test
    @DisplayName("noMatch on uninitialized ID should change from -2 to -1")
    void testNoMatch_UninitializedID_ChangesToNegativeOne_TCNM6() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        registry.noMatch(2);

        assertEquals(-1, registry.getMatch(2), "ID 2 should change from -2 to -1");
    }

    @Test
    @DisplayName("noMatch called twice on same ID should not cause error")
    void testNoMatch_CalledTwice_NoError_TCNM7() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(1, 2);
        registry.noMatch(1);

        registry.noMatch(1);

        assertEquals(-1, registry.getMatch(1), "ID 1 should remain -1");
        assertEquals(-1, registry.getMatch(2), "ID 2 should remain -1");
    }

    @Test
    @DisplayName("noMatch with id=-1 should throw IllegalArgumentException")
    void testNoMatch_NegativeID_TCNM8() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            registry.noMatch(-1);
        });

        assertTrue(ex.getMessage().contains("ID must be between 1 and"));
    }

    @Test
    @DisplayName("noMatch with id=size should clear ID to -1")
    void testNoMatch_BoundaryValidID_TCNM9() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        registry.noMatch(size);

        assertEquals(-1, registry.getMatch(size), "ID size should be -1");
    }

//neutralize()

    @Test
    @DisplayName("neutralize on uninitialized registry should set all IDs to -1")
    void testNeutralize_UninitiatedID_TCN1() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);

        registry.neutralize();

        // Verify all IDs are -1
        for (int i = 1; i <= size; i++) {
            assertEquals(-1, registry.getMatch(i), "ID " + i + " should be -1 after neutralize");
        }
    }

    @Test
    @DisplayName("neutralize after setMatch should set all IDs to -1")
    void testNeutralize_AfterSetMatch_TCN2() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.setMatch(1, 2);
        registry.setMatch(3, 4);

        registry.neutralize();

        // Verify all IDs are -1
        for (int i = 1; i <= size; i++) {
            assertEquals(-1, registry.getMatch(i), "ID " + i + " should be -1 after neutralize");
        }
    }

    @Test
    @DisplayName("neutralize on already neutralized registry should keep all IDs at -1")
    void testNeutralize_AlreadyNeutralized_TCN3() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        registry.neutralize();

        registry.neutralize();

        // Verify all IDs are still -1
        for (int i = 1; i <= size; i++) {
            assertEquals(-1, registry.getMatch(i), "ID " + i + " should remain -1 after second neutralize");
        }
    }

    @Test
    @DisplayName("neutralize on mixed state registry should set all IDs to -1")
    void testNeutralize_MixedState_TCN4() {
        int size = 10;
        TxConflictRegistry registry = new TxConflictRegistry(size);
        // Create mixed state: some matched, some unmatched, some uninitialized
        registry.setMatch(1, 2);  // matched
        registry.noMatch(3);      // unmatched (-1)
        // IDs 4-10 remain uninitialized (-2)

        registry.neutralize();

        // Verify all IDs are -1
        for (int i = 1; i <= size; i++) {
            assertEquals(-1, registry.getMatch(i), "ID " + i + " should be -1 after neutralize");
        }
    }

}
