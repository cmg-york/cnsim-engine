package ca.yorku.cmg.cnsim.engine.transaction;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class txConflictRegistryTest {

    @Test
    void testConstructorValidSize() {
        TxConflictRegistry registry = new TxConflictRegistry(10);
        for (int i = 1; i < 10; i++) {
            assertEquals(-2, registry.getMatch(i), "Initially all matches should be -2");
        }
    }

    @Test
    void testConstructorInvalidSizeZero() {
        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            new TxConflictRegistry(0);
        });
        assertTrue(ex.getMessage().contains("size must be >= 1, got "));
    }

    @Test
    void testConstructorInvalidSizeTooLarge() {
        long tooLarge = (long) Integer.MAX_VALUE + 1;
        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            new TxConflictRegistry(tooLarge);
        });
        assertTrue(ex.getMessage().contains("maximum size exceeded"));
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
        TxConflictRegistry registry = new TxConflictRegistry(4);
        registry.setMatch(1, 4);
        registry.setMatch(3, 2);

        assertEquals(3, registry.getMatch(2));
        assertEquals(2, registry.getMatch(3));
        assertEquals(4, registry.getMatch(1));
        assertEquals(1, registry.getMatch(4));
    }

}
