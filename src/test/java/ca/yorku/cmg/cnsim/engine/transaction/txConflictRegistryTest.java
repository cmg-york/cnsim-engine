package ca.yorku.cmg.cnsim.engine.transaction;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class txConflictRegistryTest {

    @Test
    void testConstructorValidSize() {
        TxConflictRegistry registry = new TxConflictRegistry(10);
        for (int i = 0; i < 10; i++) {
            assertEquals(-1, registry.getMatch(i), "Initially all matches should be -1");
        }
    }

    @Test
    void testConstructorInvalidSizeZero() {
        IllegalArgumentException ex = assertThrows(IllegalArgumentException.class, () -> {
            new TxConflictRegistry(0);
        });
        assertTrue(ex.getMessage().contains("size must be between 1"));
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
        assertEquals(-1, registry.getMatch(0));
        assertEquals(-1, registry.getMatch(1));

        registry.setMatch(0, 1);
        assertEquals(1, registry.getMatch(0));
        assertEquals(0, registry.getMatch(1));

        // Other indices remain unmatched
        assertEquals(-1, registry.getMatch(2));
    }

    @Test
    void testMultipleMatches() {
        TxConflictRegistry registry = new TxConflictRegistry(4);
        registry.setMatch(0, 3);
        registry.setMatch(1, 2);

        assertEquals(3, registry.getMatch(0));
        assertEquals(0, registry.getMatch(3));
        assertEquals(2, registry.getMatch(1));
        assertEquals(1, registry.getMatch(2));
    }

}
