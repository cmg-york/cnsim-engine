package ca.yorku.cmg.cnsim.engine.transaction;


import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collection;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * JUnit tests for {@link TxDependencyRegistry}.
 *
 * Test design document:
 * src/test/resources/test-design/ca/yorku/cmg/cnsim/engine/transaction/TxDependencyRegistryTest.md
 *
 */
public class TxDependencyRegistryTest {

    private TxDependencyRegistry registry;

    @BeforeEach
    void setUp() {
        // Reset Transaction ID counter for consistent testing
        Transaction.resetCurrID();
        // Default registry with size 10 for most tests
        registry = new TxDependencyRegistry(10);
    }

    // ============================================================
    // Constructor tests (TC-1 through TC-6)
    // ============================================================

    @Test
    @DisplayName("TC-1: Constructor throws IllegalArgumentException when size is zero")
    void TC_1_constructor_with_size_zero() {
        assertThrows(IllegalArgumentException.class, () -> new TxDependencyRegistry(0));
    }

    @Test
    @DisplayName("TC-2: Constructor succeeds when size is one (lower boundary)")
    void TC_2_constructor_with_size_one() {
        TxDependencyRegistry reg = new TxDependencyRegistry(1);
        assertNotNull(reg);
    }

    @Test
    @DisplayName("TC-3: Constructor succeeds when size is ten")
    void TC_3_constructor_with_size_ten() {
        TxDependencyRegistry reg = new TxDependencyRegistry(10);
        assertNotNull(reg);
    }

    @Disabled("Infeasible to allocate BitSet[Integer.MAX_VALUE] in unit test environment")
    @Test
    @DisplayName("TC-4: Constructor succeeds when size is Integer.MAX_VALUE - 1 (disabled: memory infeasible)")
    void TC_4_constructor_with_size_max_integer_minus_one() {
        assertDoesNotThrow(() -> new TxDependencyRegistry((long) Integer.MAX_VALUE - 1));
    }

    @Test
    @DisplayName("TC-5: Constructor throws IllegalArgumentException when size is Integer.MAX_VALUE")
    void TC_5_constructor_throws_when_size_is_max_integer() {
        assertThrows(IllegalArgumentException.class, () -> new TxDependencyRegistry(Integer.MAX_VALUE));
    }

    @Test
    @DisplayName("TC-6: Constructor throws IllegalArgumentException when size exceeds Integer.MAX_VALUE")
    void TC_6_constructor_throws_when_size_exceeds_max_integer() {
        long tooLarge = (long) Integer.MAX_VALUE + 1;
        assertThrows(IllegalArgumentException.class, () -> new TxDependencyRegistry(tooLarge));
    }

    // ============================================================
    // addDependency tests (TC-7 through TC-17)
    // ============================================================

    @Test
    @DisplayName("TC-7: addDependency records dependency when i < j (valid inputs)")
    void TC_7_addDependency_valid_i_less_than_j() {
        assertDoesNotThrow(() -> registry.addDependency(5, 3));

        BitSet satisfied = new BitSet();
        satisfied.set(3);
        assertTrue(registry.dependenciesMet(5, satisfied));
    }

    @Test
    @DisplayName("TC-8: addDependency records dependency when i = j - 1 (maximum valid i boundary)")
    void TC_8_addDependency_boundary_i_equals_j_minus_one() {
        assertDoesNotThrow(() -> registry.addDependency(5, 4));

        BitSet satisfied = new BitSet();
        satisfied.set(4);
        assertTrue(registry.dependenciesMet(5, satisfied));
    }

    @Test
    @DisplayName("TC-9: addDependency throws IllegalArgumentException when i == j")
    void TC_9_addDependency_throws_when_i_equals_j() {
        assertThrows(IllegalArgumentException.class, () -> registry.addDependency(5, 5));
    }

    @Test
    @DisplayName("TC-10: addDependency throws IllegalArgumentException when i > j")
    void TC_10_addDependency_throws_when_i_greater_than_j() {
        assertThrows(IllegalArgumentException.class, () -> registry.addDependency(5, 6));
    }

    @Test
    @DisplayName("TC-11: addDependency throws IllegalArgumentException when i is zero (below minimum)")
    void TC_11_addDependency_throws_when_i_is_zero() {
        assertThrows(IllegalArgumentException.class, () -> registry.addDependency(5, 0));
    }

    @Test
    @DisplayName("TC-12: addDependency throws IndexOutOfBoundsException when j is zero")
    void TC_12_addDependency_throws_when_j_is_zero() {
        assertThrows(IndexOutOfBoundsException.class, () -> registry.addDependency(0, 1));
    }

    @Test
    @DisplayName("TC-13: addDependency throws IndexOutOfBoundsException when j exceeds size")
    void TC_13_addDependency_throws_when_j_exceeds_size() {
        // registry size is 10; j=11 triggers IndexOutOfBoundsException per addDependency_pre
        assertThrows(IndexOutOfBoundsException.class, () -> registry.addDependency(11, 1));
    }

    @Test
    @DisplayName("TC-14: addDependency records dependency when i = 1 (minimum valid i boundary)")
    void TC_14_addDependency_boundary_i_equals_one() {
        assertDoesNotThrow(() -> registry.addDependency(2, 1));

        BitSet satisfied = new BitSet();
        satisfied.set(1);
        assertTrue(registry.dependenciesMet(2, satisfied));
    }

    @Test
    @DisplayName("TC-15: addDependency throws IllegalArgumentException when j = 1 and i = 1 (self-dependency at minimum j)")
    void TC_15_addDependency_boundary_j_equals_one_self_dependency() {
        assertThrows(IllegalArgumentException.class, () -> registry.addDependency(1, 1));
    }

    @Test
    @DisplayName("TC-16: addDependency records dependency when j = size (maximum valid j boundary)")
    void TC_16_addDependency_boundary_j_equals_size() {
        assertDoesNotThrow(() -> registry.addDependency(10, 1));

        BitSet satisfied = new BitSet();
        satisfied.set(1);
        assertTrue(registry.dependenciesMet(10, satisfied));
    }

    @Test
    @DisplayName("TC-17: addDependency rejects circular dependency (second call throws IllegalArgumentException)")
    void TC_17_addDependency_circular_dependency_attempt_is_rejected() {
        // Guess G1: attempt to create a cycle (2 depends on 1, then 1 depends on 2)
        assertDoesNotThrow(() -> registry.addDependency(2, 1));
        assertThrows(IllegalArgumentException.class, () -> registry.addDependency(1, 2));

        // Ensure the first dependency still holds
        BitSet satisfied = new BitSet();
        satisfied.set(1);
        assertTrue(registry.dependenciesMet(2, satisfied));
    }

    // ============================================================
    // addDependencies tests (TC-18 through TC-23)
    // ============================================================

    @Test
    @DisplayName("TC-18: addDependencies throws IndexOutOfBoundsException when id is zero")
    void TC_18_addDependencies_throws_when_id_is_zero() {
        BitSet deps = new BitSet();
        deps.set(1);
        deps.set(2);
        assertThrows(IndexOutOfBoundsException.class, () -> registry.addDependencies(0, deps));
    }

    @Test
    @DisplayName("TC-19: addDependencies succeeds at lower boundary id = 1")
    void TC_19_addDependencies_at_lower_boundary() {
        // id = 1 is the lower valid boundary
        BitSet deps = new BitSet();
        deps.set(1);
        assertDoesNotThrow(() -> registry.addDependencies(1, deps));
    }

    @Test
    @DisplayName("TC-20: addDependencies succeeds at upper boundary id = size")
    void TC_20_addDependencies_at_upper_boundary() {
        // id = size (10) is the upper valid boundary
        BitSet deps = new BitSet();
        deps.set(1);
        assertDoesNotThrow(() -> registry.addDependencies(10, deps));
    }

    @Test
    @DisplayName("TC-21: addDependencies throws IndexOutOfBoundsException when id is negative")
    void TC_21_addDependencies_throws_when_id_negative() {
        BitSet deps = new BitSet();
        assertThrows(IndexOutOfBoundsException.class, () -> registry.addDependencies(-1, deps));
    }

    @Test
    @DisplayName("TC-22: addDependencies throws IndexOutOfBoundsException when id exceeds size")
    void TC_22_addDependencies_throws_when_id_exceeds_size() {
        // id > size triggers IndexOutOfBoundsException
        BitSet deps = new BitSet();
        assertThrows(IndexOutOfBoundsException.class, () -> registry.addDependencies(11, deps));
    }

    @Test
    @DisplayName("TC-23: addDependencies accepts null dependencies; dependenciesMetFast returns true for that transaction")
    void TC_23_addDependencies_null_dependencies_accepted() {
        // null is a valid signal meaning "no dependencies" (e.g. returned by randomDependencies
        // for tx ID <= 1, or when the sampled dependency count rounds down to 0)
        assertDoesNotThrow(() -> registry.addDependencies(1, null));

        // dependenciesMetFast explicitly handles deps[j] == null as "no deps -> met"
        BitSet satisfied = new BitSet();
        BitSet scratch   = new BitSet();
        assertTrue(registry.dependenciesMetFast(1, satisfied, scratch));
    }

    // ============================================================
    // toBitSet(Collection<Integer>) tests (TC-24 through TC-27)
    // ============================================================

    @Test
    @DisplayName("TC-24: toBitSet(Collection) throws NullPointerException when collection is null")
    void TC_24_toBitSet_collection_throws_when_null() {
        Collection<Integer> nullCollection = null;
        assertThrows(NullPointerException.class, () -> registry.toBitSet(nullCollection));
    }

    @Test
    @DisplayName("TC-25: toBitSet(Collection) returns empty BitSet for empty collection")
    void TC_25_toBitSet_collection_with_empty_collection() {
        Collection<Integer> empty = new ArrayList<>();
        BitSet result = registry.toBitSet(empty);
        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @Test
    @DisplayName("TC-26: toBitSet(Collection) sets correct bits for multiple values")
    void TC_26_toBitSet_collection_with_multiple_values() {
        Collection<Integer> values = Arrays.asList(1, 3, 5);
        BitSet result = registry.toBitSet(values);
        assertNotNull(result);
        assertTrue(result.get(1));
        assertTrue(result.get(3));
        assertTrue(result.get(5));
        assertFalse(result.get(2));
        assertFalse(result.get(4));
    }

    @Test
    @DisplayName("TC-27: toBitSet(Collection) sets correct bit for single value")
    void TC_27_toBitSet_collection_with_single_value() {
        Collection<Integer> values = List.of(1);
        BitSet result = registry.toBitSet(values);
        assertNotNull(result);
        assertTrue(result.get(1));
        assertFalse(result.get(2));
    }

    // ============================================================
    // toBitSet(List<Transaction>) tests (TC-28 through TC-31)
    // ============================================================

    @Test
    @DisplayName("TC-28: toBitSet(List<Transaction>) throws NullPointerException when list is null")
    void TC_28_toBitSet_transaction_list_throws_when_null() {
        List<Transaction> nullList = null;
        assertThrows(NullPointerException.class, () -> registry.toBitSet(nullList));
    }

    @Test
    @DisplayName("TC-29: toBitSet(List<Transaction>) returns empty BitSet for empty list")
    void TC_29_toBitSet_transaction_list_with_empty_list() {
        List<Transaction> empty = new ArrayList<>();
        BitSet result = registry.toBitSet(empty);
        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @Test
    @DisplayName("TC-30: toBitSet(List<Transaction>) sets correct bits for multiple transactions")
    void TC_30_toBitSet_transaction_list_with_multiple_transactions() {
        List<Transaction> txs = Arrays.asList(
                new Transaction(2L, 0L, 1.0f, 1.0f),
                new Transaction(4L, 0L, 1.0f, 1.0f),
                new Transaction(6L, 0L, 1.0f, 1.0f)
        );
        BitSet result = registry.toBitSet(txs);
        assertNotNull(result);
        assertTrue(result.get(2));
        assertTrue(result.get(4));
        assertTrue(result.get(6));
        assertFalse(result.get(1));
        assertFalse(result.get(3));
        assertFalse(result.get(5));
    }

    @Test
    @DisplayName("TC-31: toBitSet(List<Transaction>) sets correct bit for single transaction")
    void TC_31_toBitSet_transaction_list_with_single_transaction() {
        List<Transaction> txs = List.of(new Transaction(5L, 0L, 1.0f, 1.0f));
        BitSet result = registry.toBitSet(txs);
        assertNotNull(result);
        assertTrue(result.get(5));
        assertFalse(result.get(4));
    }

    // ============================================================
    // dependenciesMet tests (TC-32 through TC-38)
    // ============================================================

    @Test
    @DisplayName("TC-32: dependenciesMet throws IndexOutOfBoundsException when j is zero")
    void TC_32_dependenciesMet_throws_when_j_is_zero() {
        BitSet satisfied = new BitSet();
        assertThrows(IndexOutOfBoundsException.class, () -> registry.dependenciesMet(0, satisfied));
    }

    @Test
    @DisplayName("TC-33: dependenciesMet returns true at lower boundary j = 1 with no dependencies")
    void TC_33_dependenciesMet_returns_true_at_lower_boundary_no_deps() {
        // j = 1 (lower boundary), no dependencies
        BitSet satisfied = new BitSet();
        assertTrue(registry.dependenciesMet(1, satisfied));
    }

    @Test
    @DisplayName("TC-34: dependenciesMet returns true at upper boundary j = size with no dependencies")
    void TC_34_dependenciesMet_returns_true_at_upper_boundary_no_deps() {
        // j = 10 (size, upper boundary), no dependencies
        BitSet satisfied = new BitSet();
        assertTrue(registry.dependenciesMet(10, satisfied));
    }

    @Test
    @DisplayName("TC-35: dependenciesMet throws IndexOutOfBoundsException when j exceeds size")
    void TC_35_dependenciesMet_throws_when_j_exceeds_size() {
        BitSet satisfied = new BitSet();
        assertThrows(IndexOutOfBoundsException.class, () -> registry.dependenciesMet(11, satisfied));
    }

    @Test
    @DisplayName("TC-36: dependenciesMet throws NullPointerException when satisfiedBits is null")
    void TC_36_dependenciesMet_throws_when_satisfiedBits_null() {
        assertThrows(NullPointerException.class, () -> registry.dependenciesMet(5, null));
    }

    @Test
    @DisplayName("TC-37: dependenciesMet returns true when all dependencies are satisfied")
    void TC_37_dependenciesMet_returns_true_when_all_deps_satisfied() {
        registry.addDependency(5, 1);
        registry.addDependency(5, 2);
        registry.addDependency(5, 3);

        BitSet satisfied = new BitSet();
        satisfied.set(1);
        satisfied.set(2);
        satisfied.set(3);

        assertTrue(registry.dependenciesMet(5, satisfied));
    }

    @Test
    @DisplayName("TC-38: dependenciesMet returns false when some dependencies are not satisfied")
    void TC_38_dependenciesMet_returns_false_when_some_deps_not_satisfied() {
        registry.addDependency(5, 1);
        registry.addDependency(5, 2);
        registry.addDependency(5, 3);

        BitSet satisfied = new BitSet();
        satisfied.set(1);
        satisfied.set(2);
        // Missing dependency 3

        assertFalse(registry.dependenciesMet(5, satisfied));
    }

    // ============================================================
    // dependenciesMetFast tests (TC-39 through TC-44)
    // ============================================================

    @Test
    @DisplayName("TC-39: dependenciesMetFast throws IndexOutOfBoundsException when j is zero")
    void TC_39_dependenciesMetFast_throws_when_j_is_zero() {
        BitSet satisfied = new BitSet();
        BitSet scratch = new BitSet();
        assertThrows(IndexOutOfBoundsException.class, () -> registry.dependenciesMetFast(0, satisfied, scratch));
    }

    @Test
    @DisplayName("TC-40: dependenciesMetFast throws IndexOutOfBoundsException when j exceeds size")
    void TC_40_dependenciesMetFast_throws_when_j_exceeds_size() {
        BitSet satisfied = new BitSet();
        BitSet scratch = new BitSet();
        assertThrows(IndexOutOfBoundsException.class, () -> registry.dependenciesMetFast(11, satisfied, scratch));
    }

    @Test
    @DisplayName("TC-41: dependenciesMetFast throws NullPointerException when satisfiedBits is null")
    void TC_41_dependenciesMetFast_throws_when_satisfiedBits_null() {
        BitSet scratch = new BitSet();
        assertThrows(NullPointerException.class, () -> registry.dependenciesMetFast(5, null, scratch));
    }

    @Test
    @DisplayName("TC-42: dependenciesMetFast throws NullPointerException when scratch is null")
    void TC_42_dependenciesMetFast_throws_when_scratch_null() {
        BitSet satisfied = new BitSet();
        assertThrows(NullPointerException.class, () -> registry.dependenciesMetFast(5, satisfied, null));
    }

    @Test
    @DisplayName("TC-43: dependenciesMetFast returns true when all dependencies are satisfied")
    void TC_43_dependenciesMetFast_returns_true_when_all_deps_satisfied() {
        registry.addDependency(5, 1);
        registry.addDependency(5, 2);

        BitSet satisfied = new BitSet();
        satisfied.set(1);
        satisfied.set(2);
        BitSet scratch = new BitSet();

        assertTrue(registry.dependenciesMetFast(5, satisfied, scratch));
    }

    @Test
    @DisplayName("TC-44: dependenciesMetFast returns false when some dependencies are not satisfied")
    void TC_44_dependenciesMetFast_returns_false_when_some_deps_not_satisfied() {
        registry.addDependency(5, 1);
        registry.addDependency(5, 2);

        BitSet satisfied = new BitSet();
        satisfied.set(1);
        // Missing dependency 2
        BitSet scratch = new BitSet();

        assertFalse(registry.dependenciesMetFast(5, satisfied, scratch));
    }

    // ============================================================
    // toString tests (TC-45 through TC-51)
    // ============================================================

    @Test
    @DisplayName("TC-45: toString throws IndexOutOfBoundsException when txID is zero")
    void TC_45_toString_throws_when_txID_zero() {
        // txID < 1 triggers IndexOutOfBoundsException per toString implementation
        assertThrows(IndexOutOfBoundsException.class, () -> registry.toString(0));
    }

    @Test
    @DisplayName("TC-46: toString returns \"-1\" at lower boundary txID = 1 with no dependencies")
    void TC_46_toString_returns_minus_one_at_lower_boundary_no_deps() {
        // txID = 1 (lower boundary), no dependencies
        assertEquals("-1", registry.toString(1));
    }

    @Test
    @DisplayName("TC-47: toString returns \"-1\" at upper boundary txID = size with no dependencies")
    void TC_47_toString_returns_minus_one_at_upper_boundary_no_deps() {
        // txID = 10 (size, upper boundary), no dependencies
        assertEquals("-1", registry.toString(10));
    }

    @Test
    @DisplayName("TC-48: toString throws IndexOutOfBoundsException when txID exceeds size")
    void TC_48_toString_throws_when_txID_exceeds_size() {
        // txID > size triggers IndexOutOfBoundsException
        assertThrows(IndexOutOfBoundsException.class, () -> registry.toString(11));
    }


    @Test
    @DisplayName("TC-49: toString returns \"-1\" when dependencies BitSet is empty")
    void TC_49_toString_returns_minus_one_when_deps_empty() {

        assertEquals("-1", registry.toString(5));
    }

    @Test
    @DisplayName("TC-50: toString returns braces format for a single dependency")
    void TC_50_toString_returns_braces_with_single_dependency() {
        registry.addDependency(5, 3);
        assertEquals("{3}", registry.toString(5));
    }

    @Test
    @DisplayName("TC-51: toString returns semicolon-separated braces format for multiple dependencies")
    void TC_51_toString_returns_braces_with_multiple_dependencies() {
        registry.addDependency(10, 1);
        registry.addDependency(10, 3);
        registry.addDependency(10, 7);

        assertEquals("{1;3;7}", registry.toString(10));
    }
}