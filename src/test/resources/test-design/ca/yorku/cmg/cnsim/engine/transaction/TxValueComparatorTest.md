# Test Design — TxValueComparator

## 1. Unit under test
- Class: `TxValueComparator`
- Package: `ca.yorku.cmg.cnsim.engine.transaction`
- Method: `compare(Transaction t1, Transaction t2)`


## 2. Purpose

To test:

- Correct ordering by transaction value
- Equality behavior when values are identical
- Comparator contract properties (antisymmetry, transitivity)
- Boundary behavior (0, large float values)
- Null handling

---

## 3. Black Box Analysis

### Input partitions

| ID | Condition | Partition | Valid? |
|----|-----------|-----------|--------|
| P1 | t1 | t1 != null | true |
| P2 | t1 | t1 == null | false |
| P3 | t2 | t2 != null | true |
| P4 | t2 | t2 == null | false |
| P5 | value relation | t1.value < t2.value | true |
| P6 | value relation | t1.value == t2.value | true |
| P7 | value relation | t1.value > t2.value | true |
| P8 | values | value == 0 | true |
| P9 | values | value > 0 | true |

---

### Boundary values

| ID | Variable-Value |
|----|----------------|
| B1 | value = 0 |
| B2 | value = Float.MIN_VALUE |
| B3 | value = 1 |
| B4 | value = Float.MAX_VALUE |

---

## 4. White Box Analysis

Current logic:
if (t1.getValue() >= t2.getValue())
return 1;
else
return -1;

### Decision

| Decision ID | Expression | Atomic Condition |
|------------|------------|------------------|
| D1 | t1.value >= t2.value | C1 |

### Coverage obligations

| Test | C1 | Expected (per code) |
|------|----|--------------------|
| CD1 | T | returns 1 |
| CD2 | F | returns -1 |

---

## 5. Test Cases (aim: detect bugs)

| ID | Input | Expected | Covers |
|----|--------|----------|--------|
| TC-1 | t1=null | NullPointerException | P2 |
| TC-2 | t2=null | NullPointerException | P4 |
| TC-3 | 100 < 200 | result < 0 | P5 |
| TC-4 | 200 > 100 | result > 0 | P7 |
| TC-5 | equal values (100 == 100) | result == 0 | P6 |
| TC-6 | antisymmetry unequal | sign(cmp(a,b)) = -sign(cmp(b,a)) basically seeing if the values return 1 and -1 | P5,P7 |
| TC-7 | antisymmetry equal | cmp(a,b)=0 and cmp(b,a)=0 | P6 |
| TC-8 | transitivity (100 < 200 < 300) | consistent ordering | P9 |
| TC-9 | boundary 0 vs positive | correct ordering | B1 |
| TC-10 | MAX_VALUE comparisons | correct ordering | B4 |

---

## 6. Expected Bug Discovery

Under current implementation:

- TC-5 and TC-7 will fail (never returns 0 on equality).
- Potential floating-point precision issues may affect equality comparisons.

---

## 7. Outcomes

### 2026-02-23 (LATEST)
PENDING

Expected failures:
- Equality handling (TC-5, TC-7)