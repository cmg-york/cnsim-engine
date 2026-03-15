# Test Design — TxSizeComparator

## 1. Unit under test
- Class: `TxSizeComparator`
- Package: `ca.yorku.cmg.cnsim.engine.transaction`
- Method: `compare(Transaction t1, Transaction t2)`

---

## 3. Purpose

This test plan is designed to expose:
- incorrect ordering behavior (t1.size <, ==, > t2.size)
- comparator-contract violations around equality and antisymmetry
- null-handling behavior (robustness)

Even if “either item is fine” under equality, a Comparator must still behave consistently;
tests intentionally check for contradictions when `t1.size == t2.size`.

---

## 4. Black Box Analysis

### Input partitions
| ID | Condition | Partition | Valid? |
|---|---|---|---|
| P1 | t1 | t1 != null | true |
| P2 | t1 | t1 == null | false |
| P3 | t2 | t2 != null | true |
| P4 | t2 | t2 == null | false |
| P5 | size relation | t1.size < t2.size | true |
| P6 | size relation | t1.size == t2.size | true |
| P7 | size relation | t1.size > t2.size | true |
| P8 | size values | size == 0 | true |
| P9 | size values | size > 0 | true |

### Boundary values
| ID | Variable-Value |
|---|---|
| B1 | size = 0 |
| B2 | size = Float.MIN_VALUE (smallest positive) |
| B3 | size = 1 |
| B4 | size = Float.MAX_VALUE |

### Guesses
| ID | Variable-Value |
|---|---|
| G1 | typical sizes: 100, 200 |
| G2 | equal sizes but different IDs |

---

## 5. White Box Analysis (based on current implementation)

Current logic:
- returns `1` if `t1.getSize() >= t2.getSize()`
- else returns `-1`

### Decisions and Conditions
| Decision ID | Decision Expression | Atomic Conditions |
|---|---|---|
| D1 | t1.getSize() >= t2.getSize() | C1: t1.size >= t2.size |

### Test obligations
| Test Case | C1 | Expected Behavior (per code) |
|---|---|---|
| CD1 | T | returns 1 |
| CD2 | F | returns -1 |

---

## 6. Test cases (aim: detect bugs and contradictions)

| ID | Input | Expected | Satisfies |
|---|---|---|---|
| TC-1 | t1=null, t2=valid tx | throws `NullPointerException` | P2,P3 |
| TC-2 | t1=valid tx, t2=null | throws `NullPointerException` | P1,P4 |
| TC-3 | t1.size < t2.size (100 < 200) | result < 0 | P5,G1,CD2 |
| TC-4 | t1.size > t2.size (200 > 100) | result > 0 | P7,G1,CD1 |
| TC-5 | t1.size == t2.size (both 100) | result == 0 (equality in ordering) | P6,G2 |
| TC-6 | antisymmetry when sizes differ | sign(cmp(a,b)) == -sign(cmp(b,a)) basically seeing if the values return 1 and -1 | P5,P7 |
| TC-7 | antisymmetry when sizes equal | cmp(a,b)=0 and cmp(b,a)=0 | P6 |
| TC-8 | transitivity with increasing sizes | if a<b and b<c then a<c | P9 |
| TC-9 | boundary: size 0 vs size > 0 | correct ordering | P8,P9,B1 |
| TC-10 | boundary: MIN_VALUE vs 0 | correct ordering | B1,B2 |
| TC-11 | boundary: MAX_VALUE comparisons | correct ordering | B4 |

### Expected bug discoveries
- TC-5 and TC-7 are expected to fail with the current implementation because it returns `1` on equality (`>=` case) (***Assuming we agree that 0 must be the result if the sizes are equal***).
- TC-6/TC-8 may also reveal ordering inconsistencies caused by equality mishandling.

---

## 7. Outcomes

### 2026-02-23 (LATEST)
PENDING

Expected failures to investigate/fix:
- TC-5, TC-7 (equality handling)