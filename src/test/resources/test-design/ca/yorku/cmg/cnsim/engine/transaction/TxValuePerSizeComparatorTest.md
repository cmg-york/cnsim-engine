# Test Design — TxValuePerSizeComparator

## 1. Unit under test
- Class: `TxValuePerSizeComparator`
- Package: `ca.yorku.cmg.cnsim.engine.transaction`
- Method: `compare(Transaction t1, Transaction t2)`

---

## 3. Purpose

This test plan aims to expose:
- ordering direction correctness (ascending vs descending)
- equality handling (ratio equal)
- comparator contract properties (antisymmetry, transitivity)
- division-by-zero behavior (Infinity)
- NaN behavior (0/0)
- null-handling robustness

---

## 4. Black Box Analysis

### Input partitions
| ID | Condition | Partition | Valid? |
|---|---|---|---|
| P1 | t1 | t1 != null | true |
| P2 | t1 | t1 == null | false |
| P3 | t2 | t2 != null | true |
| P4 | t2 | t2 == null | false |
| P5 | size values | size > 0 | true |
| P6 | size values | size = 0 | true |
| P7 | ratio relation | r1 < r2 | true |
| P8 | ratio relation | r1 == r2 | true |
| P9 | ratio relation | r1 > r2 | true |
| P10 | ratio special | r = Infinity (value>0, size=0) | true |
| P11 | ratio special | r = NaN (0/0) | true |

Where:
- `r1 = t1.value / t1.size`
- `r2 = t2.value / t2.size`

### Boundary values
| ID | Variable-Value |
|---|---|
| B1 | value = 0 |
| B2 | size = 0 |
| B3 | size = Float.MIN_VALUE |
| B4 | very large value/size |

### Guesses
| ID | Variable-Value |
|---|---|
| G1 | typical ratios: 100/10 = 10, 50/10 = 5 |
| G2 | equal ratio different pairs: 100/10 == 50/5 |

---

## 5. White Box Analysis (based on current implementation)

Current logic: 
if ((t1.value/t1.size) <= (t2.value/t2.size))
return 1;
else
return -1;

### Decision
| Decision ID | Expression | Atomic Condition |
|---|---|---|
| D1 | r1 <= r2 | C1 |

### Test obligations (per code)
| Test | C1 | Expected |
|---|---|---|
| CD1 | T | returns 1 |
| CD2 | F | returns -1 |

---

## 6. Test Cases (aim: detect bugs)

### 6.1 Null handling
| ID | Input | Expected | Satisfies |
|---|---|---|---|
| TC-1 | t1=null, t2=valid | NullPointerException | P2 |
| TC-2 | t1=valid, t2=null | NullPointerException | P4 |

### 6.2 Normal ratio ordering (size > 0)
| ID | Input | Expected | Satisfies |
|---|---|---|---|
| TC-3 | r1 < r2 (5 < 10) | result sign reflects intended ordering | P5,P7,G1 |
| TC-4 | r1 > r2 (10 > 5) | result sign reflects intended ordering | P5,P9,G1 |
| TC-5 | r1 == r2 (100/10 == 50/5) | result == 0 (equality in ordering) | P5,P8,G2 |

> Note: TC-3/TC-4 are used to confirm whether comparator is ascending or descending.  
> The current code returns positive when r1 <= r2, implying a reversed/descending-style ordering.

### 6.3 Comparator contract properties
| ID | Input | Expected |
|---|---|---|
| TC-6 | antisymmetry unequal | sign(cmp(a,b)) == -sign(cmp(b,a)) |
| TC-7 | antisymmetry equal ratio | cmp(a,b)=0 and cmp(b,a)=0 |
| TC-8 | transitivity with normal ratios | if a<b and b<c then a<c |

### 6.4 Division by zero / Infinity
| ID | Input | Expected | Satisfies |
|---|---|---|---|
| TC-9 | value>0, size=0 ⇒ r=Infinity | comparator handles without exception; ordering is consistent | P6,P10,B2 |
| TC-10 | compare Infinity vs finite ratio | Infinity should be treated as greater than finite (or documented otherwise) | P10 |

### 6.5 NaN behavior (0/0)
| ID | Input | Expected | Satisfies |
|---|---|---|---|
| TC-11 | value=0,size=0 ⇒ r=NaN vs finite | ordering should be well-defined or explicitly rejected | P6,P11,B1,B2 |
| TC-12 | NaN vs NaN | comparator should return 0 or explicitly reject | P11 |

### Expected bug discoveries
- Equality handling: TC-5, TC-7 likely fail (comparator never returns 0).
- NaN cases: TC-11/TC-12 likely expose inconsistent ordering because `(NaN <= x)` is always false.
- Division-by-zero: TC-9/TC-10 may show inconsistent ordering or direction surprises.

---

## 7. Outcomes

### 2026-02-23 (LATEST)
PENDING

Risk areas:
- size = 0 leading to Infinity/NaN
- equality handling (ratio ties)