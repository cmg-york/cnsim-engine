# Test Design: Transaction

## 1. Unit under test
- Class: `Transaction`
- Package: `ca.yorku.cmg.cnsim.engine.transaction`

### Methods/constructors which are under test by me
- `Transaction(long ID, long time, float value, float size)`
- `Transaction(long ID, long time, float value, float size, int nodeID)`
- `Transaction()`
- `Transaction(long id)`
- `makeSeedChanging()`
- `isSeedChanging()`
- `getNextTxID()`
- `resetCurrID()`
- `getCreationTime()`
- `getValue()`
- `setValue(float value)`
- `setSize(float size)`
- `getSize()`
- `setID(long ID)`
- `getID()`
- `getNodeID()`
- `setNodeID(int nodeID)`

Notations used:

| Symbol | Meaning                        | Type of Testing |
|--------|--------------------------------|-----------------|
| P[X]   | Partition                      | Black-box       |
| B[X]   | Boundary value                 | Black-box       |
| G[X]   | Guess / edge case              | Black-box       |
| C[X]   | Atomic condition               | White-box       |
| D[X]   | Decision expression            | White-box       |
| CD[X]  | Condition–Decision combination | White-box       |

## 2. Black Box Analysis

### 2.1 Input partitions

#### A) Constructor: `Transaction(long ID, long time, float value, float size)`
| ID | Condition | Partition | Valid? |
|----|-----------|-----------|--------|
| P1 | time      | time < 0  | false  |
| P2 | time      | time = 0  | true   |
| P3 | time      | time > 0  | true   |
| P4 | value     | value < 0 | false  |
| P5 | value     | value = 0 | true   |
| P6 | value     | value > 0 | true   |
| P7 | size      | size < 0  | false  |
| P8 | size      | size = 0  | true   |
| P9 | size      | size > 0  | true   |

#### B) Constructor: `Transaction(long ID, long time, float value, float size, int nodeID)`
Note: Current implementation sets `nodeID` directly (no exception thrown in code). Documentation mentions `nodeID < 0` exception, but code does not enforce it.

| ID  | Condition | Partition                 | Valid?                       |
|-----|-----------|---------------------------|------------------------------|
| P10 | nodeID    | nodeID = -1 (unspecified) | true                         |
| P11 | nodeID    | nodeID >= 0               | true                         |
| P12 | nodeID    | nodeID < -1               | (behavior: accepted by code) |

#### C) Setter: `setValue(float value)`
| ID  | Condition | Partition | Valid? |
|-----|-----------|-----------|--------|
| P13 | value     | value < 0 | false  |
| P14 | value     | value = 0 | true   |
| P15 | value     | value > 0 | true   |

#### D) Setter: `setSize(float size)`
| ID  | Condition | Partition | Valid? |
|-----|-----------|-----------|--------|
| P16 | size      | size < 0  | false  |
| P17 | size      | size = 0  | true   |
| P18 | size      | size > 0  | true   |

#### E)`getNextTxID()` / `resetCurrID()`
| ID  | Condition    | Partition  | Valid? |
|-----|--------------|------------|--------|
| P19 | currID state | currID = 1 | true   |
| P20 | currID state | currID > 1 | true   |


### 2.2 Boundary values

| ID  | Variable-Value            |
|-----|---------------------------|
| B1  | time = -1                 |
| B2  | time = 0                  |
| B3  | time = 1                  |
| B4  | value = -0.01f (negative) |
| B5  | value = 0.0f              |
| B6  | value = 0.01f             |
| B7  | size = -0.01f (negative)  |
| B8  | size = 0.0f               |
| B9  | size = 0.01f              |
| B10 | nodeID = -1               |
| B11 | nodeID = 0                |
| B12 | nodeID = 1                |


### 2.3 Error guessing by my guesses

| ID | Variable-Value                               |
|----|----------------------------------------------|
| G1 | ID = 0                                       |
| G2 | ID = -5                                      |
| G3 | Very large time (eg., Long.MAX_VALUE)        |
| G4 | Very large value/size (eg., Float.MAX_VALUE) |
| G5 | nodeID very large (eg., Integer.MAX_VALUE)   |


## 3. White Box Analysis

### 3.1 Decisions and Conditions

| Decision ID | Decision Expression | Atomic Conditions |
|-------------|---------------------|-------------------|
| D1          | time < 0            | C1: time < 0      |
| D2          | value < 0           | C2: value < 0     |
| D3          | size < 0            | C3: size < 0      |


#### A) Method: `Transaction_pre(long time, float value, float size)`

| Decision ID | Decision Expression | Atomic Conditions |
|-------------|---------------------|-------------------|
| D1          | time < 0            | C1: time < 0      |
| D2          | value < 0           | C2: value < 0     |
| D3          | size < 0            | C3: size < 0      |

---

#### B) Method: `setValue_pre(float value)`

| Decision ID | Decision Expression | Atomic Conditions |
|-------------|---------------------|-------------------|
| D4          | value < 0           | C4: value < 0     |

---

#### C) Method: `setSize_pre(float size)`

| Decision ID | Decision Expression | Atomic Conditions |
|-------------|---------------------|-------------------|
| D5          | size < 0            | C5: size < 0      |

#### D) `getNextTxID()`
No branches, but has state transition:
- ensures result == old(currID)
- ensures currID == old(currID) + 1

#### E) `makeSeedChanging()` / `isSeedChanging()`
No branches, but changes state behavior:
- makeSeedChanging sets `seedChanging = true`
- isSeedChanging returns the current flag


### 3.2 Test obligations (condition/decision coverage)
| ID   | Covers                                           |
|------|--------------------------------------------------|
| CD1  | C1 true: ArithmeticException (time negative)     |
| CD2  | C2 true: ArithmeticException (value negative)    |
| CD3  | C3 true: ArithmeticException (size negative)     |
| CD4  | C4 true: ArithmeticException (setValue negative) |
| CD5  | C5 true: ArithmeticException (setSize negative)  |
| CD6  | Seed flag toggles and reads correctly            |
| CD7  | getNextTxID increments and returns old           |
| CD8  | resetCurrID resets to 1                          |


## 4. Test cases

### Constructor tests
| ID   | Input                         | Expected                   | Satisfies         |
|------|-------------------------------|----------------------------|-------------------|
| TC-1 | time=-1, value=1, size=1      | throws ArithmeticException | P1, B1, CD1       |
| TC-2 | time=0, value=-1, size=1      | throws ArithmeticException | P4, B4, CD2       |
| TC-3 | time=0, value=1, size=-1      | throws ArithmeticException | P7, B7, CD3       |
| TC-4 | time=0, value=0, size=0       | creates tx; fields set     | P2,P5,P8,B2,B5,B8 |
| TC-5 | time=1, value=0.01, size=0.01 | creates tx; fields set     | P3,P6,P9,B3,B6,B9 |

### Constructor with nodeID tests (not sure about this due to nodeID confusion in original code)
| ID   | Input                       | Expected              | Satisfies |
|------|-----------------------------|-----------------------|-----------|
| TC-6 | nodeID=-1 (default meaning) | creates tx; nodeID=-1 | P10, B10  |
| TC-7 | nodeID=0                    | creates tx; nodeID=0  | P11, B11  |
| TC-8 | nodeID=1                    | creates tx; nodeID=1  | P11, B12  |

### Setter/getter tests
| ID    | Input                       | Expected                   | Satisfies |
|-------|-----------------------------|----------------------------|-----------|
| TC-9  | setValue(-1)                | throws ArithmeticException | P13, CD4  |
| TC-10 | setValue(0)                 | value becomes 0            | P14       |
| TC-11 | setSize(-1)                 | throws ArithmeticException | P16, CD5  |
| TC-12 | setSize(0)                  | size becomes 0             | P17       |
| TC-13 | setID(123) then getID       | returns 123                | G1        |
| TC-14 | setNodeID(5) then getNodeID | returns 5                  | P11       |

### Seed flag behavior
| ID    | Input                                | Expected                        | Satisfies |
|-------|--------------------------------------|---------------------------------|-----------|
| TC-15 | new tx; isSeedChanging()             | returns false (default boolean) | CD6       |
| TC-16 | makeSeedChanging(); isSeedChanging() | returns true                    | CD6       |

### Static currID behavior
| ID    | Input                                                               | Expected                           | Satisfies   |
|-------|---------------------------------------------------------------------|------------------------------------|-------------|
| TC-17 | resetCurrID(); getNextTxID(); getNextTxID()                         | results 1 then 2; currID ends at 3 | CD7, CD8    |
| TC-18 | set currID to known state (via reset + calls) then verify increment | correct increment behavior         | P19,P20,CD7 |


## 5. Outcomes

### 2026-01-05 (LATEST)
All designed test cases implemented.
All tests pass successfully.
Remaining uncovered branches are due to internal contract checks.
CLOSED. STILL NEED TO COMMIT