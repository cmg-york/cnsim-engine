# Test Design — Transaction

## 1. Unit under test
- Class: `Transaction`
- Package: `ca.yorku.cmg.cnsim.engine.transaction`

---

## 2. Constructor: `Transaction(long ID, long time, float value, float size)`

### Black Box Analysis

#### Input partitions
| ID  | Condition       | Partition         | Valid? |
|-----|-----------------|-------------------|--------|
| P1  | Value of time   | time >= 0         | true   |
| P2  | Value of time   | time < 0          | false  |
| P3  | Value of value  | value >= 0        | true   |
| P4  | Value of value  | value < 0         | false  |
| P5  | Value of size   | size >= 0         | true   |
| P6  | Value of size   | size < 0          | false  |
| P7  | Value of ID     | any long          | true   |

#### Boundary values
| ID  | Variable-Value         |
|-----|------------------------|
| B1  | time = 0               |
| B2  | time = Long.MAX_VALUE  |
| B3  | value = 0              |
| B4  | value = Float.MAX_VALUE|
| B5  | size = 0               |
| B6  | size = Float.MAX_VALUE |
| B7  | time = -1              |
| B8  | value = -1             |
| B9  | size = -1              |

#### Guesses
| ID  | Variable-Value              |
|-----|-----------------------------|
| G1  | Typical valid values        |
| G2  | Large ID value              |

### White Box Analysis

#### Decisions and Conditions

| Decision ID | Decision Expression | Atomic Conditions |
|-------------|---------------------|-------------------|
| D1          | time < 0            | C1: time < 0      |
| D2          | value < 0           | C2: value < 0     |
| D3          | size < 0            | C3: size < 0      |

#### Test obligations

| Test Case | C1 (time<0) | C2 (value<0) | C3 (size<0) | Expected         |
|-----------|-------------|--------------|-------------|------------------|
| CD1       | F           | F            | F           | Success          |
| CD2       | T           | -            | -           | Exception (time) |
| CD3       | F           | T            | -           | Exception (value)|
| CD4       | F           | F            | T           | Exception (size) |

### Test cases
| ID   | Input                          | Expected                     | Satisfies      |
|------|--------------------------------|------------------------------|----------------|
| TC-1 | ID=1, time=0, value=0, size=0  | Success, all fields set to 0 | P1,P3,P5,B1,B3,B5,CD1 |
| TC-2 | ID=1, time=100, value=50, size=200 | Success, fields set correctly | G1,CD1 |
| TC-3 | ID=1, time=-1, value=50, size=200 | ArithmeticException         | P2,B7,CD2      |
| TC-4 | ID=1, time=100, value=-1, size=200 | ArithmeticException        | P4,B8,CD3      |
| TC-5 | ID=1, time=100, value=50, size=-1 | ArithmeticException         | P6,B9,CD4      |

---

## 3. Constructor: `Transaction(long ID, long time, float value, float size, int nodeID)`

### Black Box Analysis

#### Input partitions
| ID   | Condition        | Partition         | Valid? |
|------|------------------|-------------------|--------|
| P8   | Value of nodeID  | nodeID = -1       | true   |
| P9   | Value of nodeID  | nodeID >= 0       | true   |
| P10  | Value of nodeID  | nodeID < -1       | true   |

### Test cases
| ID    | Input                                    | Expected                      | Satisfies |
|-------|------------------------------------------|-------------------------------|-----------|
| TC-6  | ID=1, time=100, value=50, size=200, nodeID=5 | Success, nodeID=5         | P9        |
| TC-7  | ID=1, time=100, value=50, size=200, nodeID=-1 | Success, nodeID=-1        | P8        |
| TC-8  | ID=1, time=-1, value=50, size=200, nodeID=5 | ArithmeticException        | P2        |
| TC-9  | ID=1, time=100, value=-1, size=200, nodeID=5 | ArithmeticException       | P4        |
| TC-10 | ID=1, time=100, value=50, size=-1, nodeID=5 | ArithmeticException        | P6        |

---

## 4. Constructor: `Transaction()`

### Test cases
| ID    | Input | Expected                           | Satisfies |
|-------|-------|------------------------------------|-----------|
| TC-11 | None  | Success, default values (0, -1), seedChanging=false | Default   |

---

## 5. Constructor: `Transaction(long id)`

### Test cases
| ID    | Input   | Expected              | Satisfies |
|-------|---------|----------------------|-----------|
| TC-12 | id=42   | Success, ID=42       | Valid ID  |
| TC-13 | id=0    | Success, ID=0        | Boundary  |

---

## 6. Method: `makeSeedChanging()` and `isSeedChanging()`

### Black Box Analysis

#### Input partitions
| ID   | Condition                | Partition              | Valid? |
|------|--------------------------|------------------------|--------|
| P11  | seedChanging before call | seedChanging = false   | true   |
| P12  | seedChanging after call  | seedChanging = true    | true   |

### Test cases
| ID    | Input/Action                    | Expected              | Satisfies |
|-------|--------------------------------|----------------------|-----------|
| TC-14 | New tx, call isSeedChanging()  | false                | P11       |
| TC-15 | Call makeSeedChanging(), then isSeedChanging() | true | P12       |

---

## 7. Method: `getNextTxID()` and `resetCurrID()`

### Black Box Analysis

#### Input partitions
| ID   | Condition            | Partition                  | Valid? |
|------|----------------------|----------------------------|--------|
| P13  | Initial state        | currID = 1                 | true   |
| P14  | After getNextTxID()  | currID increments          | true   |
| P15  | After resetCurrID()  | currID = 1                 | true   |

### Test cases
| ID    | Input/Action                              | Expected   | Satisfies |
|-------|-------------------------------------------|------------|-----------|
| TC-16 | After @BeforeEach reset, getNextTxID()    | returns 1  | P13,P15   |
| TC-17 | getNextTxID() called twice consecutively  | 1, 2       | P14       |
| TC-18 | getNextTxID(), resetCurrID(), getNextTxID() | 1        | P14,P15   |

---

## 8. Method: `setValue(float value)`

### Black Box Analysis

#### Input partitions
| ID   | Condition       | Partition    | Valid? |
|------|-----------------|--------------|--------|
| P16  | value >= 0      | value = 100  | true   |
| P17  | value < 0       | value = -1   | false  |

#### Boundary values
| ID   | Variable-Value |
|------|----------------|
| B10  | value = 0      |
| B11  | value = -0.001 |

### Test cases
| ID    | Input        | Expected            | Satisfies |
|-------|--------------|---------------------|-----------|
| TC-19 | value = 100  | Success, value=100  | P16       |
| TC-20 | value = 0    | Success, value=0    | B10       |
| TC-21 | value = -1   | ArithmeticException | P17,B11   |

---

## 9. Method: `setSize(float size)`

### Black Box Analysis

#### Input partitions
| ID   | Condition      | Partition   | Valid? |
|------|----------------|-------------|--------|
| P18  | size >= 0      | size = 500  | true   |
| P19  | size < 0       | size = -1   | false  |

#### Boundary values
| ID   | Variable-Value |
|------|----------------|
| B12  | size = 0       |
| B13  | size = -0.001  |

### Test cases
| ID    | Input       | Expected            | Satisfies |
|-------|-------------|---------------------|-----------|
| TC-22 | size = 500  | Success, size=500   | P18       |
| TC-23 | size = 0    | Success, size=0     | B12       |
| TC-24 | size = -1   | ArithmeticException | P19,B13   |

---

## 10. Method: `setID(long ID)` and `getID()`

### Test cases
| ID    | Input     | Expected      | Satisfies |
|-------|-----------|---------------|-----------|
| TC-25 | ID = 999  | getID() = 999 | Valid     |
| TC-26 | ID = 0    | getID() = 0   | Boundary  |

---

## 11. Method: `setNodeID(int nodeID)` and `getNodeID()`

### Test cases
| ID    | Input       | Expected          | Satisfies |
|-------|-------------|-------------------|-----------|
| TC-27 | nodeID = 10 | getNodeID() = 10  | Valid     |
| TC-28 | nodeID = -1 | getNodeID() = -1  | Default   |
| TC-29 | nodeID = 0  | getNodeID() = 0   | Boundary  |

---

## 12. Method: `getCreationTime()`

### Test cases
| ID    | Input                             | Expected             | Satisfies |
|-------|-----------------------------------|----------------------|-----------|
| TC-30 | Constructor with time=1000        | getCreationTime()=1000 | Valid   |

---

## 13. Method: `getValue()` and `getSize()`

### Test cases
| ID    | Input                               | Expected                      | Satisfies |
|-------|-------------------------------------|-------------------------------|-----------|
| TC-31 | Constructor with value=322,size=500 | getValue()=322, getSize()=500 | Valid     |

---

## Summary of Test Cases

| ID    | Description                                              |
|-------|----------------------------------------------------------|
| TC-1  | 4-param constructor with all zero boundary values        |
| TC-2  | 4-param constructor with typical valid values            |
| TC-3  | 4-param constructor with negative time throws exception  |
| TC-4  | 4-param constructor with negative value throws exception |
| TC-5  | 4-param constructor with negative size throws exception  |
| TC-6  | 5-param constructor with valid nodeID                    |
| TC-7  | 5-param constructor with nodeID=-1                       |
| TC-8  | 5-param constructor with negative time throws exception  |
| TC-9  | 5-param constructor with negative value throws exception |
| TC-10 | 5-param constructor with negative size throws exception  |
| TC-11 | Default constructor creates object with defaults         |
| TC-12 | Single-param constructor sets ID                         |
| TC-13 | Single-param constructor with ID=0                       |
| TC-14 | isSeedChanging() returns false initially                 |
| TC-15 | makeSeedChanging() sets flag to true                     |
| TC-16 | getNextTxID() returns 1 after reset                      |
| TC-17 | getNextTxID() increments and returns ID                  |
| TC-18 | resetCurrID() resets counter to 1                        |
| TC-19 | setValue() with positive value                           |
| TC-20 | setValue() with zero                                     |
| TC-21 | setValue() with negative throws exception                |
| TC-22 | setSize() with positive size                             |
| TC-23 | setSize() with zero                                      |
| TC-24 | setSize() with negative throws exception                 |
| TC-25 | setID() and getID() with valid ID                        |
| TC-26 | setID() and getID() with zero                            |
| TC-27 | setNodeID() and getNodeID() with positive                |
| TC-28 | setNodeID() and getNodeID() with -1                      |
| TC-29 | setNodeID() and getNodeID() with zero                    |
| TC-30 | getCreationTime() returns correct value                  |
| TC-31 | getValue() and getSize() return correct values           |

---

## Outcomes

### 2026-02-03 (LATEST)
CLOSED

All 31 test cases implemented and passing. 100% instruction and branch coverage achieved.

### 2026-02-03
Initial test design created. All test cases pending implementation.

#### Pending Tests:
TC-1 through TC-31
