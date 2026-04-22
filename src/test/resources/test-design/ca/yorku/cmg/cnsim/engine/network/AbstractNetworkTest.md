# Test Design - AbstractNetwork

## 1. Unit under test
- Class: `AbstractNetwork`
- Package: `ca.yorku.cmg.cnsim.engine.network`

---

## 2. Method: `AbstractNetwork()` (empty constructor)

### Black Box Analysis

#### Input partitions
| ID  | Condition | Partition | Valid? |
|-----|-----------|-----------|--------|
| P1  | No inputs | N/A       | true   |

#### Boundary values
None identified.

#### Guesses
None identified.

### White Box Analysis
No decisions in empty constructor.

### Test cases
| ID   | Input | Expected                              | Satisfies |
|------|-------|---------------------------------------|-----------|
| TC-1 | None  | Object created; `ns` null; `Net` null | P1        |

---

## 3. Method: `AbstractNetwork(NodeSet ns)`

### Black Box Analysis

#### Input partitions
| ID  | Condition   | Partition  | Valid? |
|-----|-------------|------------|--------|
| P2  | Value of ns | ns == null | false  |
| P3  | Value of ns | ns != null | true   |

#### Boundary values
| ID  | Variable-Value |
|-----|----------------|
| B1  | ns = null      |

#### Guesses
None identified.

### White Box Analysis

#### Decisions and Conditions

| Decision ID | Decision Expression | Atomic Conditions |
|-------------|---------------------|-------------------|
| D1          | ns == null          | C1: ns == null    |

#### Test obligations

| Test Case | C1  | D1  |
|-----------|-----|-----|
| CD1       | T   | T   |
| CD2       | F   | F   |

### Test cases
| ID   | Input      | Expected                                                           | Satisfies   |
|------|------------|--------------------------------------------------------------------|-------------|
| TC-2 | ns = null  | NullPointerException (test currently skipped)                      | P2, B1, CD1 |
| TC-3 | ns != null | Network created; `Net` allocated (size N+1 × N+1); `this.ns == ns` | P3, CD2     |

---

## 4. Method: `getTransmissionTime(int origin, int destination, float size)`

### Black Box Analysis

#### Input partitions
| ID  | Condition       | Partition   | Valid? |
|-----|-----------------|-------------|--------|
| P4  | Value of size   | size < 0    | false  |
| P5  | Value of size   | size >= 0   | true   |
| P6  | Value of origin | origin < 0  | false  |
| P7  | Value of origin | origin >= 0 | true   |
| P8  | Value of dest   | dest < 0    | false  |
| P9  | Value of dest   | dest >= 0   | true   |

#### Boundary values
| ID  | Variable-Value   |
|-----|------------------|
| B2  | size = -1.0      |
| B3  | size = 0.0       |
| B4  | origin = -1      |
| B5  | origin = 0       |
| B6  | destination = -1 |
| B7  | destination = 0  |

#### Guesses
| ID  | Scenario                                                          |
|-----|-------------------------------------------------------------------|
| G1  | Throughput between nodes is 0 -> returns -1                        |
| G2  | Normal case: size=1000 bytes, throughput=8000 bps -> returns 1000  |

### White Box Analysis

#### Decisions and Conditions

| Decision ID | Decision Expression | Atomic Conditions   |
|-------------|---------------------|---------------------|
| D2          | size < 0            | C2: size < 0        |
| D3          | origin < 0          | C3: origin < 0      |
| D4          | destination < 0     | C4: destination < 0 |

#### Test obligations

| Test Case | C2  | C3  | C4  | D2  | D3  | D4  |
|-----------|-----|-----|-----|-----|-----|-----|
| CD3       | T   | -   | -   | T   | -   | -   |
| CD4       | F   | T   | -   | F   | T   | -   |
| CD5       | F   | F   | T   | F   | F   | T   |
| CD6       | F   | F   | F   | F   | F   | F   |

### Test cases
| ID   | Input                                        | Expected            | Satisfies                    |
|------|----------------------------------------------|---------------------|------------------------------|
| TC-4 | origin=1, dest=1, size=-1                    | ArithmeticException | P4, B2, CD3                  |
| TC-5 | origin=-1, dest=1, size=100                  | ArithmeticException | P6, B4, CD4                  |
| TC-6 | origin=1, dest=-1, size=100                  | ArithmeticException | P8, B6, CD5                  |
| TC-7 | origin=0, dest=0, size=0; Net[0][0]=8000     | Returns 0 ms        | P5, P7, P9, B3, B5, B7, CD6  |
| TC-8 | origin=1, dest=2, size=100; Net[1][2]=0      | Returns -1          | G1, CD6                      |
| TC-9 | origin=1, dest=2, size=1000; Net[1][2]=8000  | Returns 1000 ms     | G2, CD6                      |

---

## 5. Method: `getTransmissionTime(float throughput, float size)`

### Black Box Analysis

#### Input partitions
| ID  | Condition           | Partition       | Valid? |
|-----|---------------------|-----------------|--------|
| P10 | Value of size       | size < 0        | false  |
| P11 | Value of size       | size >= 0       | true   |
| P12 | Value of throughput | throughput < 0  | false  |
| P13 | Value of throughput | throughput == 0 | true   |
| P14 | Value of throughput | throughput > 0  | true   |

#### Boundary values
| ID  | Variable-Value    |
|-----|-------------------|
| B8  | size = -1.0       |
| B9  | size = 0.0        |
| B10 | throughput = -1.0 |
| B11 | throughput = 0.0  |

#### Guesses
| ID  | Scenario                                        |
|-----|-------------------------------------------------|
| G3  | size=1000 bytes, throughput=8000 bps -> 1000 ms  |

### White Box Analysis

#### Decisions and Conditions

| Decision ID | Decision Expression | Atomic Conditions   |
|-------------|---------------------|---------------------|
| D5          | size < 0            | C5: size < 0        |
| D6          | throughput < 0      | C6: throughput < 0  |
| D7          | throughput == 0     | C7: throughput == 0 |

#### Test obligations

| Test Case | C5  | C6  | C7  | D5  | D6  | D7  |
|-----------|-----|-----|-----|-----|-----|-----|
| CD7       | T   | -   | -   | T   | -   | -   |
| CD8       | F   | T   | -   | F   | T   | -   |
| CD9       | F   | F   | T   | F   | F   | T   |
| CD10      | F   | F   | F   | F   | F   | F   |

### Test cases
| ID    | Input                       | Expected            | Satisfies              |
|-------|-----------------------------|---------------------|------------------------|
| TC-10 | throughput=100, size=-1     | ArithmeticException | P10, B8, CD7           |
| TC-11 | throughput=-1, size=100     | ArithmeticException | P12, B10, CD8          |
| TC-12 | throughput=0, size=100      | Returns -1          | P13, B11, CD9          |
| TC-13 | throughput=0, size=0        | Returns -1          | P13, P11, B11, B9, CD9 |
| TC-14 | throughput=8000, size=1000  | Returns 1000 ms     | P14, P11, G3, CD10     |

---

## 6. Method: `getThroughput(int origin, int destination)`

### Black Box Analysis

#### Input partitions
| ID  | Condition        | Partition   | Valid? |
|-----|------------------|-------------|--------|
| P15 | Value of origin  | origin < 0  | false  |
| P16 | Value of origin  | origin >= 0 | true   |
| P17 | Value of dest    | dest < 0    | false  |
| P18 | Value of dest    | dest >= 0   | true   |

#### Boundary values
| ID  | Variable-Value   |
|-----|------------------|
| B12 | origin = -1      |
| B13 | origin = 0       |
| B14 | destination = -1 |
| B15 | destination = 0  |

#### Guesses
None identified.

### White Box Analysis

#### Decisions and Conditions

| Decision ID | Decision Expression | Atomic Conditions   |
|-------------|---------------------|---------------------|
| D8          | origin < 0          | C8: origin < 0      |
| D9          | destination < 0     | C9: destination < 0 |

#### Test obligations

| Test Case | C8  | C9  | D8  | D9  |
|-----------|-----|-----|-----|-----|
| CD11      | T   | -   | T   | -   |
| CD12      | F   | T   | F   | T   |
| CD13      | F   | F   | F   | F   |

### Test cases
| ID    | Input                 | Expected               | Satisfies                |
|-------|-----------------------|------------------------|--------------------------|
| TC-15 | origin=-1, dest=1     | ArithmeticException    | P15, B12, CD11           |
| TC-16 | origin=1, dest=-1     | ArithmeticException    | P17, B14, CD12           |
| TC-17 | origin=0, dest=0      | Returns Net[0][0]      | P16, P18, B13, B15, CD13 |
| TC-18 | origin=1, dest=2      | Returns Net[1][2]      | P16, P18, CD13           |

---

## 7. Method: `setThroughput(int origin, int destination, float throughput)`

### Black Box Analysis

#### Input partitions
| ID  | Condition           | Partition       | Valid? |
|-----|---------------------|-----------------|--------|
| P19 | Value of origin     | origin < 0      | false  |
| P20 | Value of origin     | origin >= 0     | true   |
| P21 | Value of dest       | dest < 0        | false  |
| P22 | Value of dest       | dest >= 0       | true   |
| P23 | Value of throughput | throughput < 0  | false  |
| P24 | Value of throughput | throughput >= 0 | true   |

#### Boundary values
| ID  | Variable-Value    |
|-----|-------------------|
| B16 | origin = -1       |
| B17 | origin = 0        |
| B18 | destination = -1  |
| B19 | destination = 0   |
| B20 | throughput = -1.0 |
| B21 | throughput = 0.0  |

#### Guesses
| ID  | Scenario                                                                       |
|-----|--------------------------------------------------------------------------------|
| G4  | `Reporter.reportsNetEvents() == true`: reporter branch fires before validation |

### White Box Analysis

Note: `Reporter.reportsNetEvents()` is checked **before** precondition validation. This means the reporter branch fires even if the subsequent validation throws.

#### Decisions and Conditions

| Decision ID | Decision Expression         | Atomic Conditions                |
|-------------|-----------------------------|----------------------------------|
| D10         | Reporter.reportsNetEvents() | C10: Reporter.reportsNetEvents() |
| D11         | origin < 0                  | C11: origin < 0                  |
| D12         | destination < 0             | C12: destination < 0             |
| D13         | throughput < 0              | C13: throughput < 0              |

#### Test obligations

| Test Case | C10 | C11 | C12 | C13 | D10 | D11 | D12 | D13 |
|-----------|-----|-----|-----|-----|-----|-----|-----|-----|
| CD14      | F   | T   | -   | -   | F   | T   | -   | -   |
| CD15      | F   | F   | T   | -   | F   | F   | T   | -   |
| CD16      | F   | F   | F   | T   | F   | F   | F   | T   |
| CD17      | F   | F   | F   | F   | F   | F   | F   | F   |
| CD18      | T   | F   | F   | F   | T   | F   | F   | F   |

### Test cases
| ID    | Input                                               | Expected                                   | Satisfies                          |
|-------|-----------------------------------------------------|--------------------------------------------|------------------------------------|
| TC-19 | origin=-1, dest=1, throughput=100                   | ArithmeticException                        | P19, B16, CD14                     |
| TC-20 | origin=1, dest=-1, throughput=100                   | ArithmeticException                        | P21, B18, CD15                     |
| TC-21 | origin=1, dest=1, throughput=-1                     | ArithmeticException                        | P23, B20, CD16                     |
| TC-22 | origin=0, dest=0, throughput=0                      | Net[0][0] == 0                             | P20, P22, P24, B17, B19, B21, CD17 |
| TC-23 | origin=1, dest=2, throughput=8000                   | Net[1][2] == 8000                          | P20, P22, P24, CD17                |
| TC-24 | reporter enabled; origin=1, dest=2, throughput=9000 | Net[1][2] == 9000; reporter event recorded | G4, CD18                           |

---

## 8. Method: `getAvgTroughput(int origin)`

### Black Box Analysis

Note: This method has **no pre-condition guards** in the source. Accessing `Net[origin][i]` with an out-of-bounds `origin` causes `ArrayIndexOutOfBoundsException`. Nodes use a **1-based** index convention (valid range: 1 ≤ origin ≤ N). `origin = 0` is semantically invalid but does not throw: the loop runs i = 1..N, and since `i != 0` is always true, count = 2N and a finite float is returned (no NaN) whenever N ≥ 1.

Let N = `net.numOfNodes` (from config).

#### Input partitions
| ID  | Condition       | Partition             | Valid? |
|-----|-----------------|-----------------------|--------|
| P25 | Value of origin | origin < 0            | false  |
| P26 | Value of origin | 1 ≤ origin ≤ N        | true   |
| P27 | Value of origin | origin > N            | false  |
| P28 | Value of origin | origin == 0           | false  |

#### Boundary values
| ID  | Variable-Value  |
|-----|-----------------|
| B22 | origin = 0      |
| B23 | origin = 1      |
| B24 | origin = N      |
| B25 | origin = N + 1  |
| B26 | origin = -1     |

#### Guesses
| ID  | Scenario                                                                                    |
|-----|---------------------------------------------------------------------------------------------|
| G5  | All throughputs equal to constant C -> average equals C                                      |
| G6  | origin=0 with N ≥ 1 -> loop always executes (i != 0 always true), count > 0, returns a float |

### White Box Analysis

#### Decisions and Conditions

| Decision ID | Decision Expression | Atomic Conditions |
|-------------|---------------------|-------------------|
| D14         | i != origin         | C14: i != origin  |

#### Test obligations

| Test Case | C14 | D14 |
|-----------|-----|-----|
| CD19      | T   | T   |
| CD20      | F   | F   |

### Test cases
| ID    | Input                                 | Expected                                                                      | Satisfies            |
|-------|---------------------------------------|-------------------------------------------------------------------------------|----------------------|
| TC-25 | origin = -1                           | ArrayIndexOutOfBoundsException                                                | P25, B26             |
| TC-26 | origin = 0 (N ≥ 1)                    | Returns a finite float (not NaN); origin=0 is out-of-range but does not throw | P28, B22, G6         |
| TC-27 | origin = 1 (N ≥ 2)                    | Returns float ≥ 0, not NaN                                                    | P26, B23, CD19, CD20 |
| TC-28 | origin = N (N ≥ 2)                    | Returns float ≥ 0, not NaN                                                    | P26, B24, CD19, CD20 |
| TC-29 | origin = N + 1                        | ArrayIndexOutOfBoundsException                                                | P27, B25             |
| TC-30 | All Net[i][j] = C; origin = 1 (N ≥ 2) | Returns C                                                                     | G5                   |

---

## 9. Method: `getNodeSet()`

### Black Box Analysis

#### Input partitions
| ID  | Condition | Partition | Valid? |
|-----|-----------|-----------|--------|
| P29 | No inputs | N/A       | true   |

#### Boundary values
None identified.

#### Guesses
None identified.

### White Box Analysis
No decisions; simple getter.

### Test cases
| ID    | Input | Expected            | Satisfies |
|-------|-------|---------------------|-----------|
| TC-31 | None  | Returns stored `ns` | P29       |

---

## 10. Method: `printNetwork()`

### Black Box Analysis

#### Input partitions
| ID  | Condition | Partition   | Valid? |
|-----|-----------|-------------|--------|
| P30 | Net state | Net != null | true   |
| P31 | Net state | Net == null | false  |

#### Boundary values
None identified beyond null guard.

#### Guesses
| ID  | Scenario                                       |
|-----|------------------------------------------------|
| G7  | Net has populated throughput values -> printed  |

### White Box Analysis
No branching beyond the null pre-condition check.

### Test cases
| ID    | Input                           | Expected                       | Satisfies |
|-------|---------------------------------|--------------------------------|-----------|
| TC-32 | Net != null, values set         | stdout contains all set values | P30, G7   |
| TC-33 | Net == null (empty constructor) | NullPointerException           | P31       |

---

## 11. Method: `printNetwork2()`

### Black Box Analysis

#### Input partitions
| ID  | Condition | Partition   | Valid? |
|-----|-----------|-------------|--------|
| P32 | Net state | Net != null | true   |
| P33 | Net state | Net == null | false  |

#### Boundary values
None identified beyond null guard.

#### Guesses
| ID  | Scenario                                       |
|-----|------------------------------------------------|
| G8  | Net has populated throughput values -> printed  |

### White Box Analysis
No branching beyond the null pre-condition check.

### Test cases
| ID    | Input                           | Expected                       | Satisfies |
|-------|---------------------------------|--------------------------------|-----------|
| TC-34 | Net != null, values set         | stdout contains all set values | P32, G8   |
| TC-35 | Net == null (empty constructor) | NullPointerException           | P33       |

---

## Outcomes

### 2026-03-22 (LATEST)
CLOSED