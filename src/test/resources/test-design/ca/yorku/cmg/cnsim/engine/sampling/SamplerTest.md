# Test Design - Sampler

## 1. Unit under test
- Class: `Sampler`
- Package: `ca.yorku.cmg.cnsim.engine.sampling`

---

## 2. Constructor: `Sampler()`

### Black Box Analysis

#### Input Partitions
| ID  | Condition | Partition | Valid? |
|-----|-----------|-----------|--------|
| P1  | No inputs | N/A       | true   |

#### Boundary Values
None identified for default constructor.

#### Guesses
None identified for default constructor.

### White Box Analysis
No decisions in default constructor.

### Test Cases
| ID   | Input | Expected          | Satisfies |
|------|-------|-------------------|-----------|
| TC-1 | None  | Object created    | P1        |

---

## 3. Method: `getPoissonInterval(float lambda, Random random)`

### Black Box Analysis

#### Input Partitions
| ID  | Condition        | Partition    | Valid? |
|-----|------------------|--------------|--------|
| P2  | Value of lambda  | lambda < 0   | false  |
| P3  | Value of lambda  | lambda == 0  | true   |
| P4  | Value of lambda  | lambda > 0   | true   |
| P5  | Value of random  | random == null | false  |
| P6  | Value of random  | random != null | true   |

#### Boundary Values
| ID  | Variable-Value  |
|-----|-----------------|
| B1  | lambda = -1.0   |
| B2  | lambda = 0.0    |
| B3  | lambda = 0.001  |
| B4  | random = null   |

#### Guesses
| ID  | Scenario                          |
|-----|-----------------------------------|
| G1  | lambda = 1.0 (typical rate)       |
| G2  | lambda = 10.0 (high rate)         |

### White Box Analysis

#### Decisions and Conditions
| Decision ID | Decision Expression | Atomic Conditions     |
|-------------|---------------------|-----------------------|
| D1          | lambda < 0          | C1: lambda < 0        |
| D2          | random == null      | C2: random == null    |
| D3          | p == 0.0            | C3: p == 0.0          |

#### Test Obligations
| ID   | C1    | C2    | C3    | Covers                                |
|------|-------|-------|-------|---------------------------------------|
| CD1  | true  | -     | -     | lambda < 0: ArithmeticException       |
| CD2  | false | true  | -     | random == null: NullPointerException  |
| CD3  | false | false | true  | p == 0.0: retry sampling              |
| CD4  | false | false | false | valid inputs: calculate interval      |

### Test Cases
| ID   | Input                       | Expected                   | Satisfies           |
|------|-----------------------------|----------------------------|---------------------|
| TC-2 | lambda=-1, valid random     | ArithmeticException        | P2, B1, CD1         |
| TC-3 | lambda=1, random=null       | NullPointerException       | P5, B4, CD2         |
| TC-4 | lambda=0, valid random      | Result >= 0                | P3, B2, CD4         |
| TC-5 | lambda=0.001, valid random  | Result >= 0                | P4, B3, CD4         |
| TC-6 | lambda=1.0, valid random    | Result >= 0                | P4, G1, CD4         |
| TC-7 | lambda=10.0, valid random   | Result >= 0                | P4, G2, CD4         |

---

## 4. Method: `getGaussian(float mean, float deviation, Random random)`

### Black Box Analysis

#### Input Partitions
| ID   | Condition          | Partition         | Valid? |
|------|--------------------|-------------------|--------|
| P7   | Value of deviation | deviation < 0     | false  |
| P8   | Value of deviation | deviation == 0    | true   |
| P9   | Value of deviation | deviation > 0     | true   |
| P10  | Value of random    | random == null    | false  |
| P11  | Value of random    | random != null    | true   |
| P12  | Value of mean      | mean < 0          | true   |
| P13  | Value of mean      | mean == 0         | true   |
| P14  | Value of mean      | mean > 0          | true   |

#### Boundary Values
| ID   | Variable-Value   |
|------|------------------|
| B5   | deviation = -1.0 |
| B6   | deviation = 0.0  |
| B7   | deviation = 0.1  |
| B8   | mean = -10.0     |
| B9   | mean = 0.0       |
| B10  | mean = 10.0      |
| B11  | random = null    |

#### Guesses
| ID  | Scenario                              |
|-----|---------------------------------------|
| G3  | mean=100, deviation=10 (typical)      |
| G4  | mean=50, deviation=5 (small variance) |
| G5  | mean=1000, deviation=100 (large)      |
| G6  | mean=-1, deviation=10 (negative mean) | 

### White Box Analysis

#### Decisions and Conditions
| Decision ID | Decision Expression  | Atomic Conditions        |
|-------------|----------------------|--------------------------|
| D4          | deviation < 0        | C4: deviation < 0        |
| D5          | random == null       | C5: random == null       |
| D6          | gaussianValue <= 0   | C6: gaussianValue <= 0   |

#### Test Obligations
| ID   | C4    | C5    | C6    | Covers                                   |
|------|-------|-------|-------|------------------------------------------|
| CD5  | true  | -     | -     | deviation < 0: ArithmeticException       |
| CD6  | false | true  | -     | random == null: NullPointerException     |
| CD7  | false | false | true  | negative value: retry sampling           |
| CD8  | false | false | false | valid inputs: return positive value      |

### Test Cases
| ID    | Input                                  | Expected                 | Satisfies        |
|-------|----------------------------------------|--------------------------|------------------|
| TC-8  | mean=10, deviation=-1, valid random    | ArithmeticException      | P7, B5, CD5      |
| TC-9  | mean=10, deviation=1, random=null      | NullPointerException     | P10, B11, CD6    |
| TC-10 | mean=10, deviation=0, valid random     | Result > 0, Result == 10 | P8, B6, CD8      |
| TC-11 | mean=10, deviation=0.1, valid random   | Result > 0               | P9, B7, CD8      |
| TC-12 | mean=-10, deviation=1, valid random    | Result > 0               | P12, B8, CD8     |
| TC-13 | mean=0, deviation=1, valid random      | Result > 0               | P13, B9, CD8     |
| TC-14 | mean=10, deviation=1, valid random     | Result > 0               | P14, B10, CD8    |
| TC-15 | mean=100, deviation=10, valid random   | Result > 0               | P9, P14, G3, CD8 |
| TC-16 | mean=50, deviation=5, valid random     | Result > 0               | P9, P14, G4, CD8 |
| TC-17 | mean=1000, deviation=100, valid random | Result > 0               | P9, P14, G5, CD8 |
| TC-18 | mean=-1, deviation=10, valid random    | Result > 0               | G4               |
---

## 5. Method: `getTransactionSampler()`

### Black Box Analysis

#### Input Partitions
| ID   | Condition | Partition | Valid? |
|------|-----------|-----------|--------|
| P15  | No inputs | N/A       | true   |

#### Boundary Values
None identified for simple getter.

#### Guesses
None identified for this method.

### White Box Analysis
None

### Test Cases
| ID    | Input | Expected                        | Satisfies |
|-------|-------|---------------------------------|-----------|
| TC-18 | None  | Returns transactionSampler      | P15       |

---

## 6. Method: `setTransactionSampler(AbstractTransactionSampler txSampler)`

### Black Box Analysis

#### Input Partitions
| ID   | Condition         | Partition         | Valid? |
|------|-------------------|-------------------|--------|
| P16  | Value of txSampler| txSampler == null | true   |
| P17  | Value of txSampler| txSampler != null | true   |

#### Boundary Values
| ID   | Variable-Value    |
|------|-------------------|
| B12  | txSampler = null  |

#### Guesses
None identified for this method.

### White Box Analysis
None

### Test Cases
| ID    | Input                | Expected                | Satisfies    |
|-------|----------------------|-------------------------|--------------|
| TC-19 | txSampler = null     | Field set to null       | P16, B12     |
| TC-20 | txSampler = valid    | Field set to value      | P17          |

---

## 7. Method: `getNodeSampler()`

### Black Box Analysis

#### Input Partitions
| ID   | Condition | Partition | Valid? |
|------|-----------|-----------|--------|
| P18  | No inputs | N/A       | true   |

#### Boundary Values
None identified for simple getter.

#### Guesses
None identified for this method.

### White Box Analysis
None

### Test Cases
| ID    | Input | Expected                | Satisfies |
|-------|-------|-------------------------|-----------|
| TC-21 | None  | Returns nodeSampler     | P18       |

---

## 8. Method: `setNodeSampler(AbstractNodeSampler nodeSampler)`

### Black Box Analysis

#### Input Partitions
| ID   | Condition            | Partition            | Valid? |
|------|----------------------|----------------------|--------|
| P19  | Value of nodeSampler | nodeSampler == null  | true   |
| P20  | Value of nodeSampler | nodeSampler != null  | true   |

#### Boundary Values
| ID   | Variable-Value       |
|------|----------------------|
| B13  | nodeSampler = null   |

#### Guesses
None identified for this method.

### White Box Analysis
None

### Test Cases
| ID    | Input                 | Expected                | Satisfies    |
|-------|-----------------------|-------------------------|--------------|
| TC-22 | nodeSampler = null    | Field set to null       | P19, B13     |
| TC-23 | nodeSampler = valid   | Field set to value      | P20          |

---

## 9. Method: `getNetworkSampler()`

### Black Box Analysis

#### Input Partitions
| ID   | Condition | Partition | Valid? |
|------|-----------|-----------|--------|
| P21  | No inputs | N/A       | true   |

#### Boundary Values
None identified for simple getter.

#### Guesses
None identified for this method.

### White Box Analysis
None

### Test Cases
| ID    | Input | Expected                   | Satisfies |
|-------|-------|----------------------------|-----------|
| TC-24 | None  | Returns networkSampler     | P21       |

---

## 10. Method: `setNetworkSampler(AbstractNetworkSampler netSampler)`

### Black Box Analysis

#### Input Partitions
| ID   | Condition             | Partition             | Valid? |
|------|-----------------------|-----------------------|--------|
| P22  | Value of netSampler   | netSampler == null    | true   |
| P23  | Value of netSampler   | netSampler != null    | true   |

#### Boundary Values
| ID   | Variable-Value        |
|------|-----------------------|
| B14  | netSampler = null     |

#### Guesses
None identified for this method.

### White Box Analysis
None

### Test Cases
| ID    | Input                  | Expected                | Satisfies    |
|-------|------------------------|-------------------------|--------------|
| TC-25 | netSampler = null      | Field set to null       | P22, B14     |
| TC-26 | netSampler = valid     | Field set to value      | P23          |

---

## 11. Outcomes
