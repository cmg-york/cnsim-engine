# Test Design — TxDependencyRegistry

## 1. Unit under test
- Class: `TxDependencyRegistry`
- Package: `ca.yorku.cmg.cnsim.engine.transaction`

---

## 2. Constructor: `TxDependencyRegistry(long size)`

### Black Box Analysis

#### Input Partitions
| ID  | Condition       | Partition                        | Valid? |
|-----|-----------------|----------------------------------|--------|
| P1  | Value of size   | size <= 0                        | false  |
| P2  | Value of size   | 0 < size < Integer.MAX_VALUE     | true   |
| P3  | Value of size   | size >= Integer.MAX_VALUE        | false  |

#### Boundary Values
| ID  | Variable-Value               |
|-----|------------------------------|
| B1  | size = 0                     |
| B2  | size = 1                     |
| B3  | size = Integer.MAX_VALUE - 1 |
| B4  | size = Integer.MAX_VALUE     |
| B5  | size = Integer.MAX_VALUE + 1 |

#### Guesses
None identified for constructor.

### White Box Analysis

#### Decisions and Conditions
| Decision ID | Decision Expression           | Atomic Conditions              |
|-------------|-------------------------------|--------------------------------|
| D1          | size <= 0                     | C1: size <= 0                  |
| D2          | size >= Integer.MAX_VALUE     | C2: size >= Integer.MAX_VALUE  |

#### Test Obligations
| ID   | C1    | C2    | D1    | D2    | Covers                              |
|------|-------|-------|-------|-------|-------------------------------------|
| CD1  | true  | -     | true  | -     | size <= 0: exception                |
| CD2  | false | true  | false | true  | size >= MAX_VALUE: exception        |
| CD3  | false | false | false | false | valid size: registry created        |

### Test Cases
| ID   | Input                          | Expected                    | Satisfies        |
|------|--------------------------------|-----------------------------|------------------|
| TC-1 | size = 0                       | IllegalArgumentException    | P1, B1, CD1      |
| TC-2 | size = 1                       | Registry created            | P2, B2, CD3      |
| TC-3 | size = 10                      | Registry created            | P2, CD3          |
| TC-4 | size = Integer.MAX_VALUE - 1   | Registry created (disabled) | P2, B3, CD3      |
| TC-5 | size = Integer.MAX_VALUE       | IllegalArgumentException    | P3, B4, CD2      |
| TC-6 | size = Integer.MAX_VALUE + 1   | IllegalArgumentException    | P3, B5, CD2      |

---

## 3. Method: `addDependency(int j, int i)`

### Black Box Analysis

#### Input Partitions
| ID  | Condition                 | Partition           | Valid? |
|-----|---------------------------|---------------------|--------|
| P4  | Relationship i vs j       | i < j               | true   |
| P5  | Relationship i vs j       | i == j              | false  |
| P6  | Relationship i vs j       | i > j               | false  |
| P7  | Value of j                | j < 1               | false  |
| P8  | Value of j                | 1 <= j <= size      | true   |
| P9  | Value of j                | j > size            | false  |
| P10 | Value of i                | i < 1               | false  |
| P11 | Value of i                | i >= 1              | true   |

#### Boundary Values
| ID   | Variable-Value                    |
|------|-----------------------------------|
| B6   | i = j - 1 (maximum valid i for j) |
| B7   | i = 1 (minimum valid i)           |
| B8   | i = 0 (just below minimum)        |
| B9   | j = 0 (just below minimum)        |
| B10  | j = 1 (minimum valid j)           |
| B11  | j = size (maximum valid j)        |
| B12  | j = size + 1 (just above maximum) |

#### Guesses
| ID  | Scenario                                             |
|-----|------------------------------------------------------|
| G1  | Circular dependency attempt (i >= j after valid add) |

### White Box Analysis

#### Decisions and Conditions
| Decision ID | Decision Expression         | Atomic Conditions              |
|-------------|-----------------------------|--------------------------------|
| D3          | j < 1 &#124;&#124; j > size | C3: j < 1<br>C4: j > size      |
| D4          | i < 1                       | C5: i < 1                      |
| D5          | i >= j                      | C6: i >= j                     |

#### Test Obligations
| ID   | C3    | C4    | C5    | C6    | Covers                                   |
|------|-------|-------|-------|-------|------------------------------------------|
| CD4  | true  | -     | -     | -     | j < 1: IndexOutOfBoundsException         |
| CD5  | false | true  | -     | -     | j > size: IndexOutOfBoundsException      |
| CD6  | false | false | true  | -     | i < 1: IllegalArgumentException          |
| CD7  | false | false | false | true  | i >= j: IllegalArgumentException         |
| CD8  | false | false | false | false | valid inputs: dependency recorded        |

### Test Cases
| ID    | Input                    | Expected                  | Satisfies        |
|-------|--------------------------|---------------------------|------------------|
| TC-7  | j=5, i=3                 | Dependency recorded       | P4, P8, P11, CD8 |
| TC-8  | j=5, i=4 (i = j-1)       | Dependency recorded       | P4, B6, CD8      |
| TC-9  | j=5, i=5 (i == j)        | IllegalArgumentException  | P5, CD7          |
| TC-10 | j=5, i=6 (i > j)         | IllegalArgumentException  | P6, CD7          |
| TC-11 | j=5, i=0 (i < 1)         | IllegalArgumentException  | P10, B8, CD6     |
| TC-12 | j=0, i=1 (j < 1)         | IndexOutOfBoundsException | P7, B9, CD4      |
| TC-13 | j=11, i=1 (j > size=10)  | IndexOutOfBoundsException | P9, B12, CD5     |
| TC-14 | j=2, i=1 (i = 1)         | Dependency recorded       | P11, B7, CD8     |
| TC-15 | j=1, i=1 (self at min j) | IllegalArgumentException  | P5, B10, CD7     |
| TC-16 | j=10, i=1 (j = size)     | Dependency recorded       | P8, B11, CD8     |
| TC-17 | Add (2,1), then (1,2)    | Second throws IllegalArg  | G1, CD7          |

---

## 4. Method: `addDependencies(int id, BitSet dependencies)`

### Black Box Analysis

#### Input Partitions
| ID   | Condition             | Partition           | Valid? |
|------|-----------------------|---------------------|--------|
| P12  | Value of id           | id < 1              | false  |
| P13  | Value of id           | 1 <= id <= size     | true   |
| P14  | Value of id           | id > size           | false  |
| P15  | dependencies          | null                | true   |
| P16  | dependencies          | non-null BitSet     | true   |

#### Boundary Values
| ID   | Variable-Value          |
|------|-------------------------|
| B13  | id = 0                  |
| B14  | id = 1                  |
| B15  | id = size               |
| B16  | id = size + 1           |

#### Guesses
None identified for this method.

### White Box Analysis

#### Decisions and Conditions
| Decision ID | Decision Expression                   | Atomic Conditions              |
|-------------|---------------------------------------|--------------------------------|
| D7          | id < 1 &#124;&#124; id >= deps.length | C8: id < 1<br>C9: id >= length |

#### Test Obligations
| ID    | C8    | C9    | Covers                                   |
|-------|-------|-------|------------------------------------------|
| CD10  | true  | -     | id < 1: IndexOutOfBoundsException        |
| CD11  | false | true  | id > size: IndexOutOfBoundsException     |
| CD12  | false | false | valid inputs: dependencies set           |

### Test Cases
| ID    | Input                        | Expected                                            | Satisfies      |
|-------|------------------------------|-----------------------------------------------------|----------------|
| TC-18 | id=0, valid BitSet           | IndexOutOfBoundsException                           | P12, B13, CD10 |
| TC-19 | id=1, valid BitSet           | Dependencies set                                    | P13, B14, CD12 |
| TC-20 | id=10 (size), valid BitSet   | Dependencies set                                    | P13, B15, CD12 |
| TC-21 | id=-1, valid BitSet          | IndexOutOfBoundsException                           | P12, CD10      |
| TC-22 | id=11 (> size), valid BitSet | IndexOutOfBoundsException                           | P14, B16, CD11 |
| TC-23 | id=1, null BitSet            | No exception; `dependenciesMetFast` returns `true`  | P15, CD12      |

---

## 5. Method: `toBitSet(Collection<Integer> satisfied)`

### Black Box Analysis

#### Input Partitions
| ID   | Condition              | Partition              | Valid? |
|------|------------------------|------------------------|--------|
| P17  | satisfied collection   | null                   | false  |
| P18  | satisfied collection   | empty collection       | true   |
| P19  | satisfied collection   | single element         | true   |
| P20  | satisfied collection   | multiple elements      | true   |

#### Boundary Values
| ID   | Variable-Value               |
|------|------------------------------|
| B17  | empty collection             |
| B18  | single element               |
| B19  | multiple elements            |

#### Guesses
None identified for this method.

### White Box Analysis

#### Decisions and Conditions
| Decision ID | Decision Expression     | Atomic Conditions          |
|-------------|-------------------------|----------------------------|
| D8          | satisfied == null       | C10: satisfied == null     |

#### Test Obligations
| ID   | C10   | D8    | Covers                                |
|------|-------|-------|---------------------------------------|
| CD13 | true  | true  | satisfied == null: exception          |
| CD14 | false | false | satisfied != null: process collection |

### Test Cases
| ID    | Input                    | Expected                    | Satisfies          |
|-------|--------------------------|-----------------------------|--------------------|
| TC-24 | null collection          | NullPointerException        | P17, CD13          |
| TC-25 | empty collection         | Empty BitSet                | P18, B17, CD14     |
| TC-26 | collection with [1,3,5]  | BitSet with 1,3,5 set       | P20, B19, CD14     |
| TC-27 | collection with [1]      | BitSet with 1 set           | P19, B18, CD14     |

---

## 6. Method: `toBitSet(List<Transaction> satisfied)`

### Black Box Analysis

#### Input Partitions
| ID   | Condition            | Partition              | Valid? |
|------|----------------------|------------------------|--------|
| P21  | satisfied list       | null                   | false  |
| P22  | satisfied list       | empty list             | true   |
| P23  | satisfied list       | single transaction     | true   |
| P24  | satisfied list       | multiple transactions  | true   |

#### Boundary Values
| ID   | Variable-Value               |
|------|------------------------------|
| B20  | empty list                   |
| B21  | single transaction           |
| B22  | multiple transactions        |

#### Guesses
None identified for this method.

### White Box Analysis

#### Decisions and Conditions
| Decision ID | Decision Expression     | Atomic Conditions          |
|-------------|-------------------------|----------------------------|
| D9          | satisfied == null       | C11: satisfied == null     |

#### Test Obligations
| ID    | C11   | D9    | Covers                               |
|-------|-------|-------|--------------------------------------|
| CD15  | true  | true  | satisfied == null: exception         |
| CD16  | false | false | satisfied != null: process list      |

### Test Cases
| ID    | Input                   | Expected              | Satisfies      |
|-------|-------------------------|-----------------------|----------------|
| TC-28 | null list               | NullPointerException  | P21, CD15      |
| TC-29 | empty list              | Empty BitSet          | P22, B20, CD16 |
| TC-30 | list with txs [2,4,6]   | BitSet with 2,4,6 set | P24, B22, CD16 |
| TC-31 | list with single tx [5] | BitSet with 5 set     | P23, B21, CD16 |

---

## 7. Method: `dependenciesMet(int j, BitSet satisfiedBits)`

### Black Box Analysis

#### Input Partitions
| ID   | Condition                  | Partition                    | Valid? |
|------|----------------------------|------------------------------|--------|
| P25  | Value of j                 | j < 1                        | false  |
| P26  | Value of j                 | 1 <= j <= size               | true   |
| P27  | Value of j                 | j > size                     | false  |
| P28  | satisfiedBits              | null                         | false  |
| P29  | satisfiedBits              | non-null BitSet              | true   |
| P30  | Dependencies state         | all deps satisfied           | true   |
| P31  | Dependencies state         | some deps not satisfied      | true   |
| P32  | Dependencies state         | no dependencies exist        | true   |

#### Boundary Values
| ID   | Variable-Value       |
|------|----------------------|
| B23  | j = 0                |
| B24  | j = 1                |
| B25  | j = size             |
| B26  | j = size + 1         |

#### Guesses
None identified for this method.

### White Box Analysis

#### Decisions and Conditions
| Decision ID | Decision Expression                 | Atomic Conditions              |
|-------------|-------------------------------------|--------------------------------|
| D10         | satisfiedBits == null               | C12: satisfiedBits == null     |
| D11         | j < 1 &#124;&#124; j >= deps.length | C13: j < 1<br>C14: j >= length |

#### Test Obligations
| ID    | C12   | C13   | C14   | Covers                                     |
|-------|-------|-------|-------|--------------------------------------------|
| CD17  | true  | -     | -     | satisfiedBits null: NullPointerException   |
| CD18  | false | true  | -     | j < 1: IndexOutOfBoundsException           |
| CD19  | false | false | true  | j > size: IndexOutOfBoundsException        |
| CD20  | false | false | false | valid inputs: check dependencies           |

### Test Cases
| ID    | Input                                | Expected                    | Satisfies              |
|-------|--------------------------------------|-----------------------------|------------------------|
| TC-32 | j=0, valid BitSet                    | IndexOutOfBoundsException   | P25, B23, CD18         |
| TC-33 | j=1, valid BitSet, no deps           | true                        | P26, B24, P32, CD20    |
| TC-34 | j=10, valid BitSet, no deps          | true                        | P26, B25, P32, CD20    |
| TC-35 | j=11 (> size), valid BitSet          | IndexOutOfBoundsException   | P27, B26, CD19         |
| TC-36 | j=5, null BitSet                     | NullPointerException        | P28, CD17              |
| TC-37 | j with deps, all satisfied           | true                        | P29, P30, CD20         |
| TC-38 | j with deps, some not satisfied      | false                       | P29, P31, CD20         |

---

## 8. Method: `dependenciesMetFast(int j, BitSet satisfiedBits, BitSet scratch)`

### Black Box Analysis

#### Input Partitions
| ID   | Condition       | Partition      | Valid? |
|------|-----------------|----------------|--------|
| P33  | Value of j      | j < 1          | false  |
| P34  | Value of j      | 1 <= j <= size | true   |
| P35  | Value of j      | j > size       | false  |
| P36  | satisfiedBits   | null           | false  |
| P37  | satisfiedBits   | non-null       | true   |
| P38  | scratch         | null           | false  |
| P39  | scratch         | non-null       | true   |

#### Boundary Values
| ID   | Variable-Value       |
|------|----------------------|
| B27  | j = 0                |
| B28  | j = size + 1         |

#### Guesses
None identified for this method.

### White Box Analysis

#### Decisions and Conditions
| Decision ID | Decision Expression                 | Atomic Conditions              |
|-------------|-------------------------------------|--------------------------------|
| D12         | satisfiedBits == null               | C15: satisfiedBits == null     |
| D13         | scratch == null                     | C16: scratch == null           |
| D14         | j < 1 &#124;&#124; j >= deps.length | C17: j < 1<br>C18: j >= length |

#### Test Obligations
| ID    | C15   | C16   | C17   | C18   | Covers                                    |
|-------|-------|-------|-------|-------|-------------------------------------------|
| CD21  | true  | -     | -     | -     | satisfiedBits null: NullPointerException  |
| CD22  | false | true  | -     | -     | scratch null: NullPointerException        |
| CD23  | false | false | true  | -     | j < 1: IndexOutOfBoundsException          |
| CD24  | false | false | false | true  | j > size: IndexOutOfBoundsException       |
| CD25  | false | false | false | false | valid inputs: check dependencies          |

### Test Cases
| ID    | Input                                  | Expected                  | Satisfies           |
|-------|----------------------------------------|---------------------------|---------------------|
| TC-39 | j=0, valid BitSets                     | IndexOutOfBoundsException | P33, B27, CD23      |
| TC-40 | j=11 (> size), valid BitSets           | IndexOutOfBoundsException | P35, B28, CD24      |
| TC-41 | j=5, null satisfiedBits, valid scratch | NullPointerException      | P36, CD21           |
| TC-42 | j=5, valid satisfiedBits, null scratch | NullPointerException      | P38, CD22           |
| TC-43 | j=5, all deps met, valid scratch       | true                      | P34, P37, P39, CD25 |
| TC-44 | j=5, some deps not met, valid scratch  | false                     | P34, P37, P39, CD25 |

---

## 9. Method: `toString(int txID)`

### Black Box Analysis

#### Input Partitions
| ID   | Condition           | Partition                | Valid? |
|------|---------------------|--------------------------|--------|
| P40  | Value of txID       | txID < 1                 | false  |
| P41  | Value of txID       | 1 <= txID <= size        | true   |
| P42  | Value of txID       | txID > size              | false  |
| P43  | Dependencies state  | no dependencies          | true   |
| P44  | Dependencies state  | single dependency        | true   |
| P45  | Dependencies state  | multiple dependencies    | true   |

#### Boundary Values
| ID   | Variable-Value       |
|------|----------------------|
| B29  | txID = 0             |
| B30  | txID = 1             |
| B31  | txID = size          |
| B32  | txID = size + 1      |

#### Guesses
None identified for this method.

### White Box Analysis

#### Decisions and Conditions
| Decision ID | Decision Expression                                  | Atomic Conditions                   |
|-------------|------------------------------------------------------|-------------------------------------|
| D15         | txID < 1 &#124;&#124; txID >= deps.length            | C19: txID < 1<br>C20: txID > size   |
| D16         | deps[txID] == null &#124;&#124; deps[txID].isEmpty() | C21: entry null<br>C22: entry empty |

#### Test Obligations
| ID    | C19   | C20   | C21   | C22   | Covers                                    |
|-------|-------|-------|-------|-------|-------------------------------------------|
| CD26  | true  | -     | -     | -     | txID < 1: IndexOutOfBoundsException       |
| CD27  | false | true  | -     | -     | txID > size: IndexOutOfBoundsException    |
| CD28  | false | false | true  | -     | entry null: return "-1"                   |
| CD29  | false | false | false | true  | entry empty: return "-1"                  |
| CD30  | false | false | false | false | has dependencies: return formatted string |

### Test Cases
| ID    | Input                              | Expected                    | Satisfies              |
|-------|------------------------------------|-----------------------------|------------------------|
| TC-45 | txID = 0                           | IndexOutOfBoundsException   | P40, B29, CD26         |
| TC-46 | txID = 1, no deps                  | "-1"                        | P41, B30, P43, CD29    |
| TC-47 | txID = 10 (size), no deps          | "-1"                        | P41, B31, P43, CD29    |
| TC-48 | txID = 11 (> size)                 | IndexOutOfBoundsException   | P42, B32, CD27         |
| TC-49 | txID = 5, no deps                  | "-1"                        | P43, CD29              |
| TC-50 | txID = 5, single dep (3)           | "{3}"                       | P44, CD30              |
| TC-51 | txID = 10, deps (1,3,7)            | "{1;3;7}"                   | P45, CD30              |

---

## 11. Outcomes

### 2026-03-22 (LATEST)
CLOSED