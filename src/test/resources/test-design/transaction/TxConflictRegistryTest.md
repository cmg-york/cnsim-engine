# Test Design — TxConflictRegistry

## 1. TxConflictRegistry.TxConflictRegistry(long size)

### Black Box Analysis

#### Input partitions
| ID | Condition  | Partition | Valid? |  
|--- |------------|-----------|--------|
| P1 | Value of size | 1 < size < Integer.MAX_VALUE | true |
| P2 | Value of size | size < 1   | false  |
| P3 | Value of size | size > Integer.MAX_VALUE   | false  |

##### Boundary values
| ID | Variable-Value     |
|--- |--------------------|
| B1 | size = 1              | 
| B2 | size = Integer.MAX_VALUE | 
| B3 | size = Integer.MAX_VALUE + 1 | 
| B4 | size = 0 |

##### Guesses
| ID | Variable-Value     |
|--- |--------------------|
| G1 | size = 10             | 
| G2 | size = Integer.MAX_VALUE - 1  | 


### White Box Analysis

#### Decisions and Conditions

| Decision ID | Decision Expression | Atomic Conditions |
|-----------|---------------------|-------------------|
| D1 | size < 1 | C1: size < 1 |
| D2 | size > Integer.MAX_VALUE | C2: size > Integer.MAX_VALUE |

#### Test obligations

| Test Case | C1 | C2 | D1 | D2 |
|-----------|----|----|----|----|
| CD1 | T | F | T | F |
| CD2 | F | T | F | T |
| CD3 | F | F | F | F |


### Test cases
| ID | Input | Expected | Satisfies |
|----|------|----------|-----------|
| TC-1 | size=1 | succeeds | P1, B1 |
| TC-2 | size=Integer.MAX_VALUE | succeeds | P1, B2 |
| TC-3 | size=Integer.MAX_VALUE - 1 | succeeds | G2 |
| TC-4 | size=Integer.MAX_VALUE + 1 | exception | P3, B3, CD2 |
| TC-5 | size=0 | exception | P2, B4, CD1 |
| TC-6 | size=10 | succeeds | P1, G1, CD3 |

## 2. TxConflictRegistry.neutralize()

### Black Box Analysis

#### Input partitions
N/A no inputs

##### Boundary values
N/A

##### Guesses
| ID | Variable-Value                                |
|--- |-----------------------------------------------|
| G1 | match[i] = -2 for all 1 <= i <= 10            | 
| G2 | match[i] = -1 for all 1 <= i <= 100           |
| G3 | match[i] = 5 for all 1 <= i <= 10, except i=5 |

### White Box Analysis

#### Decisions and Conditions
N/A no conditionals

#### Test obligations
N/A no decisions or conditions

### Test cases
| ID | Input                                          | Expected | Satisfies |
|----|------------------------------------------------|----------|-----------|
| TC-1 | match[i] = -2 for all 1 <= i <= 10             | succeeds | G1 |
| TC-2 | match[i] = -1 for all 1 <= i <= 100            | succeeds | G2 |
| TC-3 | match[i] = 5 for all 1 <= i <= 10, except i =5 | succeeds | G3 |


## 3. TxConflictRegistry.noMatch(int id)

### Black Box Analysis

#### Input partitions
| ID | Condition  | Partition | Valid? |  
|--- |------------|-----------|--------|
| P1 | Value of id | 1 <= id <= size | true |
| P2 | Value of id | id < 1   | false  |
| P3 | Value of id | id > size | false  |

##### Boundary values
| ID | Variable-Value     |
|--- |--------------------|
| B1 | id = 1             | 
| B2 | id = size          | 
| B3 | id = 0             | 
| B4 | id = size + 1      |

##### Guesses
| ID | Variable-Value     |
|--- |--------------------|
| G1 | id = 9, size = 10  | 
| G2 | id = 5, size = 10  | 


### White Box Analysis

#### Decisions and Conditions

| Decision ID | Decision Expression | Atomic Conditions |
|-----------|---------------------|-------------------|
| D1 | id < 1 \|\| id > size | C1: id < 1 <br> C2: id > size |
| D2 | partner > 0 | C3: partner > 0 |

**partner = match[id]

#### Test obligations

| Test Case | C1 | C2 | C3 | D1 | D2 |
|-----------|----|----|----|----|----|
| CD1 | T | F | - | T | - |
| CD2 | F | T | - | T | - |
| CD3 | F | F | - | F | - |
| CD4 | - | - | T | - | T |
| CD5 | - | - | F | - | F |


### Test cases
| ID | Input | Expected | Satisfies |
|----|------|----------|-----------|
| TC-1 | id=1, size=2 | succeeds | P1, B1, CD3 |
| TC-2 | id=0, size=2 | exception | P2, B3, CD1 |
| TC-3 | id=10, size=9 | exception | P3, B4, CD2 |
| TC-4 | id=10, size=10 | succeeds | B2 |
| TC-5 | id=9, size=10 | succeeds | G1 |
| TC-6 | id=5, size=10 | succeeds | G2 |
| TC-7 | id=5, partner > 0 | match[partner] = -1 | CD4 |
| TC-8 | id=5, partner < 0 | match[partner] remains | CD5 |

## 4. TxConflictRegistry.uninitialized(int id)

### Black Box Analysis

#### Input partitions
| ID | Condition  | Partition | Valid? |  
|--- |------------|-----------|--------|
| P1 | Value of id | 1 <= id <= size | true |
| P2 | Value of id | id < 1   | false  |
| P3 | Value of id | id > size | false  |

##### Boundary values
| ID | Variable-Value     |
|--- |--------------------|
| B1 | id = 1             | 
| B2 | id = size          | 
| B3 | id = 0             | 
| B4 | id = size + 1      |

##### Guesses
| ID | Variable-Value     |
|--- |--------------------|
| G1 | id = 9, size = 10  | 
| G2 | id = 5, size = 10  | 

### White Box Analysis

#### Decisions and Conditions

| Decision ID | Decision Expression | Atomic Conditions |
|-----------|---------------------|-------------------|
| D1 | id < 1 \|\| id > size | C1: id < 1 <br> C2: id > size |
| D2 | match[id] == -2 | C3: match[id] == -2 |

#### Test obligations

| Test Case | C1 | C2 | C3 | D1 | D2 |
|-----------|----|----|----|----|---|
| CD1 | T | F | -  | T | - |
| CD2 | F | T | -  | T | - |
| CD3 | F | F | -  | F | - |
| CD4 | - | - | T  | - | T |
| CD5 | - | - | F  | - | F |


### Test cases
| ID   | Input          | Expected | Satisfies        |
|------|----------------|----------|------------------|
| TC-1 | id=1, size=2   | succeeds | P1, B1, CD3, CD4 |
| TC-2 | id=0, size=2   | exception | P2, B3, CD1      |
| TC-3 | id=10, size=9  | exception | P3, B4, CD2      |
| TC-4 | id=10, size=10 | succeeds | B2               |
| TC-5 | id=9, size=10  | succeeds | G1               |
| TC-6 | id=5, size=10  | succeeds | G2               |
| TC-7 | match[id]!=-2  | returns false | CD5              |

## 5. TxConflictRegistry.getMatch(int id)

### Black Box Analysis

#### Input partitions
| ID | Condition  | Partition | Valid? |  
|--- |------------|-----------|--------|
| P1 | Value of id | 1 <= id <= size | true |
| P2 | Value of id | id < 1   | false  |
| P3 | Value of id | id > size | false  |

##### Boundary values
| ID | Variable-Value     |
|--- |--------------------|
| B1 | id = 1             | 
| B2 | id = size          | 
| B3 | id = 0             | 
| B4 | id = size + 1      |

##### Guesses
| ID | Variable-Value     |
|--- |--------------------|
| G1 | id = 9, size = 10  | 
| G2 | id = 5, size = 10  | 

### White Box Analysis

#### Decisions and Conditions

| Decision ID | Decision Expression | Atomic Conditions |
|-----------|---------------------|-------------------|
| D1 | id < 1 \|\| id > size | C1: id < 1 <br> C2: id > size |

#### Test obligations

| Test Case | C1 | C2 | D1 | D2 |
|-----------|----|----|----|----|
| CD1 | T | F | - | T | - |
| CD2 | F | T | - | T | - |
| CD3 | F | F | - | F | - |

### Test cases
| ID | Input | Expected | Satisfies |
|----|------|----------|-----------|
| TC-1 | id=1, size=2 | succeeds; returns match[id] | P1, B1, CD3 |
| TC-2 | id=0, size=2 | exception | P2, B3, CD1 |
| TC-3 | id=10, size=9 | exception | P3, B4, CD2 |
| TC-4 | id=10, size=10 | succeeds; returns match[id] | B2 |
| TC-5 | id=9, size=10 | succeeds; returns match[id] | G1 |
| TC-6 | id=5, size=10 | succeeds; returns match[id] | G2 |

## 6. TxConflictRegistry.setMatch(int a, int b)

### Black Box Analysis

#### Input partitions
| ID | Condition  | Partition | Valid? |  
|--- |------------|-----------|--------|
| P1 | Value of a | 1 <= a <= size | true |
| P2 | Value of a | a < 1   | false  |
| P3 | Value of a | a > size | false  |
| P4 | Value of b | 1 <= b <= size | true |
| P5 | Value of b | b < 1   | false  |
| P6 | Value of b | b > size | false  |
| P7 | Value of a | a == b | false  |

##### Boundary values
| ID | Variable-Value     |
|--- |--------------------|
| B1 | a = 1             | 
| B2 | a = size          | 
| B3 | a = 0             | 
| B4 | a = size + 1      |
| B5 | b = 1             | 
| B6 | b = size          | 
| B7 | b = 0             | 
| B8 | b = size + 1      |

##### Guesses
| ID | Variable-Value     |
|--- |--------------------|
| G1 | a = 9, b = 10, size = 10  | 
| G2 | a = 1, b = 5, size = 10  | 

### White Box Analysis

#### Decisions and Conditions

| Decision ID | Decision Expression | Atomic Conditions |
|-----------|---------------------|-------------------|
| D1 | a < 1 \|\| a > size | C1: a < 1 <br> C2: a > size |
| D2 | b < 1 \|\| b > size | C3: b < 1 <br> C4: b > size |
| D3 | a == b | C5: a == b |

#### Test obligations

| Test Case | C1 | C2 | C3 | C4 | C5 | D1 | D2 | D3 |
|-----------|----|----|----|----|----|----|----|----|
| CD1 | F | F | F | F | F | F | F | F |
| CD2 | F | F | F | F | T | F | F | T |
| CD3 | T | F | - | - | - | T | - | - |
| CD4 | F | T | - | - | - | T | - | - |
| CD5 | F | F | - | - | - | F | - | - |
| CD6 | - | - | T | F | - | - | T | - |
| CD7 | - | - | F | T | - | - | T | - |
| CD8 | - | - | F | F | - | - | F | - |


### Test cases
| ID   | Input | Expected | Satisfies |
|------|------|----------|-----------|
| TC-1 | a=1, b=2, size=2 | succeeds | P1, P4, B1, B6, CD1, CD5, CD8 |
| TC-2 | a=0, b=1, size=2 | exception | P2, B3, B5, CD3 |
| TC-3 | a=10, b=2, size=9 | exception | P3, B4, CD4 |
| TC-4 | a=2, b=1, size=2 | succeeds | B2, B5 |
| TC-5 | a=1, b=0, size=2 | exception | P5, B7, CD6 |
| TC-6 | a=2, b=10, size=9 | exception | P6, B8, CD7 |
| TC-7 | a=2, b=2, size=5 | exception | P7, CD2 |
| TC-8 | a = 9, b = 10, size = 10 | succeeds | G1 |
| TC-9 | a = 1, b = 5, size = 10 | succeeds | G2 |
