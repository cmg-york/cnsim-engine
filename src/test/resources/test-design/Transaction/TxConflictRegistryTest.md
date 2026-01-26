# Test Design — TxConflictRegistry


## 1. TxConflictRegistry(long size) --> Constructor

### Black Box Analysis

#### Input partitions
| ID | Condition | Partition | Valid? |
|----|-----------|-----------|--------|
| P1 | size value | size = 1 | Valid |
| P2 | size value | 1 < size <= Integer.MAX_VALUE | Valid |
| P3 | size value | size < 1 | Invalid |
| P4 | size value | size > Integer.MAX_VALUE | Invalid |

#### Boundary values
| ID | Variable-Value |
|----|----------------|
| B1 | size = 1 (minimum valid) |
| B2 | size = 2 (just above minimum) |
| B3 | size = Integer.MAX_VALUE (maximum valid) |
| B4 | size = 0 (just below valid) |
| B5 | size = -1 (negative value) |
| B6 | size = Integer.MAX_VALUE + 1L (just above valid) |

#### Guesses
| ID | Variable-Value |
|----|----------------|
| G1 | size = 100 (typical valid value) |
| G2 | size = Integer.MAX_VALUE - 1 (near upper bound) |
| G3 | All IDs initialized to -2 after construction |

### White Box Analysis

#### Decisions and Conditions

| Decision ID | Decision Expression | Atomic Conditions |
|-------------|---------------------|-------------------|
| D1 | size < 1 | C1: size < 1 |
| D2 | size > Integer.MAX_VALUE | C2: size > Integer.MAX_VALUE |

#### Test obligations

| Test Case | C1 | C2 | D1 | D2 |
|-----------|----|----|----|----|
| CD1 | T | - | T | - |
| CD2 | F | T | F | T |
| CD3 | F | F | F | F |

### Test cases
| ID | Method | Input | Expected | Satisfies |
|----|--------|-------|----------|-----------|
| TC-C1 | Constructor | size=1 | Registry created, all IDs -2 | B1, P1, CD3 |
| TC-C2 | Constructor | size=Integer.MAX_VALUE | Registry created | B3, P2, CD3 |
| TC-C3 | Constructor | size=0 | IllegalArgumentException | B4, P3, CD1 |
| TC-C4 | Constructor | size=-1 | IllegalArgumentException | B5, P3, CD1 |
| TC-C5 | Constructor | size=Integer.MAX_VALUE+1L | IllegalArgumentException | B6, P4, CD2 |



## 2. setMatch(int a, int b)

### Black Box Analysis

#### Input partitions
| ID | Condition | Partition | Valid? |
|----|-----------|-----------|--------|
| P1 | a value | a = 1 | true |
| P2 | a value | a > 1 | true |
| P3 | a value | a <= 0 | false |
| P4 | a value | a > Integer.MAX_VALUE | false |
| P5 | a value | a = b | false |
| P6 | b value | b = 1 | true |
| P7 | b value | b > 1 | true |
| P8 | b value | b <= 0 | false |
| P9 | b value | b > Integer.MAX_VALUE | false |
| P9 | b value | b = a | false |
...

##### Boundary values
| ID | Variable-Value |
|----|----------------|
| B1 | a = 1 (minimum valid) |
| B2 | a = Integer.MAX_VALUE (maximum valid) |
| B3 | a = 0 (just below valid) |
| B4 | a = Integer.MAX_VALUE + 1 (just above valid) |
| B5 | b = 1 (minimum valid) |
| B6 | b = Integer.MAX_VALUE (maximum valid) |
| B7 | b = 0 (just below valid) |
| B8 | b = Integer.MAX_VALUE + 1 (just above valid) |

##### Guesses
| ID | Variable-Value |
|----|----------------|
| G1 | Matching an ID with itself |
| G2 | Setting match twice on same ID |
| G3 | Getting match of uninitialized ID |

...


### White Box Analysis

#### Decisions and Conditions

| Decision ID | Decision Expression | Atomic Conditions |
|-------------|---------------------|-------------------|
| D1 | id < 1 || id > size | C1: id < 1<br>C2: id > size |
| D2 | a == b | C3: a == b |

#### Test obligations 
note: Dn = F: validation passed
      Dn = T: validation failed 

| Test Case | C1 (for a) | C2 (for a) | C1 (for b) | C2 (for b) | C3 (a==b) | D1 | D2 |
|-----------|------------|------------|------------|------------|-----------|----|----|
| CD1 | F | F | F | F | T | F | T |
| CD2 | F | F | F | F | F | F | F |
| CD3 | T | - | - | - | - | T | - |
| CD4 | F | T | - | - | - | T | - |
| CD5 | - | - | T | - | - | T | - |
| CD6 | - | - | F | T | - | T | - |
    
    C3 for CD3-6 is - since the (a==b) check isn't reached (validation fails before that)


### Test cases
| ID | Method | Input | Expected | Satisfies |
|----|--------|-------|----------|-----------|
| TC-SM1 | setMatch | a=1, b=1 | IllegalArgumentException | P5, P10, G1, CD1 |
| TC-SM2 | setMatch | a=1, b=2 (size=10) | Match created: getMatch(1)=2, getMatch(2)=1 | B1, P1, P6, CD2 |
| TC-SM3 | setMatch | a=size, b=size-1 | Match created: getMatch(size)=size-1 | B2, P2, P7, CD2 |
| TC-SM4 | setMatch | a=1, b=size | Match created at boundaries | B1, B2, P1, P7, CD2 |
| TC-SM5 | setMatch | a=0, b=2 | IllegalArgumentException | B3, P3, CD3 |
| TC-SM6 | setMatch | a=size+1, b=2 | IllegalArgumentException | B4, P4, CD4 |
| TC-SM7 | setMatch | a=2, b=0 | IllegalArgumentException | B7, P8, CD5 |
| TC-SM8 | setMatch | a=2, b=size+1 | IllegalArgumentException | B8, P9, CD6 |
| TC-SM9 | setMatch | setMatch(1,2) then setMatch(1,3) | Match updated: getMatch(1)=3, getMatch(2)=-1, getMatch(3)=1 | G2 |
| TC-SM10 | setMatch | setMatch(1,2) then setMatch(3,2) | Match updated: getMatch(2)=3, getMatch(1)=-1, getMatch(3)=2 | G2 |



## 3. noMatch()

### Black Box Analysis

#### Input partitions
| ID | Condition | Partition | Valid? |
|----|-----------|-----------|--------|
| P1 | id range | 1 <= id <= size  | true |
| P2 | id range | id < 1 | false |
| P3 | id range  | id > size | false |
| P4 | match state | id has a match | true
| P5 | match state | id doesn't match | true
| P6 | match state | id isn't initialized | true


...

##### Boundary values
| ID | Variable-Value |
|----|----------------|
| B1 | id = 1 (minimum valid) |
| B2 | id = 2 (just above minimum) |
| B3 | id = size (maximum valid) |
| B4 | id = 0 (just below valid) |
| B5 | id = -1 (invalid) |
| B6 | id = size + 1 (just above valid) |
| B7 | id = size + 3 (above valid) |

...

##### Guesses
| ID | Variable-Value |
|----|----------------|
| G1 | calling noMatch() on unmatched ID |
| G2 | calling the method twice in a row |


...


### White Box Analysis

#### Decisions and Conditions

| Decision ID | Decision Expression | Atomic Conditions |
|-------------|---------------------|-------------------|
| D1 | id < 1 || id > size | C1: id < 1<br>C2: id > size |
| D2 | partner > 0 | C3: partner > 0

#### Test obligations
| Test Case | C1 | C2 | C3 | D1 | D2
|---------|----|----|----|----|----|
| CD1 | T | - | - | T | - |
| CD2 | F | T | - | T | - |
| CD3 | F | F | T | F | T |
| CD4 | F | F | F | F | F |

### Test cases
| ID | Method | Input | Expected | Satisfies |
|----|--------|-------|----------|-----------|

invalid id ranges:
| TC-NM1 | noMatch | id=0 | IllegalArgumentException | B4, P2, CD1 |
| TC-NM2 | noMatch | id=size+1 | IllegalArgumentException | B6, P3, CD2 |

id with a match - verifies both ids and partner gets cleared: 
| TC-NM3 | noMatch | setMatch(1,2), then noMatch(1) | getMatch(1)=-1, getMatch(2)=-1 (partner cleared) | B1, P1, P4, CD3 |
| TC-NM4 | noMatch | setMatch(3,size), then noMatch(size) | getMatch(3)=-1, getMatch(size)=-1 | B3, P1, P4, CD3 |

already neutralized id (stays -1):
| TC-NM5 | noMatch | neutralize(), then noMatch(1) | getMatch(1)=-1 (stays -1) | B1, P1, P5, CD4, G1 |

uninitialized id (change from -2 to -1):
| TC-NM6 | noMatch | New registry, noMatch(2) | getMatch(2)=-1 (was -2, now -1) | B2, P1, P6, CD4 |

calling twice in a row:
| TC-NM7 | noMatch | setMatch(1,2), noMatch(1), noMatch(1) | Second call: getMatch(1)=-1, no error | P1, P5, CD4, G2 |

negative ID test:
| TC-NM8 | noMatch | id=-1 | IllegalArgumentException | B5, P2, CD1 |

upper boundary valid case:
| TC-NM9 | noMatch | id=size | getMatch(size)=-1 | B3, P1, CD4 |


## 4. neutralize()

### Black Box Analysis

#### Input partitions
No direct inputs, but state-based testing:

| ID | Condition | Partition | Valid? |
|----|-----------|-----------|--------|
| P1 | Registry state | All IDs uninitialized (-2) | Valid |
| P2 | Registry state | Some IDs matched (>0) | Valid |
| P3 | Registry state | All IDs already neutralized (-1) | Valid |
| P4 | Registry state | Mixed states | Valid |

#### Boundary values
No boundary values (no input parameters)

#### Guesses
| ID | Variable-Value |
|----|----------------|
| G1 | Call neutralize() on newly created registry |
| G2 | Call neutralize() twice in a row |
| G3 | Call after setMatch() operations |
| G4 | Verify all IDs set to -1 after neutralize |

### White Box Analysis

#### Decisions and Conditions
No decisions or conditions (simple Arrays.fill call)

#### Test obligations
No complex decisions to test

### Test cases
| ID | Method | Input | Expected | Satisfies |
|----|--------|-------|----------|-----------|
| TC-N1 | neutralize | Uninitialized registry | All IDs = -1 | P1, G1 |
| TC-N2 | neutralize | After setMatch(1,2) | All IDs = -1 | P2, G3 |
| TC-N3 | neutralize | Already neutralized | All IDs = -1 | P3, G2 |
| TC-N4 | neutralize | Mixed state registry | All IDs = -1 | P4 |



## 5. Simple Methods (getMatch, uninitialized)

### 5a. getMatch(int id)

#### Black Box Analysis

##### Input partitions
| ID | Condition | Partition | Valid? |
|----|-----------|-----------|--------|
| P1 | id range | 1 <= id <= size | Valid |
| P2 | id range | id < 1 | Invalid |
| P3 | id range | id > size | Invalid |
| P4 | match state | id uninitialized (-2) | Valid |
| P5 | match state | id unmatched (-1) | Valid |
| P6 | match state | id matched (>0) | Valid |

##### Boundary values
| ID | Variable-Value |
|----|----------------|
| B1 | id = 1 (minimum valid) |
| B2 | id = size (maximum valid) |
| B3 | id = 0 (just below valid) |
| B4 | id = size+1 (just above valid) |

##### Guesses
| ID | Variable-Value |
|----|----------------|
| G1 | Get match of uninitialized ID (returns -2) |
| G2 | Get match of matched ID (returns partner) |
| G3 | Get match of neutralized ID (returns -1) |

#### White Box Analysis

##### Decisions and Conditions
| Decision ID | Decision Expression | Atomic Conditions |
|-------------|---------------------|-------------------|
| D1 | id < 1 || id > size (in validateId) | C1: id < 1<br>C2: id > size |

##### Test obligations
| Test Case | C1 | C2 | D1 |
|-----------|----|----|-------|
| CD1 | T | - | T |
| CD2 | F | T | T |
| CD3 | F | F | F |

#### Test cases
| ID | Method | Input | Expected | Satisfies |
|----|--------|-------|----------|-----------|
| TC-GM1 | getMatch | id=1, uninitialized | Returns -2 | B1, P1, P4, G1, CD3 |
| TC-GM2 | getMatch | id=size, matched | Returns partner ID | B2, P1, P6, G2, CD3 |
| TC-GM3 | getMatch | id=1, neutralized | Returns -1 | B1, P1, P5, G3, CD3 |
| TC-GM4 | getMatch | id=0 | IllegalArgumentException | B3, P2, CD1 |
| TC-GM5 | getMatch | id=size+1 | IllegalArgumentException | B4, P3, CD2 |

---

### 5b. uninitialized(int id)

#### Black Box Analysis

##### Input partitions
| ID | Condition | Partition | Valid? |
|----|-----------|-----------|--------|
| P1 | id range | 1 <= id <= size (valid access) | Valid |
| P2 | id range | id out of range | Invalid |
| P3 | match state | match[id] == -2 | Returns true |
| P4 | match state | match[id] != -2 | Returns false |

##### Boundary values
| ID | Variable-Value |
|----|----------------|
| B1 | id = 1 (minimum) |
| B2 | id = size (maximum) |
| B3 | id = 0 (invalid) |
| B4 | id = size+1 (invalid) |

##### Guesses
| ID | Variable-Value |
|----|----------------|
| G1 | Check newly created registry (should be true) |
| G2 | Check after setMatch (should be false) |
| G3 | Check after neutralize (should be false) |

#### White Box Analysis

##### Decisions and Conditions
| Decision ID | Decision Expression | Atomic Conditions |
|-------------|---------------------|-------------------|
| D1 | match[id] == -2 | C1: match[id] == -2 |

Note: This method does NOT call validateId(), so invalid IDs will cause ArrayIndexOutOfBoundsException

##### Test obligations
| Test Case | C1 | D1 |
|-----------|----|-------|
| CD1 | T | T |
| CD2 | F | F |

#### Test cases
| ID | Method | Input | Expected | Satisfies |
|----|--------|-------|----------|-----------|
| TC-UI1 | uninitialized | id=1, new registry | Returns true | B1, P1, P3, G1, CD1 |
| TC-UI2 | uninitialized | id=size, after setMatch | Returns false | B2, P1, P4, G2, CD2 |
| TC-UI3 | uninitialized | id=1, after neutralize | Returns false | B1, P1, P4, G3, CD2 |
| TC-UI4 | uninitialized | id=0 | ArrayIndexOutOfBoundsException | B3, P2 |
| TC-UI5 | uninitialized | id=size+1 | ArrayIndexOutOfBoundsException | B4, P2 |


## Outcomes

Log here any failed or pending tests, and updates in the test cases (due to e.g. refactoring, group recommendations). For failed tests, add a JIRA task and refer to it from the list.

If all tests are implented and pass just write: CLOSED under the latest entry.


### 2025-11-20 (LATEST)
Initial test implementation in progress.

#### Pending Tests:
All tests pending initial implementation.

#### Failed Tests:
none yet