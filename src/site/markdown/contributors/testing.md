# Testing Conventions
- JUnit 5 shall be used for testing
- Follow maven recommendations for placing JUnit classes in codebase i.e., under `src/test/`
- Input files should be placed under `src/test/resources/inputs/` following the directory structure of the tests and source.
- Access inputs using something like: 
 
  ```
  Path path = Paths.get(
    Objects.requireNonNull(
        getClass().getResource("/inputs/xxx.csv")
    ).toURI()
);
# Testing Strategy

We follow the testing strategy due to G.J. Myers et al. 

1. Study the JML contract of the unit. If none exits, create a Jira issue and bring it up with the team.
2. Perform boundary value analysis. Yields a set of test conditions marked with `B[X]` where `X` is the id of the boundary value.
3. Identify the valid and invalid equivalence classes for the input and output, mark them with `P[X]`
4. Use error-guessing to additional conditions (`G[X]`)
5. Identify the conditions in the unit. Identify combinations of decisions and conditions and mark them as test obligations `CD[X]`
6. Gather all above conditions (`B[X], P[X], G[X], CD[X]`) and devise concrete test cases to be implemented. Mark them `TC-[X]`.
# Test Design Documentation

- Test designs shall be documented in Markdown files, stored under `src/test/resources/test-design/`, and reviewed prior to or alongside the corresponding JUnit test implementations.
- JUnit files under `src/test/` reflect the directory structure of `src/test/resources/test-design/`. Files share the same name: `[ClassName]Test.java` and `[ClassName]Test.md`, where `[ClassName]` the class being tested.
- JUnit files at the top contain a reference to the corresponding md file with the design.
- JUnit tests, refer to the IDs of the tests in the design `TC-1, TC-2, ...`
- The following is the template for a test MD file. Key:
	- `P[X]`: partition
	- `B[X]`: boundary value
	- `G[X]`: guess value
	- `D[X]`: decision (formula)
	- `C[X]`: condition (atom in formula)
	- `CD[X]`: condition/decision combo
	- `TC-[X]`: final test case

```
# Test Design — ClassName

## 1. Unit under test
- Class: `ClassName`
- Method: `doSomething(int x)`

### Black Box Analysis

#### Input partitions
| ID | Condition  | Partition | Valid? |  
|--- |------------|-----------|--------|
| P1 | Value of x | x = 0     | true   |
| P2 | Value of x | x < 0     | false  |
...

##### Boundary values
| ID | Variable-Value     |
|--- |--------------------|
| B1 | x = 0              | 
| B2 | x = Integer.MAX_INT| 
...

##### Guesses
| ID | Variable-Value     |
|--- |--------------------|
| G1 | x = 10             | 
| G2 | x = nodes.size()   | 
...


### White Box Analysis

#### Decisions and Conditions

| Decision ID | Decision Expression | Atomic Conditions |
|-----------|---------------------|-------------------|
| D1 | amount > limit && (isVip || override) | C1: amount > limit<br>C2: isVip<br>C3: override |

#### Test obligations

| Test Case | C1 | C2 | C3 | D1 |
|---------|----|----|----|----|
| CD1 | T | T | F | T |
| CD2 | F | T | F | F |
| CD3 | T | F | F | F |
| CD4 | T | F | T | T |


### Test cases
| ID | Input | Expected | Satisfies |
|----|------|----------|-----------|
| TC-1 | x=0 | returns 0 | P1, B1 |
| TC-2 | x=10 | exception | P3 |
| TC-3 | ... | exception | CD1 |
| TC-4 | ...  | exception | CD2 |
| TC-5 | ...  | returns 5 | G1 |

### Outcomes

Log here any failed or pending tests, and updates in the test cases (due to e.g. refactoring, group recommendations). For failed tests, add a JIRA task and refer to it from the list.

If all tests are implented and pass just write: CLOSED under the latest entry.

### 2025-12-13 (LATEST)
CLOSED


### 2025-11-29
[Commentary]

#### Pending Tests:
TC-4, TC-7

#### Failed Tests:
| ID   | Expected | Observed | Jira Issue |
|------|----------|----------|------------|
| TC-1 | ...      | ....     | CE-215     |


### 2025-11-20
[Commentary]

#### Pending Tests:
TC-4, TC-7.

#### Failed Tests:
| ID   | Expected | Observed |
|------|----------|----------|
| TC-1 | ...      | ....     |


```
## Generating JaCoCo report
```
mvn verify
```

Check that your class achieves 100% coverage.