---
main_authors:
  - Sotirios Liaskos <liaskos@yorku.ca>
---
## Table of Contents
- [Program Sections](#program-sections)
- [Constructors](#Constructors)
- [Methods](#Methods)
- [Code Formatting and Commenting](#code-formatting-and-commenting)

## Program Sections

Split each class into the following sections (as appropriate). The organization of logic into methods must follow this style:

```
// ================================
// CONSTANTS
// ================================

// ================================
// FIELDS
// ================================

// (first public then private)

// ================================
// CONSTRUCTORS
// ================================

// ================================
// MAIN PUBLIC METHODS
// ================================

// Accessors to buisiness logic.

// ================================
// MAIN PRIVATE METHODS
// ================================

// In calling order: top level first.

// ================================
// HELPER METHODS
// ================================

// All private

// ================================
// DEBUG/PRINT/TOSTRING METHODS
// ================================

// Probably all public

// ================================
// SETTERS AND GETTERS
// ================================

// All public

// ================================
// VALIDATOR METHODS
// ================================

//All private

```

## Constructors
- Use simple constructors with minimum number of parameters.
	- Every parameter in a constructor must be mandatory for the creation of a valid object.
	- Remaining fields are to be set via setters.
## Methods
- Every method be accompanied by a JML-style contract that specifies the allowed preconditions guaranteed postconditions.
	- JML-style 
- The method itself checks for violated preconditions in the beginning and (if necessary) postconditions in the end, throwing RunTime error in case of violations.
- For readability use private methods `methodname_pre(...)`  
 
``` 
    /**
     * Computes the square root of a given non-negative number.
     *
     * <p><b>JML Contract:</b></p>
     * <pre>
     *   //@ requires x >= 0;
     *   //@ ensures \result >= 0;
     *   //@ ensures \abs(\result * \result - x) < 1e-10;
     * </pre>
     *
     * @param x the number to compute the square root of
     * @return the non-negative square root of {@code x}
     * @throws IllegalArgumentException if {@code x < 0} (precondition violated)
     */
    public static double sqrt(double x) {
        sqrt_pre(x); // check precondition

        double result = Math.sqrt(x);

        sqrt_post(result, x); 
        return result;
    }


...

// =============================
// VALIDATOR METHODS 
// =============================

    // Private helper method to check precondition
    private static void sqrt_pre(double x) {
        if (x < 0) {
            throw new IllegalArgumentException("Precondition violated: x must be non-negative, but got " + x);
        }
    }

    // Private helper method to check postcondition
    private static void sqrt_post(double result, double x) {
        assert result >= 0 : "Postcondition violated: result must be non-negative";
        assert Math.abs(result * result - x) < 1e-10 : "Postcondition violated: result^2 must equal x";
    }

    public static void main(String[] args) {
        System.out.println(sqrt(16)); // prints 4.0
        // System.out.println(sqrt(-4)); // would throw IllegalArgumentException
    }
}
to separate these checks from the main logic of the method.
```



## Code Formatting and Commenting

We follow the following **Java coding conventions** for consistent, readable, and maintainable code across the team. It is based on Oracle’s Java Code Conventions, Google Java Style Guide, and industry best practices.
### 1. Indentation & Spacing

- **Indentation:** 4 spaces per level; do not use tabs.
- **Line length:** Prefer 100–120 characters per line.
- **Spaces:**
  - After commas: `int x, y, z;`
  - Around operators: `a + b`
  - No space between method name and parentheses: `foo(x)`
- **Blank lines:** Use a single blank line between methods or logical blocks for readability.
### 2. Braces `{}`

- **Class, method, control statements opening braces** on the same line:
```java
public class MyClass {
   public void myMethod() {
	 if (condition) {
        // code block
	 } else {
        // else block
	 }
   }
}
```

- **Closing braces** align with the start of the statement or declaration.
### 3. Naming Conventions

| Element            | Convention                   |
| ------------------ | ---------------------------- |
| Classes/Interfaces | `PascalCase` (`MyClass`)     |
| Methods/Variables  | `camelCase` (`computeSum`)   |
| Constants          | `ALL_CAPS_WITH_UNDERSCORES`  |
| Packages           | all lowercase(`com.example`) |
- Avoid underscores unless it enhances readability for longer identifiers.

### 4. Comments and JavaDoc

#### Class-level commenting 

- Class-level JavaDoc example:

```
/**
* Represents the blockchain structure for a Bitcoin simulation.
* <p>
* The {@linkplain Blockchain} maintains the main chain of blocks,
* a list of orphan blocks, and tips (latest blocks in each chain).
* Blocks can be added either as validated new blocks or received via propagation.
* Transactions are stored within {@linkplain Block} objects.
* </p>
*
* <p>
* This class implements {@linkplain IStructure} to integrate with the simulation engine.
* </p>

* @author [Name Surname] for the Conceptual Modeling Group @ York University
* @see Block
* @see BitcoinNode
* @since 0.1
*/
```

#### Method-level commenting 
-  Always link to classes and methods they first time mentioned.
	- Prefer {@linkplain xx} over {@link xxx}
- Use {@code var} when referring to variables, parameters, values etc.
- Ensure that the following are included:
	- Description
	- Contract (in `<pre>`)
	- Parameters (`@param`)
	- Return values (`@return`)
	- Exceptions (`@throws`)
	- When needed: `@see` `@deprecated`

Example:

```
/**
 * Computes the square root of a given non-negative number.
 *
 * <p><b>JML Contract:</b></p>
 * <pre>
 *   //@ requires x >= 0;
 *   //@ ensures \result >= 0;
 *   //@ ensures \abs(\result * \result - x) < 1e-10;
 * </pre>
 *
 * @param x the number to compute the square root of
 * @return the non-negative square root of {@code x}
 * @throws IllegalArgumentException if {@code x < 0} (precondition violated)
 */
	public static double sqrt(double x) {
	   ...
```

- Do not refer to versions and version numbers in code, except at the top of the class. To be used for a rough estimate of the age of the class.