---
main_authors: ["Nina Dang <nina2022@my.yorku.ca>"]

contributors: [""]

reviewers: [""]

---

# Design By Contract - JML

<!-- TOC -->
* [Design By Contract - JML](#design-by-contract---jml)
  * [Specification Inheritance](#specification-inheritance)
    * [Why preconditions can be weaker](#why-preconditions-can-be-weaker)
    * [Why postconditions can be stronger](#why-postconditions-can-be-stronger)
  * [JML](#jml)
    * [Class-level contract](#class-level-contract)
    * [Method-level contract](#method-level-contract)
    * [JML Conventions and Best Practices](#jml-conventions-and-best-practices)
  * [References](#references)
<!-- TOC -->

Design by Contract (DbC) defines obligations that both the client (caller/user)
and the supplier (callee/implementor) must follow to ensure correctness.

If the preconditions and invariants are satisfied before a call, then it is
expected that the postconditions and invariants will hold after the call.

- If preconditions are not satisfied (invalid arguments), the client violates the contract.
- If postconditions are not satisfied (incorrect implementation), the supplier violates the contract.

|          | Obligation                                     | Benefit                |
|----------|------------------------------------------------|------------------------|
| Client   | Satisfy preconditions                          | Receive service        |
| Supplier | Implement the service (satisfy postconditions) | Assume preconditions   |


## Specification Inheritance
- Subclass may weaken preconditions (accept more cases)
- Subclass may strengthen postconditions/invariant (promise more)

For example:
```
# ClassB is subclass of ClassA
ClassA x = new ClassB();
x.someMethod();
```
- Client only knows ClassA’s contract. 
- ClassB must follow what the client was promised by ClassA. 
- This is based on Liskov Substitution Principle (LSP) from SOLID: Without changing the program's behavior, 
objects of the parent type can be substituted with objects of the subclass type. 
- For invariants, ClassB must satisfy all invariants of ClassA, plus any additional invariants it introduces.

### Why preconditions can be weaker
```
# If preconditions can be stronger
ClassA.someMethod requires: input > 0
ClassB.someMethod requires: input > 10 
```

Client calls `ClassB.someMethod(5)`, satisfying ClassA’s contract but not ClassB's contract. This breaks LSP.

### Why postconditions can be stronger
```
# If postconditions can be weaker
ClassA.someMethod ensures: result >= 0
ClassB.someMethod ensures: result > -10
```
Client calls `ClassB.someMethod`, expecting `result >= 0` but it returns -5. Again, this breaks LSP.

---

## JML

JML (Java Modeling Language) is a specification language to define the behavior and interfaces of Java programs.
JML is influenced by Eiffel’s Design by Contract, but is more expressive and supports richer specification constructs.

JML supports:
- precondition: `requires`
- postcondition: `ensures`
- invariants: `invariant`
- quantifiers: `\forall`, `\exists`
- frame condition: `pure` (method is read-only), `assignable`
- visibility: `public`, `private`

Other important keywords include:
- exceptional postcondition: `signals`
- method’s return value: `\result` 
- value of `expr` in the pre-state (the moment the method is entered): `\old(expr)`

JML is written as annotations inside comments, which Java ignores but JML tools understand:
```text
# single-line
//@ JML goes here

# multi-line
/*@ JML goes here @*/
```

If you want to display JML specifications in Javadoc output, you can include them as preformatted text using `<pre>{@code...}</pre>`:
```text
/**
 * <pre>{@code
 * //@ requires x >= 0;
 * //@ ensures  \result >= 0;
 * }</pre>
 */
```

### Class-level contract
Class invariants describe conditions that should hold for every instance of a class 
whenever that object is visible to a client (at entry/exit of public method call)
Class invariants are placed typically right after the class declaration. Since these are comments, 
they won’t appear in the Javadoc output by default.

```text
public class BankAccount {
    /*@ invariant balance >= 0; @*/
    private int balance = 0;
}
```

### Method-level contract
For each public method (also often for protected methods in APIs meant to be extended), 
specify its contract using JML `requires`, `ensures`, and related clauses. 
JML specifications are placed before the method’s header (signature) in the source code. 

Method-level contract defines:
- What must be true before calling the method (precondition). 
- What the method guarantees after execution if it returns normally (postcondition). 
- What the method guarantees if it terminates with an exception (exceptional postcondition). 
- Which fields/state may be modified by the method (frame condition).

```text
/*@ 
  @ requires amount >= 0;
  @ ensures balance == \old(balance) + amount;
  @ assignable balance;
  @ signals (IllegalArgumentException) amount < 0 ==> \old(balance) == balance;
  @*/
public void deposit(int amount) { ... }
```

### JML Conventions and Best Practices
- 1 JML clause per line for readability
- JML specification clauses (like `requires`, `ensures`, `assignable`, `invariant`, `initially`, `constraint`, etc.) precede fields, constructors, methods declaration.
Note that JML has statement annotations (like `assert`, `assume`, `decreases`, `loop_invariant`) that appear inside method bodies. 
- Be consistent with keywords. There are some JML synonyms (like `requires` or `pre`, `ensures` or `post`, `assignable` or `modifies`, `signals` or `exsures`), so stick with one set. 
- Anything essential or what is intended about the behavior should be included in the contract/specification as clients may rely on it. 
At the same time, the specification can be underspecified/incomplete to give implementors freedom and 
room for improvement or change on non-essential details (implementation decisions).


## References

JML Tutorial: https://www.openjml.org/tutorial/

JML Home Page: https://www.cs.ucf.edu/~leavens/JML/index.shtml

Preliminary Design of JML: https://www.tofgarion.net/lectures/IN201/ressources/prelimdesign.pdf

Design by Contract with JML: https://www.cs.toronto.edu/~chechik/courses05/csc410/readings/jmldbc.pdf

JML/DbC Slides:
https://www.eecs.yorku.ca/~wangcw/teaching/lectures/2018/F/EECS3311/slides/EECS3311_F18_All_Slides.pdf

https://sites.cs.ucsb.edu/~bultan/courses/272/lectures/Contract-JML.pdf

https://www.ifi.uzh.ch/dam/jcr:ffffffff-fd5f-cdf8-ffff-fffffd2df706/07-jmldbc.pdf
