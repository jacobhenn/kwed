# kwed

`kwed` (/kwɛd/) is a minimal [type-theoretic](https://en.wikipedia.org/wiki/Type_theory) proof assistant based on the [Calculus of Inductive Constructions](https://ncatlab.org/nlab/show/calculus+of+constructions).

`kwed` does not use tactics; all proofs are pure expressions not unlike in Agda.

`kwed` strives to avoid compiler builtins in favor of user-defined functionality. the set of built-in types is as minimal as possible, and you can easily see how anything in the standard library is defined by looking at its source code.

some standout features of `kwed` include:
- painless module and import system
    - Rust-like import trees: `use { Super.{Map, False.Not} }`
- optionally provide trailing named arguments: `func a b (c: d, e: f)`
- non-headache-inducing anonymous function syntax, featuring terse parameter repitition: `[x y: A, z: B] f x y z`
- structs (`struct Pair(A B: Type) { first: A, second: B }`) that desugar to inductive definitions with auto-generated field accessors
- parametric induction:
  ```
  inductive IsEven: ℕ → Type { 
      0-is-even: IsEven 0, 
      plus-2-is-even: (n: ℕ, IsEven n) → IsEven (suc (suc n)),
  }
  ```

# examples

## natural number addition

the following `kwed` code defines the natural numbers (`ℕ`) and addition of natural numbers (`ℕ.+`).

```
inductive ℕ: Type {
    0: ℕ,
    suc: ℕ → ℕ,
}

def +(x y: ℕ): ℕ {
    match y to [-] ℕ {            // define by induction on y
        0 => x,                   // in the case that y=0, return x
        suc y' => ℕ.suc (rec y'), // in the case that y=y'+1, return (x+y')+1 recursively
    }
}
```

## standard library

for more advanced examples, feel free to browse [the standard library](https://github.com/jacobhenn/kwed-lib).
