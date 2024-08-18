# kwed

`kwed` (/kwɛd/) is a minimal [type-theoretic](https://en.wikipedia.org/wiki/Type_theory) proof assistant based on the [Calculus of Inductive Constructions](https://ncatlab.org/nlab/show/calculus+of+constructions).

`kwed` does not use tactics; all proofs are pure expressions not unlike in Agda.

# examples

## natural number addition

the following `kwed` code defines the natural numbers (`ℕ`) and addition of natural numbers (`ℕ.+`).

```
inductive ℕ: Type
{
  0: ℕ,
  suc: ℕ → ℕ,
}

def ℕ.+(x: ℕ, y: ℕ): ℕ
{
  ℕ.elim ([_: ℕ] ℕ)               // define by induction on `ℕ`
    x                             // in the case that `y` is `0`, return `x`
    ([y': ℕ, x+y': ℕ] ℕ.suc x+y') // in the case that `y` is `suc y'`, return `suc (x + y')` (recurse)
    y
}
```
