In this document, we might write down some things we learn about the basics of using Lean4. 

There are lots of resources, and it's simple enough to link to resources like 
  - <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/StrongLaw.html>
  - <https://leanprover-community.github.io/learn.html>
  - <https://github.com/leanprover-community/tutorials4/tree/master>

But it would be nice to include some examples that may be relevant to our use cases. 

For example, to include a simple proof below. 

```lean
def main : IO Unit :=
  IO.println "Hello, world!"


#eval main

#eval Lean.versionString
```

So we might extend this to include some more examples ... Maybe how to do some simple 
calculus, symbolic math, basic arithmetic... 

I think the below is code for instantiating an axiom that says `0 * anything = 0`
and $a * (b + 1) = a * b + a$. 

```lean
import MyNat.Definition
namespace MyNat
open MyNat

axiom mul_zero (a : MyNat) : a * 0 = 0

axiom mul_succ (a b : MyNat) : a * (succ b) = a * b + a
```
