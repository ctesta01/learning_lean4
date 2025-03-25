
# Goal:
- finish section 3: it is structred in a way that, we first summarize take away and then support each take away by examples.

- try monty hall problem

## Section 3.1 (Implication and Universal Quantifier)
Take 1:  all the assumptions together imply the conclusion.
```lean
#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε
```
yup, lean treats implication and hypothesis in similar ways.

Take 2: Use curly brackets to make quantified variables implicit when they can be inferred from subsequent hypotheses.-> we can just apply a lemma to the hypotheses without mentioning the objects.

```lean
theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry
theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

#check my_lemma a b δ h₀ h₁ ha hb
#check my_lemma2 h₀ h₁ ha hb
```


#### Take 3
- Universal quantifiers are often hidden in definitions - Even though FnUb f a just looks like a name, it's actually hiding a ∀ x behind the scenes.

```lean
example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x -- the goal shows after this line of intro x
  dsimp -- this is a goal simplifier
  apply add_le_add
  apply hfa
  apply hgb
```
### Take 4
- When argue a theorem (fnUb_add) at level of generality,holds of any structure that is an “ordered additive commutative monoid, we add this line
```lean
variable {α : Type*} {R : Type*} [OrderedCancelAddCommMonoid R]
```

### Take 5
- side note: @ means bare function: @h just treat h as the raw function

### Take 6
- This i dont quite understand but lets put it here for now

The first proof can be shortened using dsimp or change to get rid of the lambda abstraction. But you can check that the subsequent rw won’t work unless we get rid of the lambda abstraction explicitly, because otherwise it cannot find the patterns f x and g x in the expression. Contrary to some other tactics, rw operates on the syntactic level, it won’t unfold definitions or apply reductions for you (it has a variant called erw that tries a little harder in this direction, but not much harder).

### Take 7: argument on set theory
If x has type α and s has type Set α, then x ∈ s is a proposition that asserts that x is an element of s. If y has some different type β then the expression y ∈ s makes no sense

“makes no sense” means “has no type hence Lean does not accept it as a well-formed statement”. This contrasts with Zermelo-Fraenkel set theory for instance where a ∈ b is a well-formed statement for every mathematical objects a and b. For instance sin ∈ cos is a well-formed statement in ZF. This defect of set theoretic foundations is an important motivation for not using it in a proof assistant which is meant to assist us by detecting meaningless expressions. In Lean sin has type ℝ → ℝ and cos has type ℝ → ℝ which is not equal to Set (ℝ → ℝ), even after unfolding definitions, so the statement sin ∈ cos makes no sense. One can also use Lean to work on set theory itself. For instance the independence of the continuum hypothesis from the axioms of Zermelo-Fraenkel has been formalized in Lean. But such a meta-theory of set theory is completely beyond the scope of this book.

For more reading:https://www.math.uchicago.edu/~may/VIGRE/VIGRE2011/REUPapers/Lian.pdf

### Take 8: Mathlib defines $Function.Injective$ f with x₁ and x₂ implicit.

A function f is said to be injective if for every x1 and x2, if f(x1)=f(x2), then x1=x2.
