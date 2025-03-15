# History of Probability in Lean4

*Christian Testa*

What I've been reading lately: 

  * <https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/>
  * <https://leanprover.github.io/theorem_proving_in_lean4/title_page.html>

I also feel like this will be a really handy resource: 

  * <https://github.com/madvorak/lean4-tactics>

I want to pursue what was the the development history of probability in Lean4?  What did they start with? 

It turns out it was a lot of porting over what had been done in Lean3. 


The first commit to mathlib4/Probability was on May 9, 2023 

<https://github.com/leanprover-community/mathlib4/commit/68b21e12e6d612e77f34febea2e00a9358ce2f76>

> ! This file was ported from Lean 3 source module probability.probability_mass_function.basic
> ! leanprover-community/mathlib commit 4ac69b290818724c159de091daa3acd31da0ee6d 

Okay, so the work was older than that, but just ported over. 
We can see at the top of the file (c) 2017 

```lean
open Classical BigOperators NNReal ENNReal MeasureTheory

/-- A probability mass function, or discrete probability measures is a function `α → ℝ≥0∞` such
  that the values have (infinite) sum `1`. -/
def Pmf.{u} (α : Type u) : Type u :=
  { f : α → ℝ≥0∞ // HasSum f 1 }
#align pmf Pmf
```

So a Pmf is defined to be the following Type:

It is a function that arguments $\alpha$ of `Type u` 
which is a function that maps to real-nonnegative 
values and has sum 1 across possible inputs. 

Then there are a lot of theorems I don't understand. 

I do understand 

```lean
/-- The support of a `Pmf` is the set where it is nonzero. -/
def support (p : Pmf α) : Set α :=
  Function.support p
```


It looks like at this time, everything was discrete. 
There is some formalism around Carathéodory extension
and outer measure. 

The next commit, May 10th, 2023 introduces Conditional Probability: 

<https://github.com/leanprover-community/mathlib4/commit/ab8b90a8c18c410cf369537add98df0dc8f32207> 

Again this is just work being ported from Lean3 to Lean4. 

```lean
/-
Copyright (c) 2022 Rishikesh Vaishnav. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rishikesh Vaishnav

! This file was ported from Lean 3 source module probability.conditional_probability
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Conditional Probability

This file defines conditional probability and includes basic results relating to it.

Given some measure `μ` defined on a measure space on some type `Ω` and some `s : Set Ω`,
we define the measure of `μ` conditioned on `s` as the restricted measure scaled by
the inverse of the measure of `s`: `cond μ s = (μ s)⁻¹ • μ.restrict s`. The scaling
ensures that this is a probability measure (when `μ` is a finite measure).

From this definition, we derive the "axiomatic" definition of conditional probability
based on application: for any `s t : Set Ω`, we have `μ[t|s] = (μ s)⁻¹ * μ (s ∩ t)`.

## Main Statements

* `cond_cond_eq_cond_inter`: conditioning on one set and then another is equivalent
  to conditioning on their intersection.
* `cond_eq_inv_mul_cond_mul`: Bayes' Theorem, `μ[t|s] = (μ s)⁻¹ * μ[s|t] * (μ t)`.
```

I'm just going to focus on the parts I understand at all... 

Below it looks like they set up the notation for μ[t|s] and 

```lean
noncomputable section

open ENNReal MeasureTheory MeasurableSpace

variable {Ω : Type _} {m : MeasurableSpace Ω} (μ : Measure Ω) {s t : Set Ω}

namespace ProbabilityTheory

section Definitions

/-- The conditional probability measure of measure `μ` on set `s` is `μ` restricted to `s`
and scaled by the inverse of `μ s` (to make it a probability measure):
`(μ s)⁻¹ • μ.restrict s`. -/
def cond (s : Set Ω) : Measure Ω :=
  (μ s)⁻¹ • μ.restrict s
#align probability_theory.cond ProbabilityTheory.cond

end Definitions

scoped notation μ "[" s "|" t "]" => ProbabilityTheory.cond μ t s
scoped notation:60 μ "[|" t "]" => ProbabilityTheory.cond μ t

/-- The conditional probability measure of any finite measure on any set of positive measure
is a probability measure. -/
theorem cond_probabilityMeasure [FiniteMeasure μ] (hcs : μ s ≠ 0) : ProbabilityMeasure <| μ[|s] :=
  ⟨by
    rw [cond, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact ENNReal.inv_mul_cancel hcs (measure_ne_top _ s)⟩
#align probability_theory.cond_is_probability_measure ProbabilityTheory.cond_probabilityMeasure

section Bayes

@[simp]
theorem cond_empty : μ[|∅] = 0 := by simp [cond]
#align probability_theory.cond_empty ProbabilityTheory.cond_empty

@[simp]
theorem cond_univ [ProbabilityMeasure μ] : μ[|Set.univ] = μ := by
  simp [cond, measure_univ, Measure.restrict_univ]
#align probability_theory.cond_univ ProbabilityTheory.cond_univ

/-- The axiomatic definition of conditional probability derived from a measure-theoretic one. -/
theorem cond_apply (hms : MeasurableSet s) (t : Set Ω) : μ[t|s] = (μ s)⁻¹ * μ (s ∩ t) := by
  rw [cond, Measure.smul_apply, Measure.restrict_apply' hms, Set.inter_comm, smul_eq_mul]
#align probability_theory.cond_apply ProbabilityTheory.cond_apply

```

A couple interesting examples stand out to me:

```lean
/-- A version of the law of total probability. -/
theorem cond_add_cond_compl_eq [FiniteMeasure μ] (hms : MeasurableSet s) (hcs : μ s ≠ 0)
    (hcs' : μ (sᶜ) ≠ 0) : μ[t|s] * μ s + μ[t|sᶜ] * μ (sᶜ) = μ t := by
  rw [cond_mul_eq_inter μ hms hcs, cond_mul_eq_inter μ hms.compl hcs', Set.inter_comm _ t,
    Set.inter_comm _ t]
  exact measure_inter_add_diff t hms
#align probability_theory.cond_add_cond_compl_eq ProbabilityTheory.cond_add_cond_compl_eq
```


```lean
/-- **Bayes' Theorem** -/
theorem cond_eq_inv_mul_cond_mul [FiniteMeasure μ] (hms : MeasurableSet s) (hmt : MeasurableSet t) :
    μ[t|s] = (μ s)⁻¹ * μ[s|t] * μ t := by
  by_cases ht : μ t = 0
  · simp [cond, ht, Measure.restrict_apply hmt, Or.inr (measure_inter_null_of_null_left s ht)]
  · rw [mul_assoc, cond_mul_eq_inter μ hmt ht s, Set.inter_comm, cond_apply _ hms]
#align probability_theory.cond_eq_inv_mul_cond_mul ProbabilityTheory.cond_eq_inv_mul_cond_mul

end Bayes

end ProbabilityTheory
```

What stands out to me is the use of the `simp` for simplify and the `rw` tactic for rewrite. 


This [Lean 4 spellbook -- tactics overview for beginners](https://github.com/madvorak/lean4-tactics) is nice



Then we have Monad structure for Pmfs: 

<https://github.com/leanprover-community/mathlib4/commit/1a5bf78b9a1a52d104524f4483c35e94595b7916>

```lean
/-!
# Monad Operations for Probability Mass Functions

This file constructs two operations on `Pmf` that give it a monad structure.
`pure a` is the distribution where a single value `a` has probability `1`.
`bind pa pb : Pmf β` is the distribution given by sampling `a : α` from `pa : Pmf α`,
and then sampling from `pb a : Pmf β` to get a final result `b : β`.

`bindOnSupport` generalizes `bind` to allow binding to a partial function,
so that the second argument only needs to be defined on the support of the first argument.

-/
```

I think this is to say we use Monads to construct product measures. And I'm just guessing but I think we want 
to have this Monadic construction to be able to make category theoretic statements about 
`Pmf`. 

Another important commit was June 17 2023: feat: port Probability.Notation (#5187)

<https://github.com/leanprover-community/mathlib4/commit/9b59869e8c3d862fd76e003f98415445746ec57e>

```lean
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Notations for probability theory

This file defines the following notations, for functions `X,Y`, measures `P, Q` defined on a
measurable space `m0`, and another measurable space structure `m` with `hm : m ≤ m0`,
- `P[X] = ∫ a, X a ∂P`
- `𝔼[X] = ∫ a, X a`
- `𝔼[X|m]`: conditional expectation of `X` with respect to the measure `volume` and the
  measurable space `m`. The similar `P[X|m]` for a measure `P` is defined in
  `MeasureTheory.Function.ConditionalExpectation.Basic`.
- `P⟦s|m⟧ = P[s.indicator (fun ω => (1 : ℝ)) | m]`, conditional probability of a set.
- `X =ₐₛ Y`: `X =ᵐ[volume] Y`
- `X ≤ₐₛ Y`: `X ≤ᵐ[volume] Y`
- `∂P/∂Q = P.rnDeriv Q`
We note that the notation `∂P/∂Q` applies to three different cases, namely,
`MeasureTheory.Measure.rnDeriv`, `MeasureTheory.SignedMeasure.rnDeriv` and
`MeasureTheory.ComplexMeasure.rnDeriv`.

- `ℙ` is a notation for `volume` on a measured space.
-/


open MeasureTheory

open scoped MeasureTheory

-- We define notations `𝔼[f|m]` for the conditional expectation of `f` with respect to `m`.
scoped[ProbabilityTheory] notation "𝔼[" X "|" m "]" =>
  MeasureTheory.condexp m MeasureTheory.MeasureSpace.volume X

scoped[ProbabilityTheory] notation P "[" X "]" => ∫ x, X x ∂P

scoped[ProbabilityTheory] notation "𝔼[" X "]" => ∫ a, X a

scoped[ProbabilityTheory] notation P "⟦" s "|" m "⟧" =>
  MeasureTheory.condexp m P (Set.indicator s fun ω => (1 : ℝ))

scoped[ProbabilityTheory] notation:50 X " =ₐₛ " Y:50 => X =ᵐ[MeasureTheory.MeasureSpace.volume] Y

scoped[ProbabilityTheory] notation:50 X " ≤ₐₛ " Y:50 => X ≤ᵐ[MeasureTheory.MeasureSpace.volume] Y

set_option quotPrecheck false in
scoped[ProbabilityTheory] notation "∂" _P "/∂" Q:50 => P.rnDeriv Q

scoped[ProbabilityTheory] notation "ℙ" => MeasureTheory.MeasureSpace.volume
```


Interesting... I don't know that many languages where you can define notation so 
flexibly.

Now at a more rapid pace I mention: 

  * [June 17 2023 they port over some probabilistic statements](https://github.com/leanprover-community/mathlib4/blob/d62cc4a4f2e171d3baf66a16ba8a82440312f777/Mathlib/Probability/ConditionalExpectation.lean) 
  from Lean 3
```lean
/-!

# Probabilistic properties of the conditional expectation

This file contains some properties about the conditional expectation which does not belong in
the main conditional expectation file.

## Main result

* `MeasureTheory.condexp_indep_eq`: If `m₁, m₂` are independent σ-algebras and `f` is a
  `m₁`-measurable function, then `𝔼[f | m₂] = 𝔼[f]` almost everywhere.

-/
```
  * Okay, so the above mentions that there's conditional expectation details in the MeasureTheory 
  folder of Mathlib. We can find conditional expectation here: 
  <https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/Function/ConditionalExpectation/>
  * You can also find $\pi$-$\lambda$ systems here: <https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/PiSystem.lean>
  * Also, basically all of the MeasureTheory will be of interest to us:
  <https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/MeasureTheory/>
  
  
  
