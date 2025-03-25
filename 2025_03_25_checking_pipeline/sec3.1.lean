import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Linarith
import Mathlib.Order.Monotone.Defs


#check ℝ
#check (2 : ℝ) + 3
#check abs (-5 : ℝ)

#check ∀ x : ℝ, 0 ≤ x → |x| = x
#check ∀ x y ε: ℝ , 0<ε  → ε ≤ 1

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε



theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry
theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

#check my_lemma2 h₀ h₁ ha hb

-- This is my practice
theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc -- try abs_mul, mul_le_mul, abs_nonneg, mul_lt_mul_right, and one_mul
    |x * y| = |x| * |y| := abs_mul x y
   _ ≤ |x| * ε := mul_le_mul (le_refl |x|) (le_of_lt ylt) (abs_nonneg y) (abs_nonneg x)
   _ < 1 * ε := (mul_lt_mul_right epos).mpr (lt_of_lt_of_le xlt ele1)
   _ = ε := one_mul ε

-- This is the provided answer:
theorem my_lemma5 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := by apply abs_mul
    _ ≤ |x| * ε := by apply mul_le_mul; linarith; linarith; apply abs_nonneg; apply abs_nonneg;
    _ < 1 * ε := by rw [mul_lt_mul_right epos]; linarith
    _ = ε := by apply one_mul

#check my_lemma4 h₀ h₁ ha hb

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
 intro x
 dsimp
 apply add_le_add
 apply hfa
 apply hgb


-- variable {α : Type*} {R : Type*} [OrderedCancelAddCommMonoid R]

#check add_le_add

-- def FnUb' (f : α → R) (a : R) : Prop :=
--  ∀ x, f x ≤ a

--theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
--  FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)
open Function
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
 -- the above line has some unfix error
 intro a b aleb
 apply add_le_add
 apply mf aleb
 apply mg aleb


def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
-- For any real constant c, the function x ↦ x + c is injective.
  intro x₁ x₂ h'
--  we want to prove:if f(x1)=f(x2), then x1=x2.
  exact (add_left_inj c).mp h'
