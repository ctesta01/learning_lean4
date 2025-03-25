I was trying to learn how can we approach this language in a faster way, and here are my takeaway:

# Todays Takeaway
1. I suggest doing not just proof but also provide text version of what being claimed - in the future, people might transfer human language to code using LLM (I consult a lot, also my cs firends using gpt to code), and this dataset could contribute to a better math assistant.

2. I had a hard time going through library to figure out which level of package should i import, i found some link however still confused.

3. i think it is generally hard to read all the techinical proof until we try something, so I am trying to start a small project doing IF calculation.

4. GPT/Ds is stupid. The reference code was like nothing. 

5. The key is to figure out, what are necessary block we need for the theory we want to develop, and import what we need.

6. Practicing some trick is important - such as, when libarary search can help

# Goal: Learning Logic & Proof Techniques (Chapter 3)
# Note on restart lean4
If the Lean server does not start automatically, you can manually start it by opening the Command Palette (Cmd+Shift+P), typing Lean: Restart Server, and selecting the command. -> I modified the command to shift+ L

# Note on finding import
go to website:[text](https://leanprover-community.github.io/mathlib4_docs/search.html?q=) and search the import libeary

# Note on applying lemma
Remember also that you can use .mp and .mpr or .1 and .2 to extract the two directions of an if-and-only-if statement.

```lean
h.1 = h.mp — forward direction
h.2 = h.mpr — reverse direction
```

# Note on import
different level of import means different depth of specification

For example
```lean
import Mathlib.Data.Real -- only need the bare definition of real numbers

#check ℝ  -- fail ❌
#check (2 : ℝ) + 3   -- fail ❌ (if arithmetic is not included)
#check abs (-5 : ℝ)  -- fail ❌ (if absolute value is not included)

import Mathlib.Data.Real.Basic -- all works for thsi version
```


# tricks:
I asked GPT to summarise a table of input tricks, will continue to modify when typing code

# Lean 4 Input Tricks: Symbols & Notation

## 1️ Universal & Existential Quantifiers
| Meaning         | Symbol | Lean Input |
|---------------|--------|------------|
| **For all**   | `∀`    | `\forall` + Space |
| **Exists**    | `∃`    | `\exists` + Space |
| **Unique Exists** | `∃!` | `\exists!` + Space |

---

## 2️ Logical Operators
| Meaning                 | Symbol | Lean Input |
|-------------------------|--------|------------|
| **Not** (negation)      | `¬`    | `\not` or `\neg` + Space |
| **And** (conjunction)   | `∧`    | `\and` + Space |
| **Or** (disjunction)    | `∨`    | `\or` + Space |
| **Implies**             | `→`    | `\to`, `\r`, or `\imp` + Space |
| **If and only if**      | `↔`    | `\iff` or `\lr` + Space |

---

## 3️ Set & Function Notation
| Meaning                 | Symbol | Lean Input |
|-------------------------|--------|------------|
| **Subset**              | `⊆`    | `\sub` + Space |
| **Superset**            | `⊇`    | `\sup` + Space |
| **Element of**          | `∈`    | `\in` + Space |
| **Not Element of**      | `∉`    | `\notin` + Space |
| **Union**               | `∪`    | `\cup` + Space |
| **Intersection**        | `∩`    | `\cap` + Space |
| **Function maps to**    | `↦`    | `\mapsto` + Space |

---

## 4️ Relations & Orderings
| Meaning                 | Symbol | Lean Input |
|-------------------------|--------|------------|
| **Less than**           | `<`    | Standard `<` |
| **Less than or equal**  | `≤`    | `\le` + Space |
| **Greater than**        | `>`    | Standard `>` |
| **Greater than or equal** | `≥`  | `\ge` + Space |
| **Not equal**           | `≠`    | `\ne` + Space |

---

## 5️⃣ Arithmetic & Algebra
| Meaning                  | Symbol | Lean Input |
|--------------------------|--------|------------|
| **Plus**                 | `+`    | Standard `+` |
| **Minus**                | `-`    | Standard `-` |
| **Multiplication**       | `*`    | Standard `*` |
| **Division**             | `/`    | Standard `/` |
| **Power (exponentiation)** | `^` | Standard `^` |
| **Absolute value**       | `|x|`  | `abs x` in Lean |
| **Summation**            | `∑`    | `\sum` + Space |

---

## 6️ Special Math Symbols
| Meaning                 | Symbol | Lean Input |
|-------------------------|--------|------------|
| **Real numbers**        | `ℝ`    | `\R` or `\real` + Space (Needs `Mathlib.Data.Real.Basic`) |
| **Natural numbers**     | `ℕ`    | `\N` or `\nat` + Space |
| **Integers**            | `ℤ`    | `\Z` or `\int` + Space |
| **Rational numbers**    | `ℚ`    | `\Q` or `\rat` + Space |
| **Complex numbers**     | `ℂ`    | `\C` or `\complex` + Space |

---

## 7️ Miscellaneous
| Meaning                 | Symbol | Lean Input |
|-------------------------|--------|------------|
| **Lambda function**     | `λ`    | `\lambda` + Space |
| **Angle brackets**      | `⟨⟩`   | `\langle` / `\rangle` + Space |
| **Prime notation**      | `x'`   | `x'` (just type `'` after variable) |

---

## Summary (Quick Cheatsheet)

```lean
\forall → ∀
\exists → ∃
\to → →
\le → ≤
\ge → ≥
\ne → ≠
\in → ∈
\sum → ∑
\R → ℝ  (Needs Mathlib.Data.Real.Basic)
```
