import Mathlib.Tactic

/-!
# Part 1 — What is Lean?  (≈45 minutes)

Lean is a **proof assistant**: you write a mathematical statement, you write an
argument for it, and Lean checks the argument — every step, no gaps allowed.

The whole system rests on one idea:

> A statement is a **type**. A proof of it is a **term** of that type.

So checking a proof is the same job as type-checking a program, which is why a
computer can do it at all. Everything below is an illustration of that slogan.

`Mathlib` is the community library of formalised mathematics — about 1.8 million
lines of it. We import all of its tactics on line 1.

**How to work through this file:** put your cursor at the end of any line and
read Lean's response in the info view (VS Code: the pane on the right, or
`Ctrl/Cmd + Shift + Enter`). The goal state shown there *is* the tutorial.
-/

namespace Part1

/-! ## 1. Every term has a type

`#check` asks for the type of a term. `#eval` runs it. -/

#check 2 + 2                    -- ℕ, the natural numbers
#check (2 : ℤ)                  -- ℤ, the integers
#check (2 : ℝ)                  -- ℝ, the reals
#check fun n : ℕ => n + 1       -- ℕ → ℕ, a function

#eval 2 + 2                     -- 4
#eval 2 - 5                     -- 0  — ℕ-subtraction truncates at zero!
#eval (2 : ℤ) - 5               -- -3 — the type genuinely matters

/-! Lean is picky about types on purpose: `2 - 5` really is `0` in ℕ. Choosing
the right type is the first modelling decision in any formalisation. -/

/-! ## 2. Statements are types too

A *proposition* is a term whose type is `Prop`. Note that `2 + 2 = 5` is a
perfectly well-formed proposition — it is just a false one. -/

#check 2 + 2 = 4                -- Prop
#check 2 + 2 = 5                -- Prop
#check ∀ n : ℕ, n + 0 = n       -- Prop

/-! ## 3. A proof is a term of that type

`theorem name : statement := proof`. Here `rfl` means "both sides compute to
the same thing", which is enough for `2 + 2 = 4`. -/

theorem two_plus_two : 2 + 2 = 4 := rfl

-- The proof is a term, so its *type* is the statement it proves.
#check two_plus_two             -- 2 + 2 = 4

/-! ## 4. Tactic mode

Writing proof terms by hand does not scale. `by` opens **tactic mode**: instead
of building the term forwards, you transform the *goal* backwards until nothing
is left, and Lean assembles the term for you.

This is where you will spend the rest of your life with Lean. -/

example : 2 + 2 = 4 := by norm_num

-- `intro` introduces a hypothesis, `exact` closes a goal with a term.
example (p q : Prop) (hp : p) : q → p := by
  intro _
  exact hp

-- `constructor` splits an `∧` into two goals. The `·` bullets focus them.
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

-- `obtain` takes a hypothesis apart.
example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩

/-! ## 5. The three tactics that do real work

Most goals in an undergraduate course fall to one of these. Part 2 drills them. -/

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring

example (x : ℝ) (h : 2 * x + 1 ≤ 7) : x ≤ 3 := by linarith

example (n : ℕ) (h : n % 2 = 1) : n ≠ 4 := by omega

/-! ## 6. Getting unstuck

* `exact?` searches Mathlib for a lemma that closes the goal.
* `apply?` searches for lemmas that make progress.
* `hint` runs a handful of standard tactics and reports which ones worked.
* Naming convention: `add_comm`, `mul_le_mul`, `sub_nonneg` — read the name as
  a description of the statement, left to right.

Try replacing the proof below with `exact?` and see what Lean finds. -/

example (a b : ℕ) : a + b = b + a := by exact Nat.add_comm a b

/-! ## Exercises

Replace each `sorry`. Solutions are in `LeanTutorial/Solutions.lean` — resist
looking until you have tried. -/

example : (7 : ℤ) - 10 = -3 := by sorry

example (p q : Prop) (h : p ∧ q) : p := by sorry

example (x : ℝ) (h : x = 3) : 2 * x + 1 = 7 := by sorry

example (a b : ℝ) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by sorry

end Part1
