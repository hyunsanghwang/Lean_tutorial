import Mathlib.Tactic

/-!
# Part 2 — Algebra  (≈60 minutes)

Everything in this part is **quantifier-free**: fixed variables, an equation or
an inequality, and a chain of manipulations. That is deliberate. Algebra is
where you learn the tactics; Part 3 adds the quantifiers.

The four workhorses:

| Tactic     | Use it for                                              |
| ---------- | ------------------------------------------------------- |
| `ring`     | identities true in any commutative ring                 |
| `linarith` | linear inequalities, using the hypotheses in context     |
| `norm_num` | concrete numerical claims                               |
| `rw`       | rewriting with an equation you already have             |
-/

namespace Part2

/-! ## 1. `ring` — identities

`ring` proves any identity that holds in every commutative ring, by normalising
both sides. It does not look at your hypotheses. -/

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

-- It works over any commutative ring, not just ℝ.
example (n : ℤ) : (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by ring

/-! ## 2. `rw` — using an equation you have

`rw [h]` replaces the left-hand side of `h` by its right-hand side, everywhere
in the goal. `rw [← h]` goes the other way. -/

example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by
  rw [h]

example (x y : ℝ) (h : x = 2 * y) : x + y = 3 * y := by
  rw [h]
  ring

-- `rw ... at h` rewrites in a hypothesis instead of the goal.
example (a b : ℝ) (h : a = b) (hb : b = 3) : a = 3 := by
  rw [hb] at h
  exact h

/-! ## 3. `linarith` — linear inequalities

`linarith` looks for a linear combination of your hypotheses that contradicts
the negated goal. Unlike `ring`, it *does* use the context. -/

example (x : ℝ) (h : 2 * x + 1 ≤ 7) : x ≤ 3 := by linarith

example (x y : ℝ) (h₁ : x ≤ y) (h₂ : y ≤ 3) : x ≤ 3 := by linarith

-- Nonlinear facts have to be supplied as extra terms.
example (x : ℝ) : 0 ≤ x ^ 2 + 1 := by nlinarith [sq_nonneg x]

/-! ## 4. `norm_num` — concrete arithmetic -/

example : (2 : ℝ) + 2 = 4 := by norm_num

example : (17 : ℕ).Prime := by norm_num

example : (1 : ℝ) / 3 + 1 / 6 = 1 / 2 := by norm_num

/-! ## 5. `calc` — writing a derivation the reader can follow

This is the single most important thing to teach. A `calc` block looks like the
chain of equalities you would write on a blackboard, and each step carries its
own justification. -/

example (a b : ℝ) (h : a = 2 * b) (hb : b = 3) : a = 6 := by
  calc a = 2 * b := h
    _ = 2 * 3 := by rw [hb]
    _ = 6 := by norm_num

-- `calc` chains inequalities too, mixing `=` and `≤`.
example (x y : ℝ) (hx : 0 ≤ x) (h : x ≤ y) : x ^ 2 ≤ y ^ 2 := by
  calc x ^ 2 = x * x := by ring
    _ ≤ y * y := by nlinarith
    _ = y ^ 2 := by ring

/-! ## 6. `have` — naming an intermediate step

`have` proves a side fact and adds it to the context. Long proofs are mostly
`have`s followed by one `linarith`. -/

example (x : ℝ) (hx : 0 < x) : 0 < x ^ 2 + x := by
  have hx2 : 0 < x ^ 2 := by positivity
  linarith

/-! ## 7. Division: `field_simp`

Division needs the denominators to be nonzero, so you must supply that. The
idiom is `field_simp` (clear denominators) followed by `ring`. -/

example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) : 1 / x + 1 / y = (x + y) / (x * y) := by
  field_simp
  ring

/-! ## 8. Algebra without numbers

The same tactics work in an abstract group or ring — this is what makes Mathlib
a library rather than a calculator. `[Group G]` says "assume `G` is a group". -/

example (G : Type) [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  group

example (R : Type) [CommRing R] (x y : R) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

/-! ## Exercises

Replace each `sorry`. Roughly increasing difficulty; the last one wants `calc`. -/

example (x : ℝ) : (x + 3) * (x - 3) = x ^ 2 - 9 := by sorry

example (a b c : ℝ) (h₁ : a = b) (h₂ : b = c) : a = c := by sorry

example (x : ℝ) (h : 3 * x - 6 = 0) : x = 2 := by sorry

example (x y : ℝ) (h₁ : x + y = 10) (h₂ : x - y = 2) : x = 6 := by sorry

example (n : ℤ) (h : Even n) : Even (n ^ 2) := by sorry

example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by sorry

/-- A `calc` proof: `a ≤ b` and `b ≤ c` and `c ≤ d` gives `a ≤ d`, but write it
as a readable chain rather than one `linarith`. -/
example (a b c d : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c ≤ d) : a ≤ d := by sorry

end Part2
