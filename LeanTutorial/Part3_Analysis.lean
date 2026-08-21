import Mathlib.Tactic

/-!
# Part 3 — Analysis, or: living with quantifiers  (≈75 minutes)

Part 2 never left a fixed context. Analysis is different: every definition is a
nest of `∀` and `∃`, and *that* is what beginners find hard — not the ε's.

The good news is that Lean makes the quantifier discipline mechanical. There
are exactly four moves, and once you know which of the four applies you are
never stuck on "what do I do now":

|          | in the **goal**            | in a **hypothesis**   |
| -------- | -------------------------- | --------------------- |
| `∀ x, …` | `intro x` (let `x` be given) | apply it: `h a`     |
| `∃ x, …` | `use a` (produce a witness) | `obtain ⟨x, hx⟩ := h` |

Goal side = you are the *defender*. Hypothesis side = you are the *attacker*.
`∀` in the goal costs you nothing; `∃` in the goal is where you must be clever.
-/

namespace Part3

/-! ## 1. The four moves, on toy statements -/

-- `∀` in the goal: `intro`.
example : ∀ x : ℝ, x ^ 2 ≥ 0 := by
  intro x
  positivity

-- `∃` in the goal: `use` a witness, then prove the property.
example : ∃ x : ℝ, x ^ 2 = 4 := by
  use 2
  norm_num

-- `∀` in a hypothesis: apply it to whatever you like.
example (f : ℝ → ℝ) (h : ∀ x : ℝ, f x = 2 * x) : f 3 = 6 := by
  rw [h 3]
  norm_num

-- `∃` in a hypothesis: `obtain` names the witness and its property.
example (x : ℝ) (h : ∃ y : ℝ, x = 2 * y) : ∃ z : ℝ, x = z + z := by
  obtain ⟨y, hy⟩ := h
  use y
  linarith

/-! ## 2. Order of quantifiers

`∀ ε, ∃ N, …` and `∃ N, ∀ ε, …` are genuinely different statements, and Lean
will not let you confuse them. In the first, `N` may depend on `ε`; in the
second it may not. This is *the* thing to slow down on. -/

-- True: for each x, pick a bigger number depending on x.
example : ∀ x : ℝ, ∃ y : ℝ, x < y := by
  intro x
  use x + 1
  linarith

-- The swapped version is false, and Lean cannot be argued out of it:
--   ∃ y : ℝ, ∀ x : ℝ, x < y
-- would need a real number larger than every real number. Try `use` and watch
-- the goal become unprovable.

/-! ## 3. Negating quantifiers: `push Not`

`¬ ∀ x, p x` becomes `∃ x, ¬ p x`, and `¬ ∃` becomes `∀ ¬`. The `push Not`
tactic drives negations inwards for you — indispensable for proofs by
contradiction. (In older Mathlib and most tutorials this is `push_neg`, now
deprecated in favour of `push Not`.) -/

example (f : ℝ → ℝ) (h : ¬ ∀ x, f x = 0) : ∃ x, f x ≠ 0 := by
  push Not at h
  exact h

/-! ## 4. Limits of sequences

Now the real thing. We spell out the ε–N definition by hand rather than using
Mathlib's `Filter.Tendsto`, because the point today is the quantifiers. -/

/-- `TendsTo a L` means the sequence `a` converges to `L`:
for every `ε > 0` there is an `N` beyond which `a n` is within `ε` of `L`. -/
def TendsTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

/-! Read the proof skeleton off the definition, every single time:

```
intro ε hε      -- ∀ ε > 0        (defender: accept any ε)
use N           -- ∃ N            (be clever here)
intro n hn      -- ∀ n ≥ N        (accept any n)
...             -- prove |a n - L| < ε
```
-/

/-- A constant sequence converges to its value. Any `N` works — take `0`. -/
theorem tendsTo_const (c : ℝ) : TendsTo (fun _ => c) c := by
  intro ε hε
  use 0
  intro n _
  simpa using hε

/-- `1 / (n + 1) → 0`. Here the witness `N` really does depend on `ε`:
we take `N` bigger than `1 / ε`, which exists because ℝ is Archimedean. -/
theorem tendsTo_one_div : TendsTo (fun n => 1 / (n + 1 : ℝ)) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  use N
  intro n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : 1 / ε < (n : ℝ) + 1 := by linarith
  have h2 : ε * (1 / ε) = 1 := by field_simp
  simp only [sub_zero, abs_of_pos (by positivity : (0:ℝ) < 1 / ((n : ℝ) + 1))]
  rw [div_lt_iff₀ hpos]
  nlinarith [mul_lt_mul_of_pos_left h1 hε]

/-- The limit of a sum is the sum of the limits.

The classic ε/2 argument. Note the two `obtain`s: we *attack* the hypotheses
with ε/2, then combine the two thresholds with `max`. -/
theorem tendsTo_add {a b : ℕ → ℝ} {L M : ℝ} (ha : TendsTo a L) (hb : TendsTo b M) :
    TendsTo (fun n => a n + b n) (L + M) := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := ha (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hb (ε / 2) (by linarith)
  use max N₁ N₂
  intro n hn
  have h₁ := hN₁ n (le_of_max_le_left hn)
  have h₂ := hN₂ n (le_of_max_le_right hn)
  have hrw : a n + b n - (L + M) = (a n - L) + (b n - M) := by ring
  calc |a n + b n - (L + M)| = |(a n - L) + (b n - M)| := by rw [hrw]
    _ ≤ |a n - L| + |b n - M| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-! ## 5. Continuity, ε–δ

Same skeleton, one more layer. -/

/-- `ContinuousAtPt f x₀`: the ε–δ definition of continuity at a point. -/
def ContinuousAtPt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε

/-- An affine map is continuous everywhere: take `δ = ε / 2`. -/
theorem continuousAtPt_affine (x₀ : ℝ) :
    ContinuousAtPt (fun x => 2 * x + 1) x₀ := by
  intro ε hε
  use ε / 2, by linarith
  intro x hx
  have hrw : (2 * x + 1) - (2 * x₀ + 1) = 2 * (x - x₀) := by ring
  simp only [hrw, abs_mul]
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  linarith

/-! ## Exercises

The first four are quantifier gymnastics; the last two are real analysis. -/

example : ∀ x : ℝ, ∃ y : ℝ, y > x + 5 := by sorry

example (f : ℝ → ℝ) (h : ∀ x, f x ≤ 3) : ∀ x, f x - 3 ≤ 0 := by sorry

example (h : ∃ n : ℕ, n > 100) : ∃ n : ℕ, n > 50 := by sorry

example (P : ℕ → Prop) (h : ¬ ∃ n, P n) : ∀ n, ¬ P n := by sorry

/-- A sequence that is eventually equal to `L` converges to `L`. -/
example (a : ℕ → ℝ) (L : ℝ) (N₀ : ℕ) (h : ∀ n ≥ N₀, a n = L) : TendsTo a L := by
  sorry

/-- Scaling a limit. Try `ε / |c|` — and think about why `c = 0` needs care.
(Hint: `rcases eq_or_ne c 0 with rfl | hc` splits that off.) -/
example (a : ℕ → ℝ) (L c : ℝ) (ha : TendsTo a L) : TendsTo (fun n => c * a n) (c * L) := by
  sorry

end Part3
