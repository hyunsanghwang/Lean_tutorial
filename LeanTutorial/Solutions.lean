import LeanTutorial.Part1_WhatIsLean
import LeanTutorial.Part2_Algebra
import LeanTutorial.Part3_Analysis

/-!
# Solutions

One worked answer per exercise. Most have several good proofs — if yours
differs and Lean accepts it, yours is right too.
-/

namespace Solutions

/-! ## Part 1 -/

example : (7 : ℤ) - 10 = -3 := by norm_num

example (p q : Prop) (h : p ∧ q) : p := h.1

example (x : ℝ) (h : x = 3) : 2 * x + 1 = 7 := by
  rw [h]
  norm_num

example (a b : ℝ) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by ring

/-! ## Part 2 -/

example (x : ℝ) : (x + 3) * (x - 3) = x ^ 2 - 9 := by ring

example (a b c : ℝ) (h₁ : a = b) (h₂ : b = c) : a = c := by rw [h₁, h₂]

example (x : ℝ) (h : 3 * x - 6 = 0) : x = 2 := by linarith

example (x y : ℝ) (h₁ : x + y = 10) (h₂ : x - y = 2) : x = 6 := by linarith

example (n : ℤ) (h : Even n) : Even (n ^ 2) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨2 * k * k, by rw [hk]; ring⟩

example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

example (a b c d : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c ≤ d) : a ≤ d := by
  calc a ≤ b := h₁
    _ ≤ c := h₂
    _ ≤ d := h₃

/-! ## Part 3 -/

open Part3

example : ∀ x : ℝ, ∃ y : ℝ, y > x + 5 := by
  intro x
  use x + 6
  linarith

example (f : ℝ → ℝ) (h : ∀ x, f x ≤ 3) : ∀ x, f x - 3 ≤ 0 := by
  intro x
  have := h x
  linarith

example (h : ∃ n : ℕ, n > 100) : ∃ n : ℕ, n > 50 := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by omega⟩

example (P : ℕ → Prop) (h : ¬ ∃ n, P n) : ∀ n, ¬ P n := by
  intro n hn
  exact h ⟨n, hn⟩

/-- Eventually constant sequences converge. `N₀` is the witness. -/
example (a : ℕ → ℝ) (L : ℝ) (N₀ : ℕ) (h : ∀ n ≥ N₀, a n = L) : TendsTo a L := by
  intro ε hε
  use N₀
  intro n hn
  rw [h n hn]
  simpa using hε

/-- Scaling a limit. The `c = 0` case is genuinely different: `ε / |c|` is not
available, but the sequence is constantly `0` so any `N` works. -/
example (a : ℕ → ℝ) (L c : ℝ) (ha : TendsTo a L) : TendsTo (fun n => c * a n) (c * L) := by
  intro ε hε
  rcases eq_or_ne c 0 with rfl | hc
  · use 0
    intro n _
    simpa using hε
  · have hc' : 0 < |c| := abs_pos.mpr hc
    obtain ⟨N, hN⟩ := ha (ε / |c|) (div_pos hε hc')
    use N
    intro n hn
    have h := hN n hn
    have hrw : c * a n - c * L = c * (a n - L) := by ring
    rw [hrw, abs_mul]
    calc |c| * |a n - L| < |c| * (ε / |c|) := mul_lt_mul_of_pos_left h hc'
      _ = ε := by field_simp

end Solutions
