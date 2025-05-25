
import mathlib

example (a D : ℕ → ℝ) (h1 : Antitone a) (h2 : ∀ k, D k ≥ 0)
    (h3 : ∀ k, a k ≤ D k - D (k + 1)) : a k ≤ D 0 / (k + 1) := by
  suffices h4 : (k + 1) * a k ≤ D 0 - D (k + 1) by
    have h5 : (↑k + 1) * a k ≤ D 0 := by have := h2 (k + 1) ; bound
    have h6 : 0 < k + (1 : ℝ) := by bound
    exact (le_div_iff₀' h6).mpr h5
  induction' k with k h_ind <;> simp
  · exact h3 0
  calc
    (↑k + 1 + 1) * a (k + 1) = (↑k + 1) * a (k + 1) + 1 * a (k + 1) := by ring
    _ = (↑k + 1) * a (k + 1) + a (k + 1) := by field_simp
    _ ≤ (↑k + 1) * a k + a (k + 1) := by bound
    _ ≤ D 0 - D (k + 1) + a (k + 1) := by bound
    _ ≤ D 0 - D (k + 1) + D (k + 1) - D (k + 1 + 1) := by have := h3 (k + 1) ; bound
    _ ≤ D 0 - D (k + 1 + 1) := by field_simp
