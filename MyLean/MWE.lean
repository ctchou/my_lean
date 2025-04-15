
import Mathlib.Data.Nat.Basic

example : ∀ (n : ℕ ), n + 1 = 1 + n := by
  let rec fac : ℕ → ℕ
    | 0  => 1
    | n + 1 => (n + 1) * (fac n)
  have h : fac 0 = 1 := by
    simp [fac]
  sorry

def foo : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * (foo n)

example : foo 0 = 1 := by
  simp [foo]
