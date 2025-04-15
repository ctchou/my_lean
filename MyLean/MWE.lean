
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

namespace String

theorem join_eq (ss : List String) : join ss = ⟨(ss.map data).flatten⟩ := by
  let rec go : ∀ (ss : List String) cs, ss.foldl (· ++ ·) (mk cs) = ⟨cs ++ (ss.map data).flatten⟩
    | [], _ => by simp
    | ⟨s⟩::ss, _ => (go ss _).trans (by simp)
  --exact go ss []
  have h := go ss []
  exact h
