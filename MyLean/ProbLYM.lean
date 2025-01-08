
import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Probability.UniformOn

set_option diagnostics true

open BigOperators

noncomputable section

variable {α : Type*} [Fintype α]

def canonList : List α := Finset.toList (Finset.univ)

def containSet (s : Finset α) {l : List α} (h : List.Perm canonList l) : Prop :=
  sorry

variable (𝓕 : Finset (Finset α))

theorem LYM_inequality (h𝓕 : IsAntichain (· ⊆ ·) (𝓕 : Set (Finset α))) :
    ∑ A in 𝓕, (1 / (Fintype.card α).choose (A.card)) ≤ 1 := by
  sorry

end
