
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Probability.UniformOn

--set_option diagnostics true
--set_option diagnostics.threshold 10

open BigOperators Set ProbabilityTheory MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def Perm α := {l : List α // l.Nodup}

instance measurableSpace_perm : MeasurableSpace (Perm α) := ⊤

instance fintype_perm : Fintype (Perm α) := by
  sorry

theorem num_perms_all : Fintype.card (Perm α) = Nat.factorial (Fintype.card α) := by
  sorry

def hasSetPrefix (s : Finset α) : Set (Perm α) :=
  {l : Perm α | (List.take s.card l.val).toFinset = s}

theorem num_perms_set_prefix (s : Finset α) :
    Measure.count (hasSetPrefix s) = (Nat.factorial s.card) * (Nat.factorial (Fintype.card α - s.card)) := by
  sorry

theorem num_perms_with_set_prefix (s : Finset α) :
    uniformOn Set.univ (hasSetPrefix s) = 1 / (Fintype.card α).choose (s.card) :=
  sorry

variable (𝓕 : Finset (Finset α))

theorem LYM_inequality (h𝓕 : IsAntichain (· ⊆ ·) (𝓕 : Set (Finset α))) :
    ∑ A in 𝓕, (1 / (Fintype.card α).choose (A.card)) ≤ 1 := by
  sorry

end
