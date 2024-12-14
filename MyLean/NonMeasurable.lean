
import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Batteries.Tactic.Instances

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option warningAsError false

open Set Filter Real MeasureTheory BigOperators

noncomputable section

lemma shift_heasurable {s : Set ℝ} (h : MeasurableSet s) (c : ℝ) : MeasurableSet (image (fun x ↦ x + c) s) := by
  apply (MeasurableEmbedding.measurableSet_image ?_).mpr h
  exact measurableEmbedding_addRight c

lemma shift_volume (s : Set ℝ) (c : ℝ) : volume (image (fun x ↦ x + c) s) = volume s := by
  simp only [image_add_right, measure_preimage_add_right]

lemma volume_mono {s t : Set ℝ} (h : s ⊆ t) : volume s ≤ volume t := by
  exact OuterMeasureClass.measure_mono volume h

lemma volume_biUnion {ι : Type*} {s : Set ι} {f : ι → Set ℝ}
    (hs : s.Countable) (hd : s.PairwiseDisjoint f) (hm : ∀ i ∈ s, MeasurableSet (f i)) :
    volume (⋃ i ∈ s, f i) = ∑' (i : ↑s), volume (f ↑i) :=
  measure_biUnion hs hd hm

-- lemma volume_iUnion' [Countable ι] {f : ι → Set ℝ}
--     (hdis : Pairwise (Disjoint on f)) (hmea : ∀ (i : ι), MeasurableSet (f i)) :
--     volume (⋃ i, f i) = ∑' i, volume (f i) :=
--   measure_iUnion hdis hmea

instance vS : Setoid { x : ℝ // x ∈ Icc 0 1 } where
  r := fun x y ↦ (↑ x : ℝ) - (↑ y) ∈ range ((↑) : ℚ → ℝ)
  iseqv := {
    refl := by
      intro x
      simp only [sub_self, mem_range, Rat.cast_eq_zero, exists_eq]
    symm := by
      intro x y
      simp only [mem_range]
      rintro ⟨t, h⟩
      use (-t)
      simp [h]
    trans := by
      intro x y z
      simp only [mem_range]
      rintro ⟨t1, h1⟩
      rintro ⟨t2, h2⟩
      use (t1 + t2)
      simp [h1, h2]
  }

def vT : Type := Quotient vS

lemma vS_vT_surj : ∀ t : vT, ∃ x : { x : ℝ // x ∈ Icc 0 1 }, ⟦x⟧ = t := by
  intro t
  have ⟨x, eq⟩ := Quotient.mk_surjective t
  use x, eq

def vRep : vT → { x : ℝ // x ∈ Icc 0 1 } :=
  fun t ↦ Classical.choose (vS_vT_surj t)

lemma vRep_spec : ∀ t : vT, ⟦vRep t⟧ = t :=
  fun t ↦ Classical.choose_spec (vS_vT_surj t)

def vitali_set : Set ℝ := { x : ℝ | ∃ t : vT, ↑(vRep t) = x }

def vI : Set ℝ := Icc (-1) 1 ∩ range ((↑) : ℚ → ℝ)

-- def vI' : Type := { i : ℝ // i ∈ Icc (-1) 1 ∩ range ((↑) : ℚ → ℝ) }

def vitali_set' (i : ℝ) : Set ℝ := image (fun x ↦ x + i) vitali_set

def vitali_union : Set ℝ := ⋃ i ∈ vI, vitali_set' i

lemma vI_countable : vI.Countable := by
  refine Countable.mono inter_subset_right ?_
  apply countable_range

lemma vitali_set_upper_bound : vitali_set ⊆ Icc 0 1 := by
  rintro x ⟨t, ht⟩
  rw [← ht]
  exact (vRep t).property

lemma vitali_union_upper_bound : vitali_union ⊆ Icc (-1) 2 := by
  refine iUnion₂_subset ?_
  intro i
  rw [vI, Set.mem_inter_iff]
  rintro ⟨h0, _⟩
  refine image_subset_iff.mpr ?_
  simp only [preimage_add_const_Icc]
  rw [mem_Icc] at h0
  have h1 : -1 - i ≤ 0 := by linarith
  have h2 : 1 ≤ 2 - i := by linarith
  have : Icc 0 1 ⊆ Icc (-1 - i) (2 - i) := Icc_subset_Icc h1 h2
  exact subset_trans vitali_set_upper_bound this

lemma vitali_union_lower_bound : Icc 0 1 ⊆ vitali_union := by
  intro x h_x1
  have ⟨x', h_x2⟩ : ∃ x' : { x : ℝ // x ∈ Icc 0 1 }, ↑ x' = x := CanLift.prf x h_x1
  let y : ℝ := ↑(vRep ⟦x'⟧)
  have h_y1 : y ∈ Icc 0 1 := (vRep ⟦x'⟧).property
  have h_y2 : y ∈ vitali_set := by simp [vitali_set]
  have h_xy1 : x - y ∈ range ((↑) : ℚ → ℝ) := by
    have eq : vS.r x' (vRep ⟦x'⟧) := by
      refine Quotient.eq.mp ?_
      symm
      apply vRep_spec
    simp only [Setoid.r] at eq
    simpa [← h_x2]
  have h_xy2 : x - y ∈ Icc (-1) 1 := by
    simp only [mem_Icc] at h_x1
    simp only [mem_Icc] at h_y1
    simp only [mem_Icc]
    constructor <;> linarith
  simp only [vitali_union, image_add_right, mem_iUnion, mem_preimage, exists_prop]
  use (x - y)
  constructor
  . rw [vI, mem_inter_iff]
    constructor <;> assumption
  . simpa [vitali_set']

lemma vitali_union_volume_range : 1 ≤ volume vitali_union ∧ volume vitali_union ≤ 3 := by
  have h1 : MeasureTheory.volume (Icc (0 : ℝ) 1) = 1 := by simp [volume_Icc]
  have h2 : MeasureTheory.volume (Icc (-1 : ℝ) 2) = 3 := by simp [volume_Icc] ; norm_num
  constructor
  . rw [← h1]
    exact volume_mono vitali_union_lower_bound
  . rw [← h2]
    exact volume_mono vitali_union_upper_bound

lemma vitali_pairwise_disjoint : vI.PairwiseDisjoint vitali_set' := by
  intro x x_vI y y_vI x_ne_y
  refine Set.disjoint_iff.mpr ?_
  intro z
  simp only [mem_inter_iff, mem_empty_iff_false, imp_false, not_and]
  intro z_x z_y
  simp only [vitali_set', vitali_set, image_add_right, preimage_setOf_eq, mem_setOf_eq] at z_x
  simp only [vitali_set', vitali_set, image_add_right, preimage_setOf_eq, mem_setOf_eq] at z_y
  have ⟨t_x, rep_x⟩ := z_x
  have ⟨t_y, rep_y⟩ := z_y
  have vRep_eq : vS.r (vRep t_x) (vRep t_y) := by
    simp only [vS, mem_range]
    simp only [rep_x, rep_y, add_sub_add_left_eq_sub, sub_neg_eq_add]
    have : x ∈ range ((↑) : ℚ → ℝ) := by exact mem_of_mem_inter_right x_vI
    have ⟨q_x, q_x_eq⟩ := mem_range.mp (mem_of_mem_inter_right x_vI)
    have ⟨q_y, q_y_eq⟩ := mem_range.mp (mem_of_mem_inter_right y_vI)
    use (-q_x + q_y)
    simp [← q_x_eq, ← q_y_eq]
  have vT_eq := Quotient.sound vRep_eq
  simp only [vRep_spec] at vT_eq
  have x_eq_y : x = y := by
    calc x = z - ↑(vRep t_x) := by { simp [rep_x] }
         _ = z - ↑(vRep t_y) := by { simp [vT_eq] }
         _ = y := by { simp [rep_y] }
  contradiction

end

/- ================================================================================================= -/

noncomputable section

variable {α : Type*} [MeasurableSpace α]

example : MeasurableSet (∅ : Set α) :=
  MeasurableSet.empty

example : MeasurableSet (univ : Set α) :=
  MeasurableSet.univ

example {s : Set α} (hs : MeasurableSet s) : MeasurableSet (sᶜ) :=
  hs.compl

example : Encodable ℕ := by infer_instance

example (n : ℕ) : Encodable (Fin n) := by infer_instance

variable {ι : Type*} [Encodable ι]

example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  MeasurableSet.iUnion h

example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b) :=
  MeasurableSet.iInter h

variable {μ : Measure α}

example (s : Set α) : μ s = ⨅ (t : Set α) (_ : s ⊆ t) (_ : MeasurableSet t), μ t :=
  measure_eq_iInf s

example (s : ι → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s

example {f : ℕ → Set α} (hmeas : ∀ i, MeasurableSet (f i)) (hdis : Pairwise (Disjoint on f)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) :=
  μ.m_iUnion hmeas hdis

example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in ae μ, P x :=
  Iff.rfl

/- ================================================================================================= -/

end
