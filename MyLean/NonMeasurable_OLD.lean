/-
Copyright (c) 2024-present Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou <chingtsun.chou@gmail.com>
-/

import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Batteries.Tactic.Instances
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

set_option warningAsError false

/-!
# Vitali set and its non-measurability

This file defines the Vitali set and proves that it is not measurable.
The proof is essentially the one in Wikipedia:

## References

* <https://en.wikipedia.org/wiki/Vitali_set>
-/

open Set Filter Real MeasureTheory

noncomputable section

/-- We first list the measure theoretic results that we need and specialize them to the measure `volume` on the reals. -/

example {a b : ℝ} : volume (Icc a b) = ENNReal.ofReal (b - a) :=
  volume_Icc

lemma volume_mono {s t : Set ℝ} (h : s ⊆ t) : volume s ≤ volume t := by
  exact OuterMeasureClass.measure_mono volume h

lemma shift_volume (s : Set ℝ) (c : ℝ) : volume ((fun x ↦ x + c)''s) = volume s := by
  simp only [image_add_right, measure_preimage_add_right]

lemma shift_measurable {s : Set ℝ} (h : MeasurableSet s) (c : ℝ) : MeasurableSet ((fun x ↦ x + c)''s) := by
  apply (MeasurableEmbedding.measurableSet_image ?_).mpr h
  exact measurableEmbedding_addRight c

lemma union_volume {s t : Set ℝ} (hd : Disjoint s t) (h : MeasurableSet s) : volume (s ∪ t) = volume s + volume t :=
    measure_union' hd h

lemma biUnion_measurable {ι : Type*} {I : Set ι} {f : ι → Set ℝ}
    (hs : I.Countable) (hm : ∀ i ∈ I, MeasurableSet (f i)) : MeasurableSet (⋃ i ∈ I, f i) :=
  MeasurableSet.biUnion hs hm

lemma biUnion_volume {ι : Type*} {I : Set ι} {f : ι → Set ℝ}
    (hs : I.Countable) (hd : I.PairwiseDisjoint f) (hm : ∀ i ∈ I, MeasurableSet (f i)) :
    volume (⋃ i ∈ I, f i) = ∑' (i : ↑I), volume (f ↑i) :=
  measure_biUnion hs hd hm

lemma biUnion_zero {ι : Type*} {I : Set ι} {f : ι → Set ℝ}
    (hs : I.Countable) : volume (⋃ i ∈ I, f i) = 0 ↔ ∀ i ∈ I, volume (f i) = 0 :=
  measure_biUnion_null_iff hs

lemma measurable_nullmeasurable {s : Set ℝ} (h : MeasurableSet s) : NullMeasurableSet s volume :=
  MeasurableSet.nullMeasurableSet h

lemma nullmeasurable_measurable {s : Set ℝ} (h : NullMeasurableSet s volume) :
    ∃ t ⊆ s, MeasurableSet t ∧ volume t = volume s ∧ volume (s \ t) = 0 := by
  have ⟨t, t_sub_s, t_m, t_eq_s⟩ := NullMeasurableSet.exists_measurable_subset_ae_eq h
  use t, t_sub_s, t_m
  constructor
  . exact measure_congr t_eq_s
  . refine ae_le_set.mp ?_
    exact t_eq_s.symm.le

/-- We also need some results about sets and functions. -/

lemma biUnion_image_split {ι α : Type*} {I : Set ι} {s t : Set α} {f : ι → α → α}
    (h : t ⊆ s) : ⋃ i ∈ I, (f i)''s = (⋃ i ∈ I, (f i)''t) ∪ (⋃ i ∈ I, (f i)''(s \ t)) := by
  apply subset_antisymm
  . intro a
    rw [mem_union, mem_iUnion₂]
    rintro ⟨i, i_I, a_fi⟩
    rw [← union_diff_cancel h, image_union, mem_union] at a_fi
    rcases a_fi with h_t | h_nt
    . left ; rw [mem_iUnion₂] ; use i, i_I
    . right ; rw [mem_iUnion₂] ; use i, i_I
  . apply union_subset <;> apply biUnion_mono (subset_refl I) <;> intro i _
    . exact image_mono h
    . refine image_mono ?_
      exact diff_subset

lemma biUnion_image_disjoint {ι α : Type*} {I : Set ι} {s t : Set α} {f : ι → α → α}
    (h : t ⊆ s) (hi : ∀ i ∈ I, (f i).Injective) (hd : I.PairwiseDisjoint (fun i ↦ (f i)''s)) :
    Disjoint (⋃ i ∈ I, (f i)''t) (⋃ i ∈ I, (f i)''(s \ t)) := by
  rw [Set.disjoint_left]
  intro a
  rw [mem_iUnion₂] ; rintro ⟨i, i_I, a_fi⟩
  rw [mem_iUnion₂] ; rintro ⟨j, j_I, a_fj⟩
  rcases eq_or_ne i j with h_eq | h_ne
  . rw [mem_image] at a_fi a_fj
    rcases a_fi with ⟨x, x_t, x_a⟩
    rcases a_fj with ⟨y, y_nt, y_a⟩
    have h_ij : f i x = f j y := by rw [x_a, y_a]
    rw [← h_eq] at h_ij
    have h_xy := hi i i_I h_ij
    rw [← h_xy, mem_diff] at y_nt
    tauto
  . have a_fi_s : a ∈ (f i)''s := image_mono h a_fi
    have a_fj_s : a ∈ (f j)''s := image_mono diff_subset a_fj
    have := Set.disjoint_iff.mp (hd i_I j_I h_ne) (mem_inter a_fi_s a_fj_s)
    exact not_mem_empty a this

/-- In the setoid vS, two reals in the interval [0,1] are equivalent iff their difference is rational. -/

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

/-- Make a quotient type vT from the setoid vS. -/

def vT : Type := Quotient vS

lemma vS_vT_surj : ∀ t : vT, ∃ x : { x : ℝ // x ∈ Icc 0 1 }, ⟦x⟧ = t := by
  intro t
  have ⟨x, eq⟩ := Quotient.mk_surjective t
  use x, eq

/-- Use Classical.choose to make a function vRep from vT to vS. -/

def vRep : vT → { x : ℝ // x ∈ Icc 0 1 } :=
  fun t ↦ Classical.choose (vS_vT_surj t)

lemma vRep_spec : ∀ t : vT, ⟦vRep t⟧ = t :=
  fun t ↦ Classical.choose_spec (vS_vT_surj t)

/-- The image of vRep is the Vitali set. -/

def vitaliSet : Set ℝ := { x : ℝ | ∃ t : vT, ↑(vRep t) = x }

/-- We now shift the Vitali set using rational numbers in the interval [-1,1]. -/

def vI : Set ℝ := Icc (-1) 1 ∩ range ((↑) : ℚ → ℝ)

def vitaliSet' (i : ℝ) : Set ℝ := (fun x ↦ x + i)''vitaliSet

/-- Take the union of all those shifts. -/

def vitaliUnion : Set ℝ := ⋃ i ∈ vI, vitaliSet' i

/-- We now prove some results about the Vitali set and its shifts. -/

lemma vitaliSet_upper_bound : vitaliSet ⊆ Icc 0 1 := by
  rintro x ⟨t, ht⟩
  rw [← ht]
  exact (vRep t).property

lemma vitaliUnion_upper_bound : vitaliUnion ⊆ Icc (-1) 2 := by
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
  exact subset_trans vitaliSet_upper_bound this

lemma vitaliUnion_lower_bound : Icc 0 1 ⊆ vitaliUnion := by
  intro x h_x1
  have ⟨x', h_x2⟩ : ∃ x' : { x : ℝ // x ∈ Icc 0 1 }, ↑ x' = x := CanLift.prf x h_x1
  let y : ℝ := ↑(vRep ⟦x'⟧)
  have h_y1 : y ∈ Icc 0 1 := (vRep ⟦x'⟧).property
  have h_y2 : y ∈ vitaliSet := by simp [vitaliSet]
  have h_xy1 : x - y ∈ range ((↑) : ℚ → ℝ) := by
    have eq : vS.r x' (vRep ⟦x'⟧) := by
      refine Quotient.eq.mp ?_
      symm
      apply vRep_spec
    simp only [Setoid.r] at eq
    simpa [← h_x2]
  have h_xy2 : x - y ∈ Icc (-1) 1 := by
    simp only [mem_Icc] at h_x1 h_y1 ⊢
    constructor <;> linarith
  simp only [vitaliUnion, image_add_right, mem_iUnion, mem_preimage, exists_prop]
  use (x - y)
  constructor
  . rw [vI, mem_inter_iff]
    constructor <;> assumption
  . simpa [vitaliSet']

lemma vitaliUnion_volume_range : 1 ≤ volume vitaliUnion ∧ volume vitaliUnion ≤ 3 := by
  have h1 : MeasureTheory.volume (Icc (0 : ℝ) 1) = 1 := by simp [volume_Icc]
  have h2 : MeasureTheory.volume (Icc (-1 : ℝ) 2) = 3 := by simp [volume_Icc] ; norm_num
  constructor
  . rw [← h1]
    exact volume_mono vitaliUnion_lower_bound
  . rw [← h2]
    exact volume_mono vitaliUnion_upper_bound

lemma vitali_pairwise_disjoint : vI.PairwiseDisjoint vitaliSet' := by
  intro x x_vI y y_vI x_ne_y
  refine Set.disjoint_iff.mpr ?_
  intro z
  simp only [mem_inter_iff, mem_empty_iff_false, imp_false, not_and]
  intro z_x z_y
  simp only [vitaliSet', vitaliSet, image_add_right, preimage_setOf_eq, mem_setOf_eq] at z_x
  simp only [vitaliSet', vitaliSet, image_add_right, preimage_setOf_eq, mem_setOf_eq] at z_y
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

lemma vI_countable : vI.Countable := by
  refine Countable.mono inter_subset_right ?_
  apply countable_range

lemma vitaliUnion_volume_sum (hm : NullMeasurableSet vitaliSet volume) :
    volume vitaliUnion = ∑' (_ : ↑vI), volume vitaliSet := by
  have ⟨t, t_s, t_m, t_v, t_c⟩ := nullmeasurable_measurable hm
  let shift : ℝ → ℝ → ℝ := fun i ↦ fun x ↦ x + i
  have hi : ∀ i ∈ vI, vitaliSet' i = (shift i)''t ∪ (shift i)''(vitaliSet \ t) := by
    intro i i_vI
    rw [vitaliSet', ← image_union, union_diff_cancel t_s]
  have hu : vitaliUnion = (⋃ i ∈ vI, (shift i)''t) ∪ (⋃ i ∈ vI, (shift i)''(vitaliSet \ t)) := by
    exact biUnion_image_split t_s
  have hd : Disjoint (⋃ i ∈ vI, (shift i)''t) (⋃ i ∈ vI, (shift i)''(vitaliSet \ t)) := by
    have inj : ∀ i ∈ vI, (shift i).Injective := by
      intro i _ x y
      simp [shift]
    exact biUnion_image_disjoint t_s inj vitali_pairwise_disjoint
  let f : ℝ → Set ℝ := fun i ↦ (shift i)''t
  have hpd : vI.PairwiseDisjoint f := by
    refine PairwiseDisjoint.mono vitali_pairwise_disjoint ?_
    intro i
    unfold f vitaliSet'
    exact image_mono t_s
  have hm' : ∀ i ∈ vI, MeasurableSet (f i) := by
    intro i i_vI
    unfold f
    apply shift_measurable t_m
  have htv : volume (⋃ i ∈ vI, (shift i)''t) = ∑' (_ : ↑vI), volume vitaliSet := by
    rw [biUnion_volume vI_countable hpd hm']
    refine tsum_congr ?_
    intro i
    unfold f
    rw [shift_volume]
    assumption
  have htz : volume (⋃ i ∈ vI, (shift i)''(vitaliSet \ t)) = 0 := by
    rw [biUnion_zero vI_countable]
    intro i _
    rw [shift_volume]
    assumption
  have htm : MeasurableSet (⋃ i ∈ vI, (shift i)''t) := by
    exact biUnion_measurable vI_countable hm'
  rw [hu, union_volume hd htm, htv, htz, add_zero]

lemma vI_infinite : vI.Infinite := by
  let f : ℕ → ℝ := fun n ↦ 1 / (n + 1)
  have f_inj : f.Injective := by { intro m n ; simp [f] }
  have f_rng_inf : (range f).Infinite := infinite_range_of_injective f_inj
  refine Set.Infinite.mono ?_ f_rng_inf
  apply range_subset_iff.mpr
  intro n
  simp [f, vI]
  constructor
  . simp only [inv_eq_one_div]
    have h1 : (0 : ℝ) < ↑n + 1 := by
      have : (0 : ℝ) ≤ ↑n := Nat.cast_nonneg n
      linarith
    constructor
    . rw [le_div_iff₀' h1]
      linarith
    . rw [div_le_iff₀' h1]
      linarith
  . use ((↑ n + 1)⁻¹)
    simp

/-- The following theorems are the main results. -/

theorem vitaliSet_not_nullmeasurable : ¬ (NullMeasurableSet vitaliSet volume) := by
  intro hm
  rcases eq_or_ne (volume vitaliSet) 0 with hz | hnz
  . have hv : volume vitaliUnion = 0 := by
      rw [vitaliUnion_volume_sum hm, hz, tsum_zero]
    have := vitaliUnion_volume_range.1
    simp [hv] at this
  . have hv : volume vitaliUnion = ⊤ := by
      rw [vitaliUnion_volume_sum hm]
      have : Infinite ↑vI := vI_infinite.to_subtype
      exact ENNReal.tsum_const_eq_top_of_ne_zero hnz
    have := vitaliUnion_volume_range.2
    simp [hv] at this

theorem vitaliSet_not_measurable : ¬ (MeasurableSet vitaliSet) := by
  intro hm
  exact vitaliSet_not_nullmeasurable (measurable_nullmeasurable hm)

/-- The following two results show that `vitaliSet_not_measurable` cam be proved more directly
    than via `vitaliSet_not_nullmeasurable`.  The difference is the stronger assumption
    `MeasurableSet vitaliSet` in `vitaliUnion_volume_sum'`. -/

lemma vitaliUnion_volume_sum' (hm : MeasurableSet vitaliSet) :
    volume vitaliUnion = ∑' (_ : ↑vI), volume vitaliSet := by
  have hm' : ∀ i ∈ vI, MeasurableSet (vitaliSet' i) := by
    intro i i_vI
    rw [vitaliSet']
    apply shift_measurable hm
  rw [vitaliUnion, biUnion_volume vI_countable vitali_pairwise_disjoint hm']
  refine tsum_congr ?_
  intro i
  rw [vitaliSet', shift_volume]

theorem vitaliSet_not_measurable' : ¬ (MeasurableSet vitaliSet) := by
  intro hm
  rcases eq_or_ne (volume vitaliSet) 0 with hz | hnz
  . have hv : volume vitaliUnion = 0 := by
      rw [vitaliUnion_volume_sum' hm, hz, tsum_zero]
    have := vitaliUnion_volume_range.1
    simp [hv] at this
  . have hv : volume vitaliUnion = ⊤ := by
      rw [vitaliUnion_volume_sum' hm]
      have : Infinite ↑vI := vI_infinite.to_subtype
      exact ENNReal.tsum_const_eq_top_of_ne_zero hnz
    have := vitaliUnion_volume_range.2
    simp [hv] at this

end
