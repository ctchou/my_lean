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
TO DO
-/

open Set Filter Real MeasureTheory

noncomputable section

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

end
