/-
Copyright (c) 2024-present Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Perm
--import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Probability.UniformOn

--set_option linter.unusedSectionVars false

--set_option diagnostics true
--set_option diagnostics.threshold 10

open BigOperators Fintype Finset Set MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped ENNReal

section

variable (α : Type*) [Fintype α]

def initSeg (n : ℕ) : Finset (Fin (card α + 1)) := { i | (i : ℕ) < n }

theorem init_seg_subset {n1 n2 : ℕ} (h : n1 ≤ n2) : (initSeg α n1) ⊆ (initSeg α n2) := by
  intro i ; simp [initSeg] ; omega

theorem init_seg_del_last {n : ℕ} (h0 : 0 < n) (h1 : n < card α + 1) :
    (initSeg α n).toSet \ {(n : Fin (card α + 1)) - 1} = initSeg α (n - 1) := by
  ext i
  simp [initSeg,
        ← Nat.cast_pred h0,
        ← Fin.val_eq_val,
        Nat.mod_eq_of_lt (by omega : n - 1 < card α + 1)]
  omega

theorem init_seg_no_last {n : ℕ} (h0 : 0 < n) (h1 : n < card α + 1) :
    ((n : Fin (card α + 1)) - 1) ∉ (initSeg α (n - 1)) := by
  simp [initSeg,
        Nat.mod_eq_of_lt h1,
        ← Nat.cast_pred h0,
        Nat.mod_eq_of_lt (by omega : n - 1 < card α + 1)]

theorem init_seg_add_last {n : ℕ} (h0 : 0 < n) (h1 : n < card α + 1) :
    (initSeg α n).toSet = insert ((n : Fin (card α + 1)) - 1) (initSeg α (n - 1)).toSet := by
  ext i
  simp [initSeg,
        ← Nat.cast_pred h0,
        ← Fin.val_eq_val,
        Nat.mod_eq_of_lt (by omega : n - 1 < card α + 1)]
  omega

variable [DecidableEq α]

abbrev PreNumbering := α → Fin (card α + 1)

def setNumbering (s : Finset α) : Finset (PreNumbering α) :=
  { f | BijOn f s (initSeg α s.card) ∧ ∀ a ∈ sᶜ, (f a : ℕ) = 0 }

private lemma set_numbering_empty : setNumbering α ∅ = {fun _ ↦ 0} := by
  apply Finset.ext ; intro f
  simp [setNumbering, initSeg]
  constructor <;> intro h
  · ext a ; simp [h]
  · intro a ; simp [h]

private def setNumberingLast (s : Finset α) (a : α) : Finset (PreNumbering α) :=
  { f ∈ setNumbering α s | f a = s.card - 1 }

private lemma set_numbering_last_card {s : Finset α} :
    ∀ a ∈ s, (setNumberingLast α s a).card = (setNumbering α (s \ {a})).card := by
  intro a h_as
  have h_s_lb : 0 < s.card := Nonempty.card_pos (nonempty_of_mem h_as)
  have h_s_ub : s.card < card α + 1 := by have := card_le_univ s ; omega
  have h_s_del : (s \ {a}).card = s.card - 1 := card_sdiff (Finset.singleton_subset_iff.mpr h_as)

  let φ (f : PreNumbering α) : PreNumbering α := fun b ↦ if b ∈ s \ {a} then f b else 0
  let ψ (f : PreNumbering α) : PreNumbering α := fun b ↦ if b ∈ s \ {a} then f b else if b = a then s.card - 1 else 0
  have h_φ : ∀ f ∈ (setNumberingLast α s a), φ f ∈ (setNumbering α (s \ {a})) := by
    intro f ; simp [setNumberingLast, setNumbering]
    intro h_bij h_ns h_fa
    constructor
    · rw [h_s_del]
      have h_bij' : BijOn f (↑s \ {a}) ↑(initSeg α (#s - 1)) := by
        have h1 := BijOn.sdiff_singleton h_bij h_as
        have h2 : (initSeg α #s).toSet \ {f a} = initSeg α (s.card - 1) := by
          rw [h_fa]
          exact init_seg_del_last α h_s_lb h_s_ub
        rw [h2] at h1
        assumption
      have h_eq : EqOn f (φ f) (↑s \ {a}) := by
        intro b h_b
        simp at h_b
        simp [φ, h_b]
      exact (EqOn.bijOn_iff h_eq).mp h_bij'
    · intro b h_b
      rcases dec_em (b ∈ s) with h_bs | h_bs
      · simp [φ, h_b h_bs]
      · simp [φ, h_ns b h_bs, h_bs]
  have h_ψ : ∀ f ∈ (setNumbering α (s \ {a})), ψ f ∈ (setNumberingLast α s a) := by
    intro f ; simp [setNumberingLast, setNumbering]
    intro h_bij h_ns
    constructor
    · constructor
      · have h1 : s.toSet = insert a (s.toSet \ {a}) := by
          simp [insert_diff_singleton, Set.insert_eq_of_mem (mem_coe.mpr h_as)]
        have h2 : (initSeg α #s).toSet = insert (ψ f a) ↑(initSeg α #(s \ {a})) := by
          simp [ψ, h_s_del]
          exact init_seg_add_last α h_s_lb h_s_ub
        rw [h1, h2]
        apply BijOn.insert
        · have h_eq : EqOn f (ψ f) (↑s \ {a}) := by
            intro b h_b
            simp at h_b
            simp [ψ, h_b]
          exact (EqOn.bijOn_iff h_eq).mp h_bij
        · simp [ψ, h_s_del]
          exact init_seg_no_last α h_s_lb h_s_ub
      · intro b h_bs
        rcases dec_em (b = a) with h_ba | h_ba
        · simp [h_ba] at h_bs ; contradiction
        · simp [ψ, h_bs, h_ba]
    . simp [ψ]
  have h_ψ_φ : ∀ f ∈ (setNumberingLast α s a), ψ (φ f) = f := by
    intro f ; simp [setNumberingLast, setNumbering]
    intro h_bij h_ns h_fa
    ext b
    rcases dec_em (b ∈ s) with h_bs | h_bs <;> rcases dec_em (b = a) with h_ba | h_ba
    · simp [φ, ψ, h_bs, h_ba, h_fa]
    . simp [φ, ψ, h_bs, h_ba]
    · simp [h_ba] at h_bs ; contradiction
    . simp [φ, ψ, h_bs, h_ba, h_ns]
  have h_φ_ψ : ∀ f ∈ setNumbering α (s \ {a}), φ (ψ f) = f := by
    intro f ; simp [setNumberingLast, setNumbering]
    intro h_bij h_ns
    ext b
    rcases dec_em (b ∈ s) with h_bs | h_bs <;> rcases dec_em (b = a) with h_ba | h_ba
    · have h_ns := h_ns b
      simp [h_ba] at h_ns
      simp [φ, ψ, h_bs, h_ba, h_ns]
    . simp [φ, ψ, h_bs, h_ba]
    · simp [h_ba] at h_bs ; contradiction
    . simp [φ, ψ, h_bs, h_ba, h_ns]

  exact card_nbij' φ ψ h_φ h_ψ h_ψ_φ h_φ_ψ

private lemma set_numbering_last_disj {s : Finset α} {n : ℕ} (h : s.card = n + 1) :
    ∀ a ∈ s, ∀ a' ∈ s, a ≠ a' → Disjoint (setNumberingLast α s a) (setNumberingLast α s a') := by
  intro a h_as a' h_a's h_aa'
  apply Finset.disjoint_left.mpr
  intro f h_fa h_fa'
  simp [setNumberingLast, setNumbering, h] at h_fa h_fa'
  rcases h_fa with ⟨⟨h_fs, _⟩, h_fn⟩
  rcases h_fa' with ⟨_, h_fn'⟩
  rw [← h_fn'] at h_fn
  have := (InjOn.eq_iff (BijOn.injOn h_fs) h_as h_a's ).mp h_fn
  contradiction

private lemma set_numbering_union {s : Finset α} {n : ℕ} (h : s.card = n + 1) :
    setNumbering α s = (s.biUnion (setNumberingLast α s)) := by
  apply Finset.ext ; intro f
  simp [setNumberingLast]
  constructor
  · intro h_fs
    have h_surj : SurjOn f s (initSeg α s.card) := by
      simp [setNumbering] at h_fs
      exact BijOn.surjOn h_fs.1
    rw [SurjOn] at h_surj
    have h_iseg : ↑(s.card - 1) ∈ (initSeg α s.card) := by
      simp [initSeg, h, Fin.val_last]
      have h1 := Finset.card_le_univ s
      simp [h] at h1
      have h2 : n % (Fintype.card α + 1) = n := by
        apply Nat.mod_eq_of_lt
        omega
      omega
    have h_last := h_surj h_iseg
    simp at h_last
    rcases h_last with ⟨a, h_as, h_fa⟩
    use a
    simp [h_as, h_fs, h_fa, h]
  · rintro ⟨a, h_as, h_fs, _⟩
    exact h_fs

theorem set_numbering_card (s : Finset α) :
    (setNumbering α s).card = s.card.factorial := by
  generalize h : s.card = n
  induction' n with n ih generalizing s
  · rw [Finset.card_eq_zero] at h
    simp [h]
    apply Finset.card_eq_one.mpr
    use (fun _ ↦ 0)
    exact set_numbering_empty α
  have ih' : ∀ a ∈ s, (setNumbering α (s \ {a})).card = n.factorial := by
    intro a h_mem
    have h_diff := card_sdiff (Finset.singleton_subset_iff.mpr h_mem)
    simp [h] at h_diff
    exact ih (s \ {a}) h_diff
  simp [set_numbering_union α h, card_biUnion (set_numbering_last_disj α h),
        Finset.sum_congr (rfl : s = s) (set_numbering_last_card α),
        Finset.sum_congr (rfl : s = s) ih',
        Finset.sum_const n.factorial, h, Nat.factorial_succ]

def setNumberingPrefix (s t : Finset α) : Finset (PreNumbering α) :=
  { f ∈ setNumbering α s | BijOn f t (initSeg α t.card) }

theorem set_numbering_prefix_subset {s t1 t2 : Finset α} {f : PreNumbering α}
    (h_t1 : t1 ⊆ s) (h_t2 : t2 ⊆ s) (h_f1 : f ∈ setNumberingPrefix α s t1) (h_f2 : f ∈ setNumberingPrefix α s t2)
    (h_card : t1.card ≤ t2.card) : t1 ⊆ t2 := by
  intro a h_at1
  simp [setNumberingPrefix, setNumbering] at h_f1 h_f2
  have h_fa2 := h_f2.2.2.2 (init_seg_subset α h_card (h_f1.2.1 h_at1))
  rcases h_f2.2.2.2 (init_seg_subset α h_card (h_f1.2.1 h_at1)) with ⟨b, h_bt2, h_fba⟩
  have h_ba := h_f1.1.1.2.1 (h_t2 h_bt2) (h_t1 h_at1) h_fba
  simp [← h_ba] ; assumption

theorem set_numbering_prefix_card {s t : Finset α} (h_ts : t ⊆ s) :
    (setNumberingPrefix α s t).card = t.card.factorial * (s.card - t.card).factorial := by
  have h_equiv : (setNumberingPrefix α s t).card = ((setNumbering α t) ×ˢ (setNumbering α (s \ t))).card := by
    let φ (f : PreNumbering α) : (PreNumbering α) × (PreNumbering α) := (f, f)

    have h_φ : ∀ f ∈ (setNumberingPrefix α s t), φ f ∈ ((setNumbering α t) ×ˢ (setNumbering α (s \ t))) := by
      sorry

    sorry
  have h_prod := Finset.card_product (setNumbering α t) (setNumbering α (s \ t))
  rw [h_equiv, h_prod, set_numbering_card α t, set_numbering_card α (s \ t), card_sdiff h_ts]

/-- **************************************************************************************************** -/

def Numbering := α ≃ Fin (card α)

instance : Fintype (Numbering α) := Equiv.instFintype

theorem numbering_card : card (Numbering α) = (card α).factorial := by
  exact Fintype.card_equiv (Fintype.equivFinOfCardEq rfl)

def setPrefix (s : Finset α) : Finset (Numbering α) :=
  { p : Numbering α | ∀ a : α, a ∈ s ↔ p.toFun a < s.card }

theorem set_prefix_subset {s t : Finset α} {p : Numbering α} (h_s : p ∈ setPrefix α s) (h_t : p ∈ setPrefix α t)
    (h_st : s.card ≤ t.card) : s ⊆ t := by
  intro a h_as
  simp [setPrefix] at h_s h_t
  exact (h_t a).mpr (lt_of_le_of_lt' h_st ((h_s a).mp h_as))

theorem set_prefix_card (s : Finset α) :
    (setPrefix α s).card = s.card.factorial * (card α - s.card).factorial := by
  sorry

instance : MeasurableSpace (Numbering α) := ⊤
instance : MeasurableSingletonClass (Numbering α) := ⟨fun _ => trivial⟩

lemma set_prefix_count (s : Finset α) :
    count (setPrefix α s).toSet = ↑(s.card.factorial * (card α - s.card).factorial) := by
  rw [← set_prefix_card α s, count_apply_finset]

lemma aux_1 {k m n : ℕ} (hn : 0 < n) (heq : k * m = n) :
    (↑ m : ENNReal) / (↑ n : ENNReal) = 1 / (↑ k : ENNReal) := by
  -- The following proof is due to Aaron Liu.
  subst heq
  have hm : m ≠ 0 := by rintro rfl ; simp at hn
  have hk : k ≠ 0 := by rintro rfl ; simp at hn
  refine (ENNReal.toReal_eq_toReal ?_ ?_).mp ?_
  · intro h
    apply_fun ENNReal.toReal at h
    simp [hm, hk] at h
  · intro h
    apply_fun ENNReal.toReal at h
    simp [hk] at h
  · field_simp
    ring

theorem set_prefix_prob (s : Finset α) :
    uniformOn Set.univ (setPrefix α s).toSet = 1 / (card α).choose s.card := by
  rw [uniformOn_univ, set_prefix_count, numbering_card]
  apply aux_1 (Nat.factorial_pos (card α))
  rw [← mul_assoc]
  exact Nat.choose_mul_factorial_mul_factorial (Finset.card_le_univ s)

theorem set_prefix_disj {s t : Finset α} (h_st : ¬ s ⊆ t) (h_ts : ¬ t ⊆ s) :
    Disjoint (setPrefix α s).toSet (setPrefix α t).toSet := by
  refine Set.disjoint_iff.mpr ?_
  intro p
  simp only [mem_inter_iff, Finset.mem_coe, mem_empty_iff_false, imp_false, not_and]
  intro h_s h_t
  rcases Nat.le_total s.card t.card with h_st' | h_ts'
  · exact h_st (set_prefix_subset α h_s h_t h_st')
  · exact h_ts (set_prefix_subset α h_t h_s h_ts')

variable (𝓐 : Finset (Finset α))

theorem LYM_inequality (h𝓐 : IsAntichain (· ⊆ ·) (𝓐 : Set (Finset α))) :
    ∑ s ∈ 𝓐, ((1 : ℝ) / (card α).choose s.card) ≤ 1 := by
  sorry

end
