
        /-
        case h.left.left
        A : Type u_1
        I : Type u_2
        M : I → Automaton A
        as : ℕ → A
        ss : ℕ → (i : I) × Automaton.State A
        h_next : ∀ (k : ℕ), ss (k + 1) ∈ Automaton.next (ss k) (as k)
        i : I
        s0 : Automaton.State A
        h_s0_init : s0 ∈ Automaton.init
        h_s0_ss : ⟨i, s0⟩ = ss 0
        ss_i : ℕ → Automaton.State A
        h_init : ⟨i, ss_i 0⟩ ∈ ⋃ i, Sigma.mk i '' Automaton.init
        h_ss_i : ∀ (k : ℕ), ss k = ⟨i, ss_i k⟩
        ⊢ ss_i 0 ∈ Automaton.init
        -/

import Mathlib.Data.Set.Card
import Mathlib.Data.Sigma.Basic

class C where
  T : Type*
  s : Set T

example (I : Type*) (F : I → C) (i : I) (x : (F i).T)
    (h : ⟨i, x⟩ ∈ ⋃ i, Sigma.mk i '' (F i).s) : x ∈ (F i).s := by
  simp only [Set.mem_iUnion, Set.mem_image, Sigma.mk.injEq] at h -- from simp?
  obtain ⟨i, x, hx, rfl, h⟩ := h
  rw [heq_eq_eq] at h
  cases h
  assumption

example (I : Type*) (F : I → C) (i : I) (x : (F i).T)
    (h : ⟨i, x⟩ ∈ Set.univ.sigma (fun i ↦ (F i).s)) : x ∈ (F i).s := by
  simp [Set.mk_sigma_iff] at h
  assumption
