/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Filter.ATTopBot.Basic

open Filter

section Automaton

def Concat {X : Type*} (xl : List X) (xs : ℕ → X) : ℕ → X :=
  fun i ↦ if i < xl.length then xl[i]'(by sorry) else xs (i - xl.length)

def Concat' {X : Type*} (xl : List X) (xs : ℕ → X) : ℕ → X :=
  match xl with
  | [] => xs
  | x :: tl => fun i ↦ if i = 0 then x else Concat' tl xs (i - 1)

class Automaton (A : Type*) (S : Type*) where
  init : Set S
  next : S → A → Set S

class DeterministicAutomaton (A : Type*) (S : Type*) extends Automaton A S where
  det_init : init.ncard = 1
  det_next : ∀ s a, (next s a).ncard = 1

def InfiniteOcc {S : Type*} (ss : ℕ → S) : Set S :=
  { s : S | ∃ᶠ i in atTop, ss i = s }

variable {A : Type*} {S : Type*}

def FiniteRun (M : Automaton A S) (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → S) :=
  ss 0 ∈ M.init ∧
  ∀ i : Fin n, ss (i + 1) ∈ M.next (ss i) (as i)

def InfiniteRun (M : Automaton A S) (as : ℕ → A) (ss : ℕ → S) :=
  ss 0 ∈ M.init ∧
  ∀ i : ℕ, ss (i + 1) ∈ M.next (ss i) (as i)

def FiniteAccept (M : Automaton A S) (acc : Set S) (n : ℕ) (as : Fin n → A) :=
  ∃ ss : Fin (n + 1) → S, FiniteRun M n as ss ∧ ss n ∈ acc

def BuchiAccept (M : Automaton A S) (acc : Set S) (as : ℕ → A) :=
  ∃ ss : ℕ → S, InfiniteRun M as ss ∧ InfiniteOcc ss ∩ acc ≠ ∅

def MullerAccept (M : Automaton A S) (accSet : Set (Set S)) (as : ℕ → A) :=
  ∃ ss : ℕ → S, InfiniteRun M as ss ∧ ∃ acc ∈ accSet, InfiniteOcc ss = acc

def RabinAccept (M : Automaton A S) (accPairs : Set (Set S × Set S)) (as : ℕ → A) :=
  ∃ ss : ℕ → S, InfiniteRun M as ss ∧ ∃ pair ∈ accPairs, InfiniteOcc ss ∩ pair.1 ≠ ∅ ∧ InfiniteOcc ss ∩ pair.2 = ∅

def StreettAccept (M : Automaton A S) (accPairs : Set (Set S × Set S)) (as : ℕ → A) :=
  ∃ ss : ℕ → S, InfiniteRun M as ss ∧ ∀ pair ∈ accPairs, InfiniteOcc ss ∩ pair.1 ≠ ∅ → InfiniteOcc ss ∩ pair.2 ≠ ∅

def Regular (L : Set (List A)) :=
  ∃ S : Type*, ∃ M : Automaton A S, ∃ acc : Set S, L = { al | ∃ n as, FiniteAccept M acc n as ∧ al = List.ofFn as }

def OmegaRegular (L : Set (ℕ → A)) :=
  ∃ S : Type*, ∃ M : Automaton A S, ∃ acc : Set S, L = { as | BuchiAccept M acc as }

end Automaton
