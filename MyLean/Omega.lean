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

section Language

def Concat {X : Type*} (xl : List X) (xs : ℕ → X) : ℕ → X :=
  fun i ↦ if h : i < xl.length then xl[i] else xs (i - xl.length)

def InfOcc {X : Type*} (xs : ℕ → X) : Set X :=
  { s : X | ∃ᶠ i in atTop, xs i = s }

end Language

section Automaton

class Automaton (A : Type*) (S : Type*) where
  init : Set S
  next : S → A → Set S

class DetAutomaton (A : Type*) (S : Type*) extends Automaton A S where
  det_init : init.ncard = 1
  det_next : ∀ s a, (next s a).ncard = 1

variable {A : Type*} {S : Type*}

def FinRun (M : Automaton A S) (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → S) :=
  ss 0 ∈ M.init ∧
  ∀ i : Fin n, ss (i + 1) ∈ M.next (ss i) (as i)

def InfRun (M : Automaton A S) (as : ℕ → A) (ss : ℕ → S) :=
  ss 0 ∈ M.init ∧
  ∀ i : ℕ, ss (i + 1) ∈ M.next (ss i) (as i)

def FinAccept (M : Automaton A S) (acc : Set S) (n : ℕ) (as : Fin n → A) :=
  ∃ ss : Fin (n + 1) → S, FinRun M n as ss ∧ ss n ∈ acc

def BuchiAccept (M : Automaton A S) (acc : Set S) (as : ℕ → A) :=
  ∃ ss : ℕ → S, InfRun M as ss ∧ InfOcc ss ∩ acc ≠ ∅

def MullerAccept (M : Automaton A S) (accSet : Set (Set S)) (as : ℕ → A) :=
  ∃ ss : ℕ → S, InfRun M as ss ∧ ∃ acc ∈ accSet, InfOcc ss = acc

def RabinAccept (M : Automaton A S) (accPairs : Set (Set S × Set S)) (as : ℕ → A) :=
  ∃ ss : ℕ → S, InfRun M as ss ∧ ∃ pair ∈ accPairs, InfOcc ss ∩ pair.1 ≠ ∅ ∧ InfOcc ss ∩ pair.2 = ∅

def StreettAccept (M : Automaton A S) (accPairs : Set (Set S × Set S)) (as : ℕ → A) :=
  ∃ ss : ℕ → S, InfRun M as ss ∧ ∀ pair ∈ accPairs, InfOcc ss ∩ pair.1 ≠ ∅ → InfOcc ss ∩ pair.2 ≠ ∅

def RegularLang (M : Automaton A S) (acc : Set S) : Set (List A) :=
  { al | ∃ n as, FinAccept M acc n as ∧ al = List.ofFn as }

def OmegaRegularLang (M : Automaton A S) (acc : Set S) : Set (ℕ → A) :=
  { as | BuchiAccept M acc as }

end Automaton
