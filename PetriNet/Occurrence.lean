import PetriNet.Definitions
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

--Redes de ocurrencia
def conflict {n : PetriNet α β} (t₁ : n.transition) (t₂ : n.transition) : Prop :=
  (•ₜ t₁) ∩ (•ₜ t₂) = ∅ 

notation:5 l:5 "#" r:6 => conflict l r

def acyclic (n : PetriNet α β) : Prop :=
  ∀ p : n.places, (•ₚ p) ∩ (p •ₚ) = ∅ 

def backward_conflicts {n : PetriNet α β} (a : n.places) : Prop :=
  ∃ t₁ t₂ : n.transition, (t₁ ≠ t₂) ∧  (t₁ ∈  (•ₚ a)) ∧  (t₂ ∈  (•ₚ a))

def occurrence_net (n : PetriNet α β) : Prop :=
 acyclic (n) ∧ 
 ∀ x : n.s₀, is_initial (n) (x) ∧ 
 ∀ a : n.places, ¬ (backward_conflicts (a)) ∧
 ∀ t : n.transition, ¬ (t#t)      --No hay autoconflicto

def concurrent {n : PetriNet α β} (x y : n.places ⊕  n.transition) : Prop :=
  x ≠ y 

lemma coinitial_conc {n : PetriNet α β} (occurrence_net n) : ∀ t t' : en (n.s₀), cocurrent t t' ↔  (•ₜ t)∩ (•ₜ t') = ∅ := sorry
