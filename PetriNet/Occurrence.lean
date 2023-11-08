import PetriNet.Definitions
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

-- Relaciones --

--Flujo de dependencia causal
def flow {α β : Type} (N : PetriNet α β) : 
    (N.places ⊕  N.transition) →  (N.places ⊕  N.transition) →  Prop 
    | Sum.inl p, Sum.inr t  => N.rel_pt p t
    | Sum.inr t, Sum.inl p  => N.rel_tp t p 
    | _, _                  => false

--Clausura transitiva
inductive tranClos {α : Type} (r : α →  α →  Prop) : α →  α →  Prop
   | base {x y : α} : r x y →  tranClos r x y
   | step {x y z : α} : r x y →  tranClos r y z →  tranClos r x z

def predecesor {α β : Type} {N : PetriNet α β} 
  (x y : N.places ⊕  N.transition) :=
     (tranClos (flow N)) x y

notation:1 l:1 "≺" r:2 => predecesor l r

--###################
--Redes de ocurrencia
def conflict {N : PetriNet α β} (t₁ : N.transition) (t₂ : N.transition) : 
  Prop := 
    ¬ (Disjoint (•ₜ t₁) (•ₜ t₂))

notation:5 l:5 "#" r:6 => conflict l r

def acyclic (N : PetriNet α β) : Prop :=
  ∀ x : N.places ⊕  N.transition , ¬ (x ≺ x)

def backward_conflicts {N : PetriNet α β} (a : N.places) : Prop :=
  ∃ t₁ t₂ : N.transition, (t₁ ≠ t₂) ∧  (t₁ ∈  (•ₚ a)) ∧  (t₂ ∈  (•ₚ a))

def occurrence_net (N : PetriNet α β) : Prop :=
 acyclic (N) ∧ 
 ∀ x : N.m₀, is_initial (N) (x) ∧ 
 ∀ a : N.places, ¬ (backward_conflicts (a)) ∧
 ∀ t : N.transition, ¬ (t#t)      --No hay autoconflicto


def concurrent {N : PetriNet α β} (x y : N.places ⊕  N.transition) : Prop :=
  x ≠ y ∧  ¬(x ≺ y) ∧  ¬ (y ≺ x) 

lemma coinitial_conc {α β : Type} {N : PetriNet α β} (occurrence_net N) 
  : ∀ t t' : enable (N.m₀), concurrent t t' ↔  (•ₜ t) ∩ (•ₜ t') = ∅  := sorry
