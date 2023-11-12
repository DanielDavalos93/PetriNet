import PetriNet.Definitions
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

--###################
-- Relaciones y conjunto --
variable {α β : Type}

--Flujo de dependencia causal
@[reducible] def flow (N : PetriNet α β) :
    (N.places ⊕  N.transition) →  (N.places ⊕  N.transition) →  Prop
    | Sum.inl p, Sum.inr t  => N.rel_pt p t
    | Sum.inr t, Sum.inl p  => N.rel_tp t p
    | _, _                  => false

--Clausura transitiva
@[reducible] inductive tranClos (r : α →  α →  Prop) : α →  α →  Prop
   | base {x y : α} : r x y →  tranClos r x y
   | step {x y z : α} : r x y →  tranClos r y z →  tranClos r x z

def predecesor {α β : Type} {N : PetriNet α β}
  (x y : N.places ⊕  N.transition) :=
     (tranClos (flow N)) x y

notation:1 l:1 "≺" r:2 => predecesor l r

--###################
--Redes de ocurrencia
def inmediate_conflict {N : PetriNet α β} (t₁ : N.transition) (t₂ : N.transition) :
  Prop :=
    ¬ (Disjoint (•ₜ t₁) (•ₜ t₂))

notation:5 l:5 "#₀" r:6 => inmediate_conflict l r

def conflict {N : PetriNet α β} (x y : N.places ⊕ N.transition) : Prop :=
 ∃ t₁ t₂ : N.transition, (Sum.inr t₁ ≺ x) ∧ (Sum.inr t₂ ≺ y) ∧ (t₁ #₀ t₂)

notation:7 l:7 "#" r:8 => conflict l r

def acyclic (N : PetriNet α β) : Prop :=
  ∀ x : N.places ⊕  N.transition , ¬ (x ≺ x)

def backward_conflicts {N : PetriNet α β} (a : N.places) : Prop :=
  ∃ t₁ t₂ : N.transition, (t₁ ≠ t₂) ∧  (t₁ ∈  (•ₚ a)) ∧  (t₂ ∈  (•ₚ a))

def occurrence_net (N : PetriNet α β) : Prop :=
 acyclic (N) ∧
 is_initial (N.m₀) ∧
 ∀ a : N.places, ¬ (backward_conflicts (a)) ∧
 ∀ t : N.transition, ¬ ((Sum.inr t) # (Sum.inr t))      --No hay autoconflicto

def concurrent {N : PetriNet α β} (x y : N.places ⊕  N.transition) : Prop :=
  x ≠ y ∧  ¬(x ≺ y) ∧  ¬ (y ≺ x) ∧ ¬ (x # y)



lemma coinitial_conc {N : PetriNet α β} (s : Set N.places) (t t' : N.transition) (ho : occurrence_net N) (hen : {t, t'} ⊂  enable (s)) : 
  (concurrent (Sum.inr t) (Sum.inr t') ↔  Disjoint (•ₜ t ) (•ₜ t') ) := by sorry
/-  apply Iff.intro
  . intro himp
    exact 
      have hConfl : ¬ ((Sum.inr t) # (Sum.inr t')) := by sorry
      have hnegConfl : ¬ (t #₀ t') := by exact
      show (Disjoint (•ₜ t) (•ₜ t')) from
        And.right
  . intro himp -/
