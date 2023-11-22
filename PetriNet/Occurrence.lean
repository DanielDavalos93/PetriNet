import PetriNet.Definitions
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

/-
This file provides the definitions and properties necessary to construct a flow 
relationship in a Petri net. Which is necessary to establish occurrence nets.

A flow `≺ ` [abr: \prec] is a relationship between places and transitions directly. 
Their transitive closure `≼ ` [abr: \preceq] is given by `tranClos` and his construction 
by `predecesor`. 

A net (N,m₀) could be think as a tuple (P,T,•N,N•,m₀) and N = P ⊎ T. This is helpful at 
time to defined the flow relationship, because we can have x,y ∈ N with x ≼ y (for 
instance) regardless of whether x and y are the same type or not. This disjoint union
I write as `places ⊕ transition`.

  * If N is a `PetriNet α β`, and you want to write that x ≺ y, we need to know if x, y 
are places or transitions. 
  For example, if `x : N.transition` and `y : N.places`, then x ≺  y is equivalent to 
  `Sum.inr x ≺ Sum.inl y`. Is not necessary that x and y have different types, we can 
  have `x y : N.transition` and `Sum.inr x ≺ Sum.inr y`, since is a transitive closure. 
  Trichotomy is not true over this transitive closure.
  * If two transitions t₁ and t₂ are in inmediate conflict: `t₁ #₀ t₂`.
  * If x and y are in conflict: `x # y`. This is an extend definition from the inmediate 
  conflict.
  * `x co y` is an abreviature if x and y are concurrents.
  * `CO X` is an abreviature if ∀ x y ∈  X, x co y.
-/

variable {α β : Type}


--Flujo de dependencia causal
@[reducible] def flow (N : PetriNet α β) :
    (N.places ⊕  N.transition) →  (N.places ⊕  N.transition) →  Prop
    | Sum.inl p, Sum.inr t  => N.rel_pt p t
    | Sum.inr t, Sum.inl p  => N.rel_tp t p
    | _, _                  => false

notation:1 l:1 "≺ " r:2 => flow _ l r

--Clausura transitiva
@[reducible] inductive tranClos (r : α →  α →  Prop) : α →  α →  Prop
   | base {x y : α} : r x y →  tranClos r x y
   | step {x y z : α} : r x y →  tranClos r y z →  tranClos r x z

@[reducible] def predecesor {α β : Type} {N : PetriNet α β}
  (x y : N.places ⊕  N.transition) :=
     (tranClos (flow N)) x y

notation:3 l:3 "≼ " r:4 => predecesor l r
 
 
lemma direct_flow {N : PetriNet α β}
  {inlN : N.places →  N.places ⊕ N.transition}
  {inrN : N.transition →  N.places ⊕ N.transition}
  (p : N.places) (t : N.transition) (h : N.rel_pt p t) : ((inlN p) ≼  (inrN t)) := by sorry
--    tranClos.step _


def inmediate_conflict {N : PetriNet α β} (t₁ : N.transition) (t₂ : N.transition) :
  Prop :=
    ¬ (Disjoint (•ₜ t₁) (•ₜ t₂))

notation:5 l:5 "#₀" r:6 => inmediate_conflict l r


def conflict {N : PetriNet α β} (x : N.places ⊕ N.transition) (y : N.places ⊕ N.transition) : Prop :=
 ∃ t₁ t₂ : N.transition, (Sum.inr t₁ ≼  x) ∧ (Sum.inr t₂ ≼  y) ∧ (t₁ #₀ t₂)

notation:7 l:7 "#" r:8 => conflict l r

/- 
Because `≼ ` is transitive, for `x : N.places ⊕ N.transition`, suppose we have a sequence
of this relation x ≼ x₁ ≼ ...≼ xₙ. If there is i≤ n such that xᵢ= x we call this property
cyclic. Otherwise (there is not i such that xᵢ=x ) we call it acyclical.
-/

def acyclic (N : PetriNet α β) : Prop :=
  ∀ x : N.places ⊕  N.transition , ¬ (x ≼ x)

def backward_conflicts {N : PetriNet α β} (a : N.places) : Prop :=
  ∃ t₁ t₂ : N.transition, (t₁ ≠ t₂) ∧  (t₁ ∈  (•ₚ a)) ∧  (t₂ ∈  (•ₚ a))

--Occurrence net
def occurrence_net (N : PetriNet α β) : Prop :=
 acyclic (N) ∧
 (∀ t : N.transition, ¬ ((Sum.inr t) # (Sum.inr t))) ∧     --No hay autoconflicto
 is_initial (N.m₀) ∧
 (∀ a : N.places, ¬ (backward_conflicts (a))) 

/- 
The idea of the concurrent definition is that there is no conflict in the entire flow 
relationship path (i.e. a conflict between two transitions affects their predecessors).
-/
def concurrent {N : PetriNet α β} (x : N.places ⊕  N.transition) (y : N.places ⊕ N.transition) : Prop :=
  (x ≠ y ∧  ¬(x ≼  y) ∧  ¬ (y ≼  x)) ∧ ¬ (x # y)

notation:9 l:9 "co" r:10 => concurrent l r

def concurrent_set {N : PetriNet α β} (X : Set (N.places ⊕ N.transition)) : Prop :=
  ∀ x y : X, x.val co y.val

notation:11 "CO" var:11 => concurrent_set var

theorem coinitial_conc {N : PetriNet α β} (s : Set N.places) (t t' : N.transition) (ho : occurrence_net N) (hen : {t, t'} ⊂  enable (s)) (hconc : concurrent (Sum.inr t) (Sum.inr t')) : Disjoint (•ₜ t ) (•ₜ t') := by
  by_cases h : Disjoint (•ₜ t) (•ₜ t')
  . apply h
  . have h₁ : ¬ (conflict (Sum.inr t) (Sum.inr t')) := (hconc.right)
    have h₂ : ¬ (t #₀ t') := by sorry
    exact absurd h h₂
