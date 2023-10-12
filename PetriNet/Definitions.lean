import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Basic
import Mathlib.SetTheory.Cardinal.Basic


--Definicion de Redes de Petri
structure PetriNet (α : Type) (β : Type) where
  places : Set α
  transition : Set β
  rel_pt : places →  transition →  Prop
  rel_tp : transition →  places →  Prop
  s₀ : Multiset places
  states : Set.powerset places


variable {α β : Type}
variable {net : PetriNet α β}
notation:1 "(" lhs:1 ", " rhs:1 ")" => 
            (lhs : PetriNet.N) (rhs : PetriNet.s₀)

/-
De ahora en adelante se podrá representar una red de Petri
N como un par (N,m) donde m es el marking (generalmente el inicial)
-/
--#check PetriNet Nat Nat

-- Preset - Poset

def preset_p {n : PetriNet α β} (p : n.places) : Set n.transition  := 
  {t : n.transition | n.rel_tp t p}

def preset_t {n : PetriNet α β} (t : n.transition) : Set n.places  := 
  {p : n.places | n.rel_pt p t}

prefix:1 "•ₚ" => preset_p
prefix:2 "•ₜ" => preset_t

def poset_p {n : PetriNet α β} (p : n.places) : Set n.transition :=
  {t : n.transition | n.rel_tp t p} 

def poset_t {n : PetriNet α β} (t : n.transition) : Set n.places :=
  {p : n.places | n.rel_pt p t}

postfix:1 "•ₚ" => poset_p
postfix:2 "•ₜ" => poset_t
 

def is_initial (n : PetriNet α β) (x : n.places) : Prop :=
  IsEmpty (•ₚ x)

def is_final (n : PetriNet α β) (x : n.places) : Prop :=
  IsEmpty (x •ₚ)

--Se define el conjunto de los estados habilitados

def enable {n : PetriNet α β} (s : Set n.places) (t : n.transition) : Prop :=
 (•ₜ t) ⊆ s ∧ (t •ₜ)∩ s ⊆ (•ₜ t)

 def firing {n : PetriNet α β} (s : Set n.places) (t : n.transition) : Set n.places :=
   (s ∩ (•ₜ t)ᶜ ) ∪ (t •ₜ)

notation:2 lhs:3 "[" rhs:4 "⟩" => firing lhs rhs
