import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.LibrarySearch


--Definicion de Redes de Petri
structure PetriNet (α : Type) (β : Type) where
  places : Finset α
  transition : Finset β
  rel_pt : places →  transition →  Prop
  rel_tp : transition →  places →  Prop
  states : Set places
  s₀ : Set places
  

variable {α β : Type}
--#check PetriNet Nat Nat

-- Preset - Poset

def Relation.image {α β : Type} (r : α →  β →  Prop) (a : α) : Set β :=
    {b : β | r a b}

def Relation.pre_image {α β : Type} (r : α → β → Prop) (b : β) : Set α :=
    {a : α | r a b}

def preset_p {n : PetriNet α β} (p : n.places) : Set n.transition  := 
  Relation.pre_image n.rel_tp p

def preset_t {n : PetriNet α β} (t : n.transition) : Set n.places  := 
  Relation.pre_image n.rel_pt t

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
def enable {n : PetriNet α β} (s : Set n.places) : Set n.transition :=
 {t : n.transition | (•ₜ t) ⊆ s ∧ (t •ₜ)∩ s ⊆ (•ₜ t)}

def deadlock {n : PetriNet α β} (s : Set n.places) : Prop :=
  enable s = ∅ 

--Firing
def firing {n : PetriNet α β} (s : Set n.places) (t : enable (s)) : Set n.places :=
  (Set.diff s (•ₜ t) ) ∪ (t •ₜ)

notation:2 lhs:3 "[" rhs:4 "⟩" => firing lhs rhs

--Sucesion de ejecuciones

/--def firing_seq {n : PetriNet α β} : ℕ →  Set (List ((Set n.places)×(n.transition)×(Set n.places)) )
  | 0   => {[]}                                                       --Lista vacia
  | 1   => {[(s, t, s[t⟩)] | (s : (Set n.places)) (t ∈ enable (s)) } --Estado inicial
  | i+1 => let (_,_,s) := seq[i-1] in
          {seq ++ [(s, t, s[t⟩)] | (seq : firing_seq (i)) (t ∈ enable (s))} --Paso recursivo
[t1,..,tn]
s₀ s₁=s₀[t⟩ .. sn
--/

def Firing {n : PetriNet α β} (s : Set n.places) (T : Set n.transition) : Set n.places :=
  (Set.diff s (Set.sUnion {(•ₜ t) | t∈ T ∩ enable (s)})) ∪  
  (Set.sUnion {(•ₜ t) | t∈ T ∩ enable (s)})

--lemma firing_eq {n : PetriNet α β} (s : Set n.places) (t : enable (s)) : 
--  firing s t = Firing (Set.singleton t.val) := by sorry
