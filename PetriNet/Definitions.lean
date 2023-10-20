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
  s₀ : states
  

variable {α β : Type}
variable {net : PetriNet α β}
notation:1 "(" lhs:1 ", " rhs:1 ")" => 
            (lhs : PetriNet.places ⊕ PetriNet.transition) (rhs : PetriNet.s₀)

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
def enable {n : PetriNet α β} (s : Set n.places) : Set n.transition :=
 {t : n.transition | (•ₜ t) ⊆ s ∧ (t •ₜ)∩ s ⊆ (•ₜ t)}

def deadlock {n : PetriNet α β} (s : Set n.places) : Prop :=
  enable s = ∅ 

def firing {n : PetriNet α β} (s : Set n.places) (t : enable (s)) : Set n.places :=
  (Set.diff s (•ₜ t) ) ∪ (t •ₜ)

notation:2 lhs:3 "[" rhs:4 "⟩" => firing lhs rhs

--Sucesion de ejecuciones

def firing_seq {n : PetriNet α β} : ℕ →  Set (List ((Set n.places)×(n.transition)×(Set n.places)) )
  | 0   => {[]}                                                       --Lista vacia
  | 1   => {[(s, t, s[t⟩)] | (s : (Set n.places)) (t ∈ enable (s)) } --Estado inicial
  | n+1 => let (_,_,s) := seq[n-1] in
          {seq ++ [(s, t, s[t⟩)] | (seq : firing_seq (n)) (t ∈ enable (s))} --Paso recursivo
 

--def firing_seq {n : PetriNet α β} (l : List n.transition) (s0 : Set n.places) : Set n.places :=
--  List.foldr (λ t => (λ s => s[t⟩)) s0 l

--Reachable devuelve el conjunto de los estados disponibles
--def reach {n : PetriNet α β} (s : Set n.places) :  Set (Set n.places) 
--  | ∅ₛ  => {∅ₛ} 
