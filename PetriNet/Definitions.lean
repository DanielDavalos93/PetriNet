import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
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
  m₀ : Set places

variable {α β : Type} (N : PetriNet α β)

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

lemma enType {α β : Type} {N : PetriNet α β} (s : Set N.places) 
    : ∀ t, (t ∈  enable (s) →  N.transition) := by sorry

def deadlock {n : PetriNet α β} (s : Set n.places) : Prop :=
  enable s = ∅

--Firing
def firing {n : PetriNet α β} (s : Set n.places) (t : enable (s)) : Set n.places :=
  (Set.diff s (•ₜ t) ) ∪ (t •ₜ)

notation:2 lhs:3 "[" rhs:4 "⟩" => firing lhs rhs
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
  (Set.sUnion {(t •ₜ) | t∈ T ∩ enable (s)})

universe u v
def image {α : Type u} {β : Type v} (f: α →  β) (s : Set α) : Set β :=
  {f x | x ∈ s}

lemma firing_eq1 {n : PetriNet α β} (s : Set n.places) (t : enable (s)) :
  firing s t = Firing s {t.val} := by sorry
--  by apply Set.ext ; intros x; exact ⟨fun h => show x ∈ Firing s {t.val} from  by rw [Firing s {t.val}], fun h => h⟩


lemma firing_eq2 {n : PetriNet α β} (s : Set n.places) (t : enable (s)) :
  firing s t = Firing s {↑ t} := by sorry

--Aux - listas
def init {α : Type} (l : List α) : List α :=
  ((l.reverse).tail).reverse

--Lista de ejecuciones
def firing_seq {n : PetriNet α β} (l : List n.transition) (s0 : Set n.places) : List (Set n.places) :=
  List.scanl (fun s t => Firing s (Set.singleton t)) s0 l
