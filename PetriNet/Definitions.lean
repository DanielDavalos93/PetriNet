import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.SetTheory.Cardinal.Basic

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

def preset_t {n : PetriNet α β} (t : n.transition) : Set n.places :=
  Relation.pre_image n.rel_pt t

prefix:1 "•ₚ" => preset_p
prefix:2 "•ₜ" => preset_t

def poset_p {n : PetriNet α β} (p : n.places) : Set n.transition :=
  {t : n.transition | n.rel_tp t p}

def poset_t {n : PetriNet α β} (t : n.transition) : Set n.places :=
  {p : n.places | n.rel_pt p t}

postfix:1 "•ₚ" => poset_p
postfix:2 "•ₜ" => poset_t

def is_initial {n : PetriNet α β} (s : Set n.places) : Prop :=
  IsEmpty (Set.sUnion {(•ₚ x) | x ∈  s})

def is_final {n : PetriNet α β} (s : Set n.places) : Prop :=
  IsEmpty (Set.sUnion {(x •ₚ) | x ∈  s})

--Se define el conjunto de los estados habilitados
def enable {n : PetriNet α β} (s : Set n.places) : Set n.transition :=
 {t : n.transition | (•ₜ t) ⊆ s ∧ (t •ₜ)∩ s ⊆ (•ₜ t)}

lemma preset_implies_enable (N : PetriNet α β) (s : Set N.places) (t : N.transition) :
  t ∈ enable s → (•ₜ t) ⊆ s := by
  intros h_enable
  unfold enable at h_enable
  simp only [Set.mem_setOf_eq, Set.mem_sUnion, Set.mem_preimage] at h_enable
  exact h_enable.left


def deadlock {n : PetriNet α β} (s : Set n.places) : Prop :=
  IsEmpty (enable s)

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


lemma firing_eq1 {n : PetriNet α β} (s : Set n.places) (t : enable s) :
  firing s t = Firing s {↑t} := by sorry
--    unfold firing Firing
--    ext x
--  simp only [Set.mem_union, Set.mem_diff, Set.mem_sUnion, Set.mem_image]
--    apply Iff.intro
--      cases h
--      | inl h => simp [h]
--      apply simp [h] ; exact ⟨t, h_w, h_h.left⟩ 
--    . intro h 
--      cases h 
--      | left => simp [h]
--      | right => exact ⟨h_w, h_h⟩


lemma firing_eq2 {n : PetriNet α β} (s : Set n.places) (t : enable (s)) :
  firing s t = Firing s {↑ t} := by 
    exact firing_eq1 s t


--Aux - listas
def init {α : Type} (l : List α) : List α :=
  ((l.reverse).tail).reverse

def L1 := ["a","b","c"]
#eval List.length L1
#eval List.get! L1 2

--Lista de ejecuciones
/-`firing_seq s0 l` pide una lista e transiciones `l` y un estado inicial `s0`
y devuelve una lista de estados, siempre que estén habilitados
Por ejemplo: l=[t1,t2], s0={p1,p2}, s1=s[t1⟩={p3,p2} y s2=s[t2⟩={p3,p4} 
luego firing_seq s0 l = [s1,s2]
-/
@[simp] def firing_seq {N : PetriNet α β} (s0 : Set N.places)  (l : List N.transition) : List (Set N.places) :=
  List.scanl (fun s t => Firing s (Set.singleton t)) s0 l

--Concatenación de ejecuciones
/-`firing_concat l s0` pide una lita `l` y un estado inicial `s0`
y devuelve el último estado de esa secuencia, siempre y cuando estén habilidatos
Con el ejemplo anterior :
`firing_concat l s0=s2`
-/
def firing_concat {N : PetriNet α β} (s0 : Set N.places) (l : List N.transition) : Set N.places :=
  let firing_list := firing_seq s0 l
  let n := List.length firing_list
  List.get! firing_list (n-1)

def there_is_seq {N : PetriNet α β} (s0 : Set N.places) (sn : Set N.places) : Prop :=
  ∃ (l : List N.transition), firing_concat s0 l = sn

/-Abreviatura para el caso donde exista una lista de transiciones `l`
para el cual s0 sea el estado inicial y sn el estado final:
s0[*]sn
-/
notation:5 ss:5"[*]"ls:6 => there_is_seq ss ls

def reach (N : PetriNet α β) (s : Set N.places) : Set (Set N.places) :=
  {s' | s[*]s'}

