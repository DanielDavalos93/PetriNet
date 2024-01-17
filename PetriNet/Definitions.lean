import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
/-!
# Basic definitions of Petri Net

PetriNet is a structure that is build from two types α β.
The idea is similar to the classic definition, (P,T,•N,N•) and (N,m₀) is a place/transition
Petri net, where m₀ is the initial state. In our case,I've defined a Petri net as
N = (P,T,•N,N•,m₀), which is valid.
We need to construct the definition of the relations rel_pt and rel_tp.

There are two forms to define a state: as a set or as markings. In this code, we'll see
the sates as sets. This means that `p : N.places` is a place and `{p}` is a state. For
this reason, all Petri net are only 1-safe (has at most a marking in each place).

States aren't defined with a special name, but I'll allways refer it with `Set N.places`.

# Main definitions

 Notation used here:

 For a Petri net `N : Petri α β`,
  * Preset (preset_t) for a transition: `(•ₜt)` [abr: `\bu\_t t`] take a transition `t`
  and returns a set   of places `N.places`, whenever `∀ s ∈  (•ₜ t), N.rel_pt s t` is
  true.
  * Poset (poset_t) for a transition: `(t •ₜ)` the same idea but `∀ s∈ (t •ₜ),
  N.rel_tp t s` is true.
  * Preset (preset_p) and poset (poset_p) for a place: `(•ₚ p)` and `(p •ₚ)` take a
  place and returns a set of transitions, whenever `N.rel_tp t p` and `N.rel_pt p t`
  are true, respectively.
  * Execution (firing): s[t⟩ [abr: `s [ t \ran`] Given a state `s : Set N.places` and a
  transition `t`, returns the state `s'`. If `s[t⟩=s'` is true, we can denote as
  `s[t⟩s` how they are writen in books.
  * `s[*]sₙ : Prop` is an abreviature if there are sequences of states [s,s₁,...,sₙ] and
  transitions [t₁,t₂,...,tₙ] which sᵢ₋₁[tᵢ⟩sᵢ for each i = 1,...,n and s₀=s.

# [abr: _] is an abreviature to how to write a code.
-/

-- Petri net
@[ext] structure PetriNet (α : Type) (β : Type) where
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
  Relation.image n.rel_pt p

def poset_t {n : PetriNet α β} (t : n.transition) : Set n.places :=
  Relation.image n.rel_tp t

postfix:1 "•ₚ" => poset_p
postfix:2 "•ₜ" => poset_t

/-!
Next definitions say if the state doesn't have any transition before (is_initial) or
after (is_final)
-/
def is_initial {n : PetriNet α β} (s : Set n.places) : Prop :=
  IsEmpty (Set.sUnion {(•ₚ x) | x ∈  s})

def is_final {n : PetriNet α β} (s : Set n.places) : Prop :=
  IsEmpty (Set.sUnion {(x •ₚ) | x ∈  s})

/-!
# Enabled transitions
Given a state `s`, `enable s` returns the set of transitions that could be execute. The
plan is that s -> t don't have problem.
-/
def enable {n : PetriNet α β} (s : Set n.places) : Set n.transition :=
 {t : n.transition | (•ₜ t) ⊆ s ∧ (t •ₜ)∩ s ⊆ (•ₜ t)}

def is_enabled {N : PetriNet α β} (m : Set N.places) (t : N.transition) : Prop :=
    t ∈  enable m

lemma preset_implies_enable (N : PetriNet α β) (s : Set N.places) (t : N.transition) :
  t ∈ enable s → (•ₜ t) ⊆ s := by
  intros h_enable
  unfold enable at h_enable
  exact h_enable.left

/-
# Deadlock
A deadlock is when there is no transitions enabled for a state `s`.
In this case the execution are no possible.
-/
def deadlock {n : PetriNet α β} (s : Set n.places) : Prop :=
  IsEmpty (enable s)

-- Firing
def firing {n : PetriNet α β} (s : Set n.places) (t : enable (s)) : Set n.places :=
  (s \ (•ₜ t) ) ∪ (t •ₜ)

notation:2 lhs:3 "[" rhs:4 "⟩" => firing lhs rhs

def is_firing {N : PetriNet α β} (s : Set N.places) (t : enable s) (s' : Set N.places) : Prop :=
  firing s t = s'

notation:5 ls:5 "[" ts:6 "⟩" ls':7 => is_firing ls ts ls'

-- Firing as a set
def Firing {n : PetriNet α β} (s : Set n.places) (T : Set n.transition) : Set n.places :=
  (s \ (Set.sUnion {(•ₜ t) | t∈ T ∩ enable (s)})) ∪
  (Set.sUnion {(t •ₜ) | t∈ T ∩ enable (s)})

/-!
The next lemma says that `firing s t` and `Firing s T` are equals if and only if `T` is
singleton and `T = {t}`.
If |T| > 1 this is not allways true.
-/
lemma firing_eq1 {n : PetriNet α β} (s : Set n.places) (t : enable s) :
  firing s t = Firing s {t.val} := by
    unfold firing Firing
    apply Set.ext
    intro x
    apply Iff.intro
    . intro h
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, and_assoc]
      cases h
      case inl h =>
        left
        cases h with
        | intro h1 h2 =>
          constructor ; exact h1 ; simp ; exact h2
      case inr h =>
        right
        simp ; exact h
    . intro h
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, and_assoc] at h
      cases h
      case inl h =>
        left
        cases h with
        | intro h1 h2 =>
          constructor ; exact h1 ; simp at h2 ; exact h2
      case inr h =>
        right
        simp at h ; exact h


lemma firing_eq2 {n : PetriNet α β} (s : Set n.places) (t : enable (s)) :
  firing s t = Firing s {↑ t} := by
    exact firing_eq1 s t


lemma IsEmpty_to_empty {α : Type} (s : Set α) (h : IsEmpty s) : s = ∅  :=
  Iff.mp Set.isEmpty_coe_sort h


lemma no_enable_preset_to_emp {N : PetriNet α β} (s : Set N.places) (t : N.transition)
  (h : t ∉ enable (s)) : {(•ₜ y) | y∈ {↑t}∩ enable (s)} = ∅ :=
    have h1 : IsEmpty {(•ₜ y) | y∈ {↑t}∩ enable (s)} := by aesop
    calc {(•ₜ y) | y∈ {↑t}∩ enable (s)} = ∅  := by apply IsEmpty_to_empty _ h1

lemma no_enable_poset_to_emp {N : PetriNet α β} (s : Set N.places) (t : N.transition)
  (h : t ∉ enable (s)) : {(y •ₜ) | y∈ {↑t}∩ enable (s)} = ∅ :=
    have h1 : IsEmpty {(y •ₜ) | y∈ {↑t}∩ enable (s)} := by aesop
    calc {(y •ₜ) | y∈ {↑t}∩ enable (s)} = ∅  := by apply IsEmpty_to_empty _ h1


/-
This theorem says that if a transition `t` isn't enabled in a state `s` then the execution
on `firing s t` is the identity (i.e. there is no execution)
-/
theorem no_enable_to_id {N : PetriNet α β} (s : Set N.places) (t : N.transition)
  (h : t∉ enable (s)) : Firing s {↑t} = s :=
    calc Firing s {↑t} = (s\(Set.sUnion {(•ₜ y) | y∈ {↑t} ∩ enable (s)})) ∪
          (Set.sUnion {(y •ₜ) | y∈ {↑t} ∩ enable (s)})  := rfl
      _ = (s \ ∅ ) ∪ (Set.sUnion {(y •ₜ) | y∈ {↑t} ∩ enable (s)}) := by
          rw [no_enable_preset_to_emp s t h] ; simp
      _ = (s \ ∅ ) ∪ ∅  := by rw [no_enable_poset_to_emp s t h] ; simp
      _ = (s \ ∅ )      := Set.union_empty (s\∅ )
      _ = s             := Set.diff_empty


--Aux - listas
def init {α : Type} (l : List α) : List α :=
  ((l.reverse).tail).reverse

--List of executions
/-`firing_seq s0 l` ask for a list of transitions `l` and an initial state `s0` (this
initial state is not necessarily the same as the initial state of a Petri net `m₀`) and
returns a list of states, whenever they are enabled in their respective executions.
Such as: l=[t1,t2], s0={p1,p2}, s1=s[t1⟩={p3,p2} y s2=s[t2⟩={p3,p4} then
`firing_seq s0 l = [s1,s2]`
-/
/-@[simp] def firing_seq {N : PetriNet α β} (s0 : Set N.places)  (l : List N.transition)
  : List (Set N.places) :=
  List.scanl (fun s t => Firing s (Set.singleton t)) s0 l
-/

inductive firing_sequence [DecidableEq α] {N : PetriNet α β} : (s : Set N.places) →
  List N.transition →  (sn : Set N.places) → Prop
  | empty : firing_sequence s [] s
  | step : ∀ t s' s'' fs, (is_firing s t s')
    → firing_sequence s' fs s''
    → firing_sequence s (t :: fs) s''

notation:200 ls:201 "[[" ts:202 "⟩⟩" lss:203 => firing_sequence ls ts lss

--Concatenation of executions
/-`firing_concat l s0` asks for a list `l` and an initial state `s0` and returns the last
state of that sequence, whenever they are enabled.
With the previous example:
`firing l s0 = s2`
-/
/-@[simp] def firing_concat {N : PetriNet α β} (s0 : Set N.places) (l : List N.transition)
  : Set N.places :=
  List.get! (firing_seq s0 l) ((List.length (firing_seq s0 l))-1)
-/

@[simp]
def there_is_seq [DecidableEq α] {N : PetriNet α β} (s0 : Set N.places) (sn : Set N.places)
  : Prop :=
  ∃ l : List N.transition, firing_sequence s0 l sn

notation:210 ss:211"[*]"ls:212 => there_is_seq ss ls

--Reachable
/-
Given a state `s`, `reach s` return all the states that can be executed by sequences of
firing enabled.
-/
def reach [DecidableEq α] (N : PetriNet α β) (s : Set N.places) : Set (Set N.places) :=
  {s' | s[*]s'}

/- A special case, when the state initial is `m₀`.
This definition returns all the states that can be executed in a Petri net.
-/
def reach_net [DecidableEq α] (N : PetriNet α β) : Set (Set N.places) :=
  reach N (N.m₀)
