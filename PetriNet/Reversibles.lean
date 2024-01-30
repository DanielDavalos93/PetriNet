import PetriNet.Definitions
import PetriNet.Occurrence
import Mathlib.Tactic.LibrarySearch
/-
# Definitions and properties of reversible Petri Net, given a Petri Net

`revPetriNet` is a definitions which inherits all properties of `PetriNet`,
but the inverse relations are added.

* I extend a Petri Net giving only the reversible relation.
For example, if `P : PetriNet Nat Bool` with `1 ≺ True` and `True≺ 2`, then
on `R : revPetriNet Nat Bool` we have `1 ≺ Tue`, `True ≺ 2`, `2 ≺ True` and
`True≺ 1`.
* Definitions of preset and postet are analogous. Also for enabled transitions
and firing.

For notations are the same as those used for fordward nets, but eqquiped with
a sub-index `ᵣ`.

The main property is prove that s[t⟩s' iff s'[t⟩ᵣs. And for a sequence
seq = t₁;...;tₙ and sᵢ₋₁ [tᵢ⟩sᵢ then s₀[[seq⟩⟩sₙ iff sₙ[[seq'⟩⟩ᵣ s₀, where
seq' = tₙ;...;t₁.
-/

@[ext] structure revPetriNet (α : Type) (β : Type) extends (PetriNet α β) where
  rev_rel_pt : places →  transition →  Prop
  rev_rel_tp : transition →  places →  Prop

variable {α β : Type} {R : revPetriNet α β}

/- ## Axioms ##
  If F ⊂ (places × transition) ∪ (transition × places) is the fordward
  relation and R ⊆ (places × transition) ∪ (transition × places) is the
  reversible relation, we know that :
  * (p,t) ∈ F ↔ (t,p) ∈ R
  * (t,p) ∈ F ↔ (p,t) ∈ R
-/
axiom eq_rev_rel_pt : ∀ (p : R.places) (t : R.transition),
  R.rev_rel_pt p t = R.rel_tp t p

axiom eq_rev_rel_tp : ∀ (t : R.transition) (p : R.places),
  R.rev_rel_tp t p = R.rel_pt p t
--

/- Those two lemmas are used for the pres_t_equal_rev_post_t and
  post_t_equal_rev_pres_t theorems.
-/
lemma set_eq_rev_rel_pt (t : R.transition) :
    {p : R.places | R.rev_rel_pt p t} = {p : R.places | R.rel_tp t p} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [← eq_rev_rel_pt]

lemma set_eq_rev_rel_tp (t : R.transition) :
    {p : R.places | R.rev_rel_tp t p} = {p : R.places | R.rel_pt p t} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [← eq_rev_rel_tp]

/-
Proving the equality of two reversible Petri nets R₁ and R₂
-/
lemma revPetriNet_eq_places (R₁ R₂ : revPetriNet α β)
  (places : R₁.places = R₂.places) (a : α)
  : a ∈  R₁.places ↔  a ∈  R₂.places := by
    exact Iff.of_eq (congrArg (Membership.mem a) places)

lemma revPetriNet_eq_transition (R₁ R₂ : revPetriNet α β)
  (trans : R₁.transition = R₂.transition) (b : β)
  : b ∈  R₁.transition ↔  b ∈  R₂.transition := by
    exact Iff.of_eq (congrArg (Membership.mem b) trans)

@[simp] lemma revPetriNet_equality (R₁ R₂ : revPetriNet α β)
  (places : R₁.places = R₂.places) (transition : R₁.transition = R₂.transition)
  (m₀ : HEq R₁.m₀ R₂.m₀) (rel_pt : HEq R₁.rel_pt R₂.rel_pt)
  (rel_tp : HEq R₁.rel_tp R₂.rel_tp) (rev_rel_pt : HEq R₁.rev_rel_pt R₂.rev_rel_pt)
  (rev_rel_tp : HEq R₁.rev_rel_tp R₂.rev_rel_tp) : R₁ = R₂ := by
    exact revPetriNet.ext R₁ R₂ places transition rel_pt rel_tp m₀ rev_rel_pt rev_rel_tp
--------

theorem revPetriNet_type (R : revPetriNet α β) : PetriNet α β := by
  exact R.toPetriNet

/-
* Reversing Flow
-/
open Flow
@[reducible] def Reversing.flow (R : revPetriNet α β) :
    (R.places ⊕  R.transition) →  (R.places ⊕  R.transition) →  Prop
    | Sum.inl p, Sum.inr t  => R.rev_rel_pt p t
    | Sum.inr t, Sum.inl p  => R.rev_rel_tp t p
    | _, _                  => false

notation:20 l:20 "≺ ᵣ" r:21 => Reversing.flow _ l r

@[reducible] def Reversing.predecesor {α β : Type} {R : revPetriNet α β}
  (x y : R.places ⊕  R.transition) : Prop :=
     (tranClos (Reversing.flow R)) x y ∨ (x = y)

notation:22 l:22 "≼ ᵣ" r:23 => Reversing.predecesor _ l r

------

@[simp, reducible]
def Reversing.preset_t {R : revPetriNet α β} (t : R.transition)
  : Set R.places :=
  Relation.pre_image R.rev_rel_pt t

prefix:1 "•ᵣ" => Reversing.preset_t

@[simp, reducible]
def Reversing.postset_t {R : revPetriNet α β} (t : R.transition)
  : Set R.places :=
  Relation.image R.rev_rel_tp t

postfix:2 "•ᵣ" => Reversing.postset_t

@[simp]
theorem rev_pos_t_equal_pres_t {R : revPetriNet α β} (t : R.transition) : (t •ᵣ) = (•ₜ t) :=
  calc
    (t•ᵣ) = Relation.image R.rev_rel_tp t    := by rfl
       _  = {p : R.places | R.rev_rel_tp t p}:= rfl
       _  = {p : R.places | R.rel_pt p t}    := by exact set_eq_rev_rel_tp t
       _  = Relation.pre_image R.rel_pt t    := by rfl
       _  = (•ₜt)                            := rfl

@[simp]
theorem rev_pres_t_equal_pos_t {R : revPetriNet α β} (t : R.transition) : (•ᵣ t) = (t •ₜ) :=
  calc
    (•ᵣ t)  = Relation.pre_image R.rev_rel_pt t := by rfl
          _ = {p | R.rev_rel_pt p t}            := rfl
          _ = {p | R.rel_tp t p}                := by exact set_eq_rev_rel_pt t
          _ = Relation.image R.rel_tp t         := rfl
          _ = (t •ₜ)                            := rfl


/-
 ** Reversing Firing **
 First, the enable version of reversible Petri nets are analogous to the forward Petri nets.
 Second, we write `s[t⟩ᵣ = s'` for reversible firing such that s↝ s' through the transition
 t, where `s'[t⟩ = s` is the fordward version and s'↠ s.
-/

def Reversing.enable {R : revPetriNet α β} (s : Set R.places) : Set R.transition :=
 {t : R.transition | (•ᵣt) ⊆ s ∧ (t•ᵣ)∩ s ⊆ (•ᵣt)}

def Reversing.is_enabled (s : Set R.places) (t : R.transition) : Prop :=
  t ∈ Reversing.enable s

def Reversing.firing {R : revPetriNet α β} (s : Set R.places) {t : R.transition}
  (_ : Reversing.is_enabled s t)
  : Set R.places :=
    (s \ (•ᵣ t) ) ∪ (t •ᵣ)

notation:24 lhs:24 "[" rhs:25 "⟩ᵣ" => Reversing.firing lhs rhs _

def Reversing.is_firing {R : revPetriNet α β} (s : Set R.places) {t : R.transition}
  (h : Reversing.is_enabled s t) (s' : Set R.places) : Prop :=
    Reversing.firing s h = s'

notation:26 lhs:26 "[" trans:27 "⟩ᵣ" rhs:28 => Reversing.is_firing lhs trans rhs

def Reversing.Firing {R : revPetriNet α β} (s : Set R.places) (T : Set R.transition)
  : Set R.places :=
    (s \ (Set.sUnion {(•ᵣt) | t∈ T∩ Reversing.enable s})) ∪
    Set.sUnion {(t•ᵣ) | t∈ T ∩ Reversing.enable s }

notation:29 lhs:29 "[" rhs:30 "⟩ᵣ" => Reversing.Firing lhs rhs



def Reversing.is_Firing {R : revPetriNet α β} (s s' : Set R.places)
  (T : Set R.transition) : Prop :=
  Reversing.Firing s T = s'

notation:31 lhs:31 "[" trans:32 "⟩ᵣ" rhs:33 => Reversing.is_Firing lhs trans rhs


lemma enable_forward_reversible (s s' : Set R.places) (t : enable s)
  (h : s' = firing s t)
  : t.val ∈  Reversing.enable s' := by
      unfold firing at h
      unfold Reversing.enable
      simp only [Set.mem_setOf_eq, Set.mem_diff]
      unfold enable at t
      rw [← rev_pos_t_equal_pres_t,← rev_pres_t_equal_pos_t] at *
      apply Iff.mp
      . exact forall_eq
      . intros
        rename_i h1 h2
        have h3 : (•ᵣ↑t.val)⊆ s' :=
          calc
            (•ᵣ↑t.val) ⊆  (s \ (↑t•ᵣ)) ∪ (•ᵣ↑t) := by
              exact Set.subset_union_right (s\(↑t•ᵣ)) (•ᵣ↑t.val)
            (s \ (↑t•ᵣ)) ∪ (•ᵣ↑t) = s' := by exact id (Eq.symm h)
        apply And.intro
        . exact h3
        . cases h2
          rw [Set.subset_def]
          intros h4 h5
          have h6 : h4 ∈ (↑t.val•ᵣ) := by apply Set.mem_of_mem_inter_left h5
          subst h
          rw [Set.mem_inter_iff, Set.mem_union, Set.mem_diff] at h5
          have h7 : (h4 ∈ s ∧ ¬h4 ∈ (↑t.val•ᵣ) ∨ h4 ∈ (•ᵣ↑t.val)) := by apply h5.2
          cases h7
          . rename_i h8
            have h9 : ¬ h4 ∈ (↑t.val•ᵣ) := by apply h8.2
            contradiction --h6 ∧  h9 -> False
          . rename_i h8
            exact h8

lemma aux_subset {γ : Type} (s t v : Set γ) : (s\t)\v ∪ t = (s∪ t) ∩ (vᶜ∪ t) :=
  calc
    (s\t) \ v ∪ t = (s∩ tᶜ) ∩ vᶜ ∪ t    := by repeat rw [Set.diff_eq]
                _ = s ∩ vᶜ ∩ tᶜ ∪ t     := by rw [Set.inter_right_comm]
                _ = (s ∩ vᶜ ∪ t) ∩ (tᶜ ∪ t) := by rw [Set.union_distrib_right]
                _ = (s∩ vᶜ∪ t) ∩ (Set.univ) := by rw [Set.compl_union_self]
                _ = s∩ vᶜ ∪ t           := by aesop
                _ = (s∪ t) ∩ (vᶜ∪ t)    := by rw [Set.union_distrib_right]


/-
The next lemma means that if s[t⟩s' then ∃ t' : transition, s'[t'⟩ᵣs.
-/
lemma reversing_forward_firing (s s' : Set R.places) (en : enable s)
   (h : s' = firing s en)
   : ∃ (h' : en.val ∈  Reversing.enable s'), Reversing.is_firing s' h' s := by
    have h1 := enable_forward_reversible s s' en h
    exists h1
    subst h
    unfold enable Reversing.is_firing firing Reversing.firing
    unfold enable at en
    unfold Reversing.enable at h1
    simp only [Reversing.preset_t, rev_pres_t_equal_pos_t, Reversing.postset_t,
        rev_pos_t_equal_pres_t, Set.mem_setOf_eq] at h1
    simp only [rev_pos_t_equal_pres_t,rev_pres_t_equal_pos_t]
    unfold firing at h1
    have h1_1 : (en.val•ₜ) ⊆ s \ (•ₜ↑en) ∪ (↑en•ₜ) := And.left h1
    have h1_2 : (•ₜen.val) ∩ (s \ (•ₜen.val) ∪ (en.val•ₜ)) ⊆ (↑en•ₜ) := And.right h1
    have h2: (•ₜen.val) ∩ (s \ (•ₜen.val) ∪ (en.val•ₜ)) ⊆ s \ (•ₜ↑en) ∪ (↑en•ₜ) := by
      exact Set.inter_subset_right (•ₜen.val) (s \ (•ₜ↑en) ∪ (↑en•ₜ))
    rw [Set.inter_subset, Set.compl_union_self] at h2 
    let p : (t : R.transition) → Prop := λ t => (•ₜt) ⊆ s ∧ (t•ₜ) ∩ s ⊆ (•ₜt)
    have h_en : p (Subtype.val en) := Subtype.property en
    simp_all
    have h_en1 : (•ₜen.val) ⊆ s := And.left h_en
    have h_en2 :  (en.val•ₜ) ∩ s ⊆ (•ₜ↑en) := And.right h_en
    ext x
    constructor
    . intro hmp
      simp at hmp
      cases hmp
      . rename_i hx1 ; exact hx1.1.1 
      . rename_i hx2 
        exact h_en1 hx2
    . intro hmpr
      simp 
      right
      have h : s ⊆ (•ₜ↑en)∪ ((↑en•ₜ)ᶜ∩ s) := 
        sorry
      rw [Set.subset_def] at h
      have h_in : x ∈ (•ₜen.val) ∪ (en.val•ₜ)ᶜ ∩ s := by apply h x hmpr
      rw [Set.mem_union, Set.mem_inter_iff] at h_in
      
      sorry

    /-rw [Set.Subset.antisymm_iff]
    constructor
    . rw [Set.diff_eq, Set.union_distrib_right]
       
      sorry  
    . rw [Set.diff_eq, Set.diff_eq, Set.inter_distrib_right, Set.union_distrib_right,
      Set.inter_compl_self, Set.union_empty, Set.union_empty]
      intros x hx
      by_cases h : x ∈ (•ₜen.val)
      . right
        exact h
      . rw [Set.mem_union]
        left 
        repeat rw [Set.mem_inter_iff]
        constructor 
        . exact ⟨hx, h⟩
        . simp_all 
          
          sorry
    -/
/-
** List of executions **

  A reversing firing sequence is a proposition that says us if there are a list
of transitions t₁,...,tₙ and a list of states s₀, s₁, ... , sₙ which
s₀[t₁⟩ᵣ = s₁, ... , sₙ₋₁[tₙ⟩ᵣ = sₙ.

  We denote this by abreviation: s₀ [[T⟩⟩ᵣ sₙ , where s₀ sₙ and T = [t₁,...,tₙ]
are given.
-/
@[reducible]
inductive Reversing.firing_sequence [DecidableEq α] {R : revPetriNet α β} :
  (s : Set R.places) →  List R.transition →  (sn : Set R.places) → Prop
  | empty : ∀ s, Reversing.firing_sequence s [] s
  | step : ∀ {s s' s'' t} fs, (h : Reversing.is_enabled s t)
    →  Reversing.is_firing s h s'
    →  Reversing.firing_sequence s' fs s''
    →  Reversing.firing_sequence s (t :: fs) s''

notation:200 ls:201 "[[" ts:202 "⟩⟩ᵣ" rs:203 => Reversing.firing_sequence ls ts rs

@[simp] def Reversing.there_is_seq [DecidableEq α] {R : revPetriNet α β}
  (s0 sn : Set R.places) : Prop :=
  ∃ (l : List R.transition), Reversing.firing_sequence s0 l sn

notation:10 ss:10"[*]ᵣ"ls:11 => Reversing.there_is_seq ss ls

/-
--Reachable
Given a state `s`, `reach s` return all the states that can be executed by sequences of
firing enabled.
-/
def Reversing.reach [DecidableEq α] (R : revPetriNet α β) (s : Set R.places)
  : Set (Set R.places) :=
  {s' | s[*]ᵣs'}

/- A special case, where the state initial is `m₀`.
This definition returns all the states that can be executed in a Petri net.
-/
def Reversing.reach_net [DecidableEq α] (R : revPetriNet α β) : Set (Set R.places) :=
  Reversing.reach R (R.m₀)

/-
  If we have two reversing firing sequence s[[T₁⟩⟩ᵣs' and s'[[T₂⟩⟩ᵣs'', then should
be true s[[T₁ ++ T₂⟩⟩ᵣs''.
-/
lemma firing_sequence_concat [inst : DecidableEq α] (s s' s'' : Set R.places)
  (ts1 ts2 : List R.transition) (hfs1 : Reversing.firing_sequence s ts1 s')
  (hfs2 : Reversing.firing_sequence s' ts2 s'')
  : s [[(ts1 ++ ts2)⟩⟩ᵣ s'' := by
    induction hfs1 with
    | empty p =>
        rw [List.nil_append] ; exact hfs2
    | step en1 tr1 fir1 _ ih1 =>
        have h2 := ih1 hfs2
        simp
        exact Reversing.firing_sequence.step (en1++ts2) tr1 fir1 h2


/-
  The principal theorem says that if a list of transitions T = [t₁,...,tₙ] satisfies
that there are s₀,s₁,...,sₙ (with s₀ = s and sₙ = s') such that s₀[t₁⟩=s₁, ...,
sₙ₋₁[tₙ⟩ = sₙ (with us notation of firing sequence: s[[T⟩⟩s') then the reversible
way also is a firing sequence: ∃ T' : [t₁',...,tₙ'], s'[[T'⟩⟩ᵣs.

  In this case isn't very important, but we know that T' = T.reverse, i.e., t₁' = tₙ,
..., tₙ' = t₁.
-/
theorem rev_commutative [inst :  DecidableEq α] (s s' : Set R.places)
  (T : List R.transition) (hmp : s [[T⟩⟩ s' ) : ∃ T', s' [[T'⟩⟩ᵣ s := by
      induction hmp with
      | empty s =>
          exists []
          exact Reversing.firing_sequence.empty s
      | step en s₀' s₀'' tr fir fs ih =>
          rename_i s₀
          have r_fir : ∃ en', Reversing.firing s₀' en' = s₀ := by
           exact reversing_forward_firing s₀ s₀' en (Eq.symm fir)
          rcases r_fir with ⟨w, wt⟩
          rcases ih with ⟨i, it⟩
          exists i++ [en.val]
          have fs_last : s₀'[[[↑en]⟩⟩ᵣs₀ := by
           apply Reversing.firing_sequence.step [] w wt (Reversing.firing_sequence.empty s₀)
          exact firing_sequence_concat s₀'' s₀' s₀ i [en.val] it fs_last
