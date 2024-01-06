import PetriNet.Definitions
import PetriNet.Occurrence
--set_option pp.explicit true

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
seq = t₁;...;tₙ and sᵢ₋₁ [tᵢ⟩sᵢ then s₀[seq]sₙ iff sₙ[← seq]s₀, where
← seq = tₙ;...;t₁.
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

/- Those lemmas are used for the pres_t_equal_rev_post_t and
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
 Second, we write `s[t⟩ᵣ = s'` for reversible firing such that s↝ s' through the transition t,
 where `s'[t⟩ = s` is the fordward version and s'↠ s.
-/

def Reversing.enable {R : revPetriNet α β} (s : Set R.places) : Set R.transition :=
 {t : R.transition | (•ᵣt) ⊆ s ∧ (t•ᵣ)∩ s ⊆ (•ᵣt)}


def Reversing.firing {R : revPetriNet α β} (s : Set R.places) (t : Reversing.enable s)
  : Set R.places :=
    (s \ (•ᵣ t) ) ∪ (t •ᵣ)

notation:24 lhs:24 "[" rhs:25 "⟩ᵣ" => Reversing.firing lhs rhs

def Reversing.is_firing {R : revPetriNet α β} (s s' : Set R.places) (t : Reversing.enable s)
  : Prop :=
    Reversing.firing s t = s'

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


lemma enable_fordward_reversible1 (s s' : Set R.places) (t : enable s) --(s' : firing s t)
  (h : s' = firing s t)
  : t.val ∈ Reversing.enable s' := by
    unfold firing at h
    unfold Reversing.enable
    simp only [Set.mem_setOf_eq]
    apply And.intro
    . intros y h'
      subst h
      rw [Set.mem_union, Set.mem_diff, ← rev_pres_t_equal_pos_t]
      right 
      exact h'
    . intros y h'
      subst h 
      rw [← rev_pres_t_equal_pos_t] at h'
      rw [Set.mem_inter_iff, Set.mem_union,Set.mem_diff] at h'
      have h1 : y∈ s ∧ ¬y ∈ (•ₜ↑t.val) ∨ y ∈ (•ᵣ↑t.val) := by apply And.right h'
      cases h1 
      . rename_i h3
        have h4 : ¬y∈ (•ₜ↑t.val) := by apply And.right h3
        have h5 : y ∈ (•ₜ ↑t.val) := by rw [rev_pos_t_equal_pres_t] at h' ; apply And.left h'
        contradiction 
      . rename_i h3
        exact h3
      

lemma Reversing.firing_eq1 {R : revPetriNet α β} (s : Set R.places) (t : Reversing.enable s)
  : Reversing.firing s t = Reversing.Firing s {t.val} := by
   unfold Reversing.firing Reversing.Firing
   apply Set.ext
   intro x
   apply Iff.intro
   .intro h
    simp only [Set.mem_inter_iff, Set.mem_singleton, and_assoc] at h
    cases h
    case inl h =>
      left
      have h1 : x∈s := by apply Set.mem_of_mem_diff h
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, preset_t, Subtype.exists] at h
      apply And.intro
      . exact h1
      . rw [Set.mem_diff] at h
        simp 
        intros h2 h3 h4 h5 _ h7
        subst h7
        have h8 :¬x ∈ Relation.pre_image R.rev_rel_pt ↑t := And.right h
        aesop
    case inr h =>
      right
      aesop
   .intro h
    simp only [Set.mem_inter_iff, and_assoc] at h
    cases h
    case inl h =>
      left
      have h1 : x∈s := by apply Set.mem_of_mem_diff h
      aesop
    case inr h =>
      right
      aesop

lemma Reversing.Firing_eq2 {R : revPetriNet α β} (s : Set R.places) (t : Reversing.enable s)
  : Reversing.firing s t = Reversing.Firing s {↑t} := by
    exact Reversing.firing_eq1 s t




--lemma firing_fordward_reversible {R : revPetriNet α β} (s s' : Set R.places) (t : enable s)
--  (hf : firing s t = s') (ht : t.val ∈ Reversing.enable s')
--  : (Reversing.firing s' ↑t ) := by sorry


--lemma firing_fordward_reversible {R : revPetriNet α β} (s s' : Set R.places)
--  (t : enable s) : firing s t = s' →  Reversing.firing s' t = s := by
--    sorry


theorem rev_commutative {R : revPetriNet α β} (s s' : Set R.places) (t : R.transition)
  (hf : s[*]s') : s'[*]s := by sorry
