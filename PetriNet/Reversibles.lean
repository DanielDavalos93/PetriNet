import PetriNet.Definitions
import PetriNet.Occurrence

/-
# Definitions and properties of reversible Petri Net, given a Petri Net

I extend a Petri Net giving only the reversible relation.
For example, if `P : PetriNet Nat Bool` with `1 ≺ True` and `True≺ 2`, then
on `R : revPetriNet Nat Bool` we have `1 ≺ Tue`, `True ≺ 2`, `2 ≺ True` and 
`True≺ 1`.
-/
@[ext] structure revPetriNet (α : Type) (β : Type) extends (PetriNet α β) where
  rev_rel_pt : places →  transition →  Prop
  rev_rel_tp : transition →  places →  Prop

variable {α β : Type} {R : revPetriNet α β}

def rev_rel_pt (p : R.places) (t : R.transition) : Prop :=
  R.rel_tp t p

def rev_rel_tp (t : R.transition) (p : R.places) : Prop :=
  R.rev_rel_pt p t

/- 
Proving the equality of two reversible Petri nets R₁ and R₂
-/
lemma revPetriNet_eq_places (R₁ R₂ : revPetriNet α β) (places : R₁.places = R₂.places)
  (a : α) : a ∈  R₁.places ↔  a ∈  R₂.places := by
    exact Iff.of_eq (congrArg (Membership.mem a) places)

lemma revPetriNet_eq_transition (R₁ R₂ : revPetriNet α β) (trans : R₁.transition = R₂.transition)
  (b : β) : b ∈  R₁.transition ↔  b ∈  R₂.transition := by
    exact Iff.of_eq (congrArg (Membership.mem b) trans)

@[simp] lemma revPetriNet_equality (R₁ R₂ : revPetriNet α β) (places : R₁.places = R₂.places) 
  (transition : R₁.transition = R₂.transition) (m₀ : HEq R₁.m₀ R₂.m₀)  
  (rel_pt : HEq R₁.rel_pt R₂.rel_pt) (rel_tp : HEq R₁.rel_tp R₂.rel_tp)
  (rev_rel_pt : HEq R₁.rev_rel_pt R₂.rev_rel_pt) (rev_rel_tp : HEq R₁.rev_rel_tp R₂.rev_rel_tp)
  : R₁ = R₂ := by 
    exact revPetriNet.ext R₁ R₂ places transition rel_pt rel_tp m₀ rev_rel_pt rev_rel_tp
--------

@[simp] def rev_preset_t {R : revPetriNet α β} (t : R.transition) : Set R.places :=
  Relation.pre_image R.rev_rel_pt t 

prefix:1 "•ᵣ" => rev_preset_t

@[simp] def rev_postset_t {R : revPetriNet α β} (t : R.transition) : Set R.places :=
 Relation.image R.rev_rel_tp t

postfix:2 "•ᵣ" => rev_postset_t

lemma pres_s_equal_rev_post_s' {R : revPetriNet α β} (s s' : Set R.places) (t : R.transition) 
  : (•ₜ t) = (t •ᵣ) := by sorry

/-
 ** Reversing Firing 
If `rev_rel_pt p t = rel_tp t p` then •ᵣ t
-/

def rev_firing {R : revPetriNet α β} (s : Set R.places) (t : enable s) : Set R.places := sorry
  

--def rev_enable {R : revPetriNet α β} (s : Set R.places) : Set R.transition :=
-- {t : R.transition | (•ᵣ t) ⊆ s ∧ (t •ᵣ)∩ s ⊆ (•ᵣ t)}

--lemma reversible (N : PetriNet α β) (R : revPetriNet α β)


theorem rev_commutative {R : revPetriNet α β} (s s' : Set R.places) (t : R.transition)  (hf : s[*]s') : s'[*]s := by sorry 
