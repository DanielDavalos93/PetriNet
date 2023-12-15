import PetriNet.Definitions
import PetriNet.Occurrence

variable (α β : Type)

/-
# Definitions and properties of reversible Petri Net, given a Petri Net

I extend a Petri Net giving only the reversible relation.
For example, if `P : PetriNet Nat Bool` with `1 ≺ True` and `True≺ 2`, then
on `R : revPetriNet Nat Bool` we have `1 ≺ Tue`, `True ≺ 2`, `2 ≺ True` and 
`True≺ 1`.
-/
structure revPetriNet (α : Type) (β : Type) extends (PetriNet α β) where
  rev_rel_pt (p : places) (t : transition) : Prop := rel_tp t p
  rev_rel_tp (t : transition) (p : places) : Prop := rel_pt p t

def rev_preset_t {R : revPetriNet α β} (p : R.transition) : Set R.places :=
 Relation.pre_image R.rev_rel_pt p 

prefix:1 "•ᵣ" => rev_preset_t

def rev_postset_t {R : revPetriNet α β} (p : R.transition) : Set R.places :=
 Relation.image R.rev_rel_tp p 

prefix:2 "•ᵣ" => rev_postset_t

def rev_enable {R : PetriNet α β} (s : Set R.places) : Set R.transition :=
 {t : R.transition | (•ᵣ t) ⊆ s ∧ (t •ᵣ)∩ s ⊆ (•ᵣ t)}

--lemma rev_preset_p {R : revPetriNet α β} (t : R.transition) (s : Set R.places) : 

theorem rev_commutative {R : revPetriNet α β} (s s' : Set R.places) (t : R.transition)  (hf : s[*]s') : s'[*]s := by sorry 
