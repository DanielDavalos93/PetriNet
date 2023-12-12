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

--def rev_

--lemma rev_preset_p {R : revPetriNet α β} (hpres : ) 

theorem rev_commutative {R : revPetriNet α β} (s s' : Set R.places) (t : R.transition)  (hf : s[*]s') : s'[*]s := by sorry 
