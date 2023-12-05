import PetriNet.Definitions
import PetriNet.Occurrence

variable (α β : Type)

structure revPetriNet (α : Type) (β : Type) extends (PetriNet α β) where
  rev_rel_pt (p : places) (t : transition) : Prop := rel_tp t p
  rev_rel_tp (t : transition) (p : places) : Prop := rel_pt p t
 
def rev_preset_p {R : revPetriNet α β} (p : R.places) : Set R.transition :=
  Relation.pre_image R.rel_tp p ∪ Relation.pre_image R.rev_rel_tp p

def rev_poset_p {R : revPetriNet α β} (p : R.places) : Set R.transition :=
  Relation.image R.rel_pt p ∪ Relation.image R.rev_rel_pt p

theorem rev_commutative {R : revPetriNet α β} (s s' : Set R.places) (t : R.transition)  (hf : s[*]s') : s'[*]s := by sorry 
