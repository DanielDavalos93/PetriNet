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
lemma revPetriNet_eq_places (R₁ R₂ : revPetriNet α β)
  (places : R₁.places = R₂.places) (a : α) : a ∈  R₁.places ↔  a ∈  R₂.places := by
    exact Iff.of_eq (congrArg (Membership.mem a) places)

lemma revPetriNet_eq_transition (R₁ R₂ : revPetriNet α β)
  (trans : R₁.transition = R₂.transition) (b : β)
  : b ∈  R₁.transition ↔  b ∈  R₂.transition := by
    exact Iff.of_eq (congrArg (Membership.mem b) trans)

@[simp] lemma revPetriNet_equality (R₁ R₂ : revPetriNet α β)
  (places : R₁.places = R₂.places) (transition : R₁.transition = R₂.transition)
  (m₀ : HEq R₁.m₀ R₂.m₀) (rel_pt : HEq R₁.rel_pt R₂.rel_pt) (rel_tp : HEq R₁.rel_tp R₂.rel_tp)
  (rev_rel_pt : HEq R₁.rev_rel_pt R₂.rev_rel_pt) (rev_rel_tp : HEq R₁.rev_rel_tp R₂.rev_rel_tp)
  : R₁ = R₂ := by
    exact revPetriNet.ext R₁ R₂ places transition rel_pt rel_tp m₀ rev_rel_pt rev_rel_tp
--------

/-
* Reversing Flow
-/

@[reducible] def Reversing.flow (R : revPetriNet α β) :
    (R.places ⊕  R.transition) →  (R.places ⊕  R.transition) →  Prop
    | Sum.inl p, Sum.inr t  => R.rev_rel_pt p t
    | Sum.inr t, Sum.inl p  => R.rev_rel_tp t p
    | _, _                  => false

notation:20 l:20 "≺ ᵣ" r:21 => Reversing.flow _ l r

@[reducible] inductive tranClos (r : α →  α →  Prop) : α →  α →  Prop
   | base {x y : α} : r x y →  tranClos r x y
   | step {x y z : α} : r x y →  tranClos r y z →  tranClos r x z

@[reducible] def Reversing.predecesor {α β : Type} {R : revPetriNet α β}
  (x y : R.places ⊕  R.transition) : Prop :=
     (tranClos (Reversing.flow R)) x y ∨ x = y

notation:22 l:22 "≼ ᵣ" r:23 => Reversing.predecesor _ l r

------

@[simp] def Reversing.preset_t {R : revPetriNet α β} (t : R.transition) : Set R.places :=
  Relation.pre_image R.rev_rel_pt t

prefix:1 "•ᵣ" => Reversing.preset_t

@[simp] def Reversing.postset_t {R : revPetriNet α β} (t : R.transition) : Set R.places :=
 Relation.image R.rev_rel_tp t

postfix:2 "•ᵣ" => Reversing.postset_t

lemma pres_t_equal_rev_post_t {R : revPetriNet α β} (t : R.transition) : (•ₜ t) = (t •ᵣ) :=
  calc
    (•ₜt) = Relation.pre_image R.rel_pt t   := by rfl
       _  = {p : R.places | R.rel_pt p t}   := by rfl
       _ = {p : R.places | R.rev_rel_tp t p}:= by
          sorry
       _ = Relation.image R.rev_rel_tp t    := by rfl

lemma post_t_equal_rev_pres_t {R : revPetriNet α β} (t : R.transition) : (t •ₜ) = (•ᵣ t) := by
  sorry

/-
 ** Reversing Firing
 First, the enable version of reversible Petri nets are analogous to the forward Petri nets.
 Second, we write `s⟨t] = s'` for reversible firing such that s↝ s' through the transition t,
 where `s'[t⟩ = s` is the fordward version and s'↠ s.
-/
def Reversing.enable {R : revPetriNet α β} (s : Set R.places) : Set R.transition :=
 {t : R.transition | (•ᵣ t) ⊆ s ∧ (t •ᵣ)∩ s ⊆ (•ᵣ t)}

def Reversing.firing {R : revPetriNet α β} (s : Set R.places) (t : Reversing.enable s)
  : Set R.places :=
    (Set.diff s (•ᵣ t) ) ∪ (t •ᵣ)

notation:24 lhs:24 "[" rhs:25 "⟩ᵣ" => Reversing.firing lhs rhs

--lemma firing_fordwad_reversible {R : revPetriNet α β} (s s' : Set R.places) 
--  (t : enable s) (hf : firing s t = s') : (t ∈  Reversing.enable s') := by
--  sorry


theorem rev_commutative {R : revPetriNet α β} (s s' : Set R.places) (t : R.transition)
  (hf : s[*]s') : s'[*]s := by sorry
