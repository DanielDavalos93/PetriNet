import PetriNet.Definitions
import PetriNet.Occurrence

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

def Reversing.is_enabled (s : Set R.places) : Prop :=
  ∀ t, t ∈ Reversing.enable s

def Reversing.firing {R : revPetriNet α β} (s : Set R.places) (t : Reversing.enable s)
  : Set R.places :=
    (s \ (•ᵣ t) ) ∪ (t •ᵣ)

notation:24 lhs:24 "[" rhs:25 "⟩ᵣ" => Reversing.firing lhs rhs _

def Reversing.is_firing {R : revPetriNet α β} (s : Set R.places) (t : Reversing.enable s)
  (s' : Set R.places) : Prop :=
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


lemma enable_fordward_reversible (s s' : Set R.places) (t : enable s) (h : s' = firing s t)
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
        have h5 : y ∈ (•ₜ ↑t.val) := by
          rw [rev_pos_t_equal_pres_t] at h'
          apply And.left h'
        contradiction
      . rename_i h3
        exact h3

lemma enable_fordward_reversible_iff (s s' : Set R.places) (t : enable s) (h : s' = firing s t)
  : t.val ∈  enable s ↔  t.val ∈  Reversing.enable s' := by
    unfold firing at h
    unfold Reversing.enable
    simp only [Set.mem_setOf_eq, Set.mem_diff]
    apply Iff.intro
    . intros h'
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
          unfold enable at h'
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
    . exact fun _ ↦ Subtype.mem t

lemma Reversing.firing_eq1 (s : Set R.places) (t : Reversing.enable s)
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
      have h1 : x∈ s := by apply Set.mem_of_mem_diff h
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, preset_t, Subtype.exists] at h
      apply And.intro
      . exact h1
      . rw [Set.mem_diff] at h
        simp
        intros h2 h3 h4 h5 _ h7
        subst h7
        aesop
    case inr h =>
      right
      aesop
   .intro h
    simp only [Set.mem_inter_iff, and_assoc] at h
    cases h
    case inl h =>
      left
      have h1 : x∈ s := by apply Set.mem_of_mem_diff h
      aesop
    case inr h =>
      right
      aesop

lemma Reversing.firing_eq2 {R : revPetriNet α β} (s : Set R.places)
  (t : Reversing.enable s)
  : Reversing.firing s t = Reversing.Firing s {↑t} := by
    exact Reversing.firing_eq1 s t

/-
lemma reversing_fordward_firing (s s' : Set R.places) (t : Reversing.enable s)
  (h : s' = Reversing.Firing s {t.val})
  : Reversing.Firing s {t.val} = Reversing.Firing s' {t.val} := by
    unfold Reversing.Firing Reversing.enable
    --simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    have h1 : Firing s {t.val} = firing s t := by exact Eq.symm (firing_eq1 s t)
    have h2 : s' = firing s t := by apply Eq.trans h h1
    have h3 : t.val ∈ Reversing.enable s' := by
      apply Iff.mp (enable_fordward_reversible_iff s s' t h2)
      exact Subtype.mem t
    ext x
    simp [rev_pos_t_equal_pres_t, rev_pres_t_equal_pos_t]
    unfold enable at t
    unfold Firing at h h1
    unfold Reversing.enable at h3
    unfold firing at h2
    apply Iff.intro
    . intros himp
      cases himp
      . rename_i h4
        cases h4
        rename_i h5 h6
        have h7 : x∈ s' := by
          simp only [Reversing.preset_t, rev_pres_t_equal_pos_t, Reversing.postset_t, rev_pos_t_equal_pres_t,
            Set.mem_setOf_eq] at h3
          rw [h] at *
          simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq]
          sorry
        left

        sorry
      . rename_i h4
        right

        sorry
    . intro himp
      sorry
-/
/-
** List of executions **
-/
@[simp] def Reversing.firing_seq (s0 : Set R.places)  (l : List R.transition)
  : List (Set R.places) :=
  List.scanl (fun s t => Reversing.Firing s (Set.singleton t)) s0 l

@[reducible]
inductive Reversing.firing_sequence [DecidableEq α] {R : revPetriNet α β} :
  (s : Set R.places) →  List R.transition →  (sn : Set R.places) → Prop
  | empty : ∀ s, Reversing.firing_sequence s [] s
  | step : ∀ s' s'' t fs, (Reversing.firing s t = s')
    →  Reversing.firing_sequence s' fs s''
    →  Reversing.firing_sequence s (t :: fs) s''

notation:200 ls:201 "[[" ts:202 "⟩⟩ᵣ" rs:203 => firing_sequence ls ts rs

@[simp] def Reversing.there_is_seq [DecidableEq α] {R : revPetriNet α β} (s0 sn : Set R.places) : Prop :=
  ∃ (l : List R.transition), Reversing.firing_sequence s0 l sn

notation:10 ss:10"[*]ᵣ"ls:11 => Reversing.there_is_seq ss ls

--Reachable
/-
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



theorem rev_commutative [inst : DecidableEq α] (s s' : Set R.places) (T : List R.transition)
  : Reversing.firing_sequence s T s' ↔ Reversing.firing_sequence s' T.reverse s := by
    apply Iff.intro
    . intro hmp
      cases hmp
      . rw [List.reverse_nil]
        exact Reversing.firing_sequence.empty s
      . rename_i s'' tr en fir stp 
        simp only [List.reverse_cons]
        sorry
    . intro hmpr
      induction T
      . rw [List.reverse_nil] at hmpr
          
        sorry
      . rename_i hd tail stp
        sorry
