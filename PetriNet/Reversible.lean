import PetriNet.Definitions
import PetriNet.Occurrence
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Prod
/-
# Definitions and properties of reversible Petri Net, given a Petri Net

`reversiblePN` is a definition which inherits all properties of `PetriNet`,
with the inverse relations.

* I extend a Petri Net giving only the reversible relation.
For example, if `P : PetriNet Nat Bool` with `1 ≺ True` and `True≺ 2`, then
on `R : reversiblePN Nat Bool` we have `1 ≺ Tue`, `True ≺ 2`, `2 ≺ True` and
`True≺ 1`.
* Definitions of preset and postet are the same. Also for enabled transitions
and firing.

For notations are the same as those used for forward nets, but eqquiped with
a sub-index `ᵣ`.

The main property is prove that s[t⟩s' iff s'[t⟩ᵣs. And for a sequence
seq = t₁;...;tₙ and sᵢ₋₁ [tᵢ⟩sᵢ then s₀[seq]sₙ iff sₙ[← seq]s₀, where
← seq = tₙ;...;t₁.
-/

variable {α β : Type}

/--`Transition` is a type to give orientation on a Petri net's transition, which
are `forward` and `backward`.
-/
inductive Transition where
  | forward : Transition
  | backward : Transition
deriving DecidableEq

open Transition

def isForward (t : β × Transition) : Prop :=
  match t.snd with
    | forward => True
    | backward => False

def isBackward (t : β × Transition) : Prop :=
  match t.snd with
    | forward => False
    | backward => True

def change_orientation (t : β × Transition) : Transition :=
  match t.snd with
    | forward => backward
    | backward => forward

@[simp]
def fw_emb {β : Type} : β ↪ β × Transition :=
  {toFun := fun t => ⟨t, forward⟩, inj' := by exact Prod.mk.inj_right forward}

@[simp]
def bw_emb {β : Type} : β ↪ β × Transition :=
  {toFun := fun t => ⟨t, backward⟩, inj' := by exact Prod.mk.inj_right backward}

def fw_bw_emb {t : Transition} : β ↪ β × Transition :=
    match t with
    | forward => fw_emb
    | backward => bw_emb


--EXAMPLE
--Places
inductive pl
  | a
  | b
  | c
deriving DecidableEq

--Transitions
inductive tr
  | t₁
  | t₂
  | t'₁
  | t'₂

open pl
open tr

def isFw_or_Bw : tr →  Transition
  | t₁ => forward
  | t₂ => forward
  | t'₁ => backward
  | t'₂ => backward

--

lemma not_forward_and_backward : ∀ (t : β × Transition), isForward t → isBackward t → False := by
  unfold isForward isBackward
  intro t fw bw
  cases h : t.snd
  repeat simp_all

def ts_not_fwd_and_bwd : ∀ (t t' : β × Transition), isForward t → isBackward t' → t ≠ t' := by
  unfold isForward isBackward
  intros t t' fw bw ne
  cases h : t.snd
  . simp_all
  . simp_all

def reverse (t : β × Transition) : β × Transition :=
  ⟨t.fst, change_orientation t⟩

prefix:100 "↝ " => reverse
--↝ : write`leadsto` | ... | `lea`

--Alternative prefix
prefix:101 "~>" => reverse

@[simp]
def pair_reverse (t₁ t₂ : β × Transition) : Prop :=
  t₁ = ↝ t₂

notation:110 t₁:110 "↭ " t₂:111 => pair_reverse t₁ t₂
--↭ : write `leftrightsquigarrow` | ... | `leftrightsq`

--Alternative notation
notation:112 t₁:112 "<~>" t₂:113 => pair_reverse t₁ t₂

/--The pair reverse of a reverse transition `~>t` is itself.
-/
@[simp]
def reverse_conv (t : β × Transition) : ↝ (↝ t) = t := by
  unfold reverse
  rcases t with ⟨w, fw | bw⟩
  repeat {. exact rfl}

/--Two transitions are reversing in the order `⟨t₁,t₂⟩` iff are also
  reversing in the order `⟨t₂, t₁⟩`
-/
@[simp]
def reverse_symm (t₁ t₂ : β × Transition) : t₁ ↭ t₂ ↔  t₂ ↭ t₁ := by
  unfold pair_reverse reverse change_orientation
  rcases t₁ with ⟨w, fw | bw⟩
  . rcases t₂ with ⟨w', fw | bw⟩
    . simp_all
    . simp
      constructor ; repeat
      . exact λ x ↦  id (Eq.symm x)
      . simp_all
  . rcases t₂ with ⟨w', fw | bw⟩
    . simp_all
      constructor ; repeat
      . exact λ x ↦  id (Eq.symm x)
      . simp_all
    . simp

@[simp]
lemma self_reverse (t : β × Transition) : t ↭ (↝ t) := by
  unfold pair_reverse
  simp_all


@[simp]
lemma fw_bw_disjoint (T : Finset β) : Disjoint (Finset.map fw_emb T) (Finset.map bw_emb T) := by
  unfold Disjoint
  simp_all
  intros fin hfw hbw b hin
  have h_bfw_emb : b ∈ Finset.map fw_emb T := by exact hfw hin
  have h_bbw_emb : b ∈ Finset.map bw_emb T := by exact hbw hin
  unfold Finset.map at *
  simp_all
  rcases h_bfw_emb with ⟨w, wf⟩
  rcases h_bbw_emb with ⟨w', w'b⟩
  have contra : (w,forward) ≠ (w',backward) := by
    exact ts_not_fwd_and_bwd (w, forward) (w', backward) trivial trivial
  simp_all

/--`revTrans (T)` is the disjoint union of `T` which for each element
`x ∈ revTrans (T)`, `x = (t,forward)` or `x = (t,backward)`.
-/
def revTrans (T : Finset β) : Finset (β × Transition) :=
  Finset.disjUnion (Finset.map fw_emb T) (Finset.map bw_emb T) (fw_bw_disjoint T)

theorem revTrans.singleton {t : β} {tr : Transition} (h : revTrans {t}) : β × Transition := by
  unfold revTrans at h
  exact ~>(fw_bw_emb (t := tr) t)

lemma revTrans.fst_in (T : Finset β) (x : revTrans T) : x.val.fst ∈ T.val := by
sorry

def revTrans.val {T : Finset β} (x : revTrans T) : T :=
  { val := x.val.1, property := by exact Iff.mp Finset.mem_val (revTrans.fst_in T x)}


lemma revTrans.val_fst {T : Finset β} (x : revTrans T) : (revTrans.val x ).val = x.val.1 := by
  rfl

/--
  # Reversible Petri net
  `revPetriNet` is the same definition of a `P : PetriNet α β`, but specifically
  the transition `t` in `P` are now the form `(t,fw|bw)`. This new net, given `P`,
  has the type `: PetriNet α (β × Transition)`.
-/
@[simp]
def revPetriNet (P : PetriNet α β) : PetriNet α (β × Transition) := {
 places := P.places
 transition := revTrans (P.transition)
 rel_pt :=  λ (p : P.places) (t : revTrans (P.transition)) =>
  match t.val with
  | (_,forward) => P.rel_pt p (revTrans.val t)
  | (_, backward) => P.rel_tp (revTrans.val t) p
 rel_tp :=  λ (t : revTrans P.transition) (p : P.places) =>
  match t.val with
  | (_, forward) => P.rel_tp (revTrans.val t) p
  | (_, backward) => P.rel_pt p (revTrans.val t)
 m₀ := P.m₀
}

def revTrans_singleton {P : PetriNet α β} (t : P.transition) : (revPetriNet P).transition := by sorry

lemma rev_is_enabled (P : PetriNet α β) (s : Set P.places) (t : P.transition)
  (h : is_enabled s t) : is_enabled (P := revPetriNet P) s (revTrans_singleton t) := by
  sorry


lemma rev_enable (P : PetriNet α β) (s : Set P.places) (t : enable s)
  : enable (P := revPetriNet P) s := by
  sorry

lemma rev_firing (P : PetriNet α β) (s : Set P.places) (t : enable s) (h : firing s t)
  : firing (P := revPetriNet P) s (rev_enable P s t) := by
  sorry

lemma firing_fw_bw (P : PetriNet α β) (s s' : Set P.places) (t : enable s) (t' : enable s')
  (h : is_firing s t s') : is_firing (P := revPetriNet P) s' (rev_enable P s' t') s := by sorry

open Nat
open String

def ex_places : Finset String := {"a","b"}

def ex_trans : Finset Nat := {1}
