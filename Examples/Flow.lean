import PetriNet
open Nat
open Sum


lemma inFS {n m : ℕ} (h : LT.lt n m) : n ∈ Finset.range m :=
   Finset.mem_range.mpr h

def p₀ : Finset.range 2  := ⟨0, inFS (zero_lt_succ  (succ 0))⟩
def p₁ : Finset.range 2 := ⟨succ 0, inFS (lt.base  (succ 0))⟩

def t₀ : Finset.range 1 := ⟨0, inFS (zero_lt_succ 0)⟩

def N₁ : PetriNet (Finset.range 2) (Finset.range 1) :=
{
  places := {p₀, p₁}  
  transition := {t₀}
  rel_pt := fun p t => (p = p₀ ∨ p = p₁) ∧ t = t₀
  rel_tp := fun t p => t = t₀ ∧ p = p₁
  m₀ := {p₀}
}



noncomputable def N₀ : PetriNet (Fin 2) (Fin 1) :=
{
  places := {0,1}
  transition := {0,1}
  rel_pt := fun p _ =>  ite (p = 0) true false
  rel_tp := fun _ p =>  ite (p = 1) true false
  m₀ := {1,2}
}

#eval N₀.rel_pt 0 0 -- true
#eval N₀.rel_pt 1 0 -- false

#eval N₀.rel_tp 0 0 -- false
#eval N₀.rel_tp 0 1 -- true

#eval (flow N₀) (inl 0) (inr 0) -- true
#eval (flow N₀) (inr 0) (inl 1) -- true

--#eval tc (flow N₀) (inr 1) (inl 2)
#reduce tc (flow N₀) (inr 0) (inl 0)

#check ((flow N₀) (inl 0) (inr 0)) = true
#check N₀.rel_pt 0 0

lemma x : (flow N₀) (inl 0) (inr 0) := by
  unfold flow N₀;
  simp

lemma y : (flow N₀) (inr 0) (inl 1) := by
  unfold flow N₀;
  simp

example:  tc (flow N₀) (inl 0) (inl 1) :=
  tc.trans x (tc.base y)

