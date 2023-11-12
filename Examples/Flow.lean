import PetriNet.Ocurrence

lemma inFS {n m : ℕ} (h : LT.lt n m) : n ∈ Finset.range m :=
   Finset.mem_range.mpr h

def p₀ : Finset.range 2  := ⟨0, inFS (zero_lt_succ  (succ 0))⟩
def p₁ : Finset.range 2 := ⟨succ 0, inFS (lt.base  (succ 0))⟩

def t₀ : Finset.range 1 := ⟨0, inFS (zero_lt_succ 0)⟩

def N₁ : PetriNet (Finset.range 2) (Finset.range 1) :=
{
  rel_pt := fun p t => (p = p₀ ∨ p = p₁) ∧ t = t₀
  rel_tp := fun t p => t = t₀ ∧ p = p₁
  m := {p₀, p₁}
}

#check (fun p t => (p = p₀ ∨ p = p₁) ∧ t = t₀)

def f := (fun p t => (p = p₀ ∨ p = p₁) ∧ t = t₀)
#eval f  p₀ t₀

#eval N₁.rel_pt p₀ t₀

#check (flow  N₁) (inr t₀)  (inl p₀)
#eval (flow  N₁) (inr t₀)  (inl p₀)
