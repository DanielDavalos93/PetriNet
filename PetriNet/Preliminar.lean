import Mathlib.Data.Finset.Basic

def supp {S : Type} (m : S →  ℕ ) : Set S := 
  {x : S | m (x) >0}


--def union {S : Type} (m₁ : S →  ℕ ) (m₂ : S →  ℕ ) : ℕ := ∀ x : S, m₁ (x) + m₂ (x)
