import PetriNet.Definitions

def MenoresQue4 : Finset Nat := {0,1,2,3}

def RelPlacesTrans : MenoresQue4 → MenoresQue4 → Prop :=
  fun p t => match (p : Nat) with
    | 0 => t.1 < 3
    | 1 => 1 ≤ t.1
    | 2 => t.1 = 3
    | 3 => False
    | _ => False

def RelTransPlaces : MenoresQue4 → MenoresQue4 → Prop :=
  fun t p => match (t : Nat) with
    | 0 => p.1 = 2
    | 1 => p.1 = 2
    | 2 => p.1 = 3
    | 3 => p.1 = 3
    | _ => False

lemma m₁ : Set MenoresQue4 := by
  have s₀: Set MenoresQue4 := by exact Set.univ
  have zM: {x // x∈ MenoresQue4} := {val := 0, property := by simp}
  have uM: {x // x∈ MenoresQue4} := {val := 0, property := by simp}
  exact insert uM (insert zM (insert zM s₀))
  
lemma P0 : {1} ∈ 𝒫 MenoresQue4 := by simp
lemma P01 : {0,1} ∈ 𝒫 MenoresQue4 := by
  intro x p
  simp at *
  cases p 
  repeat simp [*]
  
noncomputable def N₁ : PetriNet Nat Nat :=  {
  places := {0,1,2,3},
  transition := {0,1,2,3},
  rel_pt := RelPlacesTrans,
  rel_tp := RelTransPlaces,
  m₀ := m₁
  }

lemma n (x : Nat) : ¬ (x+4) ∈ MenoresQue4 := by simp [MenoresQue4]
lemma obvio (h : 0 ∈  N₁.places) (t : N₁.transition) : ¬ (RelTransPlaces t {val := 0,property:= h}) := 
  by match t with
  | ⟨0,_⟩ => simp [RelTransPlaces]
  | ⟨1,_⟩ => simp [RelTransPlaces]
  | ⟨2,_⟩ => simp [RelTransPlaces]
  | ⟨3,_⟩ => simp [RelTransPlaces]
  | ⟨x+4,p⟩ => 
        have := n x p
        exfalso

example : preset_p (n := N₁) {val := 0 , property := by simp} = ∅ := by
  unfold preset_p
  apply Set.ext
  intro ⟨x,h⟩
  apply Iff.intro
  case mp => 
    intro tr
    apply (obvio _ ⟨x,h⟩ tr)
  case mpr => simp [*]


