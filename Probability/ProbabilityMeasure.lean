
import Mathlib
/-- The outcome of rolling a single die -/
inductive DieOutcome where
  | one | two | three | four | five | six
  deriving DecidableEq

/-- The sample space for a die roll with the discrete σ-algebra
    (all subsets are measurable) -/
def DieMeasurableSpace : MeasurableSpace DieOutcome where
  -- For the discrete σ-algebra, every subset is measurable
  MeasurableSet' := fun _ => True

  -- Property 1: The empty set is measurable
  measurableSet_empty := trivial

  -- Property 2: The complement of any measurable set is measurable
  measurableSet_compl := fun _ _ => trivial

  -- Property 3: Countable unions of measurable sets are measurable
  measurableSet_iUnion := fun _ _ => trivial

/-- Helper function to convert die outcomes to natural numbers -/
def DieOutcome.toNat : DieOutcome → Nat
  | one => 1 | two => 2 | three => 3
  | four => 4 | five => 5 | six => 6

/-- Example: Define some events as sets -/

-- Event: rolling an even number
def even : Set DieOutcome :=
  {d | d.toNat % 2 = 0}

-- Event: rolling at least 4
def atLeastFour : Set DieOutcome :=
  {d | d.toNat ≥ 4}

-- Event: rolling a prime number (2, 3, 5)
def prime : Set DieOutcome :=
  {DieOutcome.two, DieOutcome.three, DieOutcome.five}





/-- Alternative: A more interesting σ-algebra example -/
def DieCoarseMeasurableSpace : MeasurableSpace DieOutcome where
  -- Only sets that can be expressed in terms of "low" (1,2,3) vs "high" (4,5,6)
  -- plus empty set and full set are measurable
  MeasurableSet' := fun s =>
    s = ∅ ∨
    s = Set.univ ∨
    s = {d | d.toNat ≤ 3} ∨
    s = {d | d.toNat > 3}

  -- Property 1: Empty set is measurable
  measurableSet_empty := Or.inl rfl

  -- Property 2: Complement of measurable set is measurable
  measurableSet_compl := by
    intro s hs
    rcases hs with h | h | h | h
    · simp [h, Set.compl_empty]
    · simp [h, Set.compl_univ]
    · right; right; right
      simp [h, Set.ext_iff, Set.mem_compl_iff, Set.mem_setOf]
      
      
    · right; right; left
      simp [h, Set.ext_iff, Set.mem_compl_iff, Set.mem_setOf]
      
  -- Property 3: Countable union (this would require more work to prove properly)
  measurableSet_iUnion := by
    intro f h
    simp only [Set.iUnion_eq_empty, not_forall]
    
    by_cases h_all_empty : ∀ i, f i = ∅
    · left; exact h_all_empty
    
    push_neg at h_all_empty
    obtain ⟨j, hj⟩ := h_all_empty
    
    -- Determine which types of sets exist
    by_cases h_univ : ∃ i, f i = Set.univ
    · -- Universe exists: union is universe
      obtain ⟨k, hk⟩ := h_univ
      simp [Set.eq_univ_iff_forall, Set.mem_iUnion]
      right ; left 
      intro x 
      use k 
      rw [hk] 
      trivial 

      
    
    -- No universe, check for both partition types
    by_cases h_both : (∃ i, f i = {d | d.toNat ≤ 3}) ∧ (∃ k, f k = {d | d.toNat > 3})
    · -- Both partition types exist: union is universe
      obtain ⟨⟨i, hi⟩, ⟨k, hk⟩⟩ := h_both
      right; left
      simp [Set.eq_univ_iff_forall, Set.mem_iUnion]
      intro d
      by_cases hd : d.toNat ≤ 3 <;> [use i; use k] <;> simp [hi, hk, hd]
    
    -- Only one partition type exists
    push_neg at h_both
    rcases h j with hempty | huniv | hle3 | hgt3
    · simp [hempty] at hj  -- Contradiction
    · simp at h_univ 
      specialize h_univ j
      contradiction 
      


    · -- Only ≤3 sets exist
      right; right; left
      ext b; simp only [Set.mem_iUnion, Set.mem_setOf]
      constructor
      · intro ⟨i, hi⟩
        have := h_both ⟨j, hle3⟩
        rcases h i with h1 | h2 | h3 | h4
        · simp [h1] at hi
        · simp at h_univ 
          specialize h_univ i 
          contradiction 
          
          
        · simp [h3] at hi; exact hi
        · exact absurd h4 (this i)
      · intro hb; use j; simp [hle3, hb]
    · -- Only >3 sets exist  
      right; right; right
      have no_le3 : ∀ i, f i ≠ {d | d.toNat ≤ 3} := fun i h_contra => 
        h_both ⟨i, h_contra⟩ j hgt3
      ext b; simp only [Set.mem_iUnion, Set.mem_setOf]
      constructor
      · intro ⟨i, hi⟩
        rcases h i with h1 | h2 | h3 | h4
        · simp [h1] at hi
        · simp at h_univ 
          specialize h_univ i
          contradiction 

        · exact absurd h3 (no_le3 i)
        · simp [h4] at hi; exact hi
      · intro hb; use j; simp [hgt3, hb]













