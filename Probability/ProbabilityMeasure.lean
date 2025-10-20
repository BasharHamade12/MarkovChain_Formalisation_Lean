
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
    cases hs with
    | inl h => -- s = ∅
      simp [h, Set.compl_empty]

    | inr hs' => cases hs' with
      | inl h => -- s = univ
        simp [h, Set.compl_univ]

      | inr hs'' => cases hs'' with
        | inl h =>
          right
          right
          right
          ext d

          simp only [Set.mem_setOf, h]
          cases d
          constructor
          .
            simp
          .
            simp
          constructor
          .
            simp
          .
            simp
          constructor
          .
            simp
          .
            simp
          constructor
          .
            simp
          .
            simp
          constructor
          .
            simp
          .
            simp
          constructor
          .
            simp
          .
            simp




          -- Would need to prove that complement of low is high
        | inr h => -- s = high outcomes
          right
          right
          left
          ext d

          simp only [Set.mem_setOf, h]
          cases d
          constructor
          .
            simp
          .
            simp
          constructor
          .
            simp
          .
            simp
          constructor
          .
            simp
          .
            simp
          constructor
          .
            simp
          .
            simp
          constructor
          .
            simp
          .
            simp
          constructor
          .
            simp
          .
            simp


  -- Property 3: Countable union (this would require more work to prove properly)
  measurableSet_iUnion := by
    intro f h


    simp
    by_cases h_all_empty : ∀ i, f i = ∅
    · left
      trivial
    · -- Since not all are empty, at least one is non-empty
      push_neg at h_all_empty
      obtain ⟨j, hj⟩ := h_all_empty
      by_cases h_univ : ∃ i, f i = Set.univ
      · obtain ⟨k, hk⟩ := h_univ
        right
        left
        ext x
        simp only [Set.mem_iUnion, Set.mem_univ]
        constructor
        · intro blah
          trivial
        · simp
          use k
          rw [hk]
          trivial
      · simp at h_univ
        by_cases h_both : (∃ i, f i = {d | d.toNat ≤ 3}) ∧ (∃ k, f k = {d | d.toNat > 3})
        · right
          left
          obtain ⟨i, hi⟩ := h_both.1
          obtain ⟨k, hk⟩ := h_both.2
          ext d
          constructor
          · intro h
            trivial
          · intro h
            simp only [Set.mem_iUnion]
            by_cases hd : (d.toNat : ℕ) ≤ 3
            · use i
              rw [hi]
              trivial
            · use k
              rw [hk]
              simp at hd
              trivial
        · push_neg at h_both
          obtain (hempty | huniv | hle3 | hgt3) := h j
          · rw [hempty] at hj
            exfalso
            simp at hj
          · right
            left
            ext a
            constructor
            .
              intro h
              simp only [Set.mem_iUnion] at h
              obtain ⟨i, hi⟩ := h
              trivial

            .
              intro h
              simp only [Set.mem_iUnion]
              use j
              rw [huniv]
              exact h






          · right
            right
            left
            ext b
            constructor
            · intro hh
              simp only [Set.mem_iUnion] at hh
              obtain ⟨i, hi⟩ := hh
              have no_gt3 : ∀ x, f x ≠ {d | d.toNat > 3} := h_both ⟨j, hle3⟩
              -- Now examine what f i can be (using h)
              obtain (hempty | huniv | hle3' | hgt3') := h i
              · -- f i = ∅: impossible since b ∈ f i
                rw [hempty] at hi
                exact absurd hi (Set.not_mem_empty b)
              · -- f i = Set.univ: impossible by h_univ
                exact absurd huniv (h_univ i)
              · -- f i = {d | d.toNat ≤ 3}: this gives us what we need
                rw [hle3'] at hi
                exact hi
              · -- f i = {d | d.toNat > 3}: impossible by no_gt3
                exact absurd hgt3' (no_gt3 i)
            · intro hh
              simp only [Set.mem_iUnion]
              use j
              rw [hle3]
              exact hh
          · -- Case: f j = {d | d.toNat > 3}
            right
            right
            right
            -- Since f j = {d | d.toNat > 3}, no set can be {d | d.toNat ≤ 3}
            have no_le3 : ∀ i, f i ≠ {d | d.toNat ≤ 3} := by
              intro i h_contra
              have := h_both ⟨i, h_contra⟩ j
              exact this hgt3
            ext b
            constructor
            · intro hh
              simp only [Set.mem_iUnion] at hh
              obtain ⟨i, hi⟩ := hh
              obtain (hempty | huniv | hle3' | hgt3') := h i
              · rw [hempty] at hi
                exact absurd hi (Set.not_mem_empty b)
              · exact absurd huniv (h_univ i)
              · exact absurd hle3' (no_le3 i)
              · rw [hgt3'] at hi
                exact hi
            · intro hh
              simp only [Set.mem_iUnion]
              use j
              rw [hgt3]
              exact hh








































     -- Implementation would show closure under countable unions

/-- Example showing that not all sets are measurable in the coarse σ-algebra -/
def singletonOne : Set DieOutcome := {DieOutcome.one}

-- This singleton set would NOT be measurable in the coarse σ-algebra
-- (though we can't easily express this negative statement in Lean)
