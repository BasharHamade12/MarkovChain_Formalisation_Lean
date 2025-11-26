
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
  
  MeasurableSet' := fun _ => True

  
  measurableSet_empty := trivial 


  
  measurableSet_compl := fun _ _ => trivial
      
  measurableSet_iUnion := fun _ _ => trivial  
 





open MeasureTheory 
open Measurable
 



-- Let's prove it from scratch using the axioms
variable {α : Type*} [MeasurableSpace α]


-- Step-by-step proof that Set.univ is measurable
theorem universal_set_measurable : MeasurableSet (Set.univ : Set α) := by
  -- Step 1: Recall that Set.univ = ∅ᶜ (complement of empty set)
  have h1 : (Set.univ : Set α) = ∅ᶜ := by
    -- Prove this equality by extensionality
    ext x
    simp only [Set.mem_univ, Set.mem_compl_iff, Set.mem_empty_iff_false]
    -- x ∈ Set.univ is always true
    -- x ∈ ∅ᶜ means x ∉ ∅, which is also always true
    constructor
    · intro _
      -- If x ∈ Set.univ, then x ∉ ∅
      simp
    · intro _
      -- If x ∉ ∅, then x ∈ Set.univ
      trivial
  
  -- Step 2: Rewrite our goal using this equality
  rw [h1]
  
  -- Step 3: Apply the axiom that complement of measurable is measurable
  apply MeasurableSet.compl
  
  -- Step 4: We need to prove that ∅ is measurable
  -- This is one of the axioms of a measurable space
  exact MeasurableSet.empty  


-- Step-by-step proof that Set.univ is measurable
theorem universal_set_measurable2 : MeasurableSet (Set.univ : Set α) := by
  -- Step 1: Recall that Set.univ = ∅ᶜ (complement of empty set)
  have h1 : (Set.univ : Set α) = ∅ᶜ := by
    -- Prove this equality by extensionality
    ext x
    simp only [Set.mem_univ, Set.mem_compl_iff, Set.mem_empty_iff_false]
    -- x ∈ Set.univ is always true
    -- x ∈ ∅ᶜ means x ∉ ∅, which is also always true
    constructor
    · intro _
      -- If x ∈ Set.univ, then x ∉ ∅
      simp
    · intro _
      -- If x ∉ ∅, then x ∈ Set.univ
      trivial
  
  -- Step 2: Rewrite our goal using this equality
  rw [h1]
  
  -- Step 3: Apply the axiom that complement of measurable is measurable
  apply MeasurableSet.compl
  
  -- Step 4: We need to prove that ∅ is measurable
  -- This is one of the axioms of a measurable space
  exact MeasurableSet.empty 


instance : MeasurableSpace DieOutcome where
  MeasurableSet' := fun _ => True  
  measurableSet_empty := trivial
  measurableSet_compl := fun _ _ => trivial
  measurableSet_iUnion := fun _ _ => trivial 



variable [MeasurableSpace Ω]  



 -- variable (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
variable {E : Type*} [MeasurableSpace E]
variable (X : DieOutcome → E) (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
variable (hX : Measurable X)


-- Define events (sets of outcomes)
def isEven (d : DieOutcome) : Prop :=
  d = DieOutcome.two ∨ d = DieOutcome.four ∨ d = DieOutcome.six

def isLow (d : DieOutcome) : Prop :=
  d = DieOutcome.one ∨ d = DieOutcome.two ∨ d = DieOutcome.three

-- The event "X is even"
def X_is_even (X : Ω → DieOutcome) : Set Ω :=
  {ω | isEven (X ω)}

-- General lemma for any predicate on DieOutcome
lemma measurable_set_preimage_pred (Ω : Type*) [MeasurableSpace Ω]
    (X : Ω → DieOutcome) (hX : Measurable X)
    (P : DieOutcome → Prop) :
    MeasurableSet {ω | P (X ω)} :=
  by
  
  have h_eq : {ω | P (X ω)} = X ⁻¹' {d | P d} := rfl
  rw [h_eq]

 
  have h_target_measurable : MeasurableSet {d | P d} := by
    
    trivial
  
  unfold Measurable at hX 

  apply hX 

  --exact hX h_target_measurable

-- The final application lemma is now correct:
lemma X_is_even_measurable_final (Ω : Type*) [MeasurableSpace Ω]
    (X : Ω → DieOutcome) (hX : Measurable X) :
    MeasurableSet (X_is_even X) :=
  measurable_set_preimage_pred Ω X hX isEven 


  -- Two events are independent
def IndepSet [MeasurableSpace Ω] (μ : Measure Ω) 
    (s t : Set Ω) : Prop :=
  μ (s ∩ t) = μ s * μ t

-- Independence is symmetric
theorem indepSet_symm (μ : Measure Ω) 
    {s t : Set Ω} (h : IndepSet μ s t) :
    IndepSet μ t s := by
  rw [IndepSet] 

  rw [Set.inter_comm] 

  rw [mul_comm] 

  unfold IndepSet at h 
  
  exact h




-- Finite version


theorem measure_eq_sum_of_partition  (μ : Measure Ω) 
    {s : Set Ω} {f : ℕ → Set Ω} (hf : ∀ i, MeasurableSet (f i)) 
    (hs : MeasurableSet s) 
    (hdisj : Pairwise fun i j => Disjoint (f i) (f j))
    (hunion : s ⊆ ⋃ i, f i) :
    μ s = ∑' i, μ (s ∩ f i) := by 
  -- First, use the fact that s ⊆ ⋃ i, f i to write s = s ∩ (⋃ i, f i)
  have : s = s ∩ (⋃ i, f i) := by 
    simp 
    trivial 
  
  rw [this]

  -- Now apply Set.inter_iUnion
  rw [Set.inter_iUnion]
  -- Apply measure_iUnion for disjoint sets
  rw [measure_iUnion] 

  ·

    congr 1 
    ext i  
    
    rw [Set.iUnion_inter] 
    
    congr 1
    ext j
    simp 
    intro j_fi j_a 
    exists i 

  

  
  · -- rw [Set.disjoint_iff] 
    unfold Pairwise  
    intro i j i_not_j 
    rw [Function.onFun_apply]
    rw [Set.disjoint_iff]  
    rw [Set.inter_assoc, Set.inter_comm, Set.inter_left_comm] 
    simp 
    have hfifj : Disjoint (f i) (f j) := hdisj i_not_j 
    rw [Set.disjoint_iff_inter_eq_empty] at hfifj 
    rw [hfifj] 
    simp
    --rw [Set.inter_empty]   
    
    --simp  
  .

    intro i  
    
    apply MeasurableSet.inter 
    . 
      trivial 
    .
      apply hf
      
  
      
      
      

    


    

  


-- Composition of measurable functions is measurable
theorem Measurable_comp {α β γ : Type*} [MeasurableSpace α] 
    [MeasurableSpace β] [MeasurableSpace γ]
    {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    Measurable (g ∘ f) := by   
    unfold Measurable 
    intro t 
    intro measurable_t  
    unfold Measurable at hg   
    rw [Set.preimage_comp] 
    unfold Measurable at hf 
    apply hf 
    apply hg 
    exact measurable_t 
  
