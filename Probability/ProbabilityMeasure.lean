
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
  


open MeasureTheory ProbabilityTheory
namespace WeatherMarkovChain

/-- The state space of our Markov chain -/
inductive State where
  | Good
  | Bad
  deriving DecidableEq, Fintype, Repr

/-- Discrete σ-algebra (power set) - every subset is measurable -/
instance : MeasurableSpace State := ⊤

instance : MeasurableSingletonClass State := ⟨fun _ => trivial⟩

instance : DiscreteMeasurableSpace State := ⟨fun _ => trivial⟩

/-- Transition probabilities P(next | current) as ENNReal -/
noncomputable def transProb : State → State → ENNReal
  | .Good, .Good => 3/5
  | .Good, .Bad  => 2/5
  | .Bad,  .Good => 7/10
  | .Bad,  .Bad  => 3/10

/-- Stochastic matrix property: each row sums to 1 -/

theorem transProb_sum (s : State) : transProb s .Good + transProb s .Bad = 1 := by
  cases s <;> simp only [transProb]
  · -- Good case: 3/5 + 2/5 = 1
    calc (3 : ENNReal) / 5 + 2 / 5 
        = (3 + 2) / 5 := by rw [← ENNReal.add_div]
      _ = 5 / 5 := by norm_num
      _ = 1 := ENNReal.div_self (by norm_num) ENNReal.coe_ne_top
  · -- Bad case: 7/10 + 3/10 = 1
    calc (7 : ENNReal) / 10 + 3 / 10 
        = (7 + 3) / 10 := by rw [← ENNReal.add_div]
      _ = 10 / 10 := by norm_num
      _ = 1 := ENNReal.div_self (by norm_num) ENNReal.coe_ne_top

/-- Transition measure: weighted sum of Dirac measures -/
noncomputable def transMeasure (s : State) : Measure State :=
  transProb s .Good • Measure.dirac .Good + transProb s .Bad • Measure.dirac .Bad

/-- The transition measure assigns probability 1 to the full space -/
theorem transMeasure_univ (s : State) : transMeasure s Set.univ = 1 := by
  unfold transMeasure 
  
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply] 
  
  simp only [Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ,
    Pi.one_apply, smul_eq_mul, mul_one]
  exact transProb_sum s

/-- Each transition measure is a probability measure -/
instance transMeasure_isProbabilityMeasure (s : State) :
    IsProbabilityMeasure (transMeasure s) :=
  ⟨transMeasure_univ s⟩

/-- Measurability of the transition measure (trivial for discrete domain) -/
theorem transMeasure_measurable : Measurable transMeasure := by
  

  intro s _
  -- State has discrete σ-algebra (= ⊤), so every set is measurable
  trivial

/-- The Markov kernel for the weather chain -/
noncomputable def weatherKernel : Kernel State State where
  toFun := transMeasure
  measurable' := transMeasure_measurable

/-- Proof that it's a Markov kernel (each fiber is a probability measure) -/
instance : IsMarkovKernel weatherKernel where
  isProbabilityMeasure s := transMeasure_isProbabilityMeasure s



end WeatherMarkovChain
