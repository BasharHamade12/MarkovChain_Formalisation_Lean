import Mathlib

open MeasureTheory ProbabilityTheory

/-- A Markov chain is defined by an initial distribution and a transition kernel -/
structure MarkovChain (S : Type*) [MeasurableSpace S] where
  μ₀ : Measure S
  κ : Kernel S S
  hκ : IsMarkovKernel κ

variable {S : Type*} [MeasurableSpace S] (mc : MarkovChain S)



/-! ## The 4-State DTMC -/

namespace FourStateDTMC

inductive State4 where
  | S0 | S1 | S2 | S3
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace State4 := ⊤
instance : MeasurableSingletonClass State4 := ⟨fun _ => trivial⟩

noncomputable def transProb4 : State4 → State4 → ENNReal
  | .S0, .S0 => 0
  | .S0, .S1 => 1/2
  | .S0, .S2 => 1/4
  | .S0, .S3 => 1/4
  | .S1, .S0 => 1/2
  | .S1, .S1 => 0
  | .S1, .S2 => 1/4
  | .S1, .S3 => 1/4
  | .S2, .S0 => 0
  | .S2, .S1 => 0
  | .S2, .S2 => 1/2
  | .S2, .S3 => 1/2
  | .S3, .S0 => 0
  | .S3, .S1 => 0
  | .S3, .S2 => 1/2
  | .S3, .S3 => 1/2

noncomputable def transMeasure4 (s : State4) : Measure State4 :=
  transProb4 s .S0 • Measure.dirac .S0 +
  transProb4 s .S1 • Measure.dirac .S1 +
  transProb4 s .S2 • Measure.dirac .S2 +
  transProb4 s .S3 • Measure.dirac .S3

noncomputable def kernel4 : Kernel State4 State4 where
  toFun := transMeasure4
  measurable' := by
    intro s _; trivial

instance : IsMarkovKernel kernel4 where
  isProbabilityMeasure s := by
    cases s <;>
    simp only [kernel4] <;>
    constructor <;>
    simp <;>
    rw [transMeasure4]
    case S0 =>
      simp [transProb4]
      have h1 : (4 : ENNReal)⁻¹ + 4⁻¹ = 2⁻¹ := by
        have h4eq : (4 : ENNReal) = 2 * 2 := by norm_num
        rw [h4eq]
        rw [ENNReal.mul_inv ]
        rw [← two_mul]
        rw [mul_comm 2 (2⁻¹ * 2⁻¹)]
        rw [mul_assoc]
        nth_rewrite 2 [mul_comm]
        rw [ENNReal.mul_inv_cancel]
        simp
        exact Ne.symm (NeZero.ne' 2)
        exact Ne.symm ENNReal.top_ne_ofNat
        left
        exact Ne.symm (NeZero.ne' 2)
        right
        exact Ne.symm (NeZero.ne' 2)

      rw [add_assoc, h1]
      rw [← two_mul]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    case S1 =>
      simp [transProb4]
      have h1 : (4 : ENNReal)⁻¹ + 4⁻¹ = 2⁻¹ := by
        have h4eq : (4 : ENNReal) = 2 * 2 := by norm_num
        rw [h4eq]
        rw [ENNReal.mul_inv]
        rw [← two_mul]
        rw [mul_comm 2 (2⁻¹ * 2⁻¹)]
        rw [mul_assoc]
        nth_rewrite 2 [mul_comm]
        rw [ENNReal.mul_inv_cancel]
        ring
        exact Ne.symm (NeZero.ne' 2)
        exact Ne.symm ENNReal.top_ne_ofNat
        left
        exact Ne.symm (NeZero.ne' 2)
        right
        exact Ne.symm (NeZero.ne' 2)

      rw [add_assoc, h1]
      rw [← two_mul]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    case S2 =>
      simp [transProb4]
      rw [← two_mul]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    case S3 =>
      simp [transProb4]
      rw [← two_mul]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)






def class01 : Set State4 := {.S0, .S1}
def class23 : Set State4 := {.S2, .S3}

end FourStateDTMC

/-! ## The 2-State DTMC (Quotient) -/

namespace TwoStateDTMC

inductive State2 where
  | S0  -- Represents equivalence class {S0, S1}
  | S2  -- Represents equivalence class {S2, S3}
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace State2 := ⊤
instance : MeasurableSingletonClass State2 := ⟨fun _ => trivial⟩

/-- Transition probabilities for the 2-state DTMC
    |    | S0  | S2  |
    |-----------------|
    | S0 | 0.5 | 0.5 |
    | S2 | 0   | 1   |
-/
noncomputable def transProb2 : State2 → State2 → ENNReal
  | .S0, .S0 => 1/2
  | .S0, .S2 => 1/2
  | .S2, .S0 => 0
  | .S2, .S2 => 1

theorem transProb2_sum (s : State2) : transProb2 s .S0 + transProb2 s .S2 = 1 := by
  cases s <;> simp [transProb2]
  · -- S0 case: 1/2 + 1/2 = 1
    rw [← two_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)


noncomputable def transMeasure2 (s : State2) : Measure State2 :=
  transProb2 s .S0 • Measure.dirac .S0 +
  transProb2 s .S2 • Measure.dirac .S2

noncomputable def kernel2 : Kernel State2 State2 where
  toFun := transMeasure2
  measurable' := by intro s _; trivial

instance : IsMarkovKernel kernel2 where
  isProbabilityMeasure s := by
    cases s <;>
    simp only [kernel2] <;>
    constructor <;>
    simp only [Kernel.coe_mk]
    rw [transMeasure2]

    case S0 =>
      simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
        smul_eq_mul, mul_one,transProb2]
      rw [← two_mul]
      ring_nf
      norm_num
      rw [mul_comm,ENNReal.mul_inv_cancel]
      .
        apply Ne.symm
        exact NeZero.ne' 2
      .
        rw [<-not_isTop_iff_ne_top]
        simp




    case S2 =>
      simp [transMeasure2]
      simp [transProb2]







end TwoStateDTMC





open FourStateDTMC TwoStateDTMC




/-! ## Labeled Markov Chain Definition -/
structure LabeledMarkovChain (S : Type*) (L : Type*) [MeasurableSpace S] where
  μ₀ : Measure S                    -- Initial distribution
  κ : Kernel S S                     -- Transition kernel
  hκ : IsMarkovKernel κ              -- Markov property
  label : S → L                      -- Labeling function

/-! ## The 4-State Labeled DTMC -/
namespace FourStateDTMC

-- Define our label type
inductive Label4 where
  | Red
  | Blue
  deriving DecidableEq, Repr

-- Labeling function
def label4 : State4 → Label4
  | .S0 => .Red
  | .S1 => .Red
  | .S2 => .Blue
  | .S3 => .Blue

-- Create the labeled Markov chain instance
noncomputable def lmc4 : LabeledMarkovChain State4 Label4 where
  μ₀ := Measure.dirac .S0
  κ := kernel4
  hκ := inferInstance
  label := label4

end FourStateDTMC

/-! ## The 2-State Labeled DTMC -/
namespace TwoStateDTMC

abbrev Label2 := FourStateDTMC.Label4

def label2 : State2 → Label2
  | .S0 => .Red
  | .S2 => .Blue

noncomputable def lmc2 : LabeledMarkovChain State2 Label2 where
  μ₀ := Measure.dirac .S0
  κ := kernel2
  hκ := inferInstance
  label := label2

end TwoStateDTMC

/-! ## Quotient Map Preserves Labels -/
namespace BisimulationProof

open FourStateDTMC TwoStateDTMC

universe u v

/-- A probabilistic bisimulation relation for labeled Markov chains.

    The transition_preserving condition requires that for each equivalence
    class [u]_R, related states have equal transition probabilities into it. -/
structure IsProbBisimulation {S : Type u} {L : Type v} [MeasurableSpace S]
    (lmc : LabeledMarkovChain S L) (R : S → S → Prop) : Prop where
  equivalence : Equivalence R
  label_preserving : ∀ s t, R s t → lmc.label s = lmc.label t
  /-- For each equivalence class [u]_R, related states have equal transition probs -/
  transition_preserving : ∀ s t, R s t →
    ∀ u : S, lmc.κ s {x | R u x} = lmc.κ t {x | R u x}

/-- Two states are probabilistically bisimilar if there exists a bisimulation relating them -/
def ProbBisimilar {S : Type u} {L : Type v} [MeasurableSpace S]
    (lmc : LabeledMarkovChain S L) (s t : S) : Prop :=
  ∃ R : S → S → Prop, IsProbBisimulation lmc R ∧ R s t

/-! ## Bisimulation for our specific DTMCs -/

namespace FourStateDTMC

/-- The equivalence relation: S0 ~ S1 and S2 ~ S3 -/
def bisim_rel : State4 → State4 → Prop
  | .S0, .S0 => True | .S0, .S1 => True | .S0, .S2 => False | .S0, .S3 => False
  | .S1, .S0 => True | .S1, .S1 => True | .S1, .S2 => False | .S1, .S3 => False
  | .S2, .S0 => False | .S2, .S1 => False | .S2, .S2 => True | .S2, .S3 => True
  | .S3, .S0 => False | .S3, .S1 => False | .S3, .S2 => True | .S3, .S3 => True

theorem bisim_rel_refl : ∀ s : State4, bisim_rel s s := by
  intro s; cases s <;> trivial

theorem bisim_rel_symm : ∀ s t : State4, bisim_rel s t → bisim_rel t s := by
  intro s t h; cases s <;> cases t <;> trivial

theorem bisim_rel_trans : ∀ s t u : State4, bisim_rel s t → bisim_rel t u → bisim_rel s u := by
  intro s t u hst htu
  cases s <;> cases t <;> cases u <;> simp_all [bisim_rel]

theorem bisim_rel_equivalence : Equivalence bisim_rel where
  refl := bisim_rel_refl
  symm := @bisim_rel_symm
  trans := @bisim_rel_trans

/-- The equivalence class of S0 (and S1) is {S0, S1} -/
theorem equiv_class_S0 : {x : State4 | bisim_rel .S0 x} = {.S0, .S1} := by
  ext x; cases x <;> simp [bisim_rel]

/-- The equivalence class of S2 (and S3) is {S2, S3} -/
theorem equiv_class_S2 : {x : State4 | bisim_rel .S2 x} = {.S2, .S3} := by
  ext x; cases x <;> simp [bisim_rel]

/-- Equivalence class of S1 equals that of S0 -/
theorem equiv_class_S1 : {x : State4 | bisim_rel .S1 x} = {.S0, .S1} := by
  ext x; cases x <;> simp [bisim_rel]

/-- Equivalence class of S3 equals that of S2 -/
theorem equiv_class_S3 : {x : State4 | bisim_rel .S3 x} = {.S2, .S3} := by
  ext x; cases x <;> simp [bisim_rel]

/-- Get the equivalence class for any state -/
theorem equiv_class_eq (u : State4) :
    {x | bisim_rel u x} = class01 ∨ {x | bisim_rel u x} = class23 := by
  cases u with
  | S0 => left; rw [equiv_class_S0]; rfl
  | S1 => left; rw [equiv_class_S1]; rfl
  | S2 => right; rw [equiv_class_S2]; rfl
  | S3 => right; rw [equiv_class_S3]; rfl


theorem kernel4_class01 (s : State4) :
    kernel4 s class01 = transProb4 s .S0 + transProb4 s .S1 := by
  unfold kernel4 transMeasure4 class01
  simp


/-- kernel4 on class23 equals sum of transition probs to S2 and S3 -/
theorem kernel4_class23 (s : State4) :
    kernel4 s class23 = transProb4 s .S2 + transProb4 s .S3 := by
  unfold kernel4 transMeasure4 class23
  simp

/-- Main theorem: bisim_rel is a probabilistic bisimulation -/
theorem is_bisimulation : IsProbBisimulation lmc4 bisim_rel where
  equivalence := bisim_rel_equivalence

  label_preserving := by
    intro s t h
    cases s <;> cases t <;> simp_all [bisim_rel]
    rfl
    rfl
    rfl
    rfl

  transition_preserving := by
    intro s t hst u
    -- Get which equivalence class [u] is
    have h_class := equiv_class_eq u
    cases h_class with
    | inl h_01 =>
      -- [u] = class01 = {S0, S1}
      simp only [lmc4]
      rw [h_01]
      -- Now show kernel4 s class01 = kernel4 t class01 for bisimilar s, t
      cases s <;> cases t <;> simp only [bisim_rel] at hst
      -- S0, S0 case
      · rfl
      -- S0, S1 case
      ·
        repeat rw [kernel4_class01]
        simp only [transProb4]
        ring

      -- S1, S0 case
      ·
        repeat rw [kernel4_class01]
        simp only [transProb4]
        ring
      -- S1, S1 case
      · rfl
      -- S2, S2 case
      · rfl
      -- S2, S3 case
      ·
        repeat rw [kernel4_class01]
        simp only [transProb4]

      -- S3, S2 case
      · repeat rw [kernel4_class01]
        simp only [transProb4]

      -- S3, S3 case
      · rfl
    | inr h_23 =>
      -- [u] = class23 = {S2, S3}
      simp only [lmc4]
      rw [h_23]
      -- Now show kernel4 s class23 = kernel4 t class23 for bisimilar s, t
      cases s <;> cases t <;> simp only [bisim_rel] at hst
      -- S0, S0 case
      · rfl
      -- S0, S1 case
      · repeat rw [kernel4_class23]
        simp only [transProb4]

      -- S1, S0 case
      · repeat rw [kernel4_class23]
        simp only [transProb4]

      -- S1, S1 case
      · rfl
      -- S2, S2 case
      · rfl
      -- S2, S3 case
      · repeat rw [kernel4_class23]
        simp only [transProb4]

      -- S3, S2 case
      · repeat rw [kernel4_class23]
        simp only [transProb4]

      -- S3, S3 case
      · rfl

/-- S0 and S1 are probabilistically bisimilar -/
theorem S0_bisimilar_S1 : ProbBisimilar lmc4 .S0 .S1 :=
  ⟨bisim_rel, is_bisimulation, trivial⟩

/-- S2 and S3 are probabilistically bisimilar -/
theorem S2_bisimilar_S3 : ProbBisimilar lmc4 .S2 .S3 :=
  ⟨bisim_rel, is_bisimulation, trivial⟩

/-- S0 and S2 are NOT bisimilar (different labels) -/
theorem S0_not_bisimilar_S2 : ¬ bisim_rel .S0 .S2 := by simp [bisim_rel]

end FourStateDTMC

end BisimulationProof
