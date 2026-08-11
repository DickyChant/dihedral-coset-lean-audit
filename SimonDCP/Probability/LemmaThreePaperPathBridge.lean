import SimonDCP.Probability.LemmaThreeTranscriptModel

/-!
# A paper-facing finite path bridge for Lemma 3

This module instantiates the signed-path model with the classical records that
occur in Steps 3--7 of the paper.  A hidden state `phi` has a measured `Y`, an
`h` bit, Step-5 and Step-6 records determined after the measured Walsh mask
`D`, a computed bit `hStar`, and a Boolean Walsh phase.  Compatibility with a
measured transcript

```text
M = (Y, D, W', S, h')
```

requires all recorded values to agree and requires `h' = h xor hStar`.  The
residual branch label is `hStar`; its circuit-level orthogonality is one of the
explicit remaining obligations below.  The path sign is exactly

```text
(-1)^(h * secretBit + walshPhase(phi,D)).
```

The branch amplitude in this finite model is defined as the raw common path
amplitude times `tPlus - tMinus`, and its squared norm is proved to be the
corresponding squared signed count.  The common amplitude contains the Step-4
and Step-6 Hadamard factors.  It deliberately does not contain the paper's
outcome-dependent postmeasurement normalization `nu4`.

The model leaves the arithmetic implementations of `W'`, `S`, and `hStar` as
functions.  Identifying those functions with the concrete group and carry
circuits, proving that the actual circuit-level finite coherent sum equals
`paperBranchAmplitude`, and proving that the resulting residual `hStar`
branches are orthogonal circuit sectors remain separate obligations.
`LemmaThreePaperPathEnergy` proves the finite-model common-path energy bound
from an explicit Step-2 diagonal-energy premise; identifying and proving that
premise for the paper's actual Step-2 state remains part of the circuit/Born
model-identification work.
-/

namespace SimonDCP.Probability.LemmaThreePaperPathBridge

open scoped BigOperators

open SimonDCP.Probability.LemmaThreePathRefinement
open SimonDCP.Probability.LemmaThreeTranscriptModel
open SimonDCP.Probability.LemmaThreeBornBounds

/-- Deterministic classical data associated with a hidden Step-2 state along
one measured Step-4 Walsh outcome. -/
structure PaperStepSevenModel
    (Hidden Y D W S : Type*) where
  yOf : Hidden -> Y
  hOf : Hidden -> Bool
  stepFiveRecord : Hidden -> D -> S
  stepSixRecord : Hidden -> D -> W
  hStarOf : Hidden -> D -> Bool
  accepts : Hidden -> D -> Bool
  walshPhase : Hidden -> D -> Bool
  secretBit : Bool

variable {Hidden Y D W S Low : Type*}

/-- The measured record `M = (Y,D,W',S,h')` used in Definition 1 of the
paper. -/
abbrev PaperMeasuredTranscript (Y D W S : Type*) :=
  StepSevenTranscript Y D W S

/-- A hidden state is compatible with a measured record precisely when it
survives the Step-4--6 filters, produces the recorded classical values, and
satisfies the Step-7 XOR equation. -/
def paperCompatible
    [DecidableEq Y] [DecidableEq W] [DecidableEq S]
    (model : PaperStepSevenModel Hidden Y D W S)
    (transcript : PaperMeasuredTranscript Y D W S) (phi : Hidden) : Prop :=
  model.accepts phi transcript.d = true /\
    model.yOf phi = transcript.y /\
    model.stepFiveRecord phi transcript.d = transcript.s /\
    model.stepSixRecord phi transcript.d = transcript.w /\
    (model.hOf phi).xor (model.hStarOf phi transcript.d) = transcript.hPrime

instance instDecidablePredPaperCompatible
    [DecidableEq Y] [DecidableEq W] [DecidableEq S]
    (model : PaperStepSevenModel Hidden Y D W S) :
    DecidablePred fun pair : PaperMeasuredTranscript Y D W S × Hidden =>
      paperCompatible model pair.1 pair.2 := by
  intro pair
  unfold paperCompatible
  infer_instance

/-- Fine paths retain both the measured transcript and the compatible hidden
state.  This is relational: one hidden state has a path to every Walsh outcome
that survives the later filters. -/
abbrev PaperStepSevenPath
    [DecidableEq Y] [DecidableEq W] [DecidableEq S]
    (model : PaperStepSevenModel Hidden Y D W S) :=
  CompatibleStepSevenPath (PaperMeasuredTranscript Y D W S) Hidden
    (paperCompatible model)

/-- The residual branch label is the computed high bit `hStar`. -/
def paperBranch
    [DecidableEq Y] [DecidableEq W] [DecidableEq S]
    (model : PaperStepSevenModel Hidden Y D W S)
    (path : PaperStepSevenPath model) : Bool :=
  model.hStarOf path.hidden path.transcript.d

/-- The complete sign from Steps 4 and 7 is positive exactly when
`h * secretBit xor walshPhase(phi,D)` is false. -/
def paperPositive
    [DecidableEq Y] [DecidableEq W] [DecidableEq S]
    (model : PaperStepSevenModel Hidden Y D W S)
    (path : PaperStepSevenPath model) : Bool :=
  !((model.hOf path.hidden && model.secretBit).xor
    (model.walshPhase path.hidden path.transcript.d))

/-- The paper's `t_M^+` for one fixed value of `hStar`. -/
def paperTPlus
    [Fintype Hidden] [Fintype Y] [Fintype D] [Fintype W] [Fintype S]
    [DecidableEq Y] [DecidableEq D] [DecidableEq W] [DecidableEq S]
    (model : PaperStepSevenModel Hidden Y D W S)
    (transcript : PaperMeasuredTranscript Y D W S) (hStar : Bool) : Nat :=
  positivePathCount (fun path : PaperStepSevenPath model => path.transcript)
    (paperBranch model)
    (paperPositive model) transcript hStar

/-- The paper's `t_M^-` for one fixed value of `hStar`. -/
def paperTMinus
    [Fintype Hidden] [Fintype Y] [Fintype D] [Fintype W] [Fintype S]
    [DecidableEq Y] [DecidableEq D] [DecidableEq W] [DecidableEq S]
    (model : PaperStepSevenModel Hidden Y D W S)
    (transcript : PaperMeasuredTranscript Y D W S) (hStar : Bool) : Nat :=
  negativePathCount (fun path : PaperStepSevenPath model => path.transcript)
    (paperBranch model)
    (paperPositive model) transcript hStar

/-- Raw Step-4/Step-6 Hadamard factor.  `D` indexes the Step-4 Walsh outcomes
and `Low` indexes the Step-6 Hadamard outcomes before postselecting zero. -/
noncomputable def paperHadamardFactor (D Low : Type*)
    [Fintype D] [Fintype Low] : Complex :=
  (((Real.sqrt ((Fintype.card D : Real) * Fintype.card Low))⁻¹ : Real) : Complex)

/-- The common raw amplitude of each compatible path.  `stepTwoAmplitude` may
contain normalization chosen before Steps 3--7 (for example after fixing the
Step-2 record), but it cannot depend on `D`, `W'`, `S`, `h'`, or `hStar`.
In particular it is not `nu4`. -/
noncomputable def paperCommonPathAmplitude
    [Fintype D] [Fintype Low]
    (stepTwoAmplitude : Y -> Complex)
    (transcript : PaperMeasuredTranscript Y D W S) : Complex :=
  stepTwoAmplitude transcript.y * paperHadamardFactor D Low

/-- The coherent amplitude of one `(M,hStar)` branch, expressed before any
outcome-dependent postmeasurement renormalization. -/
noncomputable def paperBranchAmplitude
    [Fintype Hidden] [Fintype Y] [Fintype D] [Fintype W] [Fintype S]
    [Fintype Low]
    [DecidableEq Y] [DecidableEq D] [DecidableEq W] [DecidableEq S]
    (model : PaperStepSevenModel Hidden Y D W S)
    (stepTwoAmplitude : Y -> Complex)
    (transcript : PaperMeasuredTranscript Y D W S) (hStar : Bool) : Complex :=
  rawBranchAmplitude
    (fun path : PaperStepSevenPath model => path.transcript)
    (paperBranch model) (paperPositive model)
    (fun measured _branch =>
      paperCommonPathAmplitude (Low := Low) stepTwoAmplitude measured)
    transcript hStar

/-- The actual finite coherent sum of the signed raw path contributions in
one transcript/branch fibre.  Unlike `paperBranchAmplitude`, this definition
does not build in the signed-count factorization. -/
noncomputable def paperDirectBranchAmplitude
    [Fintype Hidden] [Fintype Y] [Fintype D] [Fintype W] [Fintype S]
    [Fintype Low]
    [DecidableEq Y] [DecidableEq D] [DecidableEq W] [DecidableEq S]
    (model : PaperStepSevenModel Hidden Y D W S)
    (stepTwoAmplitude : Y -> Complex)
    (transcript : PaperMeasuredTranscript Y D W S) (hStar : Bool) : Complex :=
  (transcriptBranchFibre
    (fun path : PaperStepSevenPath model => path.transcript)
    (paperBranch model) transcript hStar).sum fun path =>
      if paperPositive model path = true then
        paperCommonPathAmplitude (Low := Low) stepTwoAmplitude transcript
      else
        -paperCommonPathAmplitude (Low := Low) stepTwoAmplitude transcript

private theorem finset_sum_signed_common
    {Path : Type*} (paths : Finset Path) (positive : Path -> Bool)
    (common : Complex) :
    paths.sum (fun path =>
      if positive path = true then common else -common) =
      common *
        (((paths.filter fun path => positive path = true).card : Complex) -
          ((paths.filter fun path => positive path = false).card : Complex)) := by
  classical
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [show
    paths.filter (fun path => ¬ positive path = true) =
      paths.filter (fun path => positive path = false) by
    apply Finset.filter_congr
    intro path _
    simp only [Bool.not_eq_true]]
  ring

/-- The explicit finite coherent sum agrees with the signed-count branch
amplitude used by the abstract transcript model. -/
theorem paperDirectBranchAmplitude_eq_paperBranchAmplitude
    [Fintype Hidden] [Fintype Y] [Fintype D] [Fintype W] [Fintype S]
    [Fintype Low]
    [DecidableEq Y] [DecidableEq D] [DecidableEq W] [DecidableEq S]
    (model : PaperStepSevenModel Hidden Y D W S)
    (stepTwoAmplitude : Y -> Complex)
    (transcript : PaperMeasuredTranscript Y D W S) (hStar : Bool) :
    paperDirectBranchAmplitude (Low := Low) model stepTwoAmplitude transcript hStar =
      paperBranchAmplitude (Low := Low) model stepTwoAmplitude transcript hStar := by
  unfold paperDirectBranchAmplitude paperBranchAmplitude rawBranchAmplitude
  rw [finset_sum_signed_common]
  unfold signedPathCountReal
  norm_cast

/-- The Step-7 compatibility equation reconstructs `h` from the measured
`h'` and the residual `hStar` branch. -/
theorem hiddenBit_xor_branch_eq_hPrime
    [Fintype Hidden] [Fintype Y] [Fintype D] [Fintype W] [Fintype S]
    [DecidableEq Y] [DecidableEq D] [DecidableEq W] [DecidableEq S]
    (model : PaperStepSevenModel Hidden Y D W S)
    (path : PaperStepSevenPath model) :
    (model.hOf path.hidden).xor (paperBranch model path) =
      path.transcript.hPrime := by
  exact path.compatible_property.2.2.2.2

/-- Exact `tPlus - tMinus` factorization in the paper-facing finite model. -/
theorem paperBranchAmplitude_eq_tPlus_sub_tMinus
    [Fintype Hidden] [Fintype Y] [Fintype D] [Fintype W] [Fintype S]
    [Fintype Low]
    [DecidableEq Y] [DecidableEq D] [DecidableEq W] [DecidableEq S]
    (model : PaperStepSevenModel Hidden Y D W S)
    (stepTwoAmplitude : Y -> Complex)
    (transcript : PaperMeasuredTranscript Y D W S) (hStar : Bool) :
    paperBranchAmplitude (Low := Low) model stepTwoAmplitude transcript hStar =
      paperCommonPathAmplitude (Low := Low) stepTwoAmplitude transcript *
        (((paperTPlus model transcript hStar : Real) -
          (paperTMinus model transcript hStar : Real) : Real) : Complex) := by
  rfl

/-- Non-definitional signed-count factorization of the explicit finite
coherent sum. -/
theorem paperDirectBranchAmplitude_eq_tPlus_sub_tMinus
    [Fintype Hidden] [Fintype Y] [Fintype D] [Fintype W] [Fintype S]
    [Fintype Low]
    [DecidableEq Y] [DecidableEq D] [DecidableEq W] [DecidableEq S]
    (model : PaperStepSevenModel Hidden Y D W S)
    (stepTwoAmplitude : Y -> Complex)
    (transcript : PaperMeasuredTranscript Y D W S) (hStar : Bool) :
    paperDirectBranchAmplitude (Low := Low) model stepTwoAmplitude transcript hStar =
      paperCommonPathAmplitude (Low := Low) stepTwoAmplitude transcript *
        (((paperTPlus model transcript hStar : Real) -
          (paperTMinus model transcript hStar : Real) : Real) : Complex) := by
  rw [paperDirectBranchAmplitude_eq_paperBranchAmplitude,
    paperBranchAmplitude_eq_tPlus_sub_tMinus]

/-- Squaring the exact path sum gives the paper's squared signed-count
formula, with the raw common path energy rather than `nu4`. -/
theorem normSq_paperBranchAmplitude
    [Fintype Hidden] [Fintype Y] [Fintype D] [Fintype W] [Fintype S]
    [Fintype Low]
    [DecidableEq Y] [DecidableEq D] [DecidableEq W] [DecidableEq S]
    (model : PaperStepSevenModel Hidden Y D W S)
    (stepTwoAmplitude : Y -> Complex)
    (transcript : PaperMeasuredTranscript Y D W S) (hStar : Bool) :
    Complex.normSq
        (paperBranchAmplitude (Low := Low) model stepTwoAmplitude transcript hStar) =
      Complex.normSq
          (paperCommonPathAmplitude (Low := Low) stepTwoAmplitude transcript) *
        signedCountSq (paperTPlus model transcript hStar)
          (paperTMinus model transcript hStar) := by
  rw [paperBranchAmplitude_eq_tPlus_sub_tMinus, Complex.normSq_mul,
    Complex.normSq_ofReal]
  simp only [signedCountSq, pow_two]

end SimonDCP.Probability.LemmaThreePaperPathBridge
