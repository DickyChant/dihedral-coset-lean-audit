import SimonDCP.Probability.LemmaThreePathRefinement

/-!
# A finite transcript model for the repaired Lemma 3

This module packages the paper-facing data that remain after Steps 3--7.  A
complete transcript records `Y`, the measured Hadamard mask `D`, the later
records `W` and `S`, and the measured bit `hPrime`.  Any selected set `A(D)` is
therefore allowed to be reconstructed from the `D` field; the probability
theorems below never require that selection to be independent of `D`.

Every surviving path has a Boolean sign and belongs to one residual branch.
The analytic premise is that paths in one transcript/branch fibre have a common
complex amplitude before that sign is applied.  This is exactly the premise
suggested by the displayed Step-7 amplitude in the paper.  The module proves
the resulting branch Born weight is the common squared magnitude times the
squared signed count, and then invokes the path-refinement theorem to obtain
the repaired `2^(-n)` small-branch bound.

Instantiating `commonAmplitude` with the actual Step-3--7 computation remains a
separate bridge.  For the joint-mass theorem it must be the unnormalized joint
Kraus/path amplitude: it includes unitary and Hadamard normalization factors
and the relevant projection filters, but excludes an outcome-dependent
postmeasurement renormalization such as the paper's `nu4`.  Conditioning and
its denominator are handled separately by `LemmaThreePostselection`.

The residual `Branch` labels must also be orthogonal output sectors.  Only then
is the sum of their squared coherent amplitudes the actual Born weight of the
complete transcript.
-/

namespace SimonDCP.Probability.LemmaThreeTranscriptModel

open scoped BigOperators

open SimonDCP.Probability.LemmaThreeBornBounds
open SimonDCP.Probability.LemmaThreePathRefinement

/-- The complete classical record used to index a Step-7 residual state. -/
structure StepSevenTranscript
    (Y D W S : Type*) where
  y : Y
  d : D
  w : W
  s : S
  hPrime : Bool
deriving DecidableEq, Fintype

/--
A fine Step-3--7 path is a complete measured transcript together with one
hidden pre-Hadamard selection compatible with that transcript.  This relation,
rather than a function from hidden selections to transcripts, is the right
finite model: one hidden selection contributes an amplitude to many possible
Hadamard outcomes.
-/
abbrev CompatibleStepSevenPath
    (Transcript Hidden : Type*)
    (compatible : Transcript -> Hidden -> Prop) [DecidablePred fun pair : Transcript × Hidden =>
      compatible pair.1 pair.2] :=
  {pair : Transcript × Hidden // compatible pair.1 pair.2}

namespace CompatibleStepSevenPath

variable {Transcript Hidden : Type*} {compatible : Transcript -> Hidden -> Prop}
  [DecidablePred fun pair : Transcript × Hidden => compatible pair.1 pair.2]

/-- The measured record carried by a compatible fine path. -/
def transcript (path : CompatibleStepSevenPath Transcript Hidden compatible) : Transcript :=
  path.1.1

/-- The hidden pre-Hadamard selection carried by a compatible fine path. -/
def hidden (path : CompatibleStepSevenPath Transcript Hidden compatible) : Hidden :=
  path.1.2

theorem compatible_property
    (path : CompatibleStepSevenPath Transcript Hidden compatible) :
    compatible path.transcript path.hidden :=
  path.2

end CompatibleStepSevenPath

/-- A transcript constructor that makes an arbitrary adaptive selection from `D`. -/
def adaptiveStepSevenTranscript
    {Y D W S Selection : Type*}
    (select : D -> Selection) (y : Y) (d : D) (w : W) (s : S) (hPrime : Bool) :
    StepSevenTranscript Y D W S × Selection :=
  (⟨y, d, w, s, hPrime⟩, select d)

variable {Path Transcript Branch : Type*}

/-- The real signed count in one complete transcript/branch fibre. -/
def signedPathCountReal
    [Fintype Path] [DecidableEq Transcript] [DecidableEq Branch]
    (transcriptOf : Path -> Transcript) (branchOf : Path -> Branch)
    (positive : Path -> Bool) (transcript : Transcript) (branch : Branch) : Real :=
  (positivePathCount transcriptOf branchOf positive transcript branch : Real) -
    (negativePathCount transcriptOf branchOf positive transcript branch : Real)

/--
Raw coherent amplitude in one branch: a common complex path amplitude times
the signed path count.
-/
def rawBranchAmplitude
    [Fintype Path] [DecidableEq Transcript] [DecidableEq Branch]
    (transcriptOf : Path -> Transcript) (branchOf : Path -> Branch)
    (positive : Path -> Bool) (commonAmplitude : Transcript -> Branch -> Complex)
    (transcript : Transcript) (branch : Branch) : Complex :=
  commonAmplitude transcript branch *
    (signedPathCountReal transcriptOf branchOf positive transcript branch : Complex)

/-- The raw branch Born energy factors into common path energy and imbalance. -/
theorem normSq_rawBranchAmplitude
    [Fintype Path] [DecidableEq Transcript] [DecidableEq Branch]
    (transcriptOf : Path -> Transcript) (branchOf : Path -> Branch)
    (positive : Path -> Bool) (commonAmplitude : Transcript -> Branch -> Complex)
    (transcript : Transcript) (branch : Branch) :
    Complex.normSq
        (rawBranchAmplitude transcriptOf branchOf positive commonAmplitude
          transcript branch) =
      Complex.normSq (commonAmplitude transcript branch) *
        signedCountSq
          (positivePathCount transcriptOf branchOf positive transcript branch)
          (negativePathCount transcriptOf branchOf positive transcript branch) := by
  rw [rawBranchAmplitude, Complex.normSq_mul, Complex.normSq_ofReal]
  simp only [signedPathCountReal, signedCountSq, pow_two]

/-- Total unnormalized Born mass of one complete transcript. -/
def transcriptBornWeight
    [Fintype Path] [Fintype Branch]
    [DecidableEq Transcript] [DecidableEq Branch]
    (transcriptOf : Path -> Transcript) (branchOf : Path -> Branch)
    (positive : Path -> Bool) (commonAmplitude : Transcript -> Branch -> Complex)
    (transcript : Transcript) : Real :=
  ∑ branch,
    Complex.normSq
      (rawBranchAmplitude transcriptOf branchOf positive commonAmplitude
        transcript branch)

/-- Transcript Born mass is exactly the scaled squared signed-count formula. -/
theorem transcriptBornWeight_eq_scaledSignedCounts
    [Fintype Path] [Fintype Branch]
    [DecidableEq Transcript] [DecidableEq Branch]
    (transcriptOf : Path -> Transcript) (branchOf : Path -> Branch)
    (positive : Path -> Bool) (commonAmplitude : Transcript -> Branch -> Complex)
    (transcript : Transcript) :
    transcriptBornWeight transcriptOf branchOf positive commonAmplitude transcript =
      ∑ branch,
        Complex.normSq (commonAmplitude transcript branch) *
          signedCountSq
            (positivePathCount transcriptOf branchOf positive transcript branch)
            (negativePathCount transcriptOf branchOf positive transcript branch) := by
  unfold transcriptBornWeight
  apply Finset.sum_congr rfl
  intro branch _
  exact normSq_rawBranchAmplitude transcriptOf branchOf positive commonAmplitude
    transcript branch

/-- Every residual branch is at or below the paper's squared threshold. -/
def allStepSevenBranchesSmall
    [Fintype Path] [Fintype Branch]
    [DecidableEq Transcript] [DecidableEq Branch]
    (transcriptOf : Path -> Transcript) (branchOf : Path -> Branch)
    (positive : Path -> Bool) (n : Nat) (transcript : Transcript) : Prop :=
  countSmallBranchEvent
    (positivePathCount transcriptOf branchOf positive)
    (negativePathCount transcriptOf branchOf positive)
    ((2 : Real)⁻¹ ^ n) transcript

/--
The first repaired Lemma 3 conclusion in the complete transcript model.  The
only normalization premise is the total energy of the orthogonally retained
paths.  The transcript may depend arbitrarily on every path coordinate.
-/
theorem allStepSevenBranchesSmall_mass_le
    [Fintype Path] [Fintype Transcript] [Fintype Branch]
    [DecidableEq Transcript] [DecidableEq Branch]
    (transcriptOf : Path -> Transcript) (branchOf : Path -> Branch)
    (positive : Path -> Bool) (commonAmplitude : Transcript -> Branch -> Complex)
    (n : Nat)
    (hTotalPathEnergy :
      (∑ path,
        Complex.normSq
          (commonAmplitude (transcriptOf path) (branchOf path))) <= 1) :
    realFiniteMass
        (transcriptBornWeight transcriptOf branchOf positive commonAmplitude)
        (allStepSevenBranchesSmall transcriptOf branchOf positive n) <=
      (2 : Real)⁻¹ ^ n := by
  rw [show
    transcriptBornWeight transcriptOf branchOf positive commonAmplitude =
      fun transcript => ∑ branch,
        Complex.normSq (commonAmplitude transcript branch) *
          signedCountSq
            (positivePathCount transcriptOf branchOf positive transcript branch)
            (negativePathCount transcriptOf branchOf positive transcript branch) by
      funext transcript
      exact transcriptBornWeight_eq_scaledSignedCounts
        transcriptOf branchOf positive commonAmplitude transcript]
  apply pathModel_smallBranchMass_le_paperThreshold
    transcriptOf branchOf positive
    (fun transcript branch => Complex.normSq (commonAmplitude transcript branch)) n
  · intro transcript branch
    exact Complex.normSq_nonneg _
  · exact hTotalPathEnergy

/--
Relational specialization of `allStepSevenBranchesSmall_mass_le`.  The
compatibility predicate may encode all measured constraints from Steps 2--7,
including the adaptive choice `A(D)`.  The remaining two pieces of analytic
data are the residual branch and the Boolean path sign.
-/
theorem compatiblePaths_allBranchesSmall_mass_le
    {Hidden Branch : Type*}
    [Fintype Transcript] [Fintype Hidden] [Fintype Branch]
    [DecidableEq Transcript] [DecidableEq Branch]
    (compatible : Transcript -> Hidden -> Prop)
    [DecidablePred fun pair : Transcript × Hidden => compatible pair.1 pair.2]
    (branchOf : CompatibleStepSevenPath Transcript Hidden compatible -> Branch)
    (positive : CompatibleStepSevenPath Transcript Hidden compatible -> Bool)
    (commonAmplitude : Transcript -> Branch -> Complex)
    (n : Nat)
    (hTotalPathEnergy :
      (∑ path : CompatibleStepSevenPath Transcript Hidden compatible,
        Complex.normSq
          (commonAmplitude path.transcript (branchOf path))) <= 1) :
    realFiniteMass
        (transcriptBornWeight
          CompatibleStepSevenPath.transcript branchOf positive commonAmplitude)
        (allStepSevenBranchesSmall
          CompatibleStepSevenPath.transcript branchOf positive n) <=
      (2 : Real)⁻¹ ^ n := by
  exact allStepSevenBranchesSmall_mass_le
    CompatibleStepSevenPath.transcript branchOf positive commonAmplitude n
      hTotalPathEnergy

end SimonDCP.Probability.LemmaThreeTranscriptModel
