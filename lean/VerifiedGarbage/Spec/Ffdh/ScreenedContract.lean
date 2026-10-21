module

public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Spec.Ffdh.ScreenedGeneration

/-! # Exact candidate and controller contracts for early p screening

Trusted. Buffer requirements, public timing data, initialization and search
bounds match the original APIs. Separate names preserve their exact tape
semantics for existing implementations.
-/

@[expose] public section
namespace VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp scratchWords)

def screenedParameterCandidateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  parameterCandidateSig.contract A
    (pre := fun _out outLen _used bits generator _rand _randLen _scratch scratchLen _ =>
      512 ≤ bits.toNat ∧ bits.toNat ≤ 8192 ∧ outLen.toNat = (bits.toNat + 7) / 8 ∧
        (generator.toNat = 2 ∨ generator.toNat = 5) ∧
        scratchWords outLen.toNat ≤ scratchLen.toNat)
    (post := fun out outLen used bits generator rand randLen _scratch _scratchLen m m' r =>
      let res := screenedParameterCandidate bits.toNat generator.toNat (bytesAt m rand randLen.toNat)
      r.toNat = candidateStatus res ∧
        bytesAt m' out outLen.toNat =
          (match res with
            | some (some p, _) => i2osp p outLen.toNat
            | _ => List.replicate outLen.toNat 0) ∧
        wordsAt m' used 1 =
          [BitVec.ofNat 64 (match res with
            | some (_, rest) => randLen.toNat - rest.length
            | none => 0)])
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _used _bits _generator rand randLen _scratch _scratchLen m =>
      (bytesAt m rand randLen.toNat).map (·.toNat))


def screenedParameterCandidateApi : Api := { parameterCandidateApi with
  name := "vg_ffdh_parameter_candidate_screened"
  contracts := some fun A stack => screenedParameterCandidateContract A stack
  summary := "One FFDH probable safe-prime candidate with early p screening. Uses the \
    original candidate shaping, generator congruences and small-prime tests. Draws \
    and tests one uniform p witness first, then the full q batch, then the remaining \
    p witnesses. Acceptance requires the original 64 witnesses per modulus, or 128 \
    above 2048 bits; the first p witness counts toward that total. Returns 1 and p \
    on acceptance, 2 on rejection, or 0 on entropy shortage; output is zero otherwise. \
    `used` is the exact consumed prefix, or zero on shortage. Contract: \
    `VG.Spec.Ffdh.screenedParameterCandidateContract`. Timing may depend on the public tape." }

def screenedParameterSearchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  parameterSearchSig.contract A
    (pre := fun _out outLen _used bits generator _rand randLen _scratch scratchLen state m =>
      512 ≤ bits.toNat ∧ bits.toNat ≤ 8192 ∧ outLen.toNat = (bits.toNat + 7) / 8 ∧
      (generator.toNat = 2 ∨ generator.toNat = 5) ∧
      Spec.Rsa.scratchWords outLen.toNat ≤ scratchLen.toNat ∧
      (m.readW state 64).toNat ≤ parameterAttempts bits.toNat ∧
      m.readW (state + 8) 64 = BitVec.ofNat 64 outLen.toNat ∧
      m.readW (state + 16) 64 = BitVec.ofNat 64 (parameterEntropy bits.toNat) ∧
      randLen.toNat ≤ parameterEntropy bits.toNat)
    (post := fun out outLen used bits generator rand randLen _scratch _scratchLen state m m' r =>
      let result := screenedParameterSearch bits.toNat generator.toNat (m.readW state 64).toNat
        (bytesAt m rand randLen.toNat)
      r.toNat = result.status ∧
      bytesAt m' out outLen.toNat =
        (match result with
          | .accepted p _ => i2osp p outLen.toNat
          | _ => List.replicate outLen.toNat 0) ∧
      wordsAt m' used 1 = [BitVec.ofNat 64 result.used] ∧
      wordsAt m' state 4 = [BitVec.ofNat 64 result.remaining, BitVec.ofNat 64 outLen.toNat,
        BitVec.ofNat 64 (parameterEntropy bits.toNat), BitVec.ofNat 64 result.requested])
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _used _bits _generator rand randLen _scratch _scratchLen state m =>
      (bytesAt m rand randLen.toNat).map (·.toNat) ++ (wordsAt m state 4).map (·.toNat))


def screenedParameterSearchApi : Api := { parameterSearchApi with
  name := "vg_ffdh_generate_parameters_screened"
  contracts := some fun A stack => screenedParameterSearchContract A stack
  summary := "Run native FFDH parameter generation with early p screening. The routine \
    owns candidate retries, witness selection, all primality rounds, attempt limits \
    and entropy budgets. Initialize with `vg_ffdh_parameter_generation_init`. Returns \
    1 with p, 3 on exhaustion, or 0 to request more entropy. On 0, discard `used` bytes \
    and extend the preserved suffix to `state[3]` bytes before retrying. Output is zero \
    for 0 and 3. Accepted p and q retain the original 64/128 independent witness counts. \
    Contract: `VG.Spec.Ffdh.screenedParameterSearchContract`. Timing may depend on the \
    public tape and the first four controller words." }

end VG.Spec.Ffdh
