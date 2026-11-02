module

public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Spec.Ffdh.ScreenedGeneration

/-! # Exact controller contract for early p screening

Trusted. Buffer requirements, public timing data, initialization and search
bounds match the original APIs. Separate names preserve their exact tape
semantics for existing implementations.
-/

@[expose] public section
namespace VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp scratchWords)

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
