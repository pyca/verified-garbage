module

public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Spec.Ffdh.SievedGeneration

/-! # Exact controller contract for RSA-sieved safe-prime generation

Trusted. `vg_ffdh_generate_parameters`: buffer requirements, public timing
data, initialization and search bounds as `parameterSearchSig` and
`parameterInitApi` set them.
-/

@[expose] public section
namespace VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp scratchWords)

def sievedParameterSearchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
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
      let result := sievedParameterSearch bits.toNat generator.toNat (m.readW state 64).toNat
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

def sievedParameterSearchApi : Api where
  module := "ffdh"
  name := "vg_ffdh_generate_parameters"
  sig := parameterSearchSig
  writeArgs := true
  contracts := some fun A stack => sievedParameterSearchContract A stack
  summary := "Run native finite-field Diffie–Hellman parameter generation, with RSA's \
    trial-division sieve. The routine owns candidate retries, attempt limits, witness \
    selection, primality rounds and entropy budgets. Initialize with \
    `vg_ffdh_parameter_generation_init`. Returns 1 with the probable safe prime in `out`, \
    3 when a bound is exhausted, or 0 only when it needs more entropy. On 0, discard \
    `used` bytes of `rand`, preserve its remaining suffix and extend that suffix to at \
    least `state[3]` bytes before calling again. `state[1]` is the output width and \
    `state[2]` the maximum tape length. The output is zero for 0 and 3. Accepted p and q \
    pass the full 64/128 independent witness counts. Contract: \
    `VG.Spec.Ffdh.sievedParameterSearchContract`. Timing may depend on the public tape \
    and the first four controller words."
  safety := ["`state` must be initialized by `vg_ffdh_parameter_generation_init` for the \
      supplied `bits` and `generator`, or be the state returned by this routine.",
    "`out_len` must equal `state[1]`, and `rand_len` must not exceed `state[2]`.",
    "`scratch_len` must be at least `16 * out_len + 32`.",
    "The last twelve controller words and the scratch contents are private workspace."]

end VG.Spec.Ffdh
