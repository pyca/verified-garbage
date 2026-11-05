module

public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract

/-! # The contract of the refillable-tape search for one modulus width

`vg_dsa_parameter_search` forwards its arguments to its width's function
(`Impl/Dsa/X86_64/ParameterSearch.lean`), whose contract is the search's
with `state[1]`, the width, fixed to `pBytes`. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.Refill

open VG VG.Spec.Dsa
open VG.Spec.Rsa (bytesAt wordsAt)

def contract {M : ISA} (pBytes : Nat) (A : Abi M) (stack : Nat := 0) : Contract M :=
  parameterSearchSig.contract A
    (pre := fun _out outLen _used _rand randLen _scratch scratchLen state m =>
      let pLen := (m.readW (state + 8) 64).toNat
      pLen = pBytes ∧ generationPLenValid pLen ∧
      outLen.toNat = 2 * pLen + generationQLen pLen ∧
      generationScratchWords pLen ≤ scratchLen.toNat ∧
      (m.readW state 64).toNat ≤ parameterSeeds ∧
      m.readW (state + 16) 64 = BitVec.ofNat 64 (parameterEntropy pLen) ∧
      randLen.toNat ≤ parameterEntropy pLen)
    (post := fun out outLen used rand randLen _scratch _scratchLen state m m' r =>
      let pLen := (m.readW (state + 8) 64).toNat
      let result := parameterSearch pLen (m.readW state 64).toNat (bytesAt m rand randLen.toNat)
      r.toNat = result.status ∧
      bytesAt m' out outLen.toNat =
        (match result.outcome with
          | .accepted a => encodeParams pLen (generationQLen pLen) a
          | _ => List.replicate outLen.toNat 0) ∧
      wordsAt m' used 1 = [BitVec.ofNat 64 result.used] ∧
      wordsAt m' state 4 = [BitVec.ofNat 64 result.remaining, BitVec.ofNat 64 pLen,
        BitVec.ofNat 64 (parameterEntropy pLen), BitVec.ofNat 64 result.requested])
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _used rand randLen _scratch _scratchLen state m =>
      (wordsAt m state 4).map (·.toNat) ++ (bytesAt m rand randLen.toNat).map (·.toNat))

end VG.Proof.Dsa.X86_64.Generation.Refill
