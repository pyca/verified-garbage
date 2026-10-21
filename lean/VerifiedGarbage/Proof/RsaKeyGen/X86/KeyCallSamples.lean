module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFrameResult
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadInputs
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSizes

/-! # The native saved-register push preserves the original prime and exponent snapshots -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86

theorem entered_exponent {s : State} (h : contract.pre s) :
    inputExponent (callEnvironment s) (Compact.entered s).mem = inputExponent (callEnvironment s) s.mem := by
  have D := call_separation h
  unfold inputExponent
  congr 1
  exact pushed_bytes h D.stackExponent (by change (arg s 15).toNat < 2 ^ 64; have := (arg s 15).isLt; omega)

theorem entered_prime {s : State} (h : contract.pre s) {i : Nat} (hi : i < 7) :
    inputPrime (callEnvironment s) (Compact.entered s).mem i = inputPrime (callEnvironment s) s.mem i := by
  have Z := call_sizes h
  have D := call_separation h
  unfold inputPrime
  rw [Z.outputRegion hi]
  congr 1
  exact pushed_bytes h (D.stackOutput i hi)
    (by change (arg s (2 * i + 1)).toNat < 2 ^ 64; have := (arg s (2 * i + 1)).isLt; omega)

end VG.Proof.RsaKeyGen.X86.Key
