module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Framed
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFrameResult
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEncodedResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSeparation
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallValid
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSizes
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyABI

/-! # The callable key operation uses the caller's original encoded inputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.RsaKeyGen.X86.Key (contract call_layout call_valid call_separation call_sizes
  callEnvironment EncodedResult BodyOutcome reservedRegion pushed_bytes)

theorem framed_result_ok {s : State} (h : contract.pre s) :
    WP isa VG.Impl.RsaKeyGen.X86.KeyRuntime.code s fun t =>
      abiPreserved s t ∧ EncodedResult (callEnvironment s) s.mem t := by
  have v := call_valid h
  have A := call_layout h
  have D := call_separation h
  have Z := call_sizes h
  have eBytes : Spec.Rsa.bytesAt (Compact.entered s).mem (callEnvironment s).exponentRegion.base
      (callEnvironment s).exponentRegion.len =
      Spec.Rsa.bytesAt s.mem (callEnvironment s).exponentRegion.base (callEnvironment s).exponentRegion.len :=
    pushed_bytes h D.stackExponent (by change (arg s 15).toNat < 2 ^ 64; have := (arg s 15).isLt; omega)
  have primeBytes (i : Nat) (hi : i < 7) :
      Spec.Rsa.bytesAt (Compact.entered s).mem ((callEnvironment s).outputRegion i).base ((callEnvironment s).outputRegion i).len =
        Spec.Rsa.bytesAt s.mem ((callEnvironment s).outputRegion i).base ((callEnvironment s).outputRegion i).len := by
    rw [Z.outputRegion hi]
    apply pushed_bytes h (D.stackOutput i hi)
    change (arg s (2 * i + 1)).toNat < 2 ^ 64
    have := (arg s (2 * i + 1)).isLt
    omega
  refine WP.mono (framed_ok h) fun t ⟨preserved, R⟩ => ?_
  unfold BodyOutcome at R
  rw [eBytes, primeBytes 2 (by decide), primeBytes 3 (by decide)] at R
  exact ⟨preserved, BodyOutcome.encoded v R⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
