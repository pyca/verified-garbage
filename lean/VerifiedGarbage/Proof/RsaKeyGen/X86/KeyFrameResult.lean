module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFramed
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEncodedResult
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSeparation
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallValid
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSizes

/-! # The callable key operation uses the caller's original encoded inputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem pushed_bytes {s : State} (h : contract.pre s) {r : Region}
    (far : r.Disjoint (reservedRegion s)) (size : r.len < 2 ^ 64) :
    Spec.Rsa.bytesAt (Compact.entered s).mem r.base r.len = Spec.Rsa.bytesAt s.mem r.base r.len := by
  have A := call_layout h
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  have F := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
  apply VG.Proof.Rsa.rsa_bytes_frame F size
  intro R hr
  obtain rfl := List.mem_singleton.mp hr
  exact far.sub_right A.savedSub

theorem framed_result_ok {s : State} (h : contract.pre s) :
    WP isa VG.Impl.RsaKeyGen.X86.Key.code s fun t =>
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

end VG.Proof.RsaKeyGen.X86.Key
