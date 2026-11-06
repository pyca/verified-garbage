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

end VG.Proof.RsaKeyGen.X86.Key
