module
public import VerifiedGarbage.Impl.Bignum.X86.CrtFn
public import VerifiedGarbage.Proof.Bignum.X86.CrtBodyFrame
public import VerifiedGarbage.Proof.Bignum.X86.CrtOutputMath

import VerifiedGarbage.Proof.Bignum.X86.CrtSized
import VerifiedGarbage.Proof.Bignum.X86.PublicFailure
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The private CRT wrapper implements the shared optional-output contract -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86

def specResult (m : Mem) (args : Nat → BitVec 32) : Option (List Byte) :=
  Spec.Rsa.privateCrt (Spec.Rsa.bytesAt m (byteAddr (args 2)) (args 3).toNat)
    (Spec.Rsa.bytesAt m (byteAddr (args 4)) (args 5).toNat)
    (Spec.Rsa.bytesAt m (byteAddr (args 6)) (args 7).toNat)
    (Spec.Rsa.bytesAt m (byteAddr (args 8)) (args 9).toNat)
    (Spec.Rsa.bytesAt m (byteAddr (args 10)) (args 11).toNat)
    (Spec.Rsa.bytesAt m (byteAddr (args 12)) (args 13).toNat)
    (Spec.Rsa.bytesAt m (byteAddr (args 14)) (args 15).toNat)

theorem specResult_eq (m : Mem) (args : Nat → BitVec 32) :
    specResult m args = if Spec.Rsa.modulusValid (componentValue m args 2) (args 3).toNat then
      if accepted m args then some (Spec.Rsa.i2osp (outputValue m args) (args 3).toNat) else none
    else none := by
  unfold specResult Spec.Rsa.privateCrt
  dsimp only
  rw [VG.Proof.Bignum.bytesAt_length, VG.Proof.Bignum.decryptCrt_eq]
  change (if Spec.Rsa.modulusValid (componentValue m args 2) (args 3).toNat then
    (if componentValue m args 4 < componentValue m args 2 ∧
      componentValue m args 6 * componentValue m args 8 = componentValue m args 2 ∧
      componentValue m args 14 < componentValue m args 6 then some (outputValue m args) else none).map
        (fun v => Spec.Rsa.i2osp v (args 3).toNat) else none) = _
  have order : (componentValue m args 4 < componentValue m args 2 ∧
      componentValue m args 6 * componentValue m args 8 = componentValue m args 2 ∧
      componentValue m args 14 < componentValue m args 6) ↔ accepted m args :=
    ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩
  cases Spec.Rsa.modulusValid (componentValue m args 2) (args 3).toNat <;>
    by_cases a : accepted m args <;>
    simp only [order, a, Bool.false_eq_true, ite_false, ite_true, Option.map_some, Option.map_none]

def Post (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (m : Mem) (t : State) : Prop :=
  Spec.Rsa.written t.mem (byteAddr (args 0)) len (t.gpr .eax) (specResult m args) ∧
    Frame (bodyRegions base (byteAddr (args 0)) bytes len) m t.mem

theorem sized_post {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : Inputs base bytes len args s)
    (valid : Spec.Rsa.modulusValid (componentValue s.mem args 2) len = true) :
    WP isa (Crt.sized (Spec.Rsa.modulusWords len)) s fun t => Post base bytes len args s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.mono (sized_ok h valid) fun t ⟨Y, B, F, K⟩ => ⟨⟨?_, F⟩, K⟩
  rw [specResult_eq, h.modulus_length, valid]
  by_cases acc : accepted s.mem args
  · simp only [ite_true, acc, Spec.Rsa.written]
    exact ⟨by simp only [B, acc, decide_true]; rfl, by simpa only [acc, ite_true] using Y⟩
  · simp only [ite_true, acc, ite_false, Spec.Rsa.written]
    exact ⟨by simp only [B, acc, decide_false]; rfl,
      by simpa only [acc, ite_false, VG.Proof.Bignum.i2osp_zero'] using Y⟩

theorem failure_post {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : Inputs base bytes len args s) (failed : specResult s.mem args = none) :
    WP isa PublicFn.failure s fun t => Post base bytes len args s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have lo := h.lower
  have hi := h.upper
  refine WP.mono (publicFailure_ok (by omega) (by omega) h.outFit
    ((h.stack 0 (by decide)).readSrc)
    (by rw [← h.outLen]; exact (h.stack 1 (by decide)).readSrc) h.outWrite)
    fun t ⟨Y, B, O, K⟩ => ?_
  refine ⟨⟨?_, ?_⟩, K.mono (by decide)⟩
  · simp only [failed, Spec.Rsa.written]; exact ⟨B, Y⟩
  · have F := VG.Proof.Bignum.outside_frame O (by omega : 0 + len ≤ 2 ^ 64)
    simp only [BitVec.add_zero] at F
    exact F.mono (by simp [bodyRegions, byteAddr])

end VG.Proof.Bignum.X86.Crt
