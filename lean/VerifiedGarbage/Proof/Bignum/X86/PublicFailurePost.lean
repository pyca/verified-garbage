module

public import VerifiedGarbage.Proof.Bignum.X86.PublicFailure
import VerifiedGarbage.Proof.Bignum.PublicWritten
public import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.Bignum.X86.PublicInputs

/-! # The checked-RSA contract's postcondition, and the failure path meeting it -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

def PublicPost (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (mem : Mem) (t : State) : Prop :=
  Spec.Rsa.written t.mem (byteAddr (args 0)) len (t.gpr .eax)
    (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt mem (byteAddr (args 2)) len)
      (Spec.Rsa.bytesAt mem (byteAddr (args 4)) (args 5).toNat)
      (Spec.Rsa.bytesAt mem (byteAddr (args 6)) len)) ∧
  Frame [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), len⟩] mem t.mem

theorem publicFailure_post {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s)
    (failed : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)
      (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)
      (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len) = none) :
    WP isa PublicFn.failure s fun t => PublicPost base bytes len args s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have hl := h.lower
  have hu := h.upper
  refine WP.mono (publicFailure_ok (by omega) (by omega) h.outFit
    ((h.stack 0 (by decide)).readSrc)
    (by rw [← h.outLen]; exact (h.stack 1 (by decide)).readSrc) h.outWrite)
    fun t ⟨Y, B, O, K⟩ => ?_
  refine ⟨⟨?_, ?_⟩, K.mono (by decide)⟩
  · simp only [failed, Spec.Rsa.written]
    exact ⟨B, Y⟩
  · have F := outside_frame O (by omega : 0 + len ≤ 2 ^ 64)
    simp only [BitVec.add_zero] at F
    exact F.mono (by simp [byteAddr])

end VG.Proof.Bignum.X86.PublicContext
