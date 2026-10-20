module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInputs
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86.PublicFailure
import VerifiedGarbage.Proof.Bignum.MemoryFrame

/-! # Output obligations for every modulus represented by a packed key -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

def PrecomputedPost (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (mem : Mem) (t : State) : Prop :=
  (∀ nB : List Byte, nB.length = len →
    Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt mem (byteAddr (args 2)) (2 * Spec.Rsa.modulusWords len)) →
    Spec.Rsa.written t.mem (byteAddr (args 0)) len (t.gpr .eax)
      (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt mem (byteAddr (args 4)) (args 5).toNat)
        (Spec.Rsa.bytesAt mem (byteAddr (args 6)) len))) ∧
  Frame [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), len⟩] mem t.mem

theorem precomputedFailure_post {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputedInputs base bytes len args s)
    (failed : ∀ nB : List Byte, nB.length = len →
      Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (byteAddr (args 2)) (2 * Spec.Rsa.modulusWords len)) →
      Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)
        (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len) = none) :
    WP isa VG.Impl.Bignum.X86.PublicFn.failure s fun t => PrecomputedPost base bytes len args s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have hl := h.lower
  have hu := h.upper
  refine WP.mono (publicFailure_ok (by omega) (by omega) h.outFit
    ((h.stack 0 (by decide)).readSrc)
    (by rw [← h.outLen]; exact (h.stack 1 (by decide)).readSrc) h.outWrite)
    fun t ⟨Y, B, O, K⟩ => ?_
  refine ⟨⟨?_, ?_⟩, K.mono (by decide)⟩
  · intro nB length key
    simp only [failed nB length key, Spec.Rsa.written]
    exact ⟨B, Y⟩
  · have F := outside_frame O (by omega : 0 + len ≤ 2 ^ 64)
    simp only [BitVec.add_zero] at F
    exact F.mono (by simp [byteAddr])

end VG.Proof.Bignum.X86.PublicContext
