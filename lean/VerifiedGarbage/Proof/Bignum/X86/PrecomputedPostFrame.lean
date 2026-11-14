module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInputs
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86.PublicFailure
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.WordsFrame
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout

/-! ### `Bignum.X86.PrecomputedPost`, which only this module used -/

section

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
  refine WP.mono (publicFailure_ok (by omega_using [hl]) (by omega_using [hu]) h.outFit
    ((h.stack 0 (by decide)).readSrc)
    (by rw [← h.outLen]; exact (h.stack 1 (by decide)).readSrc) h.outWrite)
    fun t ⟨Y, B, O, K⟩ => ?_
  refine ⟨⟨?_, ?_⟩, K.mono (by decide)⟩
  · intro nB length key
    simp only [failed nB length key, Spec.Rsa.written]
    exact ⟨B, Y⟩
  · have F := outside_frame O (by omega_using [hu] : 0 + len ≤ 2 ^ 64)
    simp only [BitVec.add_zero] at F
    exact F.mono (by simp [byteAddr])

end VG.Proof.Bignum.X86.PublicContext

end

end


/-! # Scratch work preserves the original packed-key output obligation -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem precomputedPost_compose {s u t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputedInputs base bytes len args s) (O : Outside base 16 (bytes - 16) s.mem u.mem)
    (P : PrecomputedPost base bytes len args u.mem t) : PrecomputedPost base bytes len args s.mem t := by
  have nw := h.scratch.nowrap
  have sz := h.space
  have size := size_eq (Spec.Rsa.modulusWords len)
  have Os : Outside base 0 bytes s.mem u.mem := O.mono (by omega_using []) (by omega_using [sz, size])
  have dims := h.dimensions
  have W := scratch_words Os (by omega_using [nw]) (n := 2 * Spec.Rsa.modulusWords len) (by omega_using [dims])
    (by simpa only [show 8 * (2 * Spec.Rsa.modulusWords len) = 16 * Spec.Rsa.modulusWords len by omega_using []] using h.preApart)
  have E := scratch_bytes Os (by have := h.eBound; have := h.upper; omega_using []) h.eApart
  have X := scratch_bytes Os (by have := h.upper; omega_using [dims]) h.inApart
  refine ⟨?_, ((outside_frame O (by omega_using [nw])).mono (by simp)).trans P.2⟩
  intro nB length key
  have R := P.1 nB length (by rw [W]; exact key)
  rw [E, X] at R
  exact R

end VG.Proof.Bignum.X86.PublicContext
