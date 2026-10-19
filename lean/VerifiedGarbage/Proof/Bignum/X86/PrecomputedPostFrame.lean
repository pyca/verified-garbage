module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPost

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
  have Os : Outside base 0 bytes s.mem u.mem := O.mono (by omega) (by omega)
  have dims := h.dimensions
  have W := scratch_words Os (by omega) (n := 2 * Spec.Rsa.modulusWords len) (by omega)
    (by simpa only [show 8 * (2 * Spec.Rsa.modulusWords len) = 16 * Spec.Rsa.modulusWords len by omega] using h.preApart)
  have E := scratch_bytes Os (by have := h.eBound; have := h.upper; omega) h.eApart
  have X := scratch_bytes Os (by have := h.upper; omega) h.inApart
  refine ⟨?_, ((outside_frame O (by omega)).mono (by simp)).trans P.2⟩
  intro nB length key
  have R := P.1 nB length (by rw [W]; exact key)
  rw [E, X] at R
  exact R

end VG.Proof.Bignum.X86.PublicContext
