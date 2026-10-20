module
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPost
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedFn

import VerifiedGarbage.Proof.Bignum.X86.PrecomputedKey
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedChecked
import VerifiedGarbage.Proof.Bignum.PackedFrame
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPostFrame
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Spec.RsaKeyGen

/-! # Complete fixed-width public RSA from a stored precomputation -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem precomputedSized_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputedInputs base bytes len args s)
    (E : val32 s.mem base 128 2 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat))
    (validE : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)) = true) :
    WP isa (VG.Impl.Bignum.X86.PrecomputedFn.sized (Spec.Rsa.modulusWords len)) s fun t =>
      PrecomputedPost base bytes len args s.mem t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nw := h.scratch.nowrap
  have sz := h.space
  have size := size_eq (Spec.Rsa.modulusWords len)
  have dims := h.dimensions
  unfold VG.Impl.Bignum.X86.PrecomputedFn.sized
  refine WP.seq (WP.mono (precomputedKey_ok h) fun u ⟨N, R, O, K⟩ => ?_)
  have Os : Outside base 16 (bytes - 16) s.mem u.mem := O.mono (by omega) (by omega)
  have Os' : Outside base 0 bytes s.mem u.mem := O.mono (by omega) (by omega)
  have hu := h.keep K (by decide) (by decide) Os'
  have M := scratch_wv Os' (by omega) (by omega) (n := Spec.Rsa.modulusWords len)
    (d := 0) (by omega) (by omega) h.preApart
  have P := scratch_wv Os' (by omega) (by omega) (n := Spec.Rsa.modulusWords len)
    (d := 8 * Spec.Rsa.modulusWords len) (by omega) (by omega) h.preApart
  have EB := scratch_bytes Os' (by have := h.eBound; have := h.upper; omega) h.eApart
  refine WP.mono (precomputedChecked_ok hu (by rw [M]; exact N) (by rw [P]; exact R)
    (by rw [VG.Proof.Mont.Outside.val32 O (.inl (by decide)) (by decide), EB, E]) (by rw [EB]; exact validE)) fun t ⟨Post, Keep⟩ => ?_
  exact ⟨precomputedPost_compose h Os Post, (K.mono (by decide)).trans Keep⟩

end VG.Proof.Bignum.X86.PublicContext
