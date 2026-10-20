module

public import VerifiedGarbage.Proof.Bignum.X86.CrtPost
import VerifiedGarbage.Proof.Bignum.X86.CrtDispatch
import VerifiedGarbage.Proof.Bignum.X86.PublicControls
import VerifiedGarbage.Proof.Bignum.X86.PublicDispatch

/-! # Public modulus length selects the complete private CRT implementation -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86

theorem valid_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : Inputs base bytes len args s)
    (valid : Spec.Rsa.modulusValid (componentValue s.mem args 2) len = true) :
    WP isa Crt.valid s fun t => Post base bytes len args s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold Crt.valid
  refine WP.seq (WP.mono (widthArgs_ok h.upper
    (by rw [← h.nLen]; exact (h.stack 3 (by decide)).readSrc)) fun u ⟨W, M, K⟩ => ?_)
  refine dispatch_ok PublicFn.widths (publicWidths_member h.lower h.upper) ?_ W ?_
  · intro n hn
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hn
    have := List.mem_range.mp hi
    omega
  · intro v Kv Mv
    have Ksv := K.trans (Kv.mono (by decide))
    have Msv := Mv.trans M
    have hv := h.keep Ksv (by decide) (by decide) (by rw [Msv]; exact Outside.refl _ _ _ _)
    refine WP.mono (sized_post hv (by rw [Msv]; exact valid)) fun t ⟨R, T⟩ => ?_
    exact ⟨by simpa only [Msv] using R, (Ksv.mono (by decide)).trans T⟩

end VG.Proof.Bignum.X86.Crt
