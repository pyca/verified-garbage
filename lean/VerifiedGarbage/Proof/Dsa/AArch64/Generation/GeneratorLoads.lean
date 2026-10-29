module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorRange
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
import VerifiedGarbage.Proof.Framework.Omega

/-! # Load a modulus and a candidate into the range-check workspace -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.Rsa VG.Impl.Bignum VG.Impl.Bignum.AArch64

theorem generatorLoadPair_ok {s : State} {B pp hp : Addr} {Z w : Nat} {pb hb : List Byte}
    (h : Ws s B Z w)
    (hptr : word s.mem B 128 = pp) (hlen : word s.mem B 136 = BitVec.ofNat 64 pb.length)
    (xptr : word s.mem B 144 = hp) (xlen : word s.mem B 152 = BitVec.ofNat 64 hb.length)
    (sp : Src s B Z pp pb) (sx : Src s B Z hp hb)
    (hp1 : 1 ≤ pb.length) (hpw : pb.length ≤ 8 * w)
    (hx1 : 1 ≤ hb.length) (hxw : hb.length ≤ 8 * w) :
    WP isa Impl.Dsa.AArch64.Generation.generatorLoadPair s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w 0) w = Spec.Rsa.os2ip pb ∧
      wv t.mem B (slot w 1) w = Spec.Rsa.os2ip hb ∧
      Frm B [ar w 0, ar w 1] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.generatorLoadPair
  refine WP.seq (WP.mono (loadCandidateArray_ok h (by decide : 0 < 16) (by decide : 16 < 32)
    (by decide : 17 < 32) hptr hlen sp hp1 hpw) fun u ⟨hu, up, fu, ku⟩ => ?_)
  have uh : ∀ d, d + 8 ≤ 256 → word u.mem B d = word s.mem B d := by
    intro d hd
    exact fu.word_eq (by simp only [List.mem_singleton]; rintro r rfl; simp [slot, hdrBytes]; omega)
      (by have := h.scr.nowrap; have := h.h256; omega)
  have sxu := sx.congrK (InScr.of_frm fu (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; exact h.sl (by decide))) ku
  refine WP.mono (loadCandidateArray_ok hu (by decide : 1 < 16) (by decide : 18 < 32)
    (by decide : 19 < 32) (by rw [uh 144 (by decide)]; exact xptr)
    (by rw [uh 152 (by decide)]; exact xlen) sxu hx1 hxw) fun v ⟨hv, vx, fv, kv⟩ => ?_
  have vp : wv v.mem B (slot w 0) w = Spec.Rsa.os2ip pb := by
    rw [fv.wv_eq (by
      simp only [List.mem_singleton]; rintro r rfl; left; simp only [slot, hdrBytes]; omega)
      (by have := h.sl (by decide : 0 < 16); have := h.scr.nowrap; omega), up]
  exact ⟨hv, vp, vx, (fu.mono (by simp)).trans (fv.mono (by simp)), (ku.trans kv).mono (by decide)⟩


end VG.Proof.Dsa.AArch64.Generation
