module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorLoads
public import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
import VerifiedGarbage.Proof.Framework.Omega

/-! # Accept the computed generator exactly when it is greater than one -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.Rsa VG.Impl.Bignum VG.Impl.Bignum.AArch64

theorem generatorResult_ok {s : State} {B pp gp : Addr} {Z w : Nat} {pb gb : List Byte}
    (h : Ws s B Z w)
    (hptr : word s.mem B 128 = pp) (hlen : word s.mem B 136 = BitVec.ofNat 64 pb.length)
    (xptr : word s.mem B 144 = gp) (xlen : word s.mem B 152 = BitVec.ofNat 64 gb.length)
    (sp : Src s B Z pp pb) (sx : Src s B Z gp gb)
    (hp1 : 1 ≤ pb.length) (hpw : pb.length ≤ 8 * w)
    (hx1 : 1 ≤ gb.length) (hxw : gb.length ≤ 8 * w) (hlt : Spec.Rsa.os2ip gb < Spec.Rsa.os2ip pb) :
    WP isa Impl.Dsa.AArch64.Generation.generatorResult s fun t =>
      t.gpr .x3 = mask (decide (1 < Spec.Rsa.os2ip gb)) ∧
      Ws t B Z w ∧ Frm B [ar w 0, ar w 1] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.generatorResult
  refine WP.seq (WP.mono (generatorLoadPair_ok h hptr hlen xptr xlen sp sx hp1 hpw hx1 hxw)
    fun u ⟨hu, up, ug, fu, ku⟩ => ?_)
  refine WP.mono (VG.Proof.Dsa.AArch64.rangeMask_ok hu.good.1 hu.good.2 h.w1 (by have := h.w2; omega) true)
    fun t ⟨htmask, hm, kt⟩ => ?_
  refine ⟨?_, hu.congr (by rw [hm]; exact Frm.refl B [] _) (by simp) kt (by decide),
    hm ▸ fu, (ku.trans kt).mono (by decide)⟩
  simpa only [VG.Impl.Bignum.Public.aX, VG.Impl.Bignum.Public.aN, ite_true, ug, up, hlt, and_true] using htmask

end VG.Proof.Dsa.AArch64.Generation
