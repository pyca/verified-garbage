module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorRange
public import VerifiedGarbage.Proof.Rsa.Ranges
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorLoads
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DecrementOdd
import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
import VerifiedGarbage.Proof.Framework.Omega

/-! # Exact range filtering of each public generator input -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.Rsa VG.Impl.Bignum VG.Impl.Bignum.AArch64

theorem generatorRange_ok {s : State} {B pp hp : Addr} {Z w : Nat} {pb hb : List Byte}
    (h : Ws s B Z w)
    (hptr : word s.mem B 128 = pp) (hlen : word s.mem B 136 = BitVec.ofNat 64 pb.length)
    (xptr : word s.mem B 144 = hp) (xlen : word s.mem B 152 = BitVec.ofNat 64 hb.length)
    (sp : Src s B Z pp pb) (sx : Src s B Z hp hb)
    (hp1 : 1 ≤ pb.length) (hpw : pb.length ≤ 8 * w)
    (hx1 : 1 ≤ hb.length) (hxw : hb.length ≤ 8 * w) (hodd : Spec.Rsa.os2ip pb % 2 = 1) :
    WP isa Impl.Dsa.AArch64.Generation.generatorRange s fun t =>
      t.gpr .x3 = mask (decide (1 < Spec.Rsa.os2ip hb ∧ Spec.Rsa.os2ip hb < Spec.Rsa.os2ip pb - 1)) ∧
      Ws t B Z w ∧ Frm B [ar w 0, ar w 1] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.generatorRange
  refine WP.seq (WP.mono (generatorLoadPair_ok h hptr hlen xptr xlen sp sx hp1 hpw hx1 hxw)
    fun v ⟨hv, vp, vx, fv, kv⟩ => ?_)
  refine WP.seq (WP.mono (decrementOdd_ok hv (by decide : 0 < 16) (by rw [vp]; exact hodd))
    fun z ⟨hz, zp, fz, kz⟩ => ?_)
  have zx : wv z.mem B (slot w 1) w = Spec.Rsa.os2ip hb := by
    rw [fz.wv (Or.inr (by simp only [slot, hdrBytes]; omega))
      (by have := h.sl (by decide : 1 < 16); have := h.scr.nowrap; omega), vx]
  refine WP.mono (VG.Proof.Dsa.AArch64.rangeMask_ok hz.good.1 hz.good.2 h.w1 (by have := h.w2; omega) true)
    fun t ⟨htmask, hm, kt⟩ => ?_
  have ht : Ws t B Z w := hz.congr (by rw [hm]; exact Frm.refl B [] _)
    (by simp) kt (by decide)
  refine ⟨?_, ht, ?_, ((kv.trans kz).trans kt).mono (by decide)⟩
  · simpa only [VG.Impl.Bignum.Public.aX, VG.Impl.Bignum.Public.aN, ite_true, zx, zp, vp] using htmask
  · have fz' : Frm B [ar w 0, ar w 1] v.mem z.mem :=
      Frm.of_outside (fz.mono (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp [ar])
    rw [hm]
    exact fv.trans fz'

end VG.Proof.Dsa.AArch64.Generation
