import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.P256.EcdhJac.Prep
import VerifiedGarbage.Proof.P256.EcdhJac.Wrapped
import VerifiedGarbage.Proof.P256.EcdhJac.Multiply
import VerifiedGarbage.Proof.P256.EcdhJac.Lit

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdsa.AArch64

theorem mul_of_window (hc : CfgOk p256)
    (hw : ∀ {base : Addr} {P : Point C} {k : Nat} {s : State},onCurve C P=true → k<2^256 →
      Fixed base P k s → WP isa Impl.P256.EcdhJac.window s (WindowPost base P k s)) :
    MulOk p256 mq := by
  intro base s hs g hf P hP hpx hpy hrep rest R h
  have hk : sv p256 base s VG.Impl.Ecdsa.AArch64.K<2^256 := wordsVal_lt ..
  apply WP.assoc'
  refine WP.seq (WP.mono (prep_ok hc hs hf hpx hpy hrep) fun u ⟨fu,hu,ku⟩=>?_)
  refine WP.seq (WP.mono (wrapped_ok hu (fun v hv=>hw hP hk hv)) fun t ht=>?_)
  apply finishPow_ok hc (s:=s) (k:=sv p256 base s VG.Impl.Ecdsa.AArch64.K) (h:=h)
  have unch : Unch base (prepWrites++wrappedWrites) s.mem t.mem := fu.unch.trans ht.frame.unch
  refine ⟨ht.field.scr,hf.unch hc.n10 hs.nowrap (by unfold FixedOk; decide) unch,?_,?_,
    ht.frame.regs.rd.trans fu.regs.rd,ht.frame.regs.wr.trans fu.regs.wr,?_,?_,ht.point,?_⟩
  · intro r hr
    rw [ht.restored r (by
      have hh : ∀ r∈[Reg.x26,.x27,.x28],r∈extraRegs := by decide
      exact hh r hr),ku.gpr r (by
      have hh : ∀ r∈[Reg.x26,.x27,.x28],r∉Reg.x19::clob 4 := by decide
      exact hh r hr)]
  · rw [ht.restored .x20 (by decide),ku.gpr .x20 (by decide)]
  · exact unch.word (by decide) (by decide)
  · exact unch.wordsVal (by decide) (by decide)
  · exact ht.field.lt K.R.z (by decide)

end VG.Proof.P256.EcdhJac
