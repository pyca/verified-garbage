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

theorem mulWithInverse_of_window (hc : CfgOk p256) {ip : Prog isa} {W : List (Nat × Nat)}
    (hfixed : FixedOk p256 W)
    (hslots : ∀ i,i<45 → i∉[VG.Impl.Ecdsa.AArch64.ACC,VG.Impl.Ecdsa.AArch64.TMP] → ∀w∈W,
      p256.sl i+8*p256.n≤w.1 ∨ w.1+w.2≤p256.sl i)
    (hflag : ∀w∈W,p256.sl VG.Impl.Ecdsa.AArch64.FLAG+8≤w.1 ∨ w.1+w.2≤p256.sl VG.Impl.Ecdsa.AArch64.FLAG)
    (hip : ∀ {s : State} {base : Addr},Scr s base 8192 → ModOkA p256.MP' 8192 C.p s.mem base →
      wordsVal s.mem base (p256.sl VG.Impl.Ecdsa.AArch64.RZ) p256.n<C.p →
      WP isa ip s fun t => KeepRegs (powClob p256.n) s t ∧ Unch base W s.mem t.mem ∧
        wordsVal t.mem base (p256.sl VG.Impl.Ecdsa.AArch64.ACC) p256.n<C.p ∧
        toM C.p (2^(64*p256.n)) (wordsVal t.mem base (p256.sl VG.Impl.Ecdsa.AArch64.ACC) p256.n)=
          toM C.p (2^(64*p256.n)) (wordsVal s.mem base (p256.sl VG.Impl.Ecdsa.AArch64.RZ) p256.n)^(C.p-2))
    (hw : ∀ {base : Addr} {P : Point C} {k : Nat} {s : State},onCurve C P=true → k<2^256 →
      Fixed base P k s → WP isa Impl.P256.EcdhJac.window s (WindowPost base P k s)) :
    MulWithInverseOk p256 mq ip := by
  intro base s hs g hf P hP hpx hpy hrep rest R h
  have hk : sv p256 base s VG.Impl.Ecdsa.AArch64.K<2^256 := wordsVal_lt ..
  apply WP.assoc'
  refine WP.seq (WP.mono (prep_ok hc hs hf hpx hpy hrep) fun u ⟨fu,hu,ku⟩=>?_)
  refine WP.seq (WP.mono (wrapped_ok hu (fun v hv=>hw hP hk hv)) fun t ht=>?_)
  have ready : MulReady base g P (sv p256 base s VG.Impl.Ecdsa.AArch64.K) s t := by
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
  exact finishInverse_ok hc hfixed hslots hflag ready
    (hip ready.scr (modP_of hc.toBaseCfgOk ready.fixed.mp) ready.rz_lt) h

theorem mul_of_window (hc : CfgOk p256)
    (hw : ∀ {base : Addr} {P : Point C} {k : Nat} {s : State},onCurve C P=true → k<2^256 →
      Fixed base P k s → WP isa Impl.P256.EcdhJac.window s (WindowPost base P k s)) :
    MulOk p256 mq :=
  mulWithInverse_of_window hc fixedOk_chainWc (fun _ hi hn => apart_chainWc hi hn)
    (by decide) (pPow_ok hc) hw

end VG.Proof.P256.EcdhJac
