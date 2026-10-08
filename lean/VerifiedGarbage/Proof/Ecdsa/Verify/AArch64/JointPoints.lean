import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointSetup
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointWindow
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFinish

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)

/-- The interleaved multiplication returns the sum required by ECDSA verification. -/
theorem jointPoints_ok (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (hM : Mid p256 s₀ base g s)
    (hTP : TblPre p256 s₀ (s₀.syms p256.tsym) base)
    {P : Point p256.C} (hP : onCurve p256.C P=true)
    (hrep : Rep p256.C (tmv p256.C 4 base s (p256.sl PX)) (tmv p256.C 4 base s (p256.sl PY))
      (tmv p256.C 4 base s (p256.sl ONEP)) P) :
    WP isa P256Joint.points s fun t => FinalState p256 s₀ base g t ∧
      Rep p256.C (tmv p256.C 4 base t (p256.sl RX)) (tmv p256.C 4 base t (p256.sl RY))
        (tmv p256.C 4 base t (p256.sl RZ))
        (add (mul (sv p256 base s U) (G p256.C)) (mul (sv p256 base s V) P)) := by
  have hm := unitMod_pow_two hc.p_odd (64*p256.n)
  have hOne : P256Joint.cfg.K.one<p256.C.p := by
    change 2^256%p256.C.p<p256.C.p
    exact Nat.mod_lt _ (by have := hc.p_ge; omega)
  have hone : toM p256.C.p (2^(64*P256Joint.cfg.K.M.n)) P256Joint.cfg.K.one=1 := toM_cmont hc.toBaseCfgOk 1
  rw [P256Joint.points,Joint.points,Joint.window]
  apply WP.assoc
  apply WP.assoc
  apply WP.assoc
  refine WP.seq (WP.mono (WP.assoc' (jointSetup_ok hc hC hT hM hTP hP hrep)) fun a ia => ?_)
  apply WP.assoc
  refine WP.seq (WP.mono (jointInitializedRun_ok hm hC hc.am3 hOne hc.onG hP
    (show sv p256 base s U<2^256 from wordsVal_lt ..)
    (show sv p256 base s V<2^256 from wordsVal_lt ..) ia.field ia.stable ia.generator)
    fun b ⟨kb,ib,_⟩ => ?_)
  refine WP.mono (jointFinish_ok (jacLay hc rfl) rfl (jacAligned p256 rfl) hm hC hOne hone
    (by decide) ib) fun t ⟨kt,ut,_,lt,rep⟩ => ?_
  have un := jointPoint_union (jointPoint_union ia.unch (kb.unch.cover jointPoint_loop))
    (ut.cover jointPoint_finish)
  have hs := ib.field.scr.of_keepRegs kt (by decide)
  exact ⟨finalState_of_joint hM hs (kt.rd.trans (kb.regs.rd.trans ia.rd))
    (kt.wr.trans (kb.regs.wr.trans ia.wr)) un (lt _ (by decide)) (lt _ (by decide)),rep⟩

end VG.Proof.Ecdsa.Verify.AArch64
