module
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointPrep
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFinal
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedBridge
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedTable
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Framework.AArch64.Syms
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)

theorem points_ok (hc : CfgOk p384) (hC : Law p384.C) (hO : PrimeOrder p384.C)
 (hn : 17≤p384.C.n) (hT : CombOkW p384.C 9 1 P384Joint.p384v.tbl P384Joint.p384v.start)
 (hD : ∀ base, DblSpec P384Joint.K p384.C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 {s₀ s : State} {base : Addr} {g : Reg→BitVec 64} (hm : Mid p384 s₀ base g s)
 (ht : TblPreW P384Joint.p384v.combWords s₀ (s₀.syms "VG_P384_GTAB") base)
 {P : Point p384.C} (hP : onCurve p384.C P=true)
 (hr : Rep p384.C (tmv p384.C p384.n base s (p384.sl PX)) (tmv p384.C p384.n base s (p384.sl PY))
  (tmv p384.C p384.n base s (p384.sl ONEP)) P) :
 WP isa P384Joint.points s fun t=>FinalState p384 s₀ base g t ∧
  Rep p384.C (tmv p384.C p384.n base t (p384.sl RX)) (tmv p384.C p384.n base t (p384.sl RY))
   (tmv p384.C p384.n base t (p384.sl RZ))
   (add (mul (sv p384 base s U) (G p384.C)) (mul (sv p384 base s V) P)) := by
 have source₀ := FixedGenerator.of_pre hc hC hT ht rfl
 have source := source₀.unch hm.unch (by decide) hm.rd hm.wr hm.syms
 have hp := unitMod_pow_two hc.p_odd (64*P384Joint.K.M.n)
 have hone : P384Joint.K.one<p384.C.p := Nat.mod_lt _ (by have := hc.p_ge; omega)
 have one : toM p384.C.p (2^(64*P384Joint.K.M.n)) (p384.mont 1)=1 := by
  rw [show P384Joint.K.M.n=p384.n from rfl,toM_cmont hc.toBaseCfgOk]; rfl
 have pn : p384.C.p<2^(64*P384Joint.K.M.n) := by
  simpa only [show P384Joint.K.M.n=p384.n from rfl] using hc.p_lt
 rw [P384Joint.points]
 apply WP.assoc
 refine WP.seq (WP.mono_syms (prepare_ok hc hC hm.scr hm.fixed hm.px_lt hm.py_lt hr)
   fun a ⟨sa,ma,fa,_,_,ua,ra,wa,_,za,ga⟩ sy=>?_)
 have srca := source.unch ua (by decide) ra wa sy
 have az : tmv p384.C P384Joint.K.M.n base a P384Joint.K.P.z=1 := by
  rw [show P384Joint.K.M.n=p384.n from rfl]; exact za
 have vb : sv p384 base s V<2^(64*P384Joint.K.M.n) := by
  rw [show P384Joint.K.M.n=p384.n from rfl]
  exact wordsVal_lt ..
 have ub : sv p384 base s U<2^(64*P384Joint.K.M.n) := by
  rw [show P384Joint.K.M.n=p384.n from rfl]
  exact wordsVal_lt ..
 refine WP.mono (window_source_ok (nafLayQ hc (by decide) (by decide)) hp hC hc.am3 pn hone one hO hn hP hc.onG
  (hD base) sa ma fa az vb
  ub srca ga)
  fun t ⟨st,kt,ut,_,lt,rep⟩=>?_
 have un : Unch base pointRanges s.mem t.mem := by
  simpa only [pointRanges,List.append_assoc] using ua.trans ut
 have ltr : ∀x∈[p384.sl RX,p384.sl RY,p384.sl RZ],wordsVal t.mem base x p384.n<p384.C.p := by
  simpa only [P384Joint.K,Cfg.winCfg,Cfg.MP',Cfg.pt] using lt
 have rr : Rep p384.C (tmv p384.C p384.n base t (p384.sl RX)) (tmv p384.C p384.n base t (p384.sl RY))
  (tmv p384.C p384.n base t (p384.sl RZ))
  (add (mul (sv p384 base s U) (G p384.C)) (mul (sv p384 base s V) P)) := by
  simpa only [P384Joint.K,Cfg.winCfg,Cfg.MP',Cfg.pt] using rep
 exact ⟨finalState_of_joint hm st (kt.rd.trans ra) (kt.wr.trans wa) un (ltr _ (by simp)) (ltr _ (by simp)),rr⟩
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
