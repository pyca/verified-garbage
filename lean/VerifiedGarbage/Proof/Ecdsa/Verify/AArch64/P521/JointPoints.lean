module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPrep
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFinal
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedBridge
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedTable
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)

theorem points_ok (hc : CfgOk p521) (hC : Law p521.C) (hO : PrimeOrder p521.C)
 (hn : 17≤p521.C.n) (hT : CombOkW p521.C 7 83 p521.tbl p521.start)
 {s₀ s : State} {base : Addr} {g : Reg→BitVec 64} (hm : Mid p521 s₀ base g s)
 (ht : TblPre p521 s₀ (s₀.syms p521.tsym) base)
 {P : Point p521.C} (hP : onCurve p521.C P=true)
 (hr : Rep p521.C (tmv p521.C p521.n base s (p521.sl PX)) (tmv p521.C p521.n base s (p521.sl PY))
  (tmv p521.C p521.n base s (p521.sl ONEP)) P) :
 WP isa P521Joint.points s fun t=>FinalState p521 s₀ base g t ∧
  Rep p521.C (tmv p521.C p521.n base t (p521.sl RX)) (tmv p521.C p521.n base t (p521.sl RY))
   (tmv p521.C p521.n base t (p521.sl RZ))
   (add (mul (sv p521 base s U) (G p521.C)) (mul (sv p521 base s V) P)) := by
 have source₀ := FixedGenerator.of_pre hc hC hT ht rfl
 have source := source₀.unch hm.unch (by decide) hm.rd hm.wr hm.syms
 have hp := unitMod_pow_two hc.p_odd (64*P521Joint.K.M.n)
 have hone : P521Joint.K.one<p521.C.p := Nat.mod_lt _ (by have := hc.p_ge; omega)
 have one : toM p521.C.p (2^(64*P521Joint.K.M.n)) (p521.mont 1)=1 := by
  rw [show P521Joint.K.M.n=p521.n from rfl,toM_cmont hc.toBaseCfgOk]; rfl
 have pn : p521.C.p<2^(64*P521Joint.K.M.n) := by
  simpa only [show P521Joint.K.M.n=p521.n from rfl] using hc.p_lt
 rw [P521Joint.points]
 apply WP.assoc
 refine WP.seq (WP.mono_syms (prepare_ok hc hC hm.scr hm.fixed hm.px_lt hm.py_lt hr)
   fun a ⟨sa,ma,fa,_,_,ua,ra,wa,_,za,ga⟩ sy=>?_)
 have srca := source.unch ua (by decide) ra wa sy
 have az : tmv p521.C P521Joint.K.M.n base a P521Joint.K.P.z=1 := by
  simpa only [P521Joint.K,VG.Impl.Ecdsa.Verify.AArch64.Cfg.packedNafQ,Cfg.winCfg,Cfg.MP',Cfg.pt] using za
 have vb : sv p521 base s V<2^(64*P521Joint.K.M.n) := by
  rw [show P521Joint.K.M.n=p521.n from rfl]
  exact wordsVal_lt ..
 have ub : sv p521 base s U<2^(64*P521Joint.K.M.n) := by
  rw [show P521Joint.K.M.n=p521.n from rfl]
  exact wordsVal_lt ..
 refine WP.mono (window_source_ok (packedNafLay hc rfl) hp hC hc.am3 pn hone one hO hn hP hc.onG
  sa ma fa az vb
  ub srca ga)
  fun t ⟨st,kt,ut,_,lt,rep⟩=>?_
 have un : Unch base pointRanges s.mem t.mem := by
  simpa only [pointRanges,List.append_assoc] using ua.trans ut
 have ltr : ∀x∈[p521.sl RX,p521.sl RY,p521.sl RZ],wordsVal t.mem base x p521.n<p521.C.p := by
  simpa only [P521Joint.K,VG.Impl.Ecdsa.Verify.AArch64.Cfg.packedNafQ,Cfg.winCfg,Cfg.MP',Cfg.pt] using lt
 have rr : Rep p521.C (tmv p521.C p521.n base t (p521.sl RX)) (tmv p521.C p521.n base t (p521.sl RY))
  (tmv p521.C p521.n base t (p521.sl RZ))
  (add (mul (sv p521 base s U) (G p521.C)) (mul (sv p521 base s V) P)) := by
  simpa only [P521Joint.K,VG.Impl.Ecdsa.Verify.AArch64.Cfg.packedNafQ,Cfg.winCfg,Cfg.MP',Cfg.pt] using rep
 exact ⟨finalState_of_joint hm st (kt.rd.trans ra) (kt.wr.trans wa) un (ltr _ (by simp)) (ltr _ (by simp)),rr⟩
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
