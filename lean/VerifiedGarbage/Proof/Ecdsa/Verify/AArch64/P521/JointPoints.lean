module

public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointLayout
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.ProjectiveFlags

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPrep
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedBridge
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedTable
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Framework.AArch64.Syms

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P521/JointFinal.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass

def pointRanges : List (Nat×Nat) := prepRanges ++ winW P521Joint.K ++ PubNaf.cacheW P521Joint.K

theorem point_bounds : ∀w∈pointRanges,w.1+w.2≤8192 := by decide

theorem point_fixed : FixedOk p521 pointRanges := by unfold FixedOk; decide

/-- The joint path preserves all flag/scalar inputs to the unchanged final check. -/
theorem finalState_of_joint {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64}
 (h : Mid p521 s₀ base g s) (hs : Scr t base size)
 (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hu : Unch base pointRanges s.mem t.mem)
 (hx : sv p521 base t RX<p521.C.p) (hz : sv p521 base t RZ<p521.C.p) :
 FinalState p521 s₀ base g t := by
 have same (i : Nat) (hi : i∈[RM',K]) : sv p521 base t i=sv p521 base s i := by
  apply hu.wordsVal
  · have he : ∀i∈[RM',K],∀w∈pointRanges,p521.sl i+72≤w.1 ∨ w.1+w.2≤p521.sl i := by decide
    exact he i hi
  · have he : ∀i∈[RM',K],p521.sl i+72≤2^64 := by decide
    exact he i hi
 refine ⟨hs,hw.trans h.wr,hr.trans h.rd,h.fixed.unch (by decide) h.scr.nowrap point_fixed hu,
  ?_,?_,?_,hz,?_,?_,hx⟩
 · rw [hu.word (by decide) (by decide)]
   exact h.flag
 · rw [same RM' (by simp)]; exact h.rm_lt
 · change toM _ _ (sv p521 base t RM')=_
   rw [same RM' (by simp)]; exact h.rm
 · exact unch_whole (h.unch.trans hu) (by
     intro w hw
     rcases List.mem_append.mp hw with hw|hw
     · rw [List.mem_singleton.mp hw]; exact Nat.le_refl _
     · exact point_bounds w hw)
 · rw [same K (by simp)]; exact h.k
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
end

end

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
