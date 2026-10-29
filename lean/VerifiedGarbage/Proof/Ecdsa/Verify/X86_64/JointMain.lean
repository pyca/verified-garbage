module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64.Joint
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointGenerator
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointFrame
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDoubler
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepFields

import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTail
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointMul
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointInput
/-! End-to-end correctness of public Jacobian joint verification. -/

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/X86_64/JointPoints.lean`, which only this module imported.
section

/-! The joint multiplication consumes the verifier's actual scalars and preserves its final inputs. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)
open VG.Impl.Ecdsa.Verify.X86_64 (U V)

structure JointPointsPost (c : Cfg) (s₀ sM : State) (g : Reg → BitVec 64) (Q : Point c.C) (t : State) : Prop where
  input : ProjectiveInput c s₀ (s₀.gpr .rcx) g t
  point : InvJ c.C (tmv c.C c.n (s₀.gpr .rcx) t (c.sl RX))
    (tmv c.C c.n (s₀.gpr .rcx) t (c.sl RY)) (tmv c.C c.n (s₀.gpr .rcx) t (c.sl RZ))
    (add (mul (sv c (s₀.gpr .rcx) sM U) (G c.C)) (mul (sv c (s₀.gpr .rcx) sM V) Q))

theorem jointPoints_ok {c : Cfg} {j : Joint.Cfg} {d : CombData} {double : Prog isa}
    (hc : CfgOk c) (hC : Law c.C) {J : Nat} (hG : JointGTable c j d J)
    (hK : j.K=c.winCfg PX PY BP) (ha : AM3 c.C) (hnp : c.C.n≤c.C.p)
    (hL : JointAddLayout j size) (hInit : JointInitLayout j size)
    (hPrep : JointPrepLayout j size (c.sl U) (c.sl V)) (hFrame : JointFrameLayout c j)
    (hD : JointDoubler j c.C size double) (hZ : j.coZ=true → PrimeOrder c.C ∧ 17≤c.C.n)
    {s₀ s : State} {g : Reg → BitVec 64} (hp : VPre c s₀) (h : Mid c s₀ (s₀.gpr .rcx) g s)
    {Q : Point c.C} (hQ : onCurve c.C Q=true)
    (hq : Rep c.C (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PX))
      (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PY)) (tmv c.C c.n (s₀.gpr .rcx) s (c.sl ONEP)) Q) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointPoints c j double).inline s (JointPointsPost c s₀ s g Q) := by
  have field := jointMid_field hc hK hnp h
  have point := jointMid_point hc hC hK h hq
  have zero := jointMid_zero hK h
  have generator := jointMid_generator hc hC hG hK hp h
  have hjn : j.K.M.n=c.n := by rw [hK]; rfl
  have hm : UnitMod c.C.p (2^(64*j.K.M.n)) := unitMod_pow_two hc.p_odd _
  have hone : j.K.one<c.C.p := by
    rw [hK]
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne c.C.p))
  have honeval : toM c.C.p (2^(64*j.K.M.n)) j.K.one=1 := by
    rw [hK]
    change toM c.C.p (2^(64*c.n)) (c.mont 1)=1
    simp only [Cfg.mont,Cfg.R,Nat.one_mul]
    exact toM_one (unitMod_pow_two hc.p_odd _)
  have nlt : c.C.n<2^(64*j.K.M.n) := by rw [hjn]; exact hc.n_lt
  have sv4 (i : Nat) : wordsVal s.mem (s₀.gpr .rcx) (c.sl i) j.K.M.n=sv c (s₀.gpr .rcx) s i := by
    unfold sv
    rw [hjn]
  refine WP.mono (jointMul_ok hL hInit hPrep hm hC ha hD hone honeval hc.onG hQ
    point (jointMid_affine hc hK h) zero hZ (Nat.lt_trans h.u_lt nlt) (Nat.lt_trans h.v_lt nlt) field generator (sv4 U) (sv4 V))
    fun t ⟨ct,_,_,_,ut⟩ => ?_
  refine ⟨jointFrame_input hc hK hFrame h ct ut,?_⟩
  have pt := ct.point
  rw [hK] at pt
  exact pt

end VG.Proof.Ecdsa.Verify.X86_64
end

end

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY)

/-- Joint verification inlined: only the points and the tail call functions. -/
theorem jointVerify_inline (c : Cfg) (j : Joint.Cfg) (double : Prog isa) :
    (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify c j double).inline =
    .seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.args c)) (.seq (Impl.Ecdh.X86_64.Cfg.prefix' c (some D))
      (.seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.loadS c)) (.seq (.block (Impl.Ecdh.X86_64.Cfg.peer c))
      (.seq (Impl.Ecdh.X86_64.Cfg.check c).inline (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.scalars c).inline
      (.seq c.nPow.inline (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.uv c).inline
      (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.jointPoints c j double).inline
        (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail c).inline)))))))) := by
  show Code.seq _ (Code.seq _ (Code.seq _ (Code.seq _ (Code.seq (Impl.Ecdh.X86_64.Cfg.check c).inline
    (Code.seq (Impl.Ecdsa.Verify.X86_64.Cfg.scalars c).inline (Code.seq c.nPow.inline
    (Code.seq (Impl.Ecdsa.Verify.X86_64.Cfg.uv c).inline _))))))) = _
  rfl

theorem jointVerify_ok {c : Cfg} {j : Joint.Cfg} {double : Prog isa}
    (hc : CfgOk c) (hC : Law c.C)
    (hpub : c.pubVerify=true) (hnp : c.C.n<c.C.p) (hpn : c.C.p≤2*c.C.n)
    {s₀ : State} (hp : VPre c s₀)
    (hpoints : ∀ {s : State} {g : Reg → BitVec 64} (_h : Mid c s₀ (s₀.gpr .rcx) g s)
      {Q : Point c.C}, onCurve c.C Q=true →
      Rep c.C (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PX))
        (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PY)) (tmv c.C c.n (s₀.gpr .rcx) s (c.sl ONEP)) Q →
      WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointPoints c j double).inline s (JointPointsPost c s₀ s g Q)) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify c j double).inline s₀ fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s₀.gpr r) ∧ VPost c s₀ t := by
  rw [jointVerify_inline]
  refine front_ok hc hp fun g s₁ hg hF => mid_ok hc hF fun s₂ hM => ?_
  have one := (consts_tmv hc hM.fixed).2.2
  let Q := peerPt c (s₀.mem (s₀.gpr .rdi)=4) (keyX c s₀) (keyY c s₀)
  have hQ : onCurve c.C Q=true := peerPt_onCurve hc _ _ _
  have hRep : Rep c.C (tmv c.C c.n (s₀.gpr .rcx) s₂ (c.sl PX))
      (tmv c.C c.n (s₀.gpr .rcx) s₂ (c.sl PY)) (tmv c.C c.n (s₀.gpr .rcx) s₂ (c.sl ONEP)) Q := by
    rw [one]
    exact peerPt_rep hC _ _ _ hM.px hM.py
  apply WP.seq
  refine WP.mono (hpoints hM hQ hRep) fun s₃ hP => ?_
  refine WP.mono (jointTail_ok hc hC hpub hnp hpn hM hP.input hP.point) fun t ⟨saved,post⟩ => ?_
  exact ⟨fun r hr => (saved r hr).trans (hg r hr),post⟩

end VG.Proof.Ecdsa.Verify.X86_64
