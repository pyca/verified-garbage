import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64.Joint
import VerifiedGarbage.Proof.P256.X86_64.JointMul
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointGenerator
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointFrame

/-! The joint multiplication consumes the verifier's actual scalars and preserves its final inputs. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P256.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)
open VG.Impl.Ecdsa.Verify.X86_64 (U V)

structure JointPointsPost (c : Cfg) (s₀ sM : State) (g : Reg → BitVec 64) (Q : Point c.C) (t : State) : Prop where
  input : ProjectiveInput c s₀ (s₀.gpr .rcx) g t
  point : InvJ c.C (tmv c.C c.n (s₀.gpr .rcx) t (c.sl RX))
    (tmv c.C c.n (s₀.gpr .rcx) t (c.sl RY)) (tmv c.C c.n (s₀.gpr .rcx) t (c.sl RZ))
    (add (mul (sv c (s₀.gpr .rcx) sM U) (G c.C)) (mul (sv c (s₀.gpr .rcx) sM V) Q))

theorem jointPoints_ok {c : Cfg} {j : Joint.Cfg} {d : CombData}
    (hCurve : c.C=Spec.P256.curve) (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c)
    (hcd : c.comb=some d) (hn : c.n=4) (hw : d.w=7) (hsym : j.tsym=d.tsym)
    (hK : j.K=c.winCfg PX PY BP) (ha : AM3 c.C) (hnp : c.C.n≤c.C.p)
    (hL : JointAddLayout j size) (hInit : JointInitLayout j size)
    (hPrep : JointPrepLayout j size (c.sl U) (c.sl V)) (hFrame : JointFrameLayout c j)
    (hd : (doubleSlots j.K.S j.K.R).Nodup)
    {s₀ s : State} {g : Reg → BitVec 64} (hp : VPre c s₀) (h : Mid c s₀ (s₀.gpr .rcx) g s)
    {Q : Point c.C} (hQ : onCurve c.C Q=true)
    (hq : Rep c.C (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PX))
      (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PY)) (tmv c.C c.n (s₀.gpr .rcx) s (c.sl ONEP)) Q) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointPoints c j) s (JointPointsPost c s₀ s g Q) := by
  have field := jointMid_field hc hK hnp h
  have point := jointMid_point hc hC hK h hq
  have zero := jointMid_zero hK h
  have generator := jointMid_generator hc hC hT hcd hn hw hsym hp h
  have hm : UnitMod c.C.p (2^(64*j.K.M.n)) := unitMod_pow_two hc.p_odd _
  have hone : j.K.one<c.C.p := by
    rw [hK]
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne c.C.p))
  have honeval : toM c.C.p (2^256) j.K.one=1 := by
    rw [hK]
    change toM c.C.p (2^256) (c.mont 1)=1
    simp only [Cfg.mont,Cfg.R,Nat.one_mul,hn]
    exact toM_one (unitMod_pow_two hc.p_odd _)
  have nlt : c.C.n<2^256 := by simpa only [hn] using hc.n_lt
  have sv4 (i : Nat) : wordsVal s.mem (s₀.gpr .rcx) (c.sl i) 4=sv c (s₀.gpr .rcx) s i := by
    unfold sv
    rw [hn]
  refine WP.mono (p256_jointMul_ok hCurve hL hInit hPrep hm hC ha hd hone honeval hc.onG hQ
    point zero (Nat.lt_trans h.u_lt nlt) (Nat.lt_trans h.v_lt nlt) field generator (sv4 U) (sv4 V))
    fun t ⟨ct,_,_,_,ut⟩ => ?_
  refine ⟨jointFrame_input hc hK hFrame h ct ut,?_⟩
  have pt := ct.point
  rw [hK] at pt
  exact pt

end VG.Proof.Ecdsa.Verify.X86_64
