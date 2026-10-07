import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPublic
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPoints

/-! The two-scalar multiplication leaks only the public verification inputs. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64 VG.Proof.P256.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)
open VG.Impl.Ecdsa.Verify.X86_64 (U V)

structure JointMulChecks (c : Cfg) (j : Joint.Cfg) : Prop where
  cached : JointCachedChecks j
  fixed : JointFixedChecks j
  double : ScratchCT (Impl.P256.X86_64.doubleHalfPublic j.K.M j.K.S j.K.R)
  table : NafTableChecks j.K
  cache : ScratchCT (Naf.cacheTable j.K.M j.K.tbl j.cache 8)
  seed : ScratchCT (.block (Jacobian.infinity j.K j.K.R))
  prepG : FastPrepChecks (c.sl U) j.gBits 7
  prepQ : FastPrepChecks (c.sl V) j.K.bits 5

theorem jointPoints_relCT {c : Cfg} {j : Joint.Cfg} {d : CombData}
    (hCurve : c.C=Spec.P256.curve) (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c)
    (hcd : c.comb=some d) (hn : c.n=4) (hw : d.w=7) (hsym : j.tsym=d.tsym)
    (hK : j.K=c.winCfg PX PY BP) (hnp : c.C.n≤c.C.p)
    (hL : JointAddLayout j size) (hInit : JointInitLayout j size)
    (hPrep : JointPrepLayout j size (c.sl U) (c.sl V)) (hd : (doubleSlots j.K.S j.K.R).Nodup)
    (checks : JointMulChecks c j)
    {s₀ t₀ : State} (ps : VPre c s₀) (pt : VPre c t₀) (pub : JointPublic c d s₀ t₀) :
    RelCT isa (fun s t => (∃ g,Mid c s₀ (s₀.gpr .rcx) g s) ∧ (∃ h,Mid c t₀ (t₀.gpr .rcx) h t))
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointPoints c j)
      (fun s t => X86_64.Taint.Agree (Taint.ofRegs [.rdi]) s t) := by
  intro s t ls lt s' t' ⟨⟨g,hs⟩,⟨h,ht⟩⟩ es et
  have base : s₀.gpr .rcx=t₀.gpr .rcx := pub.regs.rf.1 .rcx (by decide)
  have ht' : Mid c t₀ (s₀.gpr .rcx) h t := by rw [base]; exact ht
  have fields := jointMid_field_pair hc hK hnp pub hs ht'
  have one := (consts_tmv hc hs.fixed).2.2
  let Q := peerPt c (s₀.mem (s₀.gpr .rdi)=4) (keyX c s₀) (keyY c s₀)
  have hQ : onCurve c.C Q=true := peerPt_onCurve hc _ _ _
  have rep : Rep c.C (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PX))
      (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PY)) (tmv c.C c.n (s₀.gpr .rcx) s (c.sl ONEP)) Q := by
    rw [one]
    exact peerPt_rep hC _ _ _ hs.px hs.py
  have point := jointMid_point hc hC hK hs rep
  have zero := jointMid_zero hK hs
  have genS := jointMid_generator hc hC hT hcd hn hw hsym ps hs
  have genT : JointGenerator j c.C (s₀.gpr .rcx) (s₀.syms d.tsym) size
      (jointCombRow hc hC hT hcd hn hw) t := by
    rw [base,pub.sym]
    exact jointMid_generator hc hC hT hcd hn hw hsym pt ht
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
  have sv4 (a : State) (i : Nat) : wordsVal a.mem (s₀.gpr .rcx) (c.sl i) 4=sv c (s₀.gpr .rcx) a i := by
    unfold sv
    rw [hn]
  have u : sv c (s₀.gpr .rcx) t U=sv c (s₀.gpr .rcx) s U :=
    (mid_publicU ht').trans (pub.u.symm.trans (mid_publicU hs).symm)
  have v : sv c (s₀.gpr .rcx) t V=sv c (s₀.gpr .rcx) s V :=
    (mid_publicV ht').trans (pub.v.symm.trans (mid_publicV hs).symm)
  have ct := p256_jointMul_relCT (base:=s₀.gpr .rcx) (T:=s₀.syms d.tsym)
    (row:=jointCombRow hc hC hT hcd hn hw) hCurve hL hInit hPrep hm hC hc.am3 hd hone honeval hc.onG hQ
    point zero (Nat.lt_trans hs.u_lt nlt) (Nat.lt_trans hs.v_lt nlt)
    checks.cached checks.fixed checks.double checks.table checks.cache checks.seed checks.prepG checks.prepQ
  obtain ⟨trace,post⟩ := ct _ _ _ _ _ _
    ⟨fields,genS,genT,sv4 s U,sv4 s V,(sv4 t U).trans u,(sv4 t V).trans v⟩ es et
  obtain ⟨E,pair⟩ := post.1
  exact ⟨trace,fieldPair_public pair⟩

end VG.Proof.Ecdsa.Verify.X86_64
