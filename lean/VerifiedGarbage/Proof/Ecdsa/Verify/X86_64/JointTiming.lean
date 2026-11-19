module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPublic
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64.Joint
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDoubler
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitLayout
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitTiming
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepFields
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointMulTiming
import VerifiedGarbage.Proof.Ecdh.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointInput
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming

/-! ### `Ecdsa.Verify.X86_64.JointPointsTiming`, which the modules that import this one used -/

section

/-! The two-scalar multiplication leaks only the public verification inputs. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)
open VG.Impl.Ecdsa.Verify.X86_64 (U V)

/-- For a curve with `a = -3` (`CfgOk`), `dblJMul` doubles: the doubling of
every joint verifier on such a curve. -/
theorem _root_.VG.Proof.Ecdsa.X86_64.CfgOk.jdbl {c : Cfg} (hc : CfgOk c) (hC : Law c.C) : JDblOk c.C dblJMul :=
  jdblOk_dblJMul hC hc.am3

structure JointMulChecks (c : Cfg) (j : Joint.Cfg) : Prop where
  cached : JointCachedChecks j
  fixed : JointFixedChecks j
  table : JointTableChecks j
  cache : ScratchCT (Joint.cacheCode j).inline
  seed : ScratchCT (.block (Jacobian.infinity j.K j.K.R))
  counter : ScratchCT (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (Joint.top j)))])
  prepG : JointPrepGChecks j (c.sl U)
  prepQ : JointPrepQChecks j (c.sl V)

theorem jointPoints_relCT {c : Cfg} {j : Joint.Cfg} {d : CombData} {double : Prog isa}
    (hc : BaseCfgOk c) (hC : Law c.C) (hd : JDblOk c.C j.dbl) {J : Nat} (hG : JointGTable c j d J)
    (hK : j.K=c.winCfg PX PY BP) (hnp : c.C.n≤c.C.p)
    (hL : JointAddLayout j size) (hInit : JointInitLayout j size)
    (hPrep : JointPrepLayout j size (c.sl U) (c.sl V)) (hD : JointDoubler j c.C size double)
    (checks : JointMulChecks c j) (hZ : j.coZ=true → PrimeOrder c.C ∧ 17≤c.C.n ∧ AM3 c.C)
    {s₀ t₀ : State} (ps : VPre c s₀) (pt : VPre c t₀) (pub : JointPublic c d s₀ t₀) :
    RelCT isa (fun s t => (∃ g,Mid c s₀ (s₀.gpr .rcx) g s) ∧ (∃ h,Mid c t₀ (t₀.gpr .rcx) h t))
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointPoints c j double).inline
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
  have genS := jointMid_generator hc hC hG hK ps hs
  have hjn : j.K.M.n=c.n := by rw [hK]; rfl
  have genT : JointGenerator j c.C (s₀.gpr .rcx) (s₀.syms d.tsym) size
      (jointCombRow hc hC hG) t := by
    rw [base,pub.sym]
    exact jointMid_generator hc hC hG hK pt ht
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
  have sv4 (a : State) (i : Nat) :
      wordsVal a.mem (s₀.gpr .rcx) (c.sl i) j.K.M.n=sv c (s₀.gpr .rcx) a i := by
    unfold sv
    rw [hjn]
  have u : sv c (s₀.gpr .rcx) t U=sv c (s₀.gpr .rcx) s U :=
    (mid_publicU ht').trans (pub.u.symm.trans (mid_publicU hs).symm)
  have v : sv c (s₀.gpr .rcx) t V=sv c (s₀.gpr .rcx) s V :=
    (mid_publicV ht').trans (pub.v.symm.trans (mid_publicV hs).symm)
  have ct := jointMul_relCT (base:=s₀.gpr .rcx) (T:=s₀.syms d.tsym)
    (row:=jointCombRow hc hC hG) hL hInit hPrep hm hC hd hD hone honeval hc.onG hQ
    point (jointMid_affine hc hK hs) zero hZ (Nat.lt_trans hs.u_lt nlt) (Nat.lt_trans hs.v_lt nlt)
    checks.cached checks.fixed checks.table checks.cache checks.seed checks.counter
    checks.prepG checks.prepQ
  obtain ⟨trace,post⟩ := ct _ _ _ _ _ _
    ⟨fields,genS,genT,sv4 s U,sv4 s V,(sv4 t U).trans u,(sv4 t V).trans v⟩ es et
  obtain ⟨E,pair⟩ := post.1
  exact ⟨trace,fieldPair_public pair⟩

end VG.Proof.Ecdsa.Verify.X86_64

end

end

/-! Split the public joint verifier at the scalar and point-operation boundaries. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Weierstrass.X86_64

def jointPrefix (c : Cfg) : Prog isa :=
  .seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.args c)) <|
  .seq (Impl.Ecdh.X86_64.Cfg.prefix' c (some D)) <|
  .seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.loadS c)) <|
  .seq (.block (Impl.Ecdh.X86_64.Cfg.peer c)) <|
  .seq (Impl.Ecdh.X86_64.Cfg.check c).inline <|
  .seq (Impl.Ecdsa.Verify.X86_64.Cfg.scalars c).inline <| .seq c.nPow.inline <|
  .seq (Impl.Ecdsa.Verify.X86_64.Cfg.uv c).inline (.block [])

theorem jointPrefix_ok {c : Cfg} (hc : BaseCfgOk c) {s₀ : State} (hp : VPre c s₀) :
    WP isa (jointPrefix c) s₀ fun s => ∃ g,Mid c s₀ (s₀.gpr .rcx) g s := by
  refine front_ok hc hp fun g _ _ hF => mid_ok hc hF fun _ hM => WP.block_nil ⟨g,hM⟩

theorem jointVerify_cut {c : Cfg} {pts : Prog isa} {s s' : State} {t : List Leak}
    (he : Exec isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerifyWith c pts).inline s t s') :
    ∃ a b tp tc ts, Exec isa (jointPrefix c) s tp a ∧
      Exec isa pts.inline a tc b ∧
      Exec isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail c).inline b ts s' ∧ t=tp++tc++ts := by
  rw [jointVerifyWith_inline] at he
  cases he with
  | seq e0 h => cases h with
    | seq e1 h => cases h with
      | seq e2 h => cases h with
        | seq e3 h => cases h with
          | seq e4 h => cases h with
            | seq e5 h => cases h with
              | seq e6 h => cases h with
                | seq e7 h => cases h with
                  | seq ec es =>
                    have nil : ∀ a : State,Exec isa (.block []) a [] a := fun _ => .block rfl
                    have ep := Exec.seq e0 (.seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5
                      (.seq e6 (.seq e7 (nil _))))))))
                    exact ⟨_,_,_,_,_,ep,ec,es,by simp only [List.append_nil,List.append_assoc]⟩

/-- The joint verifier is constant time if its points' code `pts` is, between runs from public inputs. -/
theorem jointVerifyWith_ct_of_points {c : Cfg} {pts : Prog isa} {d : CombData}
    (hc : BaseCfgOk c)
    (before : ConstantTime isa (fun _ => True)
      (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix c))
    (points : ∀ {s₀ t₀ : State},VPre c s₀ → VPre c t₀ → JointPublic c d s₀ t₀ →
      RelCT isa (fun s t => (∃ g,Mid c s₀ (s₀.gpr .rcx) g s) ∧ (∃ h,Mid c t₀ (t₀.gpr .rcx) h t))
        pts.inline (fun s t => X86_64.Taint.Agree (Taint.ofRegs [.rdi]) s t))
    (after : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail c).inline) :
    ConstantTime isa (VPre c) (JointPublic c d) (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerifyWith c pts).inline := by
  intro s₀ t₀ ls lt s' t' ps pt pub es et
  obtain ⟨a,b,lp,lc,lf,ep,ec,ef,he⟩ := jointVerify_cut es
  obtain ⟨a',b',lp',lc',lf',ep',ec',ef',he'⟩ := jointVerify_cut et
  have hp := before _ _ _ _ _ _ trivial trivial pub.regs ep ep'
  obtain ⟨_,_,wp,pm⟩ := jointPrefix_ok hc ps
  obtain ⟨_,_,wp',pm'⟩ := jointPrefix_ok hc pt
  obtain ⟨_,rfl⟩ := Exec.det ep wp
  obtain ⟨_,rfl⟩ := Exec.det ep' wp'
  obtain ⟨hct,hpub⟩ := points ps pt pub _ _ _ _ _ _ ⟨pm,pm'⟩ ec ec'
  have hf := after _ _ _ _ _ _ trivial trivial hpub ef ef'
  rw [he,he',hp,hct,hf]

theorem jointVerify_ct_of_points {c : Cfg} {j : Joint.Cfg} {double : Prog isa} {d : CombData}
    (hc : BaseCfgOk c)
    (before : ConstantTime isa (fun _ => True)
      (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix c))
    (points : ∀ {s₀ t₀ : State},VPre c s₀ → VPre c t₀ → JointPublic c d s₀ t₀ →
      RelCT isa (fun s t => (∃ g,Mid c s₀ (s₀.gpr .rcx) g s) ∧ (∃ h,Mid c t₀ (t₀.gpr .rcx) h t))
        (Impl.Ecdsa.Verify.X86_64.Cfg.jointPoints c j double).inline
        (fun s t => X86_64.Taint.Agree (Taint.ofRegs [.rdi]) s t))
    (after : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail c).inline) :
    ConstantTime isa (VPre c) (JointPublic c d) (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify c j double).inline :=
  jointVerifyWith_ct_of_points hc before points after

end VG.Proof.Ecdsa.Verify.X86_64
