module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public import VerifiedGarbage.Proof.Ecdh.AArch64.Validate
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-! Native validation invokes the existing checked peer-point implementation. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)
open VG.Impl.Weierstrass.AArch64.P521Native (config outerBlock003 outerBlock004 callCheckPoint sequence)

theorem prepare_peer_source : outerBlock003=VG.Impl.Ecdh.AArch64.Cfg.peer config++
    [.vop (.ins .d2 .v28 0 .x30)] := by lit_decide

theorem prepare_check_curve : VG.Impl.Ecdh.AArch64.Cfg.checkCurve config=
    some VG.Impl.Weierstrass.CheckPoint.p521 := by
  unfold VG.Impl.Ecdh.AArch64.Cfg.checkCurve
  have pred : (fun C : VG.Impl.Weierstrass.CheckPoint.Curve => C.W.p==config.C.p && C.k==config.n)=
      (fun C => C.k==config.n && C.W.p==config.C.p) := by
    funext C
    exact Bool.and_comm _ _
  rw [pred]
  have nEq : config.n=9 := rfl
  have pEq : config.C.p=VG.Spec.P521.p := by
    simp only [config,VG.Impl.Ecdsa.AArch64.p521,VG.Spec.P521.curve]
  rw [nEq,pEq]
  simp only [VG.Impl.Weierstrass.CheckPoint.curves,List.find?_cons,
    VG.Impl.Weierstrass.CheckPoint.p192,VG.Impl.Weierstrass.CheckPoint.p224,
    VG.Impl.Weierstrass.CheckPoint.p256,VG.Impl.Weierstrass.CheckPoint.secp256k1,
    VG.Impl.Weierstrass.CheckPoint.p384,VG.Impl.Weierstrass.CheckPoint.p521,
    show (4==9)=false from rfl,show (6==9)=false from rfl,show (9==9)=true from rfl,
    Bool.false_and,Bool.true_and,VG.Spec.P521.curve,beq_self_eq_true]

theorem prepare_validate_source : VG.Impl.Ecdh.AArch64.Cfg.validate config=
    .seq (.block [.vop (.ins .d2 .v28 0 .x30)]) (.seq callCheckPoint (.block outerBlock004)) := by
  rw [VG.Impl.Ecdh.AArch64.Cfg.validate,prepare_check_curve]
  rfl

def prepareCheck : Prog isa := sequence [.block (outerBlock003.drop 137),callCheckPoint,.block outerBlock004]

theorem prepare_check_wp {s : State} {Q : State → Prop}
    (h : WP isa (VG.Impl.Ecdh.AArch64.Cfg.validate config) s Q) : WP isa prepareCheck s Q := by
  have hd : outerBlock003.drop 137=[.vop (.ins .d2 .v28 0 .x30)] := by decide
  rw [prepare_validate_source,VG.WP.seq_iff] at h
  simp only [prepareCheck,sequence,List.foldr_cons,List.foldr_nil,hd]
  rw [VG.WP.seq_iff]
  refine VG.WP.mono h fun u hu => ?_
  rw [VG.WP.seq_iff] at hu ⊢
  refine VG.WP.mono hu fun v hv => ?_
  rw [VG.WP.seq_iff]
  exact VG.WP.mono hv fun _ post => VG.WP.block_nil post

/-- Canonical selected peer coordinates and the validity mask, with the actual
memory/register frame of the pre-existing checked point function. -/
theorem prepare_validate_ok (hc : BaseCfgOk config) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (fixed : Fixed config base g s.mem)
    (hr2 : sv config base s R2P=config.R*config.R%config.C.p)
    (hbp : sv config base s BP=config.mont config.C.b) {P₀ : Prop} [Decidable P₀]
    (flag : word s.mem base (config.sl FLAG)=mask P₀) :
    WP isa prepareCheck s fun t =>
      Scr t base size ∧ (∀r,r∉clob config.n → t.gpr r=s.gpr r) ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      Unch base (slW config [QXM,QYM,TMP,W0,W1,W2,W3,PY]++[(config.sl FLAG,8)]) s.mem t.mem ∧
      word t.mem base (config.sl FLAG)=mask (VG.Proof.Ecdh.AArch64.PeerOk config base s
        ((P₀ ∧ sv config base s E<config.C.p) ∧ sv config base s QY<config.C.p)) ∧
      sv config base t PX<config.C.p ∧ sv config base t PY<config.C.p ∧
      toM config.C.p (2^(64*config.n)) (sv config base t PX)=
        (if VG.Proof.Ecdh.AArch64.PeerOk config base s ((P₀ ∧ sv config base s E<config.C.p) ∧ sv config base s QY<config.C.p)
          then Fin.ofNat config.C.p (sv config base s E) else Fin.ofNat config.C.p config.C.gx) ∧
      toM config.C.p (2^(64*config.n)) (sv config base t PY)=
        (if VG.Proof.Ecdh.AArch64.PeerOk config base s ((P₀ ∧ sv config base s E<config.C.p) ∧ sv config base s QY<config.C.p)
          then Fin.ofNat config.C.p (sv config base s QY) else Fin.ofNat config.C.p config.C.gy) := by
  exact prepare_check_wp (VG.Proof.Ecdh.AArch64.validate_ok hc hs fixed hr2 hbp flag)

end VG.Proof.Weierstrass.AArch64.P521Native
