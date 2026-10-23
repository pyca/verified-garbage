module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
meta import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.AArch64.Joint
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.AArch64.Joint
public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.State
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Scalars
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-! Fixed-address initialization up to the joint public multiplication. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

def beforeCode : Prog isa :=
  .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.args cfg)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.prefixWith cfg (some D)) <|
  .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.loadS cfg)) <|
  .seq (.block (Impl.Ecdh.AArch64.Cfg.peer cfg)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.validate cfg) <|
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.scalars cfg) <| .seq cfg.nPow <|
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.uv cfg) (.block [])

def afterCode : Prog isa := Impl.Ecdsa.Verify.AArch64.Cfg.tail cfg

materialize_code beforeCode
materialize_code afterCode

theorem prefix_ok (hc : BaseCfgOk cfg) {s : State} (hp : FrontPre cfg s) :
    WP isa beforeCode s fun t => ∃ g,Mid cfg s (s.gpr .x3) g t :=
  front_ok hc hp fun g _ _ hF => mid_ok hc hF fun _ hM => WP.block_nil ⟨g,hM⟩

theorem prefix_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3])) beforeCode :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem suffix_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) afterCode :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem verify_cut {s s' : State} {t : List Leak} (he : Exec isa verify s t s') :
    ∃ a b tp tc ts, Exec isa beforeCode s tp a ∧ Exec isa points a tc b ∧
      Exec isa afterCode b ts s' ∧ t=tp++tc++ts := by
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
                    have nil : ∀ a : State, Exec isa (.block []) a [] a := fun _ => .block rfl
                    have ep := Exec.seq e0 (.seq e1 (.seq e2 (.seq e3 (.seq e4
                      (.seq e5 (.seq e6 (.seq e7 (nil _))))))))
                    exact ⟨_,_,_,_,_,ep,ec,es,by simp only [List.append_nil,List.append_assoc]⟩
end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
