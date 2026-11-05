module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.X25519.Field
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Main
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rc2.Memory32
meta import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Impl.Ecdsa.P521.Arm
meta import VerifiedGarbage.Impl.Ecdsa.P521.Arm

/-!
# Deterministic ECDSA on 32-bit ARM: P-521

P-521 as the proof's curve (`p521`): scalars of 9 64-bit words and 66
bytes, longer than any hash function's output (`wide`), the order `n` of
521 bits, so that the signature drops 7 bits of a 66-byte digest, and
`vg_ecdsa_p521_sign_k`, proven correct (given the group law) and constant time
against its contract (`coreK` at P-521's sizes, which is
`Proof.Ecdsa.Arm.P521.signArm`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

/-- P-521, with the group law `hL`. -/
def p521 (hL : Weierstrass.Law Spec.P521.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.p521
  inst := Spec.Ecdsa.P521.inst
  curve := rfl
  big := true
  sizes := ⟨rfl, rfl, Proof.Ecdsa.Arm.P521.p521_nBits⟩
  n_lt := by decide +kernel
  sh := 7
  sh_eq := Proof.Ecdsa.Arm.P521.p521_sh
  coreN := "vg_ecdsa_p521_sign_k"
  coreC := Impl.Ecdsa.Arm.signP521
  coreConsts := []
  coreX := by
    intro s hs
    have pre : Proof.Ecdsa.Arm.P521.signArm.pre s := by
      simpa only [coreK,TablesOk,Impl.Ecdsa.Arm.p521,Spec.P521.curve,Nat.reduceMul,List.not_mem_nil,forall_const,
        false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,Proof.Ecdsa.Arm.P521.signArm] using hs
    obtain ⟨tr,t,exec,abi,post⟩ := Proof.Ecdsa.Arm.P521.sign_arm hL s pre
    refine ⟨tr,t,exec,abi,?_⟩
    change Proof.Ecdsa.Arm.P521.signArm.post s t
    exact post
  coreCT := by
    simpa only [coreK,coreSigOf,Spec.P521.curve,Nat.reduceMul,Impl.Ecdsa.Arm.p521,Proof.Ecdsa.Arm.P521.sig,TablesOk,List.not_mem_nil,forall_const,false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,
      Proof.Ecdsa.Arm.P521.signArm] using Proof.Ecdsa.Arm.P521.sign_ct
  coreStack := by lit_decide
  blk := by rfcT_decide

/-! ## With the tables of every hash function with HMAC -/

theorem p521T_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified Arm.target (signCodeT (p521 hL) Spec.Ecdsa.Rfc6979.Curves.p521.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p521 (p521 hL).coreConsts HmacTable.Arm.vars) :=
  nilT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl

end VG.Proof.Ecdsa.Rfc6979.Arm
