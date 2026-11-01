module

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

/-!
# Deterministic ECDSA on 32-bit ARM: P-521

P-521 as the proof's curve (`p521`): scalars of 9 64-bit words and 66
bytes, longer than any hash function's output (`wide`), the order `n` of
521 bits, so that the signature drops 7 bits of a 66-byte digest, and
`vg_ecdsa_p521_sign`, proven correct (given the group law) and constant time
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
  wide := true
  sizes := ⟨rfl, rfl, Proof.Ecdsa.Arm.P521.p521_nBits⟩
  n_lt := by decide +kernel
  sh := 7
  sh_eq := Proof.Ecdsa.Arm.P521.p521_sh
  coreN := "vg_ecdsa_p521_sign"
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
  reduceT := nofun

end VG.Proof.Ecdsa.Rfc6979.Arm
