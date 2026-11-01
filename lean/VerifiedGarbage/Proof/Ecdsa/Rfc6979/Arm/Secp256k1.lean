module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
public import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP

/-!
# Deterministic ECDSA on 32-bit ARM: secp256k1

secp256k1 as the proof's curve (`secp256k1`): scalars of 4 64-bit words, the order
`n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_secp256k1_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at secp256k1's sizes, which is `Proof.Ecdsa.Arm.Secp256k1.signArm`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

theorem secp256k1_nBits : Spec.Ecdsa.nBits Spec.Secp256k1.curve = 256 := by
  show Spec.Secp256k1.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.Secp256k1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Secp256k1.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- secp256k1, with the group law `hL`. -/
def secp256k1 (hL : Weierstrass.Law Spec.Secp256k1.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.secp256k1
  inst := Spec.Ecdsa.Secp256k1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, secp256k1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.Secp256k1.curve = 0; rw [secp256k1_nBits]
  coreN := "vg_ecdsa_secp256k1_sign"
  coreC := Impl.Ecdsa.Arm.signSecp256k1
  coreConsts := []
  coreX := by
    intro s hs
    have pre : Proof.Ecdsa.Arm.Secp256k1.signArm.pre s := by
      simpa only [coreK,TablesOk,Impl.Ecdsa.Arm.secp256k1,Impl.Ecdsa.Arm.secp256k1With,Spec.Secp256k1.curve,Nat.reduceMul,List.not_mem_nil,forall_const,
        false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,Proof.Ecdsa.Arm.Secp256k1.signArm] using hs
    obtain ⟨tr,t,exec,abi,post⟩ := Proof.Ecdsa.Arm.Secp256k1.sign_arm hL s pre
    refine ⟨tr,t,exec,abi,?_⟩
    change Proof.Ecdsa.Arm.Secp256k1.signArm.post s t
    exact post
  coreCT := by
    simpa only [coreK,coreSigOf,Spec.Secp256k1.curve,Nat.reduceMul,Impl.Ecdsa.Arm.secp256k1,Impl.Ecdsa.Arm.secp256k1With,Proof.Ecdsa.Arm.Secp256k1.sig,TablesOk,List.not_mem_nil,forall_const,false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,
      Proof.Ecdsa.Arm.Secp256k1.signArm] using Proof.Ecdsa.Arm.Secp256k1.sign_ct
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)

end VG.Proof.Ecdsa.Rfc6979.Arm
