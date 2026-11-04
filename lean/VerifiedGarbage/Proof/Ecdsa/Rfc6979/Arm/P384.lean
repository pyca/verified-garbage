module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP

/-!
# Deterministic ECDSA on 32-bit ARM: P-384

P-384 as the proof's curve (`p384`): scalars of 6 64-bit words, the order
`n` of exactly 384 bits with `2^384 < 2 n`, and `vg_ecdsa_p384_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-384's sizes, which is `Proof.Ecdsa.Arm.P384.signArm`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

theorem p384_nBits : Spec.Ecdsa.nBits Spec.P384.curve = 384 := by
  show Spec.P384.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.P384.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P384.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-! ## The blocks for each hash function's sizes -/

theorem p384_blk₀ : RfcT (cfgS Impl.Ecdsa.Arm.p384 false 0 16 64) := by rfcT_decide
theorem p384_blk₁ : RfcT (cfgS Impl.Ecdsa.Arm.p384 false 0 20 64) := by rfcT_decide
theorem p384_blk₂ : RfcT (cfgS Impl.Ecdsa.Arm.p384 false 0 28 64) := by rfcT_decide
theorem p384_blk₃ : RfcT (cfgS Impl.Ecdsa.Arm.p384 false 0 32 64) := by rfcT_decide
theorem p384_blk₄ : RfcT (cfgS Impl.Ecdsa.Arm.p384 false 0 48 128) := by rfcT_decide
theorem p384_blk₅ : RfcT (cfgS Impl.Ecdsa.Arm.p384 false 0 64 128) := by rfcT_decide
theorem p384_blk₆ : RfcT (cfgS Impl.Ecdsa.Arm.p384 false 0 28 128) := by rfcT_decide
theorem p384_blk₇ : RfcT (cfgS Impl.Ecdsa.Arm.p384 false 0 32 128) := by rfcT_decide

/-- P-384, with the group law `hL`. -/
def p384 (hL : Weierstrass.Law Spec.P384.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.p384
  inst := Spec.Ecdsa.P384.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inr (.inl rfl)), .inl rfl, p384_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 48 - Spec.Ecdsa.nBits Spec.P384.curve = 0; rw [p384_nBits]
  coreN := "vg_ecdsa_p384_sign_k"
  coreC := Impl.Ecdsa.Arm.signP384
  coreConsts := []
  coreX := by
    intro s hs
    have pre : Proof.Ecdsa.Arm.P384.signArm.pre s := by
      simpa only [coreK,TablesOk,Impl.Ecdsa.Arm.p384,Impl.Ecdsa.Arm.p384With,Spec.P384.curve,Nat.reduceMul,List.not_mem_nil,forall_const,
        false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,Proof.Ecdsa.Arm.P384.signArm] using hs
    obtain ⟨tr,t,exec,abi,post⟩ := Proof.Ecdsa.Arm.P384.sign_arm hL s pre
    refine ⟨tr,t,exec,abi,?_⟩
    change Proof.Ecdsa.Arm.P384.signArm.post s t
    exact post
  coreCT := by
    simpa only [coreK,coreSigOf,Spec.P384.curve,Nat.reduceMul,Impl.Ecdsa.Arm.p384,Impl.Ecdsa.Arm.p384With,Proof.Ecdsa.Arm.P384.sig,TablesOk,List.not_mem_nil,forall_const,false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,
      Proof.Ecdsa.Arm.P384.signArm] using Proof.Ecdsa.Arm.P384.sign_ct
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  blkT := blkT_of p384_blk₀ p384_blk₁ p384_blk₂ p384_blk₃ p384_blk₄ p384_blk₅ p384_blk₆ p384_blk₇

end VG.Proof.Ecdsa.Rfc6979.Arm
