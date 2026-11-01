module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP

/-!
# Deterministic ECDSA on 32-bit ARM: brainpoolP384r1

brainpoolP384r1 as the proof's curve (`brainpoolp384r1`): scalars of 6 64-bit words, the order
`n` of exactly 384 bits with `2^384 < 2 n`, and `vg_ecdsa_brainpoolp384r1_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at brainpoolP384r1's sizes, which is `Proof.Ecdsa.Arm.BrainpoolP384r1.signArm`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

theorem brainpoolp384r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP384r1.curve = 384 := by
  show Spec.BrainpoolP384r1.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.BrainpoolP384r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP384r1.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- brainpoolP384r1, with the group law `hL`. -/
def brainpoolp384r1 (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.brainpoolp384r1
  inst := Spec.Ecdsa.BrainpoolP384r1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inr (.inl rfl)), .inl rfl, brainpoolp384r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 48 - Spec.Ecdsa.nBits Spec.BrainpoolP384r1.curve = 0; rw [brainpoolp384r1_nBits]
  coreN := "vg_ecdsa_brainpoolp384r1_sign"
  coreC := Impl.Ecdsa.Arm.signBrainpoolP384r1
  coreConsts := []
  coreX := by
    intro s hs
    have pre : Proof.Ecdsa.Arm.BrainpoolP384r1.signArm.pre s := by
      simpa only [coreK,TablesOk,Impl.Ecdsa.Arm.brainpoolp384r1,Impl.Ecdsa.Arm.brainpoolp384r1With,Spec.BrainpoolP384r1.curve,Nat.reduceMul,List.not_mem_nil,forall_const,
        false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,Proof.Ecdsa.Arm.BrainpoolP384r1.signArm] using hs
    obtain ⟨tr,t,exec,abi,post⟩ := Proof.Ecdsa.Arm.BrainpoolP384r1.sign_arm hL false s pre
    refine ⟨tr,t,exec,abi,?_⟩
    change Proof.Ecdsa.Arm.BrainpoolP384r1.signArm.post s t
    exact post
  coreCT := by
    simpa only [coreK,coreSigOf,Spec.BrainpoolP384r1.curve,Nat.reduceMul,Impl.Ecdsa.Arm.brainpoolp384r1,Impl.Ecdsa.Arm.brainpoolp384r1With,Proof.Ecdsa.Arm.BrainpoolP384r1.sig,TablesOk,List.not_mem_nil,forall_const,false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,
      Proof.Ecdsa.Arm.BrainpoolP384r1.signArm] using Proof.Ecdsa.Arm.BrainpoolP384r1.sign_ct
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)


/-- `brainpoolp384r1`, calling `vg_ecdsa_brainpoolp384r1_sign_umaal`. -/
def brainpoolp384r1U (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.brainpoolp384r1
  inst := Spec.Ecdsa.BrainpoolP384r1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inr (.inl rfl)), .inl rfl, brainpoolp384r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 48 - Spec.Ecdsa.nBits Spec.BrainpoolP384r1.curve = 0; rw [brainpoolp384r1_nBits]
  coreN := "vg_ecdsa_brainpoolp384r1_sign" ++ "_umaal"
  coreC := Impl.Ecdsa.Arm.signBrainpoolP384r1U
  coreConsts := []
  coreX := by
    intro s hs
    have pre : Proof.Ecdsa.Arm.BrainpoolP384r1.signArm.pre s := by
      simpa only [coreK,TablesOk,Impl.Ecdsa.Arm.brainpoolp384r1,Impl.Ecdsa.Arm.brainpoolp384r1With,Spec.BrainpoolP384r1.curve,Nat.reduceMul,List.not_mem_nil,forall_const,
        false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,Proof.Ecdsa.Arm.BrainpoolP384r1.signArm] using hs
    obtain ⟨tr,t,exec,abi,post⟩ := Proof.Ecdsa.Arm.BrainpoolP384r1.sign_arm hL true s pre
    refine ⟨tr,t,exec,abi,?_⟩
    change Proof.Ecdsa.Arm.BrainpoolP384r1.signArm.post s t
    exact post
  coreCT := by
    simpa only [coreK,coreSigOf,Spec.BrainpoolP384r1.curve,Nat.reduceMul,Impl.Ecdsa.Arm.brainpoolp384r1,Impl.Ecdsa.Arm.brainpoolp384r1With,Proof.Ecdsa.Arm.BrainpoolP384r1.sig,TablesOk,List.not_mem_nil,forall_const,false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,
      Proof.Ecdsa.Arm.BrainpoolP384r1.signArm] using Proof.Ecdsa.Arm.BrainpoolP384r1.signU_ct
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)


end VG.Proof.Ecdsa.Rfc6979.Arm
