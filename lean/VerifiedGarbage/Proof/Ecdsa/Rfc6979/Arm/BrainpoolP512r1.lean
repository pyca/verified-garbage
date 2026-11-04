module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP

/-!
# Deterministic ECDSA on 32-bit ARM: brainpoolP512r1

brainpoolP512r1 as the proof's curve (`brainpoolp512r1`): scalars of 8 64-bit words, the order
`n` of exactly 512 bits with `2^512 < 2 n`, `h` kept at the frame's top (`hHigh`), and `vg_ecdsa_brainpoolp512r1_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at brainpoolP512r1's sizes, which is `Proof.Ecdsa.Arm.BrainpoolP512r1.signArm`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

theorem brainpoolp512r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP512r1.curve = 512 := by
  show Spec.BrainpoolP512r1.curve.n.log2 + 1 = 512
  have h₁ : 511 ≤ Spec.BrainpoolP512r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP512r1.curve.n.log2 < 512 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-! ## The blocks for each hash function's sizes -/

theorem brainpoolp512r1_blk₀ : RfcT (cfgS Impl.Ecdsa.Arm.brainpoolp512r1 true 0 16 64) := by rfcT_decide
theorem brainpoolp512r1_blk₁ : RfcT (cfgS Impl.Ecdsa.Arm.brainpoolp512r1 true 0 20 64) := by rfcT_decide
theorem brainpoolp512r1_blk₂ : RfcT (cfgS Impl.Ecdsa.Arm.brainpoolp512r1 true 0 28 64) := by rfcT_decide
theorem brainpoolp512r1_blk₃ : RfcT (cfgS Impl.Ecdsa.Arm.brainpoolp512r1 true 0 32 64) := by rfcT_decide
theorem brainpoolp512r1_blk₄ : RfcT (cfgS Impl.Ecdsa.Arm.brainpoolp512r1 true 0 48 128) := by rfcT_decide
theorem brainpoolp512r1_blk₅ : RfcT (cfgS Impl.Ecdsa.Arm.brainpoolp512r1 true 0 64 128) := by rfcT_decide
theorem brainpoolp512r1_blk₆ : RfcT (cfgS Impl.Ecdsa.Arm.brainpoolp512r1 true 0 28 128) := by rfcT_decide
theorem brainpoolp512r1_blk₇ : RfcT (cfgS Impl.Ecdsa.Arm.brainpoolp512r1 true 0 32 128) := by rfcT_decide

/-- brainpoolP512r1, with the group law `hL`. -/
def brainpoolp512r1 (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.brainpoolp512r1
  inst := Spec.Ecdsa.BrainpoolP512r1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inr (.inr rfl)), .inl rfl, brainpoolp512r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  hHigh := true
  sh := 0
  sh_eq := Proof.Ecdsa.Arm.BrainpoolP512r1.brainpoolp512r1_sh
  coreN := "vg_ecdsa_brainpoolp512r1_sign_k"
  coreC := Impl.Ecdsa.Arm.signBrainpoolP512r1
  coreConsts := []
  coreX := by
    intro s hs
    have pre : Proof.Ecdsa.Arm.BrainpoolP512r1.signArm.pre s := by
      simpa only [coreK,TablesOk,Impl.Ecdsa.Arm.brainpoolp512r1,Impl.Ecdsa.Arm.brainpoolp512r1With,Spec.BrainpoolP512r1.curve,Nat.reduceMul,List.not_mem_nil,forall_const,
        false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,Proof.Ecdsa.Arm.BrainpoolP512r1.signArm] using hs
    obtain ⟨tr,t,exec,abi,post⟩ := Proof.Ecdsa.Arm.BrainpoolP512r1.sign_arm hL false s pre
    refine ⟨tr,t,exec,abi,?_⟩
    change Proof.Ecdsa.Arm.BrainpoolP512r1.signArm.post s t
    exact post
  coreCT := by
    simpa only [coreK,coreSigOf,Spec.BrainpoolP512r1.curve,Nat.reduceMul,Impl.Ecdsa.Arm.brainpoolp512r1,Impl.Ecdsa.Arm.brainpoolp512r1With,Proof.Ecdsa.Arm.BrainpoolP512r1.sig,TablesOk,List.not_mem_nil,forall_const,false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,
      Proof.Ecdsa.Arm.BrainpoolP512r1.signArm] using Proof.Ecdsa.Arm.BrainpoolP512r1.sign_ct
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  blkT := blkT_of brainpoolp512r1_blk₀ brainpoolp512r1_blk₁ brainpoolp512r1_blk₂ brainpoolp512r1_blk₃ brainpoolp512r1_blk₄ brainpoolp512r1_blk₅ brainpoolp512r1_blk₆ brainpoolp512r1_blk₇

/-- `brainpoolp512r1`, calling `vg_ecdsa_brainpoolp512r1_sign_umaal`. -/
def brainpoolp512r1U (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.brainpoolp512r1
  inst := Spec.Ecdsa.BrainpoolP512r1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inr (.inr rfl)), .inl rfl, brainpoolp512r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  hHigh := true
  sh := 0
  sh_eq := Proof.Ecdsa.Arm.BrainpoolP512r1.brainpoolp512r1_sh
  coreN := "vg_ecdsa_brainpoolp512r1_sign_k" ++ "_umaal"
  coreC := Impl.Ecdsa.Arm.signBrainpoolP512r1U
  coreConsts := []
  coreX := by
    intro s hs
    have pre : Proof.Ecdsa.Arm.BrainpoolP512r1.signArm.pre s := by
      simpa only [coreK,TablesOk,Impl.Ecdsa.Arm.brainpoolp512r1,Impl.Ecdsa.Arm.brainpoolp512r1With,Spec.BrainpoolP512r1.curve,Nat.reduceMul,List.not_mem_nil,forall_const,
        false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,Proof.Ecdsa.Arm.BrainpoolP512r1.signArm] using hs
    obtain ⟨tr,t,exec,abi,post⟩ := Proof.Ecdsa.Arm.BrainpoolP512r1.sign_arm hL true s pre
    refine ⟨tr,t,exec,abi,?_⟩
    change Proof.Ecdsa.Arm.BrainpoolP512r1.signArm.post s t
    exact post
  coreCT := by
    simpa only [coreK,coreSigOf,Spec.BrainpoolP512r1.curve,Nat.reduceMul,Impl.Ecdsa.Arm.brainpoolp512r1,Impl.Ecdsa.Arm.brainpoolp512r1With,Proof.Ecdsa.Arm.BrainpoolP512r1.sig,TablesOk,List.not_mem_nil,forall_const,false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,
      Proof.Ecdsa.Arm.BrainpoolP512r1.signArm] using Proof.Ecdsa.Arm.BrainpoolP512r1.signU_ct
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  blkT := blkT_of brainpoolp512r1_blk₀ brainpoolp512r1_blk₁ brainpoolp512r1_blk₂ brainpoolp512r1_blk₃ brainpoolp512r1_blk₄ brainpoolp512r1_blk₅ brainpoolp512r1_blk₆ brainpoolp512r1_blk₇

/-- brainpoolP512r1, multiplying with UMAAL (`u`) or not. -/
def brainpoolp512r1Of (u : Bool) (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : RfcCurve :=
  bif u then brainpoolp512r1U hL else brainpoolp512r1 hL

/-- `vg_ecdsa_brainpoolp512r1_sign` (`_umaal`, multiplying with UMAAL), with the tables of `vs`. -/
theorem brainpoolp512r1T_verified (u : Bool) (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (vs : List Proof.HashTable.Arm.TVar)
    (h : OK vs) :
    Verified Arm.target (signCode (brainpoolp512r1Of u hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 [] vs) := by
  have hsat := sat_nil (T := Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1) h (by decide) rfl
  cases u
  · exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h hsat
  · exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h hsat

end VG.Proof.Ecdsa.Rfc6979.Arm
