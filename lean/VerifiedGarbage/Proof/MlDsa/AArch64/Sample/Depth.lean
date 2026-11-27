module

public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sample

variable (v : Proof.Sha3.AArch64.Permutation)

theorem sponge_depth (rate len : Nat) : (spongeWith v.callee rate len).aarch64Depth = 1 := by
  simp only [spongeWith, Code.aarch64Depth, v.absorb_depth, v.pad_depth, v.squeeze_depth,
    Nat.max_self, Nat.zero_max]

theorem rejNTT_depth : (rejNTTWith v.callee).aarch64Depth = 1 := by
  simp only [rejNTTWith, zeroPoly, rnLoop, rnBody, Code.aarch64Depth, sponge_depth v,
    Nat.max_self, Nat.max_zero, Nat.zero_max]

theorem ball_depth : (sampleInBallWith v.callee).aarch64Depth = 1 := by
  simp only [sampleInBallWith, zeroPoly, bLoop, bBody, bTry, Code.aarch64Depth, sponge_depth v,
    Nat.max_self, Nat.max_zero, Nat.zero_max]

theorem expandMask_depth : (expandMaskWith v.callee).aarch64Depth = 1 := by
  simp only [expandMaskWith, expandMaskTailWith, emLoop, Code.aarch64Depth, sponge_depth v,
    Nat.max_self, Nat.max_zero, Nat.zero_max]

/-! ## No access to the mode -/

theorem sponge_noDit (rate len : Nat) : (spongeWith v.callee rate len).all (fun i => !i.touchesDit) = true := by
  simp only [spongeWith, Code.all, v.absorb_noDit, v.pad_noDit, v.squeeze_noDit, Bool.and_true, List.all_append]
  simp only [absArgs, padArgs, sqzArgs, List.all_cons, List.all_nil, Instr.touchesDit, Bool.not_false,
    Bool.and_true]
  decide

theorem rejNTT_noDit : (rejNTTWith v.callee).all (fun i => !i.touchesDit) = true := by
  simp only [rejNTTWith, zeroPoly, rnLoop, rnBody, Code.all, sponge_noDit v, Bool.true_and]
  decide

theorem ball_noDit : (sampleInBallWith v.callee).all (fun i => !i.touchesDit) = true := by
  simp only [sampleInBallWith, zeroPoly, bLoop, bBody, bTry, Code.all, sponge_noDit v, Bool.true_and]
  decide

theorem expandMask_noDit : (expandMaskWith v.callee).all (fun i => !i.touchesDit) = true := by
  simp only [expandMaskWith, expandMaskTailWith, emLoop, Code.all, sponge_noDit v, Bool.true_and]
  decide

end VG.Proof.MlDsa.AArch64.Sample
