module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP512r1.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP512r1.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Main
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP512r1.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
meta import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# ECDSA verification over brainpoolP512r1 on 32-bit ARM: `Verified`

`verify_ok` for brainpoolP512r1 (`brainpoolp512r1_ok`, and `Law` for its group law, which the
registration file supplies: `Proof.BrainpoolP512r1.law`) gives the contract's
postcondition; `r4`–`r11` and `lr` are restored and `sp` kept. Constant time
by taint tracking from the arguments' registers, as for ECDH
(`Proof/Ecdh/Arm/Verified.lean`): the only branches are on loop counters,
and every address is `r12` (`scratch`) or a pointer argument plus a
constant or a counter.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.Arm.BrainpoolP512r1

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Ecdsa.Verify.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.BrainpoolP512r1 Spec.Weierstrass

theorem pre_of {u : Bool} {s : State} (h : verifyArm.pre s) : VPre (brainpoolp512r1With u) s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem post_of {u : Bool} {s s' : State} (h : VPost (brainpoolp512r1With u) s s') : verifyArm.post s s' := by
  show BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = _
  rw [BitVec.setWidth_append_eq_right]
  exact h

theorem verify_arm (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (u : Bool) (s : State) (hs : verifyArm.pre s) :
    ∃ t s', Exec isa (verifyBrainpoolP512r1With u) s t s' ∧ abiPreserved s s' ∧ verifyArm.post s s' := by
  have hp := pre_of (u := u) hs
  obtain ⟨t, s', he, K, hpost⟩ := verify_ok (brainpoolp512r1With_ok u) hL hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, K.sp⟩, post_of hpost⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact K.saved (.r4, 0) (by decide)
  · exact K.saved (.r5, 4) (by decide)
  · exact K.saved (.r6, 8) (by decide)
  · exact K.saved (.r7, 12) (by decide)
  · exact K.saved (.r8, 16) (by decide)
  · exact K.saved (.r9, 20) (by decide)
  · exact K.saved (.r10, 24) (by decide)
  · exact K.saved (.r11, 28) (by decide)
  · exact K.saved (.lr, 32) (by decide)

/-- The taint analysis starts with the arguments' registers public. -/
def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2, .r3], flags := false }

/-- The taint analysis's start agrees in the two states. -/
theorem agree_τ₀ {s t : State} (_hs : verifyArm.pre s) (_ht : verifyArm.pre t) (h : verifyArm.pub s t) :
    VG.Arm.Taint.Agree τ₀ s t := by
  obtain ⟨_, h0, h1, h2, h3⟩ := h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
      fun _ h => (List.not_mem_nil h).elim⟩,
    ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
      fun _ h => (List.not_mem_nil h).elim⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem verify_ct : ConstantTime isa verifyArm.pre verifyArm.pub verifyBrainpoolP512r1 :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ hs ht h => agree_τ₀ hs ht h) (by native_taint_decide)

theorem verifyU_ct : ConstantTime isa verifyArm.pre verifyArm.pub verifyBrainpoolP512r1U :=
  VG.Taint.constantTime (A := taintU) τ₀ (fun _ _ hs ht h => agree_τ₀ hs ht h) (by taint_decide)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x8000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 129⟩, ⟨0x2000, 64⟩, ⟨0x3000, 128⟩]
  wr := [⟨0x8000, 8192⟩]

theorem verifyWith_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (u : Bool)
    (hct : ConstantTime isa verifyArm.pre verifyArm.pub (verifyBrainpoolP512r1With u)) :
    Verified Arm.target (verifyBrainpoolP512r1With u) (Spec.Ecdsa.BrainpoolP512r1.inst.verifyContract Arm.abi) :=
  Verified.of_correct (verify_arm hL u) hct
    { pre := by
        sig_implies_pre [Spec.Ecdsa.BrainpoolP512r1.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, verifyArm, vf, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.BrainpoolP512r1.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, verifyArm, vf, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        exact h
      pub := by
        sig_implies_pub [Spec.Ecdsa.BrainpoolP512r1.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, verifyArm, vf, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Spec.Ecdsa.BrainpoolP512r1.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, verifyArm, vf, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using satState }

theorem verify_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target verifyBrainpoolP512r1 (Spec.Ecdsa.BrainpoolP512r1.inst.verifyContract Arm.abi) :=
  verifyWith_verified hL false verify_ct

theorem verifyU_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target verifyBrainpoolP512r1U (Spec.Ecdsa.BrainpoolP512r1.inst.verifyContract Arm.abi) :=
  verifyWith_verified hL true verifyU_ct

end VG.Proof.Ecdsa.Verify.Arm.BrainpoolP512r1
