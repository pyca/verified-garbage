module

import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Lit
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.Arm
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Main
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# ECDSA over brainpoolP512r1 on 32-bit ARM: `Verified`

brainpoolP512r1 is a curve the proof supports (`brainpoolp512r1_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.BrainpoolP512r1.law`), so `sign_ok` gives
the contract's postcondition; `r4`–`r11` and `lr` are restored and `sp`
kept. Constant time by taint tracking: the only branches are on loop
counters, and every address is `r12` (the working space, from the stack
argument) or `lr` (`out`) plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.BrainpoolP512r1

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass

theorem pre_of {u : Bool} {s : State} (h : signArm.pre s) : Pre (brainpoolp512r1With u) s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem sign_arm (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (u : Bool) (s : State) (hs : signArm.pre s) :
    ∃ t s', Exec isa (signBrainpoolP512r1With u) s t s' ∧ abiPreserved s s' ∧ signArm.post s s' := by
  have hp := pre_of (u := u) hs
  obtain ⟨t, s', he, K, hpost⟩ := sign_ok (brainpoolp512r1With_ok u) hL hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, K.sp⟩, ?_⟩
  swap
  · simp only [signArm, BitVec.setWidth_append_eq_right]
    exact hpost
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

/-- The taint analysis starts with the register arguments public, the stack
argument too, and that word known to be the base address of `scratch`. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [128, 8192], argLen := 4,
    argBases := [(0, 1)] }

theorem wf₀ {s : State} (h : signArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of (u := false) h
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀, brainpoolp512r1With, show Spec.BrainpoolP512r1.curve.len = 64 from rfl], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hp.sp_fit, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.out_sc
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.out_fit
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.sc_fit
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.out_args.symm
    · exact hp.sc_args.symm
  · intro p hm
    simp only [τ₀, List.mem_singleton] at hm
    subst hm
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem argByte_eq (s : State) (k : Nat) :
    VG.Arm.Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
  simp [VG.Arm.Taint.argByte, stackArgAddr]

/-- The taint analysis's start agrees in the two states. -/
theorem agree_τ₀ {s t : State} (hs : signArm.pre s) (ht : signArm.pre t) (h : signArm.pub s t) :
    VG.Arm.Taint.Agree τ₀ s t := by
  obtain ⟨hsp, h0, h1, h2, h3, ha⟩ := h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hs, wf₀ ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => hsp, fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · rw [(pre_of (u := false) hs).wr, (pre_of (u := false) ht).wr]; simp only [outR, scR, ptr, scPtr, h0, ha]
  · rw [argByte_eq, argByte_eq, Mem.readW_byte s.mem _ hk, Mem.readW_byte t.mem _ hk]
    exact congrArg (fun v : BitVec 32 => v.extractLsb' (8 * k) 8) ha

theorem sign_ct : ConstantTime isa signArm.pre signArm.pub signBrainpoolP512r1 :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ hs ht h => agree_τ₀ hs ht h) (by native_taint_decide)

theorem signU_ct : ConstantTime isa signArm.pre signArm.pub signBrainpoolP512r1U :=
  VG.Taint.constantTime (A := taintU) τ₀ (fun _ _ hs ht h => agree_τ₀ hs ht h) (by taint_decide)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x20001 then 0x80 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x4000, 64⟩, ⟨0x20000, 4⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x8000, 8192⟩]

theorem signWith_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (u : Bool)
    (hct : ConstantTime isa signArm.pre signArm.pub (signBrainpoolP512r1With u)) :
    Verified Arm.target (signBrainpoolP512r1With u) (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP512r1.inst Arm.abi) :=
  Verified.of_correct (sign_arm hL u) hct (by
    sig_implies [Spec.Ecdsa.BrainpoolP512r1.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
      Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, signArm, sig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
      [satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using satState)

theorem sign_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target signBrainpoolP512r1 (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP512r1.inst Arm.abi) :=
  signWith_verified hL false sign_ct

theorem signU_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target signBrainpoolP512r1U (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP512r1.inst Arm.abi) :=
  signWith_verified hL true signU_ct

end VG.Proof.Ecdsa.Arm.BrainpoolP512r1
