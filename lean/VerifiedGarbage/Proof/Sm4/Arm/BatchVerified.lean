module

public import VerifiedGarbage.Proof.Sm4.Arm.BatchBody
public import VerifiedGarbage.Proof.Sm4.Arm.BatchCT
public import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-! # Batched ARMv7 SM4-CTR meets the public, wiped-stack contract -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.BatchVerified

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.BatchBody VG.Proof.Sm4.Arm.BatchCT

def ctrArm : Contract isa where
  pre := Pre
  post := Post
  pub := Pub

theorem correct (s : State) (h : ctrArm.pre s) :
    ∃ t s', Exec isa BatchCtr.ctr s t s' ∧ abiPreserved s s' ∧ ctrArm.post s s' := by
  obtain ⟨t, s', e, p⟩ := body_wp h
  exact ⟨t, s', e, ⟨p.regs, p.sp⟩, p⟩

def satState : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 128⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0, 1512⟩]

theorem implies : ctrArm.Implies (Proof.Sm4.ctrScratchContract Arm.abi 189 0) where
  pre s h := by
    sig_pre [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Spec.Sm4.ctrSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    rcases h with ⟨sp, rd, wr, ki, kd, ks, id, ivs, ia, ds, da, sa, fk, fi, fd, fb⟩
    rw [Nat.mul_comm] at wr kd id ds da fd
    exact ⟨sp, rd, wr, ki, kd, ks, id, ivs, ds, ia, da, sa, fk, fi, fd, fb⟩
  post s s' _ h := by
    sig_post [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Proof.Sm4.ctrPost, Spec.Sm4.ctrSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨h.data, h.iv⟩
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Spec.Sm4.ctrSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h
  sat := by
    sig_implies_sat [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Spec.Sm4.ctrSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

theorem verified : Verified Arm.target BatchCtr.ctr (Proof.Sm4.ctrScratchContract Arm.abi 189 0) :=
  Verified.of_correct correct ctr_ct implies

def frameState : State := { satState with rd := [⟨0x1000, 128⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩] }

theorem frameSat : ∃ s, (Spec.Sm4.ctrContract Arm.abi 1520).pre s := by
  implies_sat [Spec.Sm4.ctrContract, Spec.Sm4.ctrSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, State.addr] [frameState, satState] using frameState

theorem framed : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 BatchCtr.ctr)
    (Spec.Sm4.ctrContract Arm.abi 1520) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Sm4.ctrSig) (nm := "scratch") (e := .u64) (n := 189)
    (post := Proof.Sm4.ctrPost Arm.abi.ptrBits) (wa := true) (stack := 0) (m := 0) (bytes := 1520)
    verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm4.ctrPost_local _)
    (Proof.Sm4.ctrPostOut_local _) frameSat

end VG.Proof.Sm4.Arm.BatchVerified
