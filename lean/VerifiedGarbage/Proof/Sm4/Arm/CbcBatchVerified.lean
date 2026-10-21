module

public import VerifiedGarbage.Proof.Sm4.Arm.CbcBody
public import VerifiedGarbage.Proof.Sm4.Arm.CbcCT
public import VerifiedGarbage.Proof.Sm4.CbcScratch
public import VerifiedGarbage.Spec.Sm4.Cbc
meta import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sm4.CbcScratch
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-! # Batched ARMv7 SM4-CBC decryption meets the public, wiped-stack contract -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcBatchVerified

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.CbcBody VG.Proof.Sm4.Arm.CbcCT

def cbcArm : Contract isa where
  pre := Pre
  post := Post
  pub := Pub

theorem correct (s : State) (h : cbcArm.pre s) :
    ∃ t s', Exec isa BatchCbc.decrypt s t s' ∧ abiPreserved s s' ∧ cbcArm.post s s' := by
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

theorem implies : cbcArm.Implies (Proof.Sm4.cbcDecChainedScratchContract Arm.abi 189 0) where
  pre s h := by
    sig_pre [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    rcases h with ⟨sp, rd, wr, ki, kd, ks, id, ivs, ia, ds, da, sa, fk, fi, fd, fb⟩
    rw [Nat.mul_comm] at wr kd id ds da fd
    exact ⟨sp, rd, wr, ki, kd, ks, id, ivs, ds, ia, da, sa, fk, fi, fd, fb⟩
  post s s' _ h := by
    sig_post [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Proof.Sm4.cbcDecChainedPost, Spec.Sm4.cbcChainedSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨h.data, h.iv⟩
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h
  sat := by
    sig_implies_sat [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

theorem verified : Verified Arm.target BatchCbc.decrypt (Proof.Sm4.cbcDecChainedScratchContract Arm.abi 189 0) :=
  Verified.of_correct correct cbc_ct implies

def frameState : State := { satState with rd := [⟨0x1000, 128⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩] }

theorem frameSat : ∃ s, (Spec.Sm4.cbcDecryptChainedContract Arm.abi 1520).pre s := by
  implies_sat [Spec.Sm4.cbcDecryptChainedContract, Spec.Sm4.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, State.addr] [frameState, satState] using frameState

theorem framed : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 BatchCbc.decrypt)
    (Spec.Sm4.cbcDecryptChainedContract Arm.abi 1520) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Sm4.cbcChainedSig) (nm := "scratch") (e := .u64) (n := 189)
    (post := Proof.Sm4.cbcDecChainedPost Arm.abi.ptrBits) (wa := true) (stack := 0) (m := 0) (bytes := 1520)
    verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm4.cbcDecChainedPost_local _)
    (Proof.Sm4.cbcDecChainedPostOut_local _) frameSat

end VG.Proof.Sm4.Arm.CbcBatchVerified
