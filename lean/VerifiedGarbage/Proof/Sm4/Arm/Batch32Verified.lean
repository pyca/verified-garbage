module

public import VerifiedGarbage.Proof.Sm4.Arm.Batch32Body
import VerifiedGarbage.Proof.Sm4.Arm.Batch32CT
public import VerifiedGarbage.Proof.Sm4.Ctr32Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sm4.Ctr32Scratch
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr32
public import VerifiedGarbage.Proof.Sm4.Arm.BatchCT
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Sm4.Contract

/-! # Batched ARMv7 SM4 counter mode with `inc₃₂` meets the public, wiped-stack contract -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.Batch32Verified

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.Batch32Body
open VG.Proof.Sm4.Arm.BatchCT (Pub)
open VG.Proof.Sm4.Arm.Batch32CT (ctr32_ct)

def ctr32Arm : Contract isa where
  pre := Pre
  post := Post
  pub := Pub

theorem correct (s : State) (h : ctr32Arm.pre s) :
    ∃ t s', Exec isa BatchCtr32.ctr32 s t s' ∧ abiPreserved s s' ∧ ctr32Arm.post s s' := by
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

theorem implies : ctr32Arm.Implies (Proof.Sm4.ctr32ScratchContract Arm.abi 189 0) where
  pre s h := by
    sig_pre [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Sig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    rcases h with ⟨sp, rd, wr, ki, kd, ks, id, ivs, ia, ds, da, sa, fk, fi, fd, fb⟩
    rw [Nat.mul_comm] at wr kd id ds da fd
    exact ⟨sp, rd, wr, ki, kd, ks, id, ivs, ds, ia, da, sa, fk, fi, fd, fb⟩
  post s s' _ h := by
    sig_post [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Post, Proof.Sm4.ctr32Sig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨h.data, h.iv⟩
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Sig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h
  sat := by
    sig_implies_sat [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Sig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

theorem verified : Verified Arm.target BatchCtr32.ctr32 (Proof.Sm4.ctr32ScratchContract Arm.abi 189 0) :=
  Verified.of_correct correct ctr32_ct implies

def frameState : State := { satState with rd := [⟨0x1000, 128⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩] }

theorem frameSat : ∃ s, (Proof.Sm4.ctr32Contract Arm.abi 1520).pre s := by
  implies_sat [Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, State.addr] [frameState, satState] using frameState

theorem framed : Verified Arm.target
    BatchCtr32.ctr32Framed
    (Proof.Sm4.ctr32Contract Arm.abi 1520) :=
  Arm.Verified.stackScratchWiped (sig := Proof.Sm4.ctr32Sig) (nm := "scratch") (e := .u64) (n := 189)
    (post := Proof.Sm4.ctr32Post Arm.abi.ptrBits) (wa := true) (stack := 0) (m := 0) (bytes := 1520)
    verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm4.ctr32Post_local _)
    (Proof.Sm4.ctr32PostOut_local _) frameSat

end VG.Proof.Sm4.Arm.Batch32Verified
