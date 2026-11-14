module

public import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.CbcScratch
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Rc2.Arm.Lit
public import VerifiedGarbage.Proof.Framework.Contract

/-! # RC2-CBC in place on Arm, with wiped stack working space -/
-- separate module: exporting CBC does not rebuild its existing streaming callers.

@[expose] public section

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

theorem chained_correct (d : Spec.Rc2.Direction) (s : State) (hs : (contract d).pre s) :
    ∃ t s', Exec isa (Impl.Rc2.Arm.Cbc.cbc d) s t s' ∧ abiPreserved s s' ∧ (contract d).post s s' := by
  obtain ⟨t, s', he, hp, hq⟩ := cbc_body_correct d s hs
  exact ⟨t, s', he, ⟨hp, Exec.sp he⟩, hq⟩

def scratchSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem p := if p = 0x6001 then 0x40 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x6000, 4⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 512⟩]

def frameSat : State := { scratchSat with rd := [⟨0x1000, 128⟩], wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩] }

theorem encryptChained_implies : (contract .encrypt).Implies
    (Proof.Rc2.cbcEncChainedScratchContract abi 64 0) where
  pre := by sig_implies_pre [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, contract, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
  post := by
    intro s s' _ h
    sig_post [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, contract, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
    exact Proof.Rc2.cbcEncChainedPost_of_blocks (r := 0) h.1 h.2
  pub := by sig_implies_pub [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, contract, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
  sat := by sig_implies_sat [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, contract, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr] [scratchSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using scratchSat

theorem encryptChained_verified :
    Verified Arm.target Impl.Rc2.Arm.Cbc.encrypt
      (Proof.Rc2.cbcEncChainedScratchContract abi 64 0) :=
  Verified.of_correct (chained_correct .encrypt) (cbc_constantTime .encrypt) encryptChained_implies

theorem encryptChainedFrameSat : ∃ s, (Spec.Rc2.cbcEncryptChainedContract abi 528).pre s := by
  implies_sat [Spec.Rc2.cbcEncryptChainedContract, Spec.Rc2.cbcChainedSig, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
    [frameSat, scratchSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using frameSat

theorem encryptChained_framed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.encrypt)
      (Spec.Rc2.cbcEncryptChainedContract abi 528) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Rc2.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 64) (post := Proof.Rc2.cbcEncChainedPost abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 528) encryptChained_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Rc2.cbcEncChainedPost_local _) (Proof.Rc2.cbcEncChainedPostOut_local _) encryptChainedFrameSat

theorem decryptChained_implies : (contract .decrypt).Implies
    (Proof.Rc2.cbcDecChainedScratchContract abi 64 0) where
  pre := by sig_implies_pre [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, contract, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
  post := by
    intro s s' _ h
    sig_post [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, contract, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
    exact Proof.Rc2.cbcDecChainedPost_of_blocks (r := 0) h.1 h.2
  pub := by sig_implies_pub [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, contract, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
  sat := by sig_implies_sat [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, contract, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr] [scratchSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using scratchSat

theorem decryptChained_verified :
    Verified Arm.target Impl.Rc2.Arm.Cbc.decrypt
      (Proof.Rc2.cbcDecChainedScratchContract abi 64 0) :=
  Verified.of_correct (chained_correct .decrypt) (cbc_constantTime .decrypt) decryptChained_implies

theorem decryptChainedFrameSat : ∃ s, (Spec.Rc2.cbcDecryptChainedContract abi 528).pre s := by
  implies_sat [Spec.Rc2.cbcDecryptChainedContract, Spec.Rc2.cbcChainedSig, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
    [frameSat, scratchSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using frameSat

theorem decryptChained_framed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.decrypt)
      (Spec.Rc2.cbcDecryptChainedContract abi 528) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Rc2.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 64) (post := Proof.Rc2.cbcDecChainedPost abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 528) decryptChained_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Rc2.cbcDecChainedPost_local _) (Proof.Rc2.cbcDecChainedPostOut_local _) decryptChainedFrameSat

end VG.Proof.Rc2.Arm.Cbc
