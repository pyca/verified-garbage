module

public import VerifiedGarbage.Proof.Idea.Arm.ModeCore
meta import VerifiedGarbage.Proof.Idea.Arm.ModeCore
public import VerifiedGarbage.Proof.Idea.CbcScratch
meta import VerifiedGarbage.Proof.Idea.CbcScratch
public import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# IDEA-CBC on ARMv7 meets its contracts

`cbcEncrypt_verified`, `cbcDecrypt_verified`: the generic CBC encryption and
decryption one block at a time over IDEA's ECB function
(`Proof.Modes.Arm.seq_wp`, `seq_ct` with `ecbSpec`) meet IDEA-CBC's contracts
with a scratch buffer of 7 words (`Proof.Idea.cbcEncScratchContract`), with
the 32 bytes of stack the ECB function uses. `cbcEncrypt_framed` and
`cbcDecrypt_framed` keep the buffer on the stack, zeroed on return: 64 bytes
more.
-/

@[expose] public section

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Impl.Idea.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

/-- A state satisfying the precondition with the scratch buffer (one
block): the schedule at `0x1000`, the IV at `0x2000`, the block at `0x3000`,
the scratch buffer at `0` (the stack argument, in memory that is zero). -/
def cbcSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 104⟩, ⟨0x2000, 8⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 8⟩, ⟨0, 56⟩]

theorem encTaint : SeqTaint (ecbCore) cbcEnc :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem decTaint : SeqTaint (ecbCore) cbcDec :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem enc_implies : (seqArm (ecbCore) (ecbSpec) cbcEnc).Implies
    (Proof.Idea.cbcEncScratchContract Arm.abi 7 32) where
  pre s h := seqArm_pre_ro rfl rfl rfl (by
    sig_pre [Proof.Idea.cbcEncScratchContract, Proof.Idea.cbcScratchSig, Spec.Idea.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Idea.cbcEncScratchContract, Proof.Idea.cbcScratchSig, Proof.Idea.cbcEncPost, Spec.Idea.cbcSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcEnc_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore) rfl s
    rw [show (ecbCore).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, State.addr, blocksOf_eq] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Idea.cbcEncScratchContract, Proof.Idea.cbcScratchSig, Spec.Idea.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Idea.cbcEncScratchContract, Proof.Idea.cbcScratchSig, Spec.Idea.cbcSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using cbcSat

theorem dec_implies : (seqArm (ecbCore) (ecbSpec) cbcDec).Implies
    (Proof.Idea.cbcDecScratchContract Arm.abi 7 32) where
  pre s h := seqArm_pre_ro rfl rfl rfl (by
    sig_pre [Proof.Idea.cbcDecScratchContract, Proof.Idea.cbcScratchSig, Spec.Idea.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Idea.cbcDecScratchContract, Proof.Idea.cbcScratchSig, Proof.Idea.cbcDecPost, Spec.Idea.cbcSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcDec_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore) rfl s
    rw [show (ecbCore).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, State.addr, blocksOf_eq] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Idea.cbcDecScratchContract, Proof.Idea.cbcScratchSig, Spec.Idea.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Idea.cbcDecScratchContract, Proof.Idea.cbcScratchSig, Spec.Idea.cbcSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using cbcSat

theorem cbcEncrypt_verified : Verified Arm.target cbcEncrypt (Proof.Idea.cbcEncScratchContract Arm.abi 7 32) :=
  seq_verified (ecbSpec) (cbcEnc_ok _) encTaint enc_implies

theorem cbcDecrypt_verified : Verified Arm.target cbcDecrypt (Proof.Idea.cbcDecScratchContract Arm.abi 7 32) :=
  seq_verified (ecbSpec) (cbcDec_ok _) decTaint dec_implies

/-- A state satisfying the functions' precondition (one block). -/
def cbcFrameSat : State := { cbcSat with rd := [⟨0x1000, 104⟩, ⟨0x2000, 8⟩], wr := [⟨0x3000, 8⟩] }

theorem cbcEncFrameSat : ∃ s, (Spec.Idea.cbcEncryptContract Arm.abi 96).pre s := by
  implies_sat [Spec.Idea.cbcEncryptContract, Spec.Idea.cbcSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat

theorem cbcDecFrameSat : ∃ s, (Spec.Idea.cbcDecryptContract Arm.abi 96).pre s := by
  implies_sat [Spec.Idea.cbcDecryptContract, Spec.Idea.cbcSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat

/-- IDEA-CBC encryption, with its scratch buffer on the stack (zeroed on
return). -/
theorem cbcEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cbcEncrypt)
      (Spec.Idea.cbcEncryptContract Arm.abi 96) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Idea.cbcSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.Idea.cbcEncPost Arm.abi.ptrBits) (wa := true) (stack := 32) (m := 0) (bytes := 64)
    cbcEncrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Idea.cbcEncPost_local _)
    (Proof.Idea.cbcEncPostOut_local _) cbcEncFrameSat

/-- IDEA-CBC decryption, with its scratch buffer on the stack (zeroed on
return). -/
theorem cbcDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cbcDecrypt)
      (Spec.Idea.cbcDecryptContract Arm.abi 96) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Idea.cbcSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.Idea.cbcDecPost Arm.abi.ptrBits) (wa := true) (stack := 32) (m := 0) (bytes := 64)
    cbcDecrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Idea.cbcDecPost_local _)
    (Proof.Idea.cbcDecPostOut_local _) cbcDecFrameSat

end VG.Proof.Idea.Arm
