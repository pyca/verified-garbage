module

public import VerifiedGarbage.Proof.Blowfish.Arm.ModeCore
meta import VerifiedGarbage.Proof.Blowfish.Arm.ModeCore
public import VerifiedGarbage.Proof.Blowfish.CbcScratch
meta import VerifiedGarbage.Proof.Blowfish.CbcScratch
public import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Blowfish.Arm.Run
import VerifiedGarbage.Proof.Framework.Arm.Linear
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Aes.SboxSpec
meta import VerifiedGarbage.Proof.Blowfish.Arm.Run
meta import VerifiedGarbage.Proof.Framework.Arm.Linear
meta import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum

/-!
# Blowfish-CBC on ARMv7 meets its contracts

`cbcEncrypt_verified`, `cbcDecrypt_verified`: the generic CBC encryption and
decryption one block at a time over Blowfish's ECB functions
(`Proof.Modes.Arm.seq_wp`, `seq_ct` with `ecbSpec`) meet Blowfish-CBC's contracts
with a scratch buffer of 7 words (`Proof.Blowfish.cbcEncScratchContract`), with
the 256 bytes of stack the ECB functions use. `cbcEncrypt_framed` and
`cbcDecrypt_framed` keep the buffer on the stack, zeroed on return: 64 bytes
more.
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Impl.Blowfish.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

/-- A state satisfying the precondition with the scratch buffer (one
block): the schedule at `0x1000`, the IV at `0x4000`, the block at `0x5000`,
the scratch buffer at `0` (the stack argument, in memory that is zero). -/
def cbcSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x4000 | .r2 => 0x5000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 4168⟩, ⟨0x4000, 8⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x5000, 8⟩, ⟨0, 56⟩]

theorem encTaint : SeqTaint (ecbCore true) cbcEnc :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem decTaint : SeqTaint (ecbCore false) cbcDec :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem enc_implies : (seqArm (ecbCore true) (ecbSpec true) cbcEnc).Implies
    (Proof.Blowfish.cbcEncScratchContract Arm.abi 7 256) where
  pre s h := seqArm_pre_ro rfl rfl rfl (by
    sig_pre [Proof.Blowfish.cbcEncScratchContract, Proof.Blowfish.cbcScratchSig, Spec.Blowfish.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Blowfish.cbcEncScratchContract, Proof.Blowfish.cbcScratchSig, Proof.Blowfish.cbcEncPost, Spec.Blowfish.cbcSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcEnc_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore true) rfl s
    rw [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, blocksOf_eq, ↓reduceIte] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Blowfish.cbcEncScratchContract, Proof.Blowfish.cbcScratchSig, Spec.Blowfish.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Blowfish.cbcEncScratchContract, Proof.Blowfish.cbcScratchSig, Spec.Blowfish.cbcSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using cbcSat

theorem dec_implies : (seqArm (ecbCore false) (ecbSpec false) cbcDec).Implies
    (Proof.Blowfish.cbcDecScratchContract Arm.abi 7 256) where
  pre s h := seqArm_pre_ro rfl rfl rfl (by
    sig_pre [Proof.Blowfish.cbcDecScratchContract, Proof.Blowfish.cbcScratchSig, Spec.Blowfish.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Blowfish.cbcDecScratchContract, Proof.Blowfish.cbcScratchSig, Proof.Blowfish.cbcDecPost, Spec.Blowfish.cbcSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcDec_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore false) rfl s
    rw [show (ecbCore false).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, blocksOf_eq, Bool.false_eq_true, ↓reduceIte] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Blowfish.cbcDecScratchContract, Proof.Blowfish.cbcScratchSig, Spec.Blowfish.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Blowfish.cbcDecScratchContract, Proof.Blowfish.cbcScratchSig, Spec.Blowfish.cbcSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using cbcSat

theorem cbcEncrypt_verified : Verified Arm.target cbcEncrypt (Proof.Blowfish.cbcEncScratchContract Arm.abi 7 256) :=
  seq_verified (ecbSpec true) (cbcEnc_ok _) encTaint enc_implies

theorem cbcDecrypt_verified : Verified Arm.target cbcDecrypt (Proof.Blowfish.cbcDecScratchContract Arm.abi 7 256) :=
  seq_verified (ecbSpec false) (cbcDec_ok _) decTaint dec_implies

/-- A state satisfying the functions' precondition (one block). -/
def cbcFrameSat : State := { cbcSat with rd := [⟨0x1000, 4168⟩, ⟨0x4000, 8⟩], wr := [⟨0x5000, 8⟩] }

theorem cbcEncFrameSat : ∃ s, (Spec.Blowfish.cbcEncryptContract Arm.abi 320).pre s := by
  implies_sat [Spec.Blowfish.cbcEncryptContract, Spec.Blowfish.cbcSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat

theorem cbcDecFrameSat : ∃ s, (Spec.Blowfish.cbcDecryptContract Arm.abi 320).pre s := by
  implies_sat [Spec.Blowfish.cbcDecryptContract, Spec.Blowfish.cbcSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat

/-- Blowfish-CBC encryption, with its scratch buffer on the stack (zeroed on
return). -/
theorem cbcEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cbcEncrypt)
      (Spec.Blowfish.cbcEncryptContract Arm.abi 320) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Blowfish.cbcSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.Blowfish.cbcEncPost Arm.abi.ptrBits) (wa := true) (stack := 256) (m := 0) (bytes := 64)
    cbcEncrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Blowfish.cbcEncPost_local _)
    (Proof.Blowfish.cbcEncPostOut_local _) cbcEncFrameSat

/-- Blowfish-CBC decryption, with its scratch buffer on the stack (zeroed on
return). -/
theorem cbcDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cbcDecrypt)
      (Spec.Blowfish.cbcDecryptContract Arm.abi 320) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Blowfish.cbcSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.Blowfish.cbcDecPost Arm.abi.ptrBits) (wa := true) (stack := 256) (m := 0) (bytes := 64)
    cbcDecrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Blowfish.cbcDecPost_local _)
    (Proof.Blowfish.cbcDecPostOut_local _) cbcDecFrameSat

end VG.Proof.Blowfish.Arm
