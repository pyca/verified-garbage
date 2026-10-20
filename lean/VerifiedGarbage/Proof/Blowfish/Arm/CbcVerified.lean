module

public import VerifiedGarbage.Proof.Blowfish.Arm.ModeCore
public import VerifiedGarbage.Proof.Blowfish.CbcScratch
public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
import VerifiedGarbage.Proof.Modes.Arm.CbcChained
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Blowfish.Arm.Run
meta import VerifiedGarbage.Proof.Blowfish.Arm.ModeCore
meta import VerifiedGarbage.Proof.Blowfish.CbcScratch
meta import VerifiedGarbage.Proof.Modes.Arm.SeqCT
meta import VerifiedGarbage.Proof.Modes.Arm.CbcChained
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Blowfish.Arm.Run

/-!
# Blowfish-CBC on ARMv7 meets its contracts

`cbcEncryptChained_verified`, `cbcDecryptChained_verified`: the generic CBC
encryption and decryption one block at a time, which return the chaining
value in the IV (`Impl/Modes/Arm/CbcChained.lean`), over Blowfish's ECB
functions (`Proof.Modes.Arm.seq_verified` with `ecbSpec`) meet the chained
contracts with a scratch buffer, as OFB and CFB do (`FbVerified.lean`), whose
IV is also read and written; the `_framed` theorems keep the buffer on the
stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Impl.Blowfish.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

/-- A state satisfying the precondition with the scratch buffer (one block at
`0x5000`), the IV read and written. -/
def cbcSat (len : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x4000 | .r2 => 0x5000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 4168⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x4000, 8⟩, ⟨0x5000, len⟩, ⟨0, 56⟩]

/-- A state satisfying the functions' precondition. -/
def cbcFrameSat (len : Nat) : State := { cbcSat len with rd := [⟨0x1000, 4168⟩], wr := [⟨0x4000, 8⟩, ⟨0x5000, len⟩] }

theorem cbcEncryptChainedTaint : SeqTaint (ecbCore true) cbcEncChained :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cbcEncryptChained_implies : (seqArm (ecbCore true) (ecbSpec true) cbcEncChained).Implies
    (Proof.Blowfish.cbcEncChainedScratchContract Arm.abi 7 256) where
  pre s h := seqArm_pre_rw rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.Blowfish.cbcEncChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Blowfish.cbcEncChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Proof.Blowfish.cbcEncChainedPost, Spec.Blowfish.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcEncChained_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore true) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, blocksOf_eq, ↓reduceIte] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Blowfish.cbcEncChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Blowfish.cbcEncChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using cbcSat 8

theorem cbcEncryptChained_verified : Verified Arm.target cbcEncryptChained (Proof.Blowfish.cbcEncChainedScratchContract Arm.abi 7 256) :=
  seq_verified (ecbSpec true) (cbcEncChained_ok _) cbcEncryptChainedTaint cbcEncryptChained_implies

theorem cbcEncryptChainedFrameSat : ∃ s, (Spec.Blowfish.cbcEncryptChainedContract Arm.abi 320).pre s := by
  implies_sat [Spec.Blowfish.cbcEncryptChainedContract, Spec.Blowfish.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat 8

/-- `cbcEncryptChained`, with its scratch buffer on the stack (zeroed on return). -/
theorem cbcEncryptChained_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cbcEncryptChained) (Spec.Blowfish.cbcEncryptChainedContract Arm.abi 320) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Blowfish.cbcChainedSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.Blowfish.cbcEncChainedPost Arm.abi.ptrBits) (wa := true) (stack := 256) (m := 0) (bytes := 64)
    cbcEncryptChained_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Blowfish.cbcEncChainedPost_local _)
    (Proof.Blowfish.cbcEncChainedPostOut_local _) cbcEncryptChainedFrameSat

theorem cbcDecryptChainedTaint : SeqTaint (ecbCore false) cbcDecChained :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cbcDecryptChained_implies : (seqArm (ecbCore false) (ecbSpec false) cbcDecChained).Implies
    (Proof.Blowfish.cbcDecChainedScratchContract Arm.abi 7 256) where
  pre s h := seqArm_pre_rw rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.Blowfish.cbcDecChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Blowfish.cbcDecChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Proof.Blowfish.cbcDecChainedPost, Spec.Blowfish.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcDecChained_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore false) rfl s
    simp only [show (ecbCore false).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, blocksOf_eq] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Blowfish.cbcDecChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Blowfish.cbcDecChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using cbcSat 8

theorem cbcDecryptChained_verified : Verified Arm.target cbcDecryptChained (Proof.Blowfish.cbcDecChainedScratchContract Arm.abi 7 256) :=
  seq_verified (ecbSpec false) (cbcDecChained_ok _) cbcDecryptChainedTaint cbcDecryptChained_implies

theorem cbcDecryptChainedFrameSat : ∃ s, (Spec.Blowfish.cbcDecryptChainedContract Arm.abi 320).pre s := by
  implies_sat [Spec.Blowfish.cbcDecryptChainedContract, Spec.Blowfish.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat 8

/-- `cbcDecryptChained`, with its scratch buffer on the stack (zeroed on return). -/
theorem cbcDecryptChained_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cbcDecryptChained) (Spec.Blowfish.cbcDecryptChainedContract Arm.abi 320) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Blowfish.cbcChainedSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.Blowfish.cbcDecChainedPost Arm.abi.ptrBits) (wa := true) (stack := 256) (m := 0) (bytes := 64)
    cbcDecryptChained_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Blowfish.cbcDecChainedPost_local _)
    (Proof.Blowfish.cbcDecChainedPostOut_local _) cbcDecryptChainedFrameSat

end VG.Proof.Blowfish.Arm
