module

public import VerifiedGarbage.Proof.Idea.Arm.ModeCore
public import VerifiedGarbage.Proof.Idea.CbcScratch
public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
import VerifiedGarbage.Proof.Modes.Arm.CbcChained
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Idea.Arm.ModeCore
meta import VerifiedGarbage.Proof.Idea.CbcScratch
meta import VerifiedGarbage.Proof.Modes.Arm.SeqCT
meta import VerifiedGarbage.Proof.Modes.Arm.CbcChained
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# IDEA-CBC on ARMv7 meets its contracts

`cbcEncryptChained_verified`, `cbcDecryptChained_verified`: the generic CBC
encryption and decryption one block at a time, which return the chaining
value in the IV (`Impl/Modes/Arm/CbcChained.lean`), over IDEA's ECB
function (`Proof.Modes.Arm.seq_verified` with `ecbSpec`, decryption under
the decryption subkeys its caller passes) meet the chained
contracts with a scratch buffer, as OFB and CFB do (`FbVerified.lean`), whose
IV is also read and written; the `_framed` theorems keep the buffer on the
stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Impl.Idea.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

/-- A state satisfying the precondition with the scratch buffer (one block at
`0x3000`), the IV read and written. -/
def cbcSat (len : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 104⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, len⟩, ⟨0, 56⟩]

/-- A state satisfying the functions' precondition. -/
def cbcFrameSat (len : Nat) : State := { cbcSat len with rd := [⟨0x1000, 104⟩], wr := [⟨0x2000, 8⟩, ⟨0x3000, len⟩] }

theorem cbcEncryptChainedTaint : SeqTaint (ecbCore) cbcEncChained :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cbcEncryptChained_implies : (seqArm (ecbCore) (ecbSpec) cbcEncChained).Implies
    (Proof.Idea.cbcEncChainedScratchContract Arm.abi 7 32) where
  pre s h := seqArm_pre_rw rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.Idea.cbcEncChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Spec.Idea.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Idea.cbcEncChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Proof.Idea.cbcEncChainedPost, Spec.Idea.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcEncChained_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore) rfl s
    simp only [show (ecbCore).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, State.addr, blocksOf_eq] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Idea.cbcEncChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Spec.Idea.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Idea.cbcEncChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Spec.Idea.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using cbcSat 8

theorem cbcEncryptChained_verified : Verified Arm.target cbcEncryptChained (Proof.Idea.cbcEncChainedScratchContract Arm.abi 7 32) :=
  seq_verified (ecbSpec) (cbcEncChained_ok _) cbcEncryptChainedTaint cbcEncryptChained_implies

theorem cbcEncryptChainedFrameSat : ∃ s, (Spec.Idea.cbcEncryptChainedContract Arm.abi 96).pre s := by
  implies_sat [Spec.Idea.cbcEncryptChainedContract, Spec.Idea.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat 8

/-- `cbcEncryptChained`, with its scratch buffer on the stack (zeroed on return). -/
theorem cbcEncryptChained_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cbcEncryptChained) (Spec.Idea.cbcEncryptChainedContract Arm.abi 96) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Idea.cbcChainedSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.Idea.cbcEncChainedPost Arm.abi.ptrBits) (wa := true) (stack := 32) (m := 0) (bytes := 64)
    cbcEncryptChained_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Idea.cbcEncChainedPost_local _)
    (Proof.Idea.cbcEncChainedPostOut_local _) cbcEncryptChainedFrameSat

theorem cbcDecryptChainedTaint : SeqTaint (ecbCore) cbcDecChained :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cbcDecryptChained_implies : (seqArm (ecbCore) (ecbSpec) cbcDecChained).Implies
    (Proof.Idea.cbcDecChainedScratchContract Arm.abi 7 32) where
  pre s h := seqArm_pre_rw rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.Idea.cbcDecChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Spec.Idea.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Idea.cbcDecChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Proof.Idea.cbcDecChainedPost, Spec.Idea.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcDecChained_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore) rfl s
    simp only [show (ecbCore).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, State.addr, blocksOf_eq] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Idea.cbcDecChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Spec.Idea.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Idea.cbcDecChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Spec.Idea.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using cbcSat 8

theorem cbcDecryptChained_verified : Verified Arm.target cbcDecryptChained (Proof.Idea.cbcDecChainedScratchContract Arm.abi 7 32) :=
  seq_verified (ecbSpec) (cbcDecChained_ok _) cbcDecryptChainedTaint cbcDecryptChained_implies

theorem cbcDecryptChainedFrameSat : ∃ s, (Spec.Idea.cbcDecryptChainedContract Arm.abi 96).pre s := by
  implies_sat [Spec.Idea.cbcDecryptChainedContract, Spec.Idea.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat 8

/-- `cbcDecryptChained`, with its scratch buffer on the stack (zeroed on return). -/
theorem cbcDecryptChained_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cbcDecryptChained) (Spec.Idea.cbcDecryptChainedContract Arm.abi 96) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Idea.cbcChainedSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.Idea.cbcDecChainedPost Arm.abi.ptrBits) (wa := true) (stack := 32) (m := 0) (bytes := 64)
    cbcDecryptChained_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Idea.cbcDecChainedPost_local _)
    (Proof.Idea.cbcDecChainedPostOut_local _) cbcDecryptChainedFrameSat

end VG.Proof.Idea.Arm
