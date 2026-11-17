module

import VerifiedGarbage.Proof.Modes.Arm.CbcChained
public import VerifiedGarbage.Proof.TripleDes.Arm.ModeCore
public import VerifiedGarbage.Proof.TripleDes.CbcScratch
public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Modes.Arm.CbcChained
meta import VerifiedGarbage.Proof.TripleDes.Arm.ModeCore
meta import VerifiedGarbage.Proof.TripleDes.CbcScratch
meta import VerifiedGarbage.Proof.Modes.Arm.SeqCT
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Triple DES-CBC on ARMv7 meets its contracts

`cbcEncryptChained_verified`: the generic CBC encryption one block at a
time, which returns the chaining value in the IV
(`Impl/Modes/Arm/CbcChained.lean`), over Triple DES's ECB encryption
(`Proof.Modes.Arm.seq_verified` with `ecbSpec`) meets the chained contract
with a scratch buffer, as OFB and CFB do (`FbVerified.lean`), whose IV is
also read and written; `cbcEncryptChained_framed` keeps the buffer on the
stack, zeroed on return. Decryption is `Bitsliced/WideVerified.lean`'s.
-/

@[expose] public section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

/-- A state satisfying the precondition with the scratch buffer (one block,
or `len` bytes, at `0x3000`), the IV read and written. -/
def cbcSat (len : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 384⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, len⟩, ⟨0, 56⟩]

/-- A state satisfying the functions' precondition. -/
def cbcFrameSat (len : Nat) : State := { cbcSat len with rd := [⟨0x1000, 384⟩], wr := [⟨0x2000, 8⟩, ⟨0x3000, len⟩] }

theorem cbcEncryptChainedTaint : SeqTaint (ecbCore .encrypt) cbcEncChained :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cbcEncryptChained_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) cbcEncChained).Implies
    (Proof.TripleDes.cbcEncChainedScratchContract Arm.abi 7 1024) where
  pre s h := seqArm_pre_rw rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.TripleDes.cbcEncChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig, Spec.TripleDes.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.TripleDes.cbcEncChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig, Proof.TripleDes.cbcEncChainedPost, Spec.TripleDes.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcEncChained_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore .encrypt) rfl s
    simp only [e1, e2, e3] at e
    rw [show (ecbCore .encrypt).bs = 8 from rfl] at e
    simp only [ecbSpec, dirCipher, State.addr, blocksOf_eq] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.TripleDes.cbcEncChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig, Spec.TripleDes.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.TripleDes.cbcEncChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig, Spec.TripleDes.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using cbcSat 8

theorem cbcEncryptChained_verified : Verified Arm.target cbcEncryptChained (Proof.TripleDes.cbcEncChainedScratchContract Arm.abi 7 1024) :=
  seq_verified (ecbSpec .encrypt) (cbcEncChained_ok _) cbcEncryptChainedTaint cbcEncryptChained_implies

theorem cbcEncryptChainedFrameSat : ∃ s, (Spec.TripleDes.cbcEncryptChainedContract Arm.abi 1088).pre s := by
  implies_sat [Spec.TripleDes.cbcEncryptChainedContract, Spec.TripleDes.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat 8

/-- `cbcEncryptChained`, with its scratch buffer on the stack (zeroed on return). -/
theorem cbcEncryptChained_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cbcEncryptChained) (Spec.TripleDes.cbcEncryptChainedContract Arm.abi 1088) :=
  Arm.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcChainedSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.TripleDes.cbcEncChainedPost Arm.abi.ptrBits) (wa := true) (stack := 1024) (m := 0) (bytes := 64)
    cbcEncryptChained_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.TripleDes.cbcEncChainedPost_local _)
    (Proof.TripleDes.cbcEncChainedPostOut_local _) cbcEncryptChainedFrameSat

end VG.Proof.TripleDes.Arm
