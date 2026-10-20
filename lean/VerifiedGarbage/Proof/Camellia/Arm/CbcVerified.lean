module

public import VerifiedGarbage.Proof.Camellia.Arm.ModeCore
public import VerifiedGarbage.Proof.Camellia.CbcScratch
public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
import VerifiedGarbage.Proof.Modes.Arm.CbcChained
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Camellia.Arm.ModeCore
meta import VerifiedGarbage.Proof.Camellia.CbcScratch
meta import VerifiedGarbage.Proof.Modes.Arm.SeqCT
meta import VerifiedGarbage.Proof.Modes.Arm.CbcChained
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Camellia-CBC on ARMv7 meets its contracts

`cbcEncryptChained_verified`, `cbcDecryptChained_verified`: the generic CBC
encryption and decryption one block at a time, which return the chaining
value in the IV (`Impl/Modes/Arm/CbcChained.lean`), over Camellia's ECB
functions (`Proof.Modes.Arm.seq_verified` with `ecbSpec`) meet the chained
contracts with a scratch buffer, as OFB and CFB do (`FbVerified.lean`), whose
IV is also read and written; the `_framed` theorems keep the buffer on the
stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Impl.Camellia.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

/-- A state satisfying the precondition with the scratch buffer (no blocks):
the schedule at `0x1000`, 18 rounds, the IV at `0x2000`, the data at
`0x3000`, and `n = 0` and the scratch buffer's address `0` (the stack
arguments, in memory that is zero). -/
def cbcSat (len : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 18 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, len⟩, ⟨0, 72⟩]

/-- A state satisfying the functions' precondition (no blocks). -/
def cbcFrameSat (len : Nat) : State :=
  { cbcSat len with rd := [⟨0x1000, 272⟩, ⟨0x8000, 4⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, len⟩] }

theorem cbcEncryptChainedTaint : SeqTaint (ecbCore .encrypt) cbcEncChained :=
  ⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩

theorem cbcEncryptChained_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) cbcEncChained).Implies
    (Proof.Camellia.cbcEncChainedScratchContract Arm.abi 9 2816) where
  pre s h := seqArm_pre_rwR rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Camellia.cbcEncChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcChainedPre, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Camellia.cbcEncChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Proof.Camellia.cbcEncChainedPost, Spec.Camellia.cbcChainedSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    intro hR
    have e := cbcEncChained_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, rsel_eq hR, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Camellia.cbcEncChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    exact seqArm_pubR h
  sat := by
    sig_implies_sat [Proof.Camellia.cbcEncChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcChainedPre, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [cbcSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using cbcSat 0

theorem cbcEncryptChained_verified : Verified Arm.target cbcEncryptChained (Proof.Camellia.cbcEncChainedScratchContract Arm.abi 9 2816) :=
  seq_verified (ecbSpec .encrypt) (cbcEncChained_ok _) cbcEncryptChainedTaint cbcEncryptChained_implies

theorem cbcEncryptChainedFrameSat : ∃ s, (Spec.Camellia.cbcEncryptChainedContract Arm.abi 2904).pre s := by
  implies_sat [Spec.Camellia.cbcEncryptChainedContract, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcChainedPre, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [cbcFrameSat, cbcSat, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using cbcFrameSat 0

/-- `cbcEncryptChained`, with its scratch buffer on the stack (zeroed on return). -/
theorem cbcEncryptChained_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 cbcEncryptChained)
      (Spec.Camellia.cbcEncryptChainedContract Arm.abi 2904) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Camellia.cbcChainedSig) (nm := "scratch") (e := .u64) (n := 9)
    (pre := Proof.Camellia.cbcChainedPre Arm.abi.ptrBits) (post := Proof.Camellia.cbcEncChainedPost Arm.abi.ptrBits)
    (wa := true) (stack := 2816) (m := 1) (bytes := 88)
    cbcEncryptChained_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (Proof.Camellia.cbcChainedPre_local _) (Proof.Camellia.cbcEncChainedPost_local _) (Proof.Camellia.cbcEncChainedPostOut_local _) cbcEncryptChainedFrameSat

theorem cbcDecryptChainedTaint : SeqTaint (ecbCore .decrypt) cbcDecChained :=
  ⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩

theorem cbcDecryptChained_implies : (seqArm (ecbCore .decrypt) (ecbSpec .decrypt) cbcDecChained).Implies
    (Proof.Camellia.cbcDecChainedScratchContract Arm.abi 9 2816) where
  pre s h := seqArm_pre_rwR rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcChainedPre, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Proof.Camellia.cbcDecChainedPost, Spec.Camellia.cbcChainedSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    intro hR
    have e := cbcDecChained_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore .decrypt) rfl s
    simp only [show (ecbCore .decrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, rsel_eq hR, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    exact seqArm_pubR h
  sat := by
    sig_implies_sat [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcChainedPre, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [cbcSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using cbcSat 0

theorem cbcDecryptChained_verified : Verified Arm.target cbcDecryptChained (Proof.Camellia.cbcDecChainedScratchContract Arm.abi 9 2816) :=
  seq_verified (ecbSpec .decrypt) (cbcDecChained_ok _) cbcDecryptChainedTaint cbcDecryptChained_implies

theorem cbcDecryptChainedFrameSat : ∃ s, (Spec.Camellia.cbcDecryptChainedContract Arm.abi 2904).pre s := by
  implies_sat [Spec.Camellia.cbcDecryptChainedContract, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcChainedPre, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [cbcFrameSat, cbcSat, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using cbcFrameSat 0

/-- `cbcDecryptChained`, with its scratch buffer on the stack (zeroed on return). -/
theorem cbcDecryptChained_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 cbcDecryptChained)
      (Spec.Camellia.cbcDecryptChainedContract Arm.abi 2904) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Camellia.cbcChainedSig) (nm := "scratch") (e := .u64) (n := 9)
    (pre := Proof.Camellia.cbcChainedPre Arm.abi.ptrBits) (post := Proof.Camellia.cbcDecChainedPost Arm.abi.ptrBits)
    (wa := true) (stack := 2816) (m := 1) (bytes := 88)
    cbcDecryptChained_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (Proof.Camellia.cbcChainedPre_local _) (Proof.Camellia.cbcDecChainedPost_local _) (Proof.Camellia.cbcDecChainedPostOut_local _) cbcDecryptChainedFrameSat

end VG.Proof.Camellia.Arm
