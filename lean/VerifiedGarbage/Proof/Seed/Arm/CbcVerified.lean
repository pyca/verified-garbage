module

public import VerifiedGarbage.Proof.Seed.Arm.ModeCore
public import VerifiedGarbage.Proof.Seed.CbcScratch
public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
import VerifiedGarbage.Proof.Modes.Arm.CbcChained
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Seed.Arm.ModeCore
meta import VerifiedGarbage.Proof.Seed.CbcScratch
meta import VerifiedGarbage.Proof.Modes.Arm.SeqCT
meta import VerifiedGarbage.Proof.Modes.Arm.CbcChained
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# SEED-CBC on ARMv7 meets its contracts

`cbcEncryptChained_verified`, `cbcDecryptChained_verified`: the generic CBC
encryption and decryption one block at a time, which return the chaining
value in the IV (`Impl/Modes/Arm/CbcChained.lean`), over SEED's ECB
functions (`Proof.Modes.Arm.seq_verified` with `ecbSpec`) meet the chained
contracts with a scratch buffer, as OFB and CFB do (`FbVerified.lean`), whose
IV is also read and written; the `_framed` theorems keep the buffer on the
stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Impl.Seed.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

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
  rd := [⟨0x1000, 128⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, len⟩, ⟨0, 72⟩]

/-- A state satisfying the functions' precondition. -/
def cbcFrameSat (len : Nat) : State := { cbcSat len with rd := [⟨0x1000, 128⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, len⟩] }

theorem cbcEncryptChainedTaint : SeqTaint (ecbCore .encrypt) cbcEncChained :=
  ⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩

theorem cbcEncryptChained_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) cbcEncChained).Implies
    (Proof.Seed.cbcEncChainedScratchContract Arm.abi 9 752) where
  pre s h := seqArm_pre_rw rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Seed.cbcEncChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Seed.cbcEncChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Proof.Seed.cbcEncChainedPost, Spec.Seed.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcEncChained_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore .encrypt) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Seed.cbcEncChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Seed.cbcEncChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using cbcSat 16

theorem cbcEncryptChained_verified : Verified Arm.target cbcEncryptChained (Proof.Seed.cbcEncChainedScratchContract Arm.abi 9 752) :=
  seq_verified (ecbSpec .encrypt) (cbcEncChained_ok _) cbcEncryptChainedTaint cbcEncryptChained_implies

theorem cbcEncryptChainedFrameSat : ∃ s, (Spec.Seed.cbcEncryptChainedContract Arm.abi 832).pre s := by
  implies_sat [Spec.Seed.cbcEncryptChainedContract, Spec.Seed.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat 16

/-- `cbcEncryptChained`, with its scratch buffer on the stack (zeroed on return). -/
theorem cbcEncryptChained_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 cbcEncryptChained) (Spec.Seed.cbcEncryptChainedContract Arm.abi 832) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Seed.cbcChainedSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Seed.cbcEncChainedPost Arm.abi.ptrBits) (wa := true) (stack := 752) (m := 0) (bytes := 80)
    cbcEncryptChained_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Seed.cbcEncChainedPost_local _)
    (Proof.Seed.cbcEncChainedPostOut_local _) cbcEncryptChainedFrameSat

theorem cbcDecryptChainedTaint : SeqTaint (ecbCore .decrypt) cbcDecChained :=
  ⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩

theorem cbcDecryptChained_implies : (seqArm (ecbCore .decrypt) (ecbSpec .decrypt) cbcDecChained).Implies
    (Proof.Seed.cbcDecChainedScratchContract Arm.abi 9 752) where
  pre s h := seqArm_pre_rw rfl (len := (· * 16)) (fun n => rfl) (by
    sig_pre [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Proof.Seed.cbcDecChainedPost, Spec.Seed.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcDecChained_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore .decrypt) rfl s
    simp only [show (ecbCore .decrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using cbcSat 16

theorem cbcDecryptChained_verified : Verified Arm.target cbcDecryptChained (Proof.Seed.cbcDecChainedScratchContract Arm.abi 9 752) :=
  seq_verified (ecbSpec .decrypt) (cbcDecChained_ok _) cbcDecryptChainedTaint cbcDecryptChained_implies

theorem cbcDecryptChainedFrameSat : ∃ s, (Spec.Seed.cbcDecryptChainedContract Arm.abi 832).pre s := by
  implies_sat [Spec.Seed.cbcDecryptChainedContract, Spec.Seed.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat 16

/-- `cbcDecryptChained`, with its scratch buffer on the stack (zeroed on return). -/
theorem cbcDecryptChained_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 cbcDecryptChained) (Spec.Seed.cbcDecryptChainedContract Arm.abi 832) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Seed.cbcChainedSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Seed.cbcDecChainedPost Arm.abi.ptrBits) (wa := true) (stack := 752) (m := 0) (bytes := 80)
    cbcDecryptChained_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Seed.cbcDecChainedPost_local _)
    (Proof.Seed.cbcDecChainedPostOut_local _) cbcDecryptChainedFrameSat

end VG.Proof.Seed.Arm
