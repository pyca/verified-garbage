import VerifiedGarbage.Proof.TripleDes.Arm.ModeCore
import VerifiedGarbage.Proof.TripleDes.CbcScratch
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe

/-!
# Triple DES-CBC on ARMv7 meets its contracts

`cbcEncrypt_verified`, `cbcDecrypt_verified`: the generic CBC encryption and
decryption one block at a time over Triple DES's ECB functions
(`Proof.Modes.Arm.seq_wp`, `seq_ct` with `ecbSpec`) meet Triple DES-CBC's
contracts with a scratch buffer of 7 words
(`Proof.TripleDes.cbcEncScratchContract`), with the 1024 bytes of stack the
ECB functions use. `cbcEncrypt_framed` and `cbcDecrypt_framed` keep the
buffer on the stack, zeroed on return: 64 bytes more.
-/

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

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
  rd := [⟨0x1000, 384⟩, ⟨0x2000, 8⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 8⟩, ⟨0, 56⟩]

theorem encTaint : SeqTaint (ecbCore .encrypt) cbcEnc :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem decTaint : SeqTaint (ecbCore .decrypt) cbcDec :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem enc_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) cbcEnc).Implies
    (Proof.TripleDes.cbcEncScratchContract Arm.abi 7 1024) where
  pre s h := seqArm_pre_ro rfl rfl (by
    sig_pre [Proof.TripleDes.cbcEncScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.TripleDes.cbcEncScratchContract, Proof.TripleDes.cbcScratchSig, Proof.TripleDes.cbcEncPost, Spec.TripleDes.cbcSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcEnc_post h
    rw [show (ecbCore .encrypt).bs = 8 from rfl] at e
    simp only [ecbSpec, dirCipher, State.addr, blocksOf_eq] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.TripleDes.cbcEncScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub h
  sat := by
    sig_implies_sat [Proof.TripleDes.cbcEncScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using cbcSat

theorem dec_implies : (seqArm (ecbCore .decrypt) (ecbSpec .decrypt) cbcDec).Implies
    (Proof.TripleDes.cbcDecScratchContract Arm.abi 7 1024) where
  pre s h := seqArm_pre_ro rfl rfl (by
    sig_pre [Proof.TripleDes.cbcDecScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.TripleDes.cbcDecScratchContract, Proof.TripleDes.cbcScratchSig, Proof.TripleDes.cbcDecPost, Spec.TripleDes.cbcSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcDec_post h
    rw [show (ecbCore .decrypt).bs = 8 from rfl] at e
    simp only [ecbSpec, dirCipher, State.addr, blocksOf_eq] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.TripleDes.cbcDecScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub h
  sat := by
    sig_implies_sat [Proof.TripleDes.cbcDecScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using cbcSat

theorem cbcEncrypt_verified : Verified Arm.target cbcEncrypt (Proof.TripleDes.cbcEncScratchContract Arm.abi 7 1024) :=
  seq_verified (ecbSpec .encrypt) (cbcEnc_ok _) encTaint enc_implies

theorem cbcDecrypt_verified : Verified Arm.target cbcDecrypt (Proof.TripleDes.cbcDecScratchContract Arm.abi 7 1024) :=
  seq_verified (ecbSpec .decrypt) (cbcDec_ok _) decTaint dec_implies

/-- A state satisfying the functions' precondition (one block). -/
def cbcFrameSat : State := { cbcSat with rd := [⟨0x1000, 384⟩, ⟨0x2000, 8⟩], wr := [⟨0x3000, 8⟩] }

theorem cbcEncFrameSat : ∃ s, (Spec.TripleDes.cbcEncryptContract Arm.abi 1088).pre s := by
  implies_sat [Spec.TripleDes.cbcEncryptContract, Spec.TripleDes.cbcSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat

theorem cbcDecFrameSat : ∃ s, (Spec.TripleDes.cbcDecryptContract Arm.abi 1088).pre s := by
  implies_sat [Spec.TripleDes.cbcDecryptContract, Spec.TripleDes.cbcSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat

/-- Triple DES-CBC encryption, with its scratch buffer on the stack (zeroed on
return). -/
theorem cbcEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cbcEncrypt)
      (Spec.TripleDes.cbcEncryptContract Arm.abi 1088) :=
  Arm.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.TripleDes.cbcEncPost Arm.abi.ptrBits) (wa := true) (stack := 1024) (m := 0) (bytes := 64)
    cbcEncrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.TripleDes.cbcEncPost_local _)
    (Proof.TripleDes.cbcEncPostOut_local _) cbcEncFrameSat

/-- Triple DES-CBC decryption, with its scratch buffer on the stack (zeroed on
return). -/
theorem cbcDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cbcDecrypt)
      (Spec.TripleDes.cbcDecryptContract Arm.abi 1088) :=
  Arm.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.TripleDes.cbcDecPost Arm.abi.ptrBits) (wa := true) (stack := 1024) (m := 0) (bytes := 64)
    cbcDecrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.TripleDes.cbcDecPost_local _)
    (Proof.TripleDes.cbcDecPostOut_local _) cbcDecFrameSat

end VG.Proof.TripleDes.Arm
