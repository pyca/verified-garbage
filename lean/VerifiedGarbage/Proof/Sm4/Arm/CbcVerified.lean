import VerifiedGarbage.Proof.Sm4.Arm.ModeCore
import VerifiedGarbage.Proof.Sm4.CbcScratch
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe

/-!
# SM4-CBC on ARMv7 meets its contracts

`cbcEncrypt_verified`, `cbcDecrypt_verified`: the generic CBC encryption and
decryption one block at a time over SM4's ECB functions
(`Proof.Modes.Arm.seq_wp`, `seq_ct` with `ecbSpec`) meet SM4-CBC's contracts
with a scratch buffer of 9 words (`Proof.Sm4.cbcEncScratchContract`), with
the 1456 bytes of stack the ECB functions use. `cbcEncrypt_framed` and
`cbcDecrypt_framed` keep the buffer on the stack, zeroed on return: 80 bytes
more.
-/

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Impl.Sm4.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

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
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 16⟩, ⟨0, 72⟩]

theorem encTaint : SeqTaint (ecbCore .encrypt) cbcEnc :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem decTaint : SeqTaint (ecbCore .decrypt) cbcDec :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem enc_implies : (seqArm (ecbCore .encrypt) (ecbSpec .encrypt) cbcEnc).Implies
    (Proof.Sm4.cbcEncScratchContract Arm.abi 9 1456) where
  pre s h := seqArm_pre_ro rfl rfl (by
    sig_pre [Proof.Sm4.cbcEncScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Sm4.cbcEncScratchContract, Proof.Sm4.cbcScratchSig, Proof.Sm4.cbcEncPost, Spec.Sm4.cbcSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcEnc_post h
    rw [show (ecbCore .encrypt).bs = 16 from rfl] at e
    simp only [ecbSpec, dirCipher, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Sm4.cbcEncScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub h
  sat := by
    sig_implies_sat [Proof.Sm4.cbcEncScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using cbcSat

theorem dec_implies : (seqArm (ecbCore .decrypt) (ecbSpec .decrypt) cbcDec).Implies
    (Proof.Sm4.cbcDecScratchContract Arm.abi 9 1456) where
  pre s h := seqArm_pre_ro rfl rfl (by
    sig_pre [Proof.Sm4.cbcDecScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Sm4.cbcDecScratchContract, Proof.Sm4.cbcScratchSig, Proof.Sm4.cbcDecPost, Spec.Sm4.cbcSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcDec_post h
    rw [show (ecbCore .decrypt).bs = 16 from rfl] at e
    simp only [ecbSpec, dirCipher, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Sm4.cbcDecScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub h
  sat := by
    sig_implies_sat [Proof.Sm4.cbcDecScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using cbcSat

theorem cbcEncrypt_verified : Verified Arm.target cbcEncrypt (Proof.Sm4.cbcEncScratchContract Arm.abi 9 1456) :=
  seq_verified (ecbSpec .encrypt) (cbcEnc_ok _) encTaint enc_implies

theorem cbcDecrypt_verified : Verified Arm.target cbcDecrypt (Proof.Sm4.cbcDecScratchContract Arm.abi 9 1456) :=
  seq_verified (ecbSpec .decrypt) (cbcDec_ok _) decTaint dec_implies

/-- A state satisfying the functions' precondition (one block). -/
def cbcFrameSat : State := { cbcSat with rd := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩], wr := [⟨0x3000, 16⟩] }

theorem cbcEncFrameSat : ∃ s, (Spec.Sm4.cbcEncryptContract Arm.abi 1536).pre s := by
  implies_sat [Spec.Sm4.cbcEncryptContract, Spec.Sm4.cbcSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat

theorem cbcDecFrameSat : ∃ s, (Spec.Sm4.cbcDecryptContract Arm.abi 1536).pre s := by
  implies_sat [Spec.Sm4.cbcDecryptContract, Spec.Sm4.cbcSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat

/-- SM4-CBC encryption, with its scratch buffer on the stack (zeroed on
return). -/
theorem cbcEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 cbcEncrypt)
      (Spec.Sm4.cbcEncryptContract Arm.abi 1536) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Sm4.cbcSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Sm4.cbcEncPost Arm.abi.ptrBits) (wa := true) (stack := 1456) (m := 0) (bytes := 80)
    cbcEncrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm4.cbcEncPost_local _)
    (Proof.Sm4.cbcEncPostOut_local _) cbcEncFrameSat

/-- SM4-CBC decryption, with its scratch buffer on the stack (zeroed on
return). -/
theorem cbcDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 cbcDecrypt)
      (Spec.Sm4.cbcDecryptContract Arm.abi 1536) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Sm4.cbcSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Sm4.cbcDecPost Arm.abi.ptrBits) (wa := true) (stack := 1456) (m := 0) (bytes := 80)
    cbcDecrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm4.cbcDecPost_local _)
    (Proof.Sm4.cbcDecPostOut_local _) cbcDecFrameSat

end VG.Proof.Sm4.Arm
