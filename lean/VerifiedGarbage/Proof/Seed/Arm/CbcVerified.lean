import VerifiedGarbage.Proof.Seed.Arm.ModeCore
import VerifiedGarbage.Proof.Seed.CbcScratch
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe

/-!
# SEED-CBC on ARMv7 meets its contracts

`cbcEncrypt_verified`, `cbcDecrypt_verified`: the generic CBC encryption and
decryption one block at a time over SEED's ECB functions
(`Proof.Modes.Arm.seq_wp`, `seq_ct` with `ecbSpec`) meet SEED-CBC's contracts
with a scratch buffer of 9 words (`Proof.Seed.cbcEncScratchContract`), with
the 752 bytes of stack the ECB functions use. `cbcEncrypt_framed` and
`cbcDecrypt_framed` keep the buffer on the stack, zeroed on return: 80 bytes
more.
-/

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Impl.Seed.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

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
    (Proof.Seed.cbcEncScratchContract Arm.abi 9 752) where
  pre s h := seqArm_pre_ro rfl rfl rfl (by
    sig_pre [Proof.Seed.cbcEncScratchContract, Proof.Seed.cbcScratchSig, Spec.Seed.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Seed.cbcEncScratchContract, Proof.Seed.cbcScratchSig, Proof.Seed.cbcEncPost, Spec.Seed.cbcSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcEnc_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore .encrypt) rfl s
    rw [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Seed.cbcEncScratchContract, Proof.Seed.cbcScratchSig, Spec.Seed.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Seed.cbcEncScratchContract, Proof.Seed.cbcScratchSig, Spec.Seed.cbcSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using cbcSat

theorem dec_implies : (seqArm (ecbCore .decrypt) (ecbSpec .decrypt) cbcDec).Implies
    (Proof.Seed.cbcDecScratchContract Arm.abi 9 752) where
  pre s h := seqArm_pre_ro rfl rfl rfl (by
    sig_pre [Proof.Seed.cbcDecScratchContract, Proof.Seed.cbcScratchSig, Spec.Seed.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Seed.cbcDecScratchContract, Proof.Seed.cbcScratchSig, Proof.Seed.cbcDecPost, Spec.Seed.cbcSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcDec_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := ecbCore .decrypt) rfl s
    rw [show (ecbCore .decrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, VG.Proof.Modes.blocksOf_16] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Seed.cbcDecScratchContract, Proof.Seed.cbcScratchSig, Spec.Seed.cbcSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub rfl h
  sat := by
    sig_implies_sat [Proof.Seed.cbcDecScratchContract, Proof.Seed.cbcScratchSig, Spec.Seed.cbcSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [cbcSat, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using cbcSat

theorem cbcEncrypt_verified : Verified Arm.target cbcEncrypt (Proof.Seed.cbcEncScratchContract Arm.abi 9 752) :=
  seq_verified (ecbSpec .encrypt) (cbcEnc_ok _) encTaint enc_implies

theorem cbcDecrypt_verified : Verified Arm.target cbcDecrypt (Proof.Seed.cbcDecScratchContract Arm.abi 9 752) :=
  seq_verified (ecbSpec .decrypt) (cbcDec_ok _) decTaint dec_implies

/-- A state satisfying the functions' precondition (one block). -/
def cbcFrameSat : State := { cbcSat with rd := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩], wr := [⟨0x3000, 16⟩] }

theorem cbcEncFrameSat : ∃ s, (Spec.Seed.cbcEncryptContract Arm.abi 832).pre s := by
  implies_sat [Spec.Seed.cbcEncryptContract, Spec.Seed.cbcSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat

theorem cbcDecFrameSat : ∃ s, (Spec.Seed.cbcDecryptContract Arm.abi 832).pre s := by
  implies_sat [Spec.Seed.cbcDecryptContract, Spec.Seed.cbcSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [cbcFrameSat, cbcSat] using cbcFrameSat

/-- SEED-CBC encryption, with its scratch buffer on the stack (zeroed on
return). -/
theorem cbcEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 cbcEncrypt)
      (Spec.Seed.cbcEncryptContract Arm.abi 832) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Seed.cbcSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Seed.cbcEncPost Arm.abi.ptrBits) (wa := true) (stack := 752) (m := 0) (bytes := 80)
    cbcEncrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Seed.cbcEncPost_local _)
    (Proof.Seed.cbcEncPostOut_local _) cbcEncFrameSat

/-- SEED-CBC decryption, with its scratch buffer on the stack (zeroed on
return). -/
theorem cbcDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 cbcDecrypt)
      (Spec.Seed.cbcDecryptContract Arm.abi 832) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Seed.cbcSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Seed.cbcDecPost Arm.abi.ptrBits) (wa := true) (stack := 752) (m := 0) (bytes := 80)
    cbcDecrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Seed.cbcDecPost_local _)
    (Proof.Seed.cbcDecPostOut_local _) cbcDecFrameSat

end VG.Proof.Seed.Arm
