module

public import VerifiedGarbage.Proof.Seed.Arm.FbVerified
public import VerifiedGarbage.Proof.Modes.Arm.SeqFinalCT
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Impl.Seed.Arm.FbFinal
public import VerifiedGarbage.Spec.Seed.CfbFinal
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Seed.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Seed.Arm.FbVerified
meta import VerifiedGarbage.Proof.Modes.Arm.SeqFinalCT
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Impl.Seed.Arm.FbFinal
meta import VerifiedGarbage.Spec.Seed.CfbFinal
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# SEED-CFB128 of a message's last piece on ARMv7 meets its contracts

The generic CFB over a message's last piece (`Proof.Modes.Arm.seqFinal_verified`)
over SEED's ECB function (`ecbSpec .encrypt`) meets the contracts with a scratch
buffer of 9 words, as the whole-block functions do (`FbVerified.lean`), with
the specification's results (`Proof.Modes.Arm.cfbEncFinal_post`, …); the
`_framed` theorems keep the buffer on the stack, zeroed on return: 80 bytes
more.
-/

@[expose] public section

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Impl.Seed.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

/-- SEED's cipher of the schedule at `k`. -/
abbrev ciphAt (m : Mem) (k : Addr) : Spec.Cbc.Cipher := Spec.Seed.cipher (Spec.Seed.scheduleAt m k)

/-- The final functions' signature. -/
abbrev finalSig : Sig := Proof.Modes.finalSig "schedule" .u8 128 16

theorem ciphAt_congr {m₁ m₂ : Mem} {k : Addr}
    (h : ∀ i < 128 * Elem.size .u8, m₂ (k + BitVec.ofNat 64 i) = m₁ (k + BitVec.ofNat 64 i)) :
    ciphAt m₂ k = ciphAt m₁ k := by
  simp only [ciphAt, Proof.Seed.scheduleAt_congr h]

theorem cfbEncryptFinalTaint : FinalTaint (ecbCore .encrypt) cfbEnc :=
  ⟨cfbEncryptTaint.pro, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, cfbEncryptTaint.epi⟩

theorem cfbEncryptFinal_implies : (seqFinalArm (ecbCore .encrypt) (ecbSpec .encrypt) cfbEnc).Implies
    (Sig.scratchContract Arm.abi finalSig "scratch" .u64 9 (Curry.const (fun _ => True) _)
      (Proof.Modes.encFinalPost ciphAt 16 Arm.abi.ptrBits) true 752) where
  pre s h := seqArm_pre_rw (M := byteMode) rfl (len := fun n => n) (fun n => (Nat.mul_one n).symm) (by
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbEncFinal_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := (ecbCore .encrypt)) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub (M := byteMode) rfl h
  sat := by
    sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using fbSat 1

theorem cfbEncryptFinal_verified : Verified Arm.target cfbEncryptFinal
    (Sig.scratchContract Arm.abi finalSig "scratch" .u64 9 (Curry.const (fun _ => True) _)
      (Proof.Modes.encFinalPost ciphAt 16 Arm.abi.ptrBits) true 752) :=
  seqFinal_verified (ecbSpec .encrypt) (cfbEnc_finalOk _ (by decide) (by decide) (by decide)) cfbEncryptFinalTaint
    cfbEncryptFinal_implies

theorem cfbDecryptFinalTaint : FinalTaint (ecbCore .encrypt) cfbDecF :=
  ⟨cfbDecryptTaint.pro, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, cfbDecryptTaint.epi⟩

theorem cfbDecryptFinal_implies : (seqFinalArm (ecbCore .encrypt) (ecbSpec .encrypt) cfbDecF).Implies
    (Sig.scratchContract Arm.abi finalSig "scratch" .u64 9 (Curry.const (fun _ => True) _)
      (Proof.Modes.decFinalPost ciphAt 16 Arm.abi.ptrBits) true 752) where
  pre s h := seqArm_pre_rw (M := byteMode) rfl (len := fun n => n) (fun n => (Nat.mul_one n).symm) (by
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbDecFinal_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := (ecbCore .encrypt)) rfl s
    simp only [show (ecbCore .encrypt).bs = 16 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pub (M := byteMode) rfl h
  sat := by
    sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [fbSat, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using fbSat 1

theorem cfbDecryptFinal_verified : Verified Arm.target cfbDecryptFinal
    (Sig.scratchContract Arm.abi finalSig "scratch" .u64 9 (Curry.const (fun _ => True) _)
      (Proof.Modes.decFinalPost ciphAt 16 Arm.abi.ptrBits) true 752) :=
  seqFinal_verified (ecbSpec .encrypt) (cfbDecF_finalOk _ (by decide) (by decide) (by decide)) cfbDecryptFinalTaint
    cfbDecryptFinal_implies

theorem cfbEncryptFinalFrameSat : ∃ s, (Spec.Seed.cfbEncryptFinalContract Arm.abi 832).pre s := by
  implies_sat [Spec.Seed.cfbEncryptFinalContract, Spec.Seed.cfbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 1

/-- `cfbEncryptFinal`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbEncryptFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 cfbEncryptFinal)
      (Spec.Seed.cfbEncryptFinalContract Arm.abi 832) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Seed.cfbFinalSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Modes.encFinalPost ciphAt 16 Arm.abi.ptrBits) (wa := true) (stack := 752) (m := 0) (bytes := 80)
    cfbEncryptFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Modes.encFinalPostIn_local _ ciphAt_congr)
    (Proof.Modes.encFinalPost_local _) cfbEncryptFinalFrameSat

theorem cfbDecryptFinalFrameSat : ∃ s, (Spec.Seed.cfbDecryptFinalContract Arm.abi 832).pre s := by
  implies_sat [Spec.Seed.cfbDecryptFinalContract, Spec.Seed.cfbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 1

/-- `cfbDecryptFinal`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbDecryptFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 cfbDecryptFinal)
      (Spec.Seed.cfbDecryptFinalContract Arm.abi 832) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Seed.cfbFinalSig) (nm := "scratch") (e := .u64) (n := 9)
    (post := Proof.Modes.decFinalPost ciphAt 16 Arm.abi.ptrBits) (wa := true) (stack := 752) (m := 0) (bytes := 80)
    cfbDecryptFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Modes.decFinalPostIn_local _ ciphAt_congr)
    (Proof.Modes.decFinalPost_local _) cfbDecryptFinalFrameSat

end VG.Proof.Seed.Arm
