module

public import VerifiedGarbage.Proof.Blowfish.Arm.FbVerified
public import VerifiedGarbage.Proof.Modes.Arm.SeqFinalCT
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Impl.Blowfish.Arm.FbFinal
public import VerifiedGarbage.Spec.Blowfish.CfbFinal
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Blowfish.Arm.FbVerified
meta import VerifiedGarbage.Proof.Modes.Arm.SeqFinalCT
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Impl.Blowfish.Arm.FbFinal
meta import VerifiedGarbage.Spec.Blowfish.CfbFinal
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Blowfish.Schedule
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Blowfish-CFB64 of a message's last piece on ARMv7 meets its contracts

The generic CFB over a message's last piece (`Proof.Modes.Arm.seqFinal_verified`)
over Blowfish's ECB function (`ecbSpec true`) meets the contracts with a scratch
buffer of 7 words, as the whole-block functions do (`FbVerified.lean`), with
the specification's results (`Proof.Modes.Arm.cfbEncFinal_post`, …); the
`_framed` theorems keep the buffer on the stack, zeroed on return: 64 bytes
more.
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Impl.Blowfish.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

/-- Blowfish's cipher of the schedule at `k`. -/
abbrev ciphAt (m : Mem) (k : Addr) : Spec.Cbc.Cipher := Spec.Blowfish.cipher (Spec.Blowfish.scheduleAt m k)

/-- The final functions' signature. -/
abbrev finalSig : Sig := Proof.Modes.finalSig "schedule" .u8 4168 8

theorem ciphAt_congr {m₁ m₂ : Mem} {k : Addr}
    (h : ∀ i < 4168 * Elem.size .u8, m₂ (k + BitVec.ofNat 64 i) = m₁ (k + BitVec.ofNat 64 i)) :
    ciphAt m₂ k = ciphAt m₁ k := by
  simp only [ciphAt, Proof.Blowfish.scheduleAt_congr (m := m₁) (m' := m₂) h]

theorem cfbEncryptFinalTaint : FinalTaint (ecbCore true) cfbEnc :=
  ⟨cfbEncryptTaint.pro, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, cfbEncryptTaint.epi⟩

theorem cfbEncryptFinal_implies : (seqFinalArm (ecbCore true) (ecbSpec true) cfbEnc).Implies
    (Sig.scratchContract Arm.abi finalSig "scratch" .u64 7 (Curry.const (fun _ => True) _)
      (Proof.Modes.encFinalPost ciphAt 8 Arm.abi.ptrBits) true 256) where
  pre s h := seqArm_pre_rw (M := byteMode) rfl (len := fun n => n) (fun n => (Nat.mul_one n).symm) (by
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbEncFinal_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := (ecbCore true)) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, ↓reduceIte] at e
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
    (Sig.scratchContract Arm.abi finalSig "scratch" .u64 7 (Curry.const (fun _ => True) _)
      (Proof.Modes.encFinalPost ciphAt 8 Arm.abi.ptrBits) true 256) :=
  seqFinal_verified (ecbSpec true) (cfbEnc_finalOk _ (by decide) (by decide) (by decide)) cfbEncryptFinalTaint
    cfbEncryptFinal_implies

theorem cfbDecryptFinalTaint : FinalTaint (ecbCore true) cfbDecF :=
  ⟨cfbDecryptTaint.pro, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, cfbDecryptTaint.epi⟩

theorem cfbDecryptFinal_implies : (seqFinalArm (ecbCore true) (ecbSpec true) cfbDecF).Implies
    (Sig.scratchContract Arm.abi finalSig "scratch" .u64 7 (Curry.const (fun _ => True) _)
      (Proof.Modes.decFinalPost ciphAt 8 Arm.abi.ptrBits) true 256) where
  pre s h := seqArm_pre_rw (M := byteMode) rfl (len := fun n => n) (fun n => (Nat.mul_one n).symm) (by
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbDecFinal_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_plain (c := (ecbCore true)) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, dirCipher, State.addr, ↓reduceIte] at e
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
    (Sig.scratchContract Arm.abi finalSig "scratch" .u64 7 (Curry.const (fun _ => True) _)
      (Proof.Modes.decFinalPost ciphAt 8 Arm.abi.ptrBits) true 256) :=
  seqFinal_verified (ecbSpec true) (cfbDecF_finalOk _ (by decide) (by decide) (by decide)) cfbDecryptFinalTaint
    cfbDecryptFinal_implies

theorem cfbEncryptFinalFrameSat : ∃ s, (Spec.Blowfish.cfbEncryptFinalContract Arm.abi 320).pre s := by
  implies_sat [Spec.Blowfish.cfbEncryptFinalContract, Spec.Blowfish.cfbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 1

/-- `cfbEncryptFinal`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbEncryptFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cfbEncryptFinal)
      (Spec.Blowfish.cfbEncryptFinalContract Arm.abi 320) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbFinalSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.Modes.encFinalPost ciphAt 8 Arm.abi.ptrBits) (wa := true) (stack := 256) (m := 0) (bytes := 64)
    cfbEncryptFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Modes.encFinalPostIn_local _ ciphAt_congr)
    (Proof.Modes.encFinalPost_local _) cfbEncryptFinalFrameSat

theorem cfbDecryptFinalFrameSat : ∃ s, (Spec.Blowfish.cfbDecryptFinalContract Arm.abi 320).pre s := by
  implies_sat [Spec.Blowfish.cfbDecryptFinalContract, Spec.Blowfish.cfbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat] using fbFrameSat 1

/-- `cfbDecryptFinal`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbDecryptFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 cfbDecryptFinal)
      (Spec.Blowfish.cfbDecryptFinalContract Arm.abi 320) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbFinalSig) (nm := "scratch") (e := .u64) (n := 7)
    (post := Proof.Modes.decFinalPost ciphAt 8 Arm.abi.ptrBits) (wa := true) (stack := 256) (m := 0) (bytes := 64)
    cfbDecryptFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Modes.decFinalPostIn_local _ ciphAt_congr)
    (Proof.Modes.decFinalPost_local _) cfbDecryptFinalFrameSat

end VG.Proof.Blowfish.Arm
