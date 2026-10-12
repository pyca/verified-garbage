import VerifiedGarbage.Proof.Cast5.Arm.ModeCore
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe

/-!
# CAST5-CBC, CAST5-OFB and CAST5-CFB64 on ARMv7 meet their contracts

The generic modes one block at a time over CAST5's ECB functions
(`Proof.Modes.Arm.seq_verified` with `ecbSpec`, a core taking the number of
rounds and its working space as a stack argument) meet the contracts with a
scratch buffer of 39 words (`Proof.Cast5.modeScratchContract`): the modes'
72 bytes, then the 256 bytes the ECB function works in. The ECB functions use
no stack of their own, so the modes need only the 8 bytes their push of that
working space takes. The `_framed` theorems keep the buffer on the stack,
zeroed on return: 328 bytes more.
-/

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Impl.Cast5.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm

theorem blocksOf_eq' (m : Mem) (p : Addr) (n : Nat) :
    VG.Proof.Modes.blocksOf 8 m p n = Spec.Cast5.cbcBlocksAt m p n :=
  (Proof.Cast5.cbcBlocksAt_eq m p n).symm

/-- A state satisfying the precondition with the scratch buffer (no
blocks): the subkeys at `0x1000`, 12 rounds, the IV at `0x2000`, the data at
`0x3000`, and `n` and the scratch buffer's address `0` (the stack
arguments, in memory that is zero); the IV read (`ivW = false`) or read and
written. -/
def modeSat (ivW : Bool) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 12 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := if ivW then [⟨0x1000, 128⟩, ⟨0x8000, 8⟩] else [⟨0x1000, 128⟩, ⟨0x2000, 8⟩, ⟨0x8000, 8⟩]
  wr := if ivW then [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0, 312⟩] else [⟨0x3000, 0⟩, ⟨0, 312⟩]

/-- A state satisfying the functions' precondition (no blocks). -/
def frameSat (ivW : Bool) : State :=
  { modeSat ivW with
    rd := if ivW then [⟨0x1000, 128⟩, ⟨0x8000, 4⟩] else [⟨0x1000, 128⟩, ⟨0x2000, 8⟩, ⟨0x8000, 4⟩]
    wr := if ivW then [⟨0x2000, 8⟩, ⟨0x3000, 0⟩] else [⟨0x3000, 0⟩] }

theorem cbcEncryptTaint : SeqTaint (ecbCore true) cbcEnc :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cbcEncrypt_implies : (seqArm (ecbCore true) (ecbSpec true) cbcEnc).Implies
    (Proof.Cast5.modeScratchContract Arm.abi Spec.Cast5.cbcSig 39 (Spec.Cast5.cbcPre Arm.abi.ptrBits)
      (Proof.Cast5.cbcEncPost Arm.abi.ptrBits) 8) where
  pre s h := seqArm_pre_roR rfl rfl rfl (by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cbcSig, Spec.Cast5.cbcPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cbcSig, Proof.Cast5.cbcEncPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcEnc_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore true) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, Proof.Cast5.dirCipher, ↓reduceIte, State.addr, blocksOf_eq'] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cbcSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pubR h
  sat := by
    sig_implies_sat [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cbcSig, Spec.Cast5.cbcPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Curry.app]
      [modeSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using modeSat false

theorem cbcEncrypt_verified : Verified Arm.target cbcEncrypt
    (Proof.Cast5.modeScratchContract Arm.abi Spec.Cast5.cbcSig 39 (Spec.Cast5.cbcPre Arm.abi.ptrBits)
      (Proof.Cast5.cbcEncPost Arm.abi.ptrBits) 8) :=
  seq_verified (ecbSpec true) (cbcEnc_ok _) cbcEncryptTaint cbcEncrypt_implies

theorem cbcEncryptFrameSat : ∃ s, (Spec.Cast5.cbcEncryptContract Arm.abi 336).pre s := by
  implies_sat [Spec.Cast5.cbcEncryptContract, Spec.Cast5.cbcSig, Spec.Cast5.cbcPre, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [frameSat, modeSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using frameSat false

/-- `cbcEncrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cbcEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 cbcEncrypt)
      (Spec.Cast5.cbcEncryptContract Arm.abi 336) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Cast5.cbcSig) (nm := "scratch") (e := .u64) (n := 39)
    (pre := Spec.Cast5.cbcPre Arm.abi.ptrBits) (post := Proof.Cast5.cbcEncPost Arm.abi.ptrBits)
    (wa := true) (stack := 8) (m := 1) (bytes := 328)
    cbcEncrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h) (Proof.Cast5.cbcEncPost_local _)
    (Proof.Cast5.cbcEncPostOut_local _) cbcEncryptFrameSat

theorem cbcDecryptTaint : SeqTaint (ecbCore false) cbcDec :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cbcDecrypt_implies : (seqArm (ecbCore false) (ecbSpec false) cbcDec).Implies
    (Proof.Cast5.modeScratchContract Arm.abi Spec.Cast5.cbcSig 39 (Spec.Cast5.cbcPre Arm.abi.ptrBits)
      (Proof.Cast5.cbcDecPost Arm.abi.ptrBits) 8) where
  pre s h := seqArm_pre_roR rfl rfl rfl (by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cbcSig, Spec.Cast5.cbcPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cbcSig, Proof.Cast5.cbcDecPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cbcDec_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore false) rfl s
    simp only [show (ecbCore false).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, Proof.Cast5.dirCipher, Bool.false_eq_true, ↓reduceIte, State.addr, blocksOf_eq'] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cbcSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pubR h
  sat := by
    sig_implies_sat [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cbcSig, Spec.Cast5.cbcPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Curry.app]
      [modeSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using modeSat false

theorem cbcDecrypt_verified : Verified Arm.target cbcDecrypt
    (Proof.Cast5.modeScratchContract Arm.abi Spec.Cast5.cbcSig 39 (Spec.Cast5.cbcPre Arm.abi.ptrBits)
      (Proof.Cast5.cbcDecPost Arm.abi.ptrBits) 8) :=
  seq_verified (ecbSpec false) (cbcDec_ok _) cbcDecryptTaint cbcDecrypt_implies

theorem cbcDecryptFrameSat : ∃ s, (Spec.Cast5.cbcDecryptContract Arm.abi 336).pre s := by
  implies_sat [Spec.Cast5.cbcDecryptContract, Spec.Cast5.cbcSig, Spec.Cast5.cbcPre, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [frameSat, modeSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using frameSat false

/-- `cbcDecrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cbcDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 cbcDecrypt)
      (Spec.Cast5.cbcDecryptContract Arm.abi 336) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Cast5.cbcSig) (nm := "scratch") (e := .u64) (n := 39)
    (pre := Spec.Cast5.cbcPre Arm.abi.ptrBits) (post := Proof.Cast5.cbcDecPost Arm.abi.ptrBits)
    (wa := true) (stack := 8) (m := 1) (bytes := 328)
    cbcDecrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h) (Proof.Cast5.cbcDecPost_local _)
    (Proof.Cast5.cbcDecPostOut_local _) cbcDecryptFrameSat

theorem ofbTaint : SeqTaint (ecbCore true) VG.Impl.Modes.Arm.ofb :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem ofb_implies : (seqArm (ecbCore true) (ecbSpec true) VG.Impl.Modes.Arm.ofb).Implies
    (Proof.Cast5.modeScratchContract Arm.abi Spec.Cast5.ofbSig 39 (Spec.Cast5.ofbPre Arm.abi.ptrBits)
      (Proof.Cast5.ofbPost Arm.abi.ptrBits) 8) where
  pre s h := seqArm_pre_rwR rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.ofbSig, Proof.Cast5.ofbPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := ofb_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore true) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, Proof.Cast5.dirCipher, ↓reduceIte, State.addr, blocksOf_eq'] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pubR h
  sat := by
    sig_implies_sat [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Curry.app]
      [modeSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using modeSat true

theorem ofb_verified : Verified Arm.target ofb
    (Proof.Cast5.modeScratchContract Arm.abi Spec.Cast5.ofbSig 39 (Spec.Cast5.ofbPre Arm.abi.ptrBits)
      (Proof.Cast5.ofbPost Arm.abi.ptrBits) 8) :=
  seq_verified (ecbSpec true) (ofb_ok _) ofbTaint ofb_implies

theorem ofbFrameSat : ∃ s, (Spec.Cast5.ofbContract Arm.abi 336).pre s := by
  implies_sat [Spec.Cast5.ofbContract, Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [frameSat, modeSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using frameSat true

/-- `ofb`, with its scratch buffer on the stack (zeroed on return). -/
theorem ofb_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 ofb)
      (Spec.Cast5.ofbContract Arm.abi 336) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Cast5.ofbSig) (nm := "scratch") (e := .u64) (n := 39)
    (pre := Spec.Cast5.ofbPre Arm.abi.ptrBits) (post := Proof.Cast5.ofbPost Arm.abi.ptrBits)
    (wa := true) (stack := 8) (m := 1) (bytes := 328)
    ofb_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h) (Proof.Cast5.ofbPost_local _)
    (Proof.Cast5.ofbPostOut_local _) ofbFrameSat

theorem cfbEncryptTaint : SeqTaint (ecbCore true) cfbEnc :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfbEncrypt_implies : (seqArm (ecbCore true) (ecbSpec true) cfbEnc).Implies
    (Proof.Cast5.modeScratchContract Arm.abi Spec.Cast5.cfbSig 39 (Spec.Cast5.cfbPre Arm.abi.ptrBits)
      (Proof.Cast5.cfbEncPost Arm.abi.ptrBits) 8) where
  pre s h := seqArm_pre_rwR rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cfbSig, Proof.Cast5.cfbEncPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbEnc_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore true) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, Proof.Cast5.dirCipher, ↓reduceIte, State.addr, blocksOf_eq'] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pubR h
  sat := by
    sig_implies_sat [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Curry.app]
      [modeSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using modeSat true

theorem cfbEncrypt_verified : Verified Arm.target cfbEncrypt
    (Proof.Cast5.modeScratchContract Arm.abi Spec.Cast5.cfbSig 39 (Spec.Cast5.cfbPre Arm.abi.ptrBits)
      (Proof.Cast5.cfbEncPost Arm.abi.ptrBits) 8) :=
  seq_verified (ecbSpec true) (cfbEnc_ok _) cfbEncryptTaint cfbEncrypt_implies

theorem cfbEncryptFrameSat : ∃ s, (Spec.Cast5.cfbEncryptContract Arm.abi 336).pre s := by
  implies_sat [Spec.Cast5.cfbEncryptContract, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [frameSat, modeSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using frameSat true

/-- `cfbEncrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 cfbEncrypt)
      (Spec.Cast5.cfbEncryptContract Arm.abi 336) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Cast5.cfbSig) (nm := "scratch") (e := .u64) (n := 39)
    (pre := Spec.Cast5.cfbPre Arm.abi.ptrBits) (post := Proof.Cast5.cfbEncPost Arm.abi.ptrBits)
    (wa := true) (stack := 8) (m := 1) (bytes := 328)
    cfbEncrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h) (Proof.Cast5.cfbEncPost_local _)
    (Proof.Cast5.cfbEncPostOut_local _) cfbEncryptFrameSat

theorem cfbDecryptTaint : SeqTaint (ecbCore true) cfbDec :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfbDecrypt_implies : (seqArm (ecbCore true) (ecbSpec true) cfbDec).Implies
    (Proof.Cast5.modeScratchContract Arm.abi Spec.Cast5.cfbSig 39 (Spec.Cast5.cfbPre Arm.abi.ptrBits)
      (Proof.Cast5.cfbDecPost Arm.abi.ptrBits) 8) where
  pre s h := seqArm_pre_rwR rfl (len := (· * 8)) (fun n => rfl) (by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h)
  post s s' _ h := by
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cfbSig, Proof.Cast5.cfbDecPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbDec_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore true) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, Proof.Cast5.dirCipher, ↓reduceIte, State.addr, blocksOf_eq'] at e
    exact e
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cfbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pubR h
  sat := by
    sig_implies_sat [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Curry.app]
      [modeSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using modeSat true

theorem cfbDecrypt_verified : Verified Arm.target cfbDecrypt
    (Proof.Cast5.modeScratchContract Arm.abi Spec.Cast5.cfbSig 39 (Spec.Cast5.cfbPre Arm.abi.ptrBits)
      (Proof.Cast5.cfbDecPost Arm.abi.ptrBits) 8) :=
  seq_verified (ecbSpec true) (cfbDec_ok _) cfbDecryptTaint cfbDecrypt_implies

theorem cfbDecryptFrameSat : ∃ s, (Spec.Cast5.cfbDecryptContract Arm.abi 336).pre s := by
  implies_sat [Spec.Cast5.cfbDecryptContract, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [frameSat, modeSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using frameSat true

/-- `cfbDecrypt`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 cfbDecrypt)
      (Spec.Cast5.cfbDecryptContract Arm.abi 336) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Cast5.cfbSig) (nm := "scratch") (e := .u64) (n := 39)
    (pre := Spec.Cast5.cfbPre Arm.abi.ptrBits) (post := Proof.Cast5.cfbDecPost Arm.abi.ptrBits)
    (wa := true) (stack := 8) (m := 1) (bytes := 328)
    cfbDecrypt_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h) (Proof.Cast5.cfbDecPost_local _)
    (Proof.Cast5.cfbDecPostOut_local _) cfbDecryptFrameSat

end VG.Proof.Cast5.Arm
