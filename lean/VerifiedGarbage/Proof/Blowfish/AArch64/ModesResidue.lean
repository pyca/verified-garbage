module

public import VerifiedGarbage.Proof.Blowfish.AArch64.Frame
public meta import VerifiedGarbage.Proof.Blowfish.AArch64.Frame
public import VerifiedGarbage.Proof.Blowfish.AArch64.Verified
public meta import VerifiedGarbage.Proof.Blowfish.AArch64.Verified
public import VerifiedGarbage.Proof.Blowfish.AArch64.CbcVerified
public meta import VerifiedGarbage.Proof.Blowfish.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
public meta import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalVerified
public meta import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalVerified
public import VerifiedGarbage.Impl.Residue.AArch64
public meta import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Blowfish.AArch64.Lit
meta import VerifiedGarbage.Proof.Blowfish.AArch64.Lit
import VerifiedGarbage.Proof.Blowfish.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Blowfish.AArch64.ModesLit
import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalLit
meta import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# Blowfish's modes on AArch64 return without secret residue

`vg_blowfish_ecb_*` and the CBC, CFB64 and OFB functions run in a frame
whose scratch words they zero (`withStackScratchWiped`). The analysis of the
window's bytes (`rtaintG`) finds every byte of their frames the same in both
runs on return: they need no clearing of the stack, only of what they leave
in their registers (`modeClears`, and for ECB the high halves of `v8`–`v15`
too, from `x6` once it is zero). `RTaintG.noResidue_of_doneG` proves they
then leave nothing secret.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64.ModesResidue

open VG VG.AArch64 VG.Impl.Residue.AArch64 VG.AArch64.RTaintG

/-- `c`, then the registers a mode leaves secret cleared, the scratch register `xs` among them. -/
abbrev modeCleared (xs : Reg) (c : Prog isa) : Prog isa :=
  withClears [.x6, xs] [.v0, .v1, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v28, .v29, .v30, .v31] none c

abbrev ecbCleared (c : Prog isa) : Prog isa :=
  withClearsHi [.x6, .x10] [.v0, .v1, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v28, .v29, .v30, .v31] none .x6 [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15] c

/-! ## ECB -/

abbrev ecbEncryptCode : Prog isa :=
  ecbCleared (Impl.StackScratch.AArch64.withStackScratchWiped 256 .x3 32 Impl.Blowfish.AArch64.encrypt)

abbrev ecbDecryptCode : Prog isa :=
  ecbCleared (Impl.StackScratch.AArch64.withStackScratchWiped 256 .x3 32 Impl.Blowfish.AArch64.decrypt)

theorem ecbEncryptCode_verified :
    Verified AArch64.target ecbEncryptCode (Spec.Blowfish.ecbContract AArch64.abi .encrypt 256) :=
  Clears.Verified.withClears (ecb_framed encrypt_verified) (by decide)

theorem ecbDecryptCode_verified :
    Verified AArch64.target ecbDecryptCode (Spec.Blowfish.ecbContract AArch64.abi .decrypt 256) :=
  Clears.Verified.withClears (ecb_framed decrypt_verified) (by decide)

theorem ecbEncryptCode_noResidue :
    NoResidue ecbEncryptCode (Spec.Blowfish.ecbContract AArch64.abi .encrypt 256) 0 :=
  noResidue_of_doneG ecbEncryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Blowfish.ecbSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

theorem ecbDecryptCode_noResidue :
    NoResidue ecbDecryptCode (Spec.Blowfish.ecbContract AArch64.abi .decrypt 256) 0 :=
  noResidue_of_doneG ecbDecryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Blowfish.ecbSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-! ## CBC, CFB64 and OFB -/

abbrev cbcEncryptChainedCode : Prog isa :=
  modeCleared .x7 (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cbcEncryptChained)

theorem cbcEncryptChainedCode_verified : Verified AArch64.target cbcEncryptChainedCode (Spec.Blowfish.cbcEncryptChainedContract AArch64.abi 224) :=
  Clears.Verified.withClears cbcEncryptChained_framed (by decide)

theorem cbcEncryptChainedCode_noResidue : NoResidue cbcEncryptChainedCode (Spec.Blowfish.cbcEncryptChainedContract AArch64.abi 224) 0 :=
  noResidue_of_doneG cbcEncryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Blowfish.cbcChainedSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

abbrev cbcDecryptChainedCode : Prog isa :=
  withClears [.x6, .x8, .x9] [.v0, .v1, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v28, .v29, .v30, .v31] none (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cbcDecryptChained)

theorem cbcDecryptChainedCode_verified : Verified AArch64.target cbcDecryptChainedCode (Spec.Blowfish.cbcDecryptChainedContract AArch64.abi 224) :=
  Clears.Verified.withClears cbcDecryptChained_framed (by decide)

theorem cbcDecryptChainedCode_noResidue : NoResidue cbcDecryptChainedCode (Spec.Blowfish.cbcDecryptChainedContract AArch64.abi 224) 0 :=
  noResidue_of_doneG cbcDecryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Blowfish.cbcChainedSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

abbrev cfbEncryptCode : Prog isa :=
  modeCleared .x7 (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbEncrypt)

theorem cfbEncryptCode_verified : Verified AArch64.target cfbEncryptCode (Spec.Blowfish.cfbEncryptContract AArch64.abi 224) :=
  Clears.Verified.withClears cfbEncrypt_framed (by decide)

theorem cfbEncryptCode_noResidue : NoResidue cfbEncryptCode (Spec.Blowfish.cfbEncryptContract AArch64.abi 224) 0 :=
  noResidue_of_doneG cfbEncryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Blowfish.cfbSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

abbrev cfbDecryptCode : Prog isa :=
  modeCleared .x7 (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbDecrypt)

theorem cfbDecryptCode_verified : Verified AArch64.target cfbDecryptCode (Spec.Blowfish.cfbDecryptContract AArch64.abi 224) :=
  Clears.Verified.withClears cfbDecrypt_framed (by decide)

theorem cfbDecryptCode_noResidue : NoResidue cfbDecryptCode (Spec.Blowfish.cfbDecryptContract AArch64.abi 224) 0 :=
  noResidue_of_doneG cfbDecryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Blowfish.cfbSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

abbrev cfbEncryptFinalCode : Prog isa :=
  modeCleared .x7 (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbEncryptFinal)

theorem cfbEncryptFinalCode_verified : Verified AArch64.target cfbEncryptFinalCode (Spec.Blowfish.cfbEncryptFinalContract AArch64.abi 224) :=
  Clears.Verified.withClears cfbEncryptFinal_framed (by decide)

theorem cfbEncryptFinalCode_noResidue : NoResidue cfbEncryptFinalCode (Spec.Blowfish.cfbEncryptFinalContract AArch64.abi 224) 0 :=
  noResidue_of_doneG cfbEncryptFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Blowfish.cfbFinalSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

abbrev cfbDecryptFinalCode : Prog isa :=
  modeCleared .x7 (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbDecryptFinal)

theorem cfbDecryptFinalCode_verified : Verified AArch64.target cfbDecryptFinalCode (Spec.Blowfish.cfbDecryptFinalContract AArch64.abi 224) :=
  Clears.Verified.withClears cfbDecryptFinal_framed (by decide)

theorem cfbDecryptFinalCode_noResidue : NoResidue cfbDecryptFinalCode (Spec.Blowfish.cfbDecryptFinalContract AArch64.abi 224) 0 :=
  noResidue_of_doneG cfbDecryptFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Blowfish.cfbFinalSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

abbrev ofbCode : Prog isa :=
  modeCleared .x7 (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.ofb)

theorem ofbCode_verified : Verified AArch64.target ofbCode (Spec.Blowfish.ofbContract AArch64.abi 224) :=
  Clears.Verified.withClears ofb_framed (by decide)

theorem ofbCode_noResidue : NoResidue ofbCode (Spec.Blowfish.ofbContract AArch64.abi 224) 0 :=
  noResidue_of_doneG ofbCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Blowfish.ofbSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

abbrev ofbFinalCode : Prog isa :=
  modeCleared .x7 (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.ofbFinal)

theorem ofbFinalCode_verified : Verified AArch64.target ofbFinalCode (Spec.Blowfish.ofbFinalContract AArch64.abi 224) :=
  Clears.Verified.withClears ofbFinal_framed (by decide)

theorem ofbFinalCode_noResidue : NoResidue ofbFinalCode (Spec.Blowfish.ofbFinalContract AArch64.abi 224) 0 :=
  noResidue_of_doneG ofbFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Blowfish.ofbFinalSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

end VG.Proof.Blowfish.AArch64.ModesResidue
