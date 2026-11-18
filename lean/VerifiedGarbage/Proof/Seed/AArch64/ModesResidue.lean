module

public import VerifiedGarbage.Impl.Residue.AArch64
public meta import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public import VerifiedGarbage.Proof.Seed.AArch64.CbcVerified
public meta import VerifiedGarbage.Proof.Seed.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Seed.AArch64.EcbCall
public meta import VerifiedGarbage.Proof.Seed.AArch64.EcbCall
public import VerifiedGarbage.Proof.Seed.AArch64.FbFinalVerified
public meta import VerifiedGarbage.Proof.Seed.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Seed.AArch64.FbVerified
public meta import VerifiedGarbage.Proof.Seed.AArch64.FbVerified
public import VerifiedGarbage.Proof.Seed.AArch64.Frame
public meta import VerifiedGarbage.Proof.Seed.AArch64.Frame
public import VerifiedGarbage.Proof.Seed.AArch64.Verified
public meta import VerifiedGarbage.Proof.Seed.AArch64.Verified
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Seed.AArch64.FbFinalLit
meta import VerifiedGarbage.Proof.Seed.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Seed.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Seed.AArch64.ModesLit

/-!
# SEED on AArch64 returns without secret residue

SEED's key expansion and its CBC, CFB128 and OFB functions run in frames of
976 and 1456 bytes whose scratch words they zero (`withStackScratchWiped`).
The analysis of the window's bytes (`rtaintG`) finds every byte of those
frames the same in both runs on return, so they need no clearing of the
stack (`noResidue_of_doneG`), only of what they leave in their registers,
`x9` and `v31` among them where the analysis finds them secret.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64.ModesResidue

open VG VG.AArch64 VG.Impl.Residue.AArch64 VG.AArch64.RTaintG

/-- `vg_seed_expand_key`. -/
abbrev expandKeyCode : Prog isa :=
  withClears [.x4, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14]
    [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 976 .x2 122 Impl.Seed.AArch64.expandKey)

theorem expandKeyCode_verified : Verified AArch64.target expandKeyCode (Spec.Seed.expandKeyContract AArch64.abi 976) :=
  Clears.Verified.withClears (Proof.Seed.AArch64.expandKey_framed) (by decide)

theorem expandKeyCode_noResidue : NoResidue expandKeyCode (Spec.Seed.expandKeyContract AArch64.abi 976) 0 :=
  noResidue_of_doneG expandKeyCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Seed.expandKeyApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_seed_cbc_encrypt_chained`. -/
abbrev cbcEncryptChainedCode : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cbcEncryptChained))

theorem cbcEncryptChainedCode_verified : Verified AArch64.target cbcEncryptChainedCode (Spec.Seed.cbcEncryptChainedContract AArch64.abi 1456) :=
  RTaintF.Verified.withRet (Clears.Verified.withClears (Proof.Seed.AArch64.cbcEncryptChained_framed) (by decide))

theorem cbcEncryptChainedCode_noResidue : NoResidue cbcEncryptChainedCode (Spec.Seed.cbcEncryptChainedContract AArch64.abi 1456) 0 :=
  noResidue_of_doneG cbcEncryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Seed.cbcEncryptChainedApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_seed_cbc_decrypt_chained`. -/
abbrev cbcDecryptChainedCode : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x8, .x9, .x10, .x11, .x12]
    [.v0, .v1, .v3, .v27, .v28, .v29, .v30] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cbcDecryptChained))

theorem cbcDecryptChainedCode_verified : Verified AArch64.target cbcDecryptChainedCode (Spec.Seed.cbcDecryptChainedContract AArch64.abi 1456) :=
  RTaintF.Verified.withRet (Clears.Verified.withClears (Proof.Seed.AArch64.cbcDecryptChained_framed) (by decide))

theorem cbcDecryptChainedCode_noResidue : NoResidue cbcDecryptChainedCode (Spec.Seed.cbcDecryptChainedContract AArch64.abi 1456) 0 :=
  noResidue_of_doneG cbcDecryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Seed.cbcDecryptChainedApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_seed_cfb128_encrypt`. -/
abbrev cfbEncryptCode : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cfbEncrypt))

theorem cfbEncryptCode_verified : Verified AArch64.target cfbEncryptCode (Spec.Seed.cfbEncryptContract AArch64.abi 1456) :=
  RTaintF.Verified.withRet (Clears.Verified.withClears (Proof.Seed.AArch64.cfbEncrypt_framed) (by decide))

theorem cfbEncryptCode_noResidue : NoResidue cfbEncryptCode (Spec.Seed.cfbEncryptContract AArch64.abi 1456) 0 :=
  noResidue_of_doneG cfbEncryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Seed.cfbEncryptApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_seed_cfb128_decrypt`. -/
abbrev cfbDecryptCode : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v3, .v27, .v28, .v29, .v30] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cfbDecrypt))

theorem cfbDecryptCode_verified : Verified AArch64.target cfbDecryptCode (Spec.Seed.cfbDecryptContract AArch64.abi 1456) :=
  RTaintF.Verified.withRet (Clears.Verified.withClears (Proof.Seed.AArch64.cfbDecrypt_framed) (by decide))

theorem cfbDecryptCode_noResidue : NoResidue cfbDecryptCode (Spec.Seed.cfbDecryptContract AArch64.abi 1456) 0 :=
  noResidue_of_doneG cfbDecryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Seed.cfbDecryptApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_seed_cfb128_encrypt_final`. -/
abbrev cfbEncryptFinalCode : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cfbEncryptFinal))

theorem cfbEncryptFinalCode_verified : Verified AArch64.target cfbEncryptFinalCode (Spec.Seed.cfbEncryptFinalContract AArch64.abi 1456) :=
  RTaintF.Verified.withRet (Clears.Verified.withClears (Proof.Seed.AArch64.cfbEncryptFinal_framed) (by decide))

theorem cfbEncryptFinalCode_noResidue : NoResidue cfbEncryptFinalCode (Spec.Seed.cfbEncryptFinalContract AArch64.abi 1456) 0 :=
  noResidue_of_doneG cfbEncryptFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Seed.cfbEncryptFinalApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_seed_cfb128_decrypt_final`. -/
abbrev cfbDecryptFinalCode : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cfbDecryptFinal))

theorem cfbDecryptFinalCode_verified : Verified AArch64.target cfbDecryptFinalCode (Spec.Seed.cfbDecryptFinalContract AArch64.abi 1456) :=
  RTaintF.Verified.withRet (Clears.Verified.withClears (Proof.Seed.AArch64.cfbDecryptFinal_framed) (by decide))

theorem cfbDecryptFinalCode_noResidue : NoResidue cfbDecryptFinalCode (Spec.Seed.cfbDecryptFinalContract AArch64.abi 1456) 0 :=
  noResidue_of_doneG cfbDecryptFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Seed.cfbDecryptFinalApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_seed_ofb`. -/
abbrev ofbCode : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.ofb))

theorem ofbCode_verified : Verified AArch64.target ofbCode (Spec.Seed.ofbContract AArch64.abi 1456) :=
  RTaintF.Verified.withRet (Clears.Verified.withClears (Proof.Seed.AArch64.ofb_framed) (by decide))

theorem ofbCode_noResidue : NoResidue ofbCode (Spec.Seed.ofbContract AArch64.abi 1456) 0 :=
  noResidue_of_doneG ofbCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Seed.ofbApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_seed_ofb_final`. -/
abbrev ofbFinalCode : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.ofbFinal))

theorem ofbFinalCode_verified : Verified AArch64.target ofbFinalCode (Spec.Seed.ofbFinalContract AArch64.abi 1456) :=
  RTaintF.Verified.withRet (Clears.Verified.withClears (Proof.Seed.AArch64.ofbFinal_framed) (by decide))

theorem ofbFinalCode_noResidue : NoResidue ofbFinalCode (Spec.Seed.ofbFinalContract AArch64.abi 1456) 0 :=
  noResidue_of_doneG ofbFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Seed.ofbFinalApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

end VG.Proof.Seed.AArch64.ModesResidue
