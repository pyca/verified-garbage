module

public import VerifiedGarbage.Proof.Camellia.AArch64.KeyVerified
public meta import VerifiedGarbage.Proof.Camellia.AArch64.KeyVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.Verified
public meta import VerifiedGarbage.Proof.Camellia.AArch64.Verified
public import VerifiedGarbage.Proof.Camellia.AArch64.CbcVerified
public meta import VerifiedGarbage.Proof.Camellia.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
public meta import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalVerified
public meta import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.CtrVerified
public meta import VerifiedGarbage.Proof.Camellia.AArch64.CtrVerified
public import VerifiedGarbage.Impl.Residue.AArch64
public meta import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Camellia.AArch64.Lit
meta import VerifiedGarbage.Proof.Camellia.AArch64.Lit
import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
meta import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalLit
meta import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# Camellia on AArch64 returns without secret residue

Camellia's key expansion and its ECB, CBC, CFB128, CTR and OFB functions run
in frames whose scratch words they zero (`withStackScratchWiped`): 160 bytes
for the key expansion and over 3 KB for the modes. The analysis of the
window's bytes (`rtaintG`) finds every byte of those frames the same in both
runs on return, so they need no clearing of the stack (`noResidue_of_doneG`),
only of what they leave in their registers.
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64.Residue

open VG VG.AArch64 VG.Impl.Residue.AArch64 VG.AArch64.RTaintG

/-- `vg_camellia_expand_key`. -/
abbrev expandKeyCode : Prog isa :=
  withClears [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 160 .x3 20 Impl.Camellia.AArch64.expandKey)

theorem expandKeyCode_verified : Verified AArch64.target expandKeyCode (Spec.Camellia.expandKeyContract AArch64.abi 160) :=
  Clears.Verified.withClears expandKey_framed (by decide)

theorem expandKeyCode_noResidue : NoResidue expandKeyCode (Spec.Camellia.expandKeyContract AArch64.abi 160) 0 :=
  noResidue_of_doneG expandKeyCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Camellia.expandKeySig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_ecb_encrypt`. -/
abbrev ecbEncryptCode : Prog isa :=
  withClears [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x4 406 (Impl.Camellia.AArch64.ecb .encrypt))

theorem ecbEncryptCode_verified : Verified AArch64.target ecbEncryptCode (Spec.Camellia.ecbContract AArch64.abi (specDir .encrypt) 3248) :=
  Clears.Verified.withClears (ecb_framed .encrypt) (by decide)

theorem ecbEncryptCode_noResidue : NoResidue ecbEncryptCode (Spec.Camellia.ecbContract AArch64.abi (specDir .encrypt) 3248) 0 :=
  noResidue_of_doneG ecbEncryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Camellia.ecbSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_ecb_decrypt`. -/
abbrev ecbDecryptCode : Prog isa :=
  withClears [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x4 406 (Impl.Camellia.AArch64.ecb .decrypt))

theorem ecbDecryptCode_verified : Verified AArch64.target ecbDecryptCode (Spec.Camellia.ecbContract AArch64.abi (specDir .decrypt) 3248) :=
  Clears.Verified.withClears (ecb_framed .decrypt) (by decide)

theorem ecbDecryptCode_noResidue : NoResidue ecbDecryptCode (Spec.Camellia.ecbContract AArch64.abi (specDir .decrypt) 3248) 0 :=
  noResidue_of_doneG ecbDecryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Camellia.ecbSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_cbc_encrypt_chained`. -/
abbrev cbcEncryptChainedCode : Prog isa :=
  withClears [.x6, .x7, .x8, .x10, .x11, .x12]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cbcEncryptChained)

theorem cbcEncryptChainedCode_verified : Verified AArch64.target cbcEncryptChainedCode (Spec.Camellia.cbcEncryptChainedContract AArch64.abi 3344) :=
  Clears.Verified.withClears cbcEncryptChained_framed (by decide)

theorem cbcEncryptChainedCode_noResidue : NoResidue cbcEncryptChainedCode (Spec.Camellia.cbcEncryptChainedContract AArch64.abi 3344) 0 :=
  noResidue_of_doneG cbcEncryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Camellia.cbcChainedSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_cbc_decrypt_chained`. -/
abbrev cbcDecryptChainedCode : Prog isa :=
  withClears [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cbcDecryptChained)

theorem cbcDecryptChainedCode_verified : Verified AArch64.target cbcDecryptChainedCode (Spec.Camellia.cbcDecryptChainedContract AArch64.abi 3344) :=
  Clears.Verified.withClears cbcDecryptChained_framed (by decide)

theorem cbcDecryptChainedCode_noResidue : NoResidue cbcDecryptChainedCode (Spec.Camellia.cbcDecryptChainedContract AArch64.abi 3344) 0 :=
  noResidue_of_doneG cbcDecryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Camellia.cbcChainedSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_cfb128_encrypt`. -/
abbrev cfbEncryptCode : Prog isa :=
  withClears [.x6, .x7, .x8, .x10, .x11, .x12]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cfbEncrypt)

theorem cfbEncryptCode_verified : Verified AArch64.target cfbEncryptCode (Spec.Camellia.cfbEncryptContract AArch64.abi 3344) :=
  Clears.Verified.withClears cfbEncrypt_framed (by decide)

theorem cfbEncryptCode_noResidue : NoResidue cfbEncryptCode (Spec.Camellia.cfbEncryptContract AArch64.abi 3344) 0 :=
  noResidue_of_doneG cfbEncryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Camellia.cfbSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_cfb128_decrypt`. -/
abbrev cfbDecryptCode : Prog isa :=
  withClears [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cfbDecrypt)

theorem cfbDecryptCode_verified : Verified AArch64.target cfbDecryptCode (Spec.Camellia.cfbDecryptContract AArch64.abi 3344) :=
  Clears.Verified.withClears cfbDecrypt_framed (by decide)

theorem cfbDecryptCode_noResidue : NoResidue cfbDecryptCode (Spec.Camellia.cfbDecryptContract AArch64.abi 3344) 0 :=
  noResidue_of_doneG cfbDecryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Camellia.cfbSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_cfb128_encrypt_final`. -/
abbrev cfbEncryptFinalCode : Prog isa :=
  withClears [.x6, .x7, .x10, .x11, .x12]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cfbEncryptFinal)

theorem cfbEncryptFinalCode_verified : Verified AArch64.target cfbEncryptFinalCode (Spec.Camellia.cfbEncryptFinalContract AArch64.abi 3344) :=
  Clears.Verified.withClears cfbEncryptFinal_framed (by decide)

theorem cfbEncryptFinalCode_noResidue : NoResidue cfbEncryptFinalCode (Spec.Camellia.cfbEncryptFinalContract AArch64.abi 3344) 0 :=
  noResidue_of_doneG cfbEncryptFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Camellia.cfbFinalSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_cfb128_decrypt_final`. -/
abbrev cfbDecryptFinalCode : Prog isa :=
  withClears [.x6, .x7, .x10, .x11, .x12]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cfbDecryptFinal)

theorem cfbDecryptFinalCode_verified : Verified AArch64.target cfbDecryptFinalCode (Spec.Camellia.cfbDecryptFinalContract AArch64.abi 3344) :=
  Clears.Verified.withClears cfbDecryptFinal_framed (by decide)

theorem cfbDecryptFinalCode_noResidue : NoResidue cfbDecryptFinalCode (Spec.Camellia.cfbDecryptFinalContract AArch64.abi 3344) 0 :=
  noResidue_of_doneG cfbDecryptFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Camellia.cfbFinalSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_ctr`. -/
abbrev ctrCode : Prog isa :=
  withClears [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.ctr)

theorem ctrCode_verified : Verified AArch64.target ctrCode (Spec.Camellia.ctrContract AArch64.abi 3344) :=
  Clears.Verified.withClears ctr_framed (by decide)

theorem ctrCode_noResidue : NoResidue ctrCode (Spec.Camellia.ctrContract AArch64.abi 3344) 0 :=
  noResidue_of_doneG ctrCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Camellia.ctrSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_ofb`. -/
abbrev ofbCode : Prog isa :=
  withClears [.x6, .x7, .x8, .x10, .x11, .x12]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.ofb)

theorem ofbCode_verified : Verified AArch64.target ofbCode (Spec.Camellia.ofbContract AArch64.abi 3344) :=
  Clears.Verified.withClears ofb_framed (by decide)

theorem ofbCode_noResidue : NoResidue ofbCode (Spec.Camellia.ofbContract AArch64.abi 3344) 0 :=
  noResidue_of_doneG ofbCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Camellia.ofbSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_ofb_final`. -/
abbrev ofbFinalCode : Prog isa :=
  withClears [.x6, .x7, .x10, .x11, .x12]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.ofbFinal)

theorem ofbFinalCode_verified : Verified AArch64.target ofbFinalCode (Spec.Camellia.ofbFinalContract AArch64.abi 3344) :=
  Clears.Verified.withClears ofbFinal_framed (by decide)

theorem ofbFinalCode_noResidue : NoResidue ofbFinalCode (Spec.Camellia.ofbFinalContract AArch64.abi 3344) 0 :=
  noResidue_of_doneG ofbFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Camellia.ofbFinalSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

end VG.Proof.Camellia.AArch64.Residue
