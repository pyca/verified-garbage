module

public import VerifiedGarbage.Impl.Sm4.AArch64.Fn
public meta import VerifiedGarbage.Impl.Sm4.AArch64.Fn
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Impl.Scrub.AArch64
public meta import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public import VerifiedGarbage.Proof.Sm4.AArch64.CbcVerified
public meta import VerifiedGarbage.Proof.Sm4.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.CtrFinal
public meta import VerifiedGarbage.Proof.Sm4.AArch64.CtrFinal
public import VerifiedGarbage.Proof.Sm4.AArch64.CtrVerified
public meta import VerifiedGarbage.Proof.Sm4.AArch64.CtrVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.EcbCall
public meta import VerifiedGarbage.Proof.Sm4.AArch64.EcbCall
public import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalVerified
public meta import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.FbVerified
public meta import VerifiedGarbage.Proof.Sm4.AArch64.FbVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.PreparedVerified
public meta import VerifiedGarbage.Proof.Sm4.AArch64.PreparedVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Key
public meta import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Key
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Chained
public meta import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Chained
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Ecb
public meta import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Ecb
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Key
public meta import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Key
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Modes
public meta import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Modes
public import VerifiedGarbage.Proof.Sm4.AArch64.Verified
public meta import VerifiedGarbage.Proof.Sm4.AArch64.Verified
public import VerifiedGarbage.Proof.Variants.Sm4Ctr.AArch64
public meta import VerifiedGarbage.Proof.Variants.Sm4Ctr.AArch64
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalLit
meta import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Sm4.AArch64.FbLit
meta import VerifiedGarbage.Proof.Sm4.AArch64.FbLit
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
meta import VerifiedGarbage.Proof.Sm4.AArch64.Lit

/-!
# SM4's modes on AArch64 return without secret residue

SM4's CBC, CFB128 and OFB functions, both those built on the `SM4E`
instruction (`_sm4`) and the others, run in frames whose scratch words they
zero (`withStackScratchWiped`): 112 or 224 bytes for the `_sm4` ones, and
3264 bytes for the others. The analysis of the window's bytes (`rtaintG`)
finds every byte of those frames the same in both runs on return, so they
need no clearing of the stack (`noResidue_of_doneG`), only of what they leave
in their registers, `x9` and `v31` among them where the analysis finds them
secret.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.ModesResidue

open VG VG.AArch64 VG.Impl.Scrub.AArch64 VG.AArch64.RTaintG

/-- `vg_sm4_cbc_encrypt_chained_sm4`. -/
abbrev cbcEncryptChainedSm4Code : Prog isa := Impl.Sm4.AArch64.Fn.cbcEncryptChainedSm4

theorem cbcEncryptChainedSm4Code_verified : Verified AArch64.target cbcEncryptChainedSm4Code (Spec.Sm4.cbcEncryptChainedContract AArch64.abi 112) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.Sm4e.cbcEncryptChained_framed) (by decide)

theorem cbcEncryptChainedSm4Code_noResidue : NoResidue cbcEncryptChainedSm4Code (Spec.Sm4.cbcEncryptChainedContract AArch64.abi 112) 0 :=
  noResidue_of_doneG cbcEncryptChainedSm4Code_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Sm4.cbcEncryptChainedApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_cbc_encrypt_chained`. -/
abbrev cbcEncryptChainedCode : Prog isa := Impl.Sm4.AArch64.Fn.cbcEncryptChained

theorem cbcEncryptChainedCode_verified : Verified AArch64.target cbcEncryptChainedCode (Spec.Sm4.cbcEncryptChainedContract AArch64.abi 3264) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.cbcEncryptChained_framed) (by decide)

theorem cbcEncryptChainedCode_noResidue : NoResidue cbcEncryptChainedCode (Spec.Sm4.cbcEncryptChainedContract AArch64.abi 3264) 0 :=
  noResidue_of_doneG cbcEncryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Sm4.cbcEncryptChainedApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_cbc_decrypt_chained_sm4`. -/
abbrev cbcDecryptChainedSm4Code : Prog isa := Impl.Sm4.AArch64.Fn.cbcDecryptChainedSm4

theorem cbcDecryptChainedSm4Code_verified : Verified AArch64.target cbcDecryptChainedSm4Code (Spec.Sm4.cbcDecryptChainedContract AArch64.abi 224) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.Sm4e.cbcDecryptChained_framed) (by decide)

theorem cbcDecryptChainedSm4Code_noResidue : NoResidue cbcDecryptChainedSm4Code (Spec.Sm4.cbcDecryptChainedContract AArch64.abi 224) 0 :=
  noResidue_of_doneG cbcDecryptChainedSm4Code_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Sm4.cbcDecryptChainedApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_cbc_decrypt_chained`. -/
abbrev cbcDecryptChainedCode : Prog isa := Impl.Sm4.AArch64.Fn.cbcDecryptChained

theorem cbcDecryptChainedCode_verified : Verified AArch64.target cbcDecryptChainedCode (Spec.Sm4.cbcDecryptChainedContract AArch64.abi 3264) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.cbcDecryptChained_framed) (by decide)

theorem cbcDecryptChainedCode_noResidue : NoResidue cbcDecryptChainedCode (Spec.Sm4.cbcDecryptChainedContract AArch64.abi 3264) 0 :=
  noResidue_of_doneG cbcDecryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Sm4.cbcDecryptChainedApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_cfb128_encrypt_sm4`. -/
abbrev cfbEncryptSm4Code : Prog isa := Impl.Sm4.AArch64.Fn.cfbEncryptSm4

theorem cfbEncryptSm4Code_verified : Verified AArch64.target cfbEncryptSm4Code (Spec.Sm4.cfbEncryptContract AArch64.abi 112) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.Sm4e.cfbEncrypt_framed) (by decide)

theorem cfbEncryptSm4Code_noResidue : NoResidue cfbEncryptSm4Code (Spec.Sm4.cfbEncryptContract AArch64.abi 112) 0 :=
  noResidue_of_doneG cfbEncryptSm4Code_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Sm4.cfbEncryptApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_cfb128_encrypt`. -/
abbrev cfbEncryptCode : Prog isa := Impl.Sm4.AArch64.Fn.cfbEncrypt

theorem cfbEncryptCode_verified : Verified AArch64.target cfbEncryptCode (Spec.Sm4.cfbEncryptContract AArch64.abi 3264) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.cfbEncrypt_framed) (by decide)

theorem cfbEncryptCode_noResidue : NoResidue cfbEncryptCode (Spec.Sm4.cfbEncryptContract AArch64.abi 3264) 0 :=
  noResidue_of_doneG cfbEncryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Sm4.cfbEncryptApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_cfb128_decrypt_sm4`. -/
abbrev cfbDecryptSm4Code : Prog isa := Impl.Sm4.AArch64.Fn.cfbDecryptSm4

theorem cfbDecryptSm4Code_verified : Verified AArch64.target cfbDecryptSm4Code (Spec.Sm4.cfbDecryptContract AArch64.abi 224) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.Sm4e.cfbDecrypt_framed) (by decide)

theorem cfbDecryptSm4Code_noResidue : NoResidue cfbDecryptSm4Code (Spec.Sm4.cfbDecryptContract AArch64.abi 224) 0 :=
  noResidue_of_doneG cfbDecryptSm4Code_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Sm4.cfbDecryptApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_cfb128_decrypt`. -/
abbrev cfbDecryptCode : Prog isa := Impl.Sm4.AArch64.Fn.cfbDecrypt

theorem cfbDecryptCode_verified : Verified AArch64.target cfbDecryptCode (Spec.Sm4.cfbDecryptContract AArch64.abi 3264) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.cfbDecrypt_framed) (by decide)

theorem cfbDecryptCode_noResidue : NoResidue cfbDecryptCode (Spec.Sm4.cfbDecryptContract AArch64.abi 3264) 0 :=
  noResidue_of_doneG cfbDecryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Sm4.cfbDecryptApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_cfb128_encrypt_final_sm4`. -/
abbrev cfbEncryptFinalSm4Code : Prog isa := Impl.Sm4.AArch64.Fn.cfbEncryptFinalSm4

theorem cfbEncryptFinalSm4Code_verified : Verified AArch64.target cfbEncryptFinalSm4Code (Spec.Sm4.cfbEncryptFinalContract AArch64.abi 112) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.Sm4e.cfbEncryptFinal_framed) (by decide)

theorem cfbEncryptFinalSm4Code_noResidue : NoResidue cfbEncryptFinalSm4Code (Spec.Sm4.cfbEncryptFinalContract AArch64.abi 112) 0 :=
  noResidue_of_doneG cfbEncryptFinalSm4Code_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Sm4.cfbEncryptFinalApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_cfb128_encrypt_final`. -/
abbrev cfbEncryptFinalCode : Prog isa := Impl.Sm4.AArch64.Fn.cfbEncryptFinal

theorem cfbEncryptFinalCode_verified : Verified AArch64.target cfbEncryptFinalCode (Spec.Sm4.cfbEncryptFinalContract AArch64.abi 3264) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.cfbEncryptFinal_framed) (by decide)

theorem cfbEncryptFinalCode_noResidue : NoResidue cfbEncryptFinalCode (Spec.Sm4.cfbEncryptFinalContract AArch64.abi 3264) 0 :=
  noResidue_of_doneG cfbEncryptFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Sm4.cfbEncryptFinalApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_cfb128_decrypt_final_sm4`. -/
abbrev cfbDecryptFinalSm4Code : Prog isa := Impl.Sm4.AArch64.Fn.cfbDecryptFinalSm4

theorem cfbDecryptFinalSm4Code_verified : Verified AArch64.target cfbDecryptFinalSm4Code (Spec.Sm4.cfbDecryptFinalContract AArch64.abi 112) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.Sm4e.cfbDecryptFinal_framed) (by decide)

theorem cfbDecryptFinalSm4Code_noResidue : NoResidue cfbDecryptFinalSm4Code (Spec.Sm4.cfbDecryptFinalContract AArch64.abi 112) 0 :=
  noResidue_of_doneG cfbDecryptFinalSm4Code_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Sm4.cfbDecryptFinalApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_cfb128_decrypt_final`. -/
abbrev cfbDecryptFinalCode : Prog isa := Impl.Sm4.AArch64.Fn.cfbDecryptFinal

theorem cfbDecryptFinalCode_verified : Verified AArch64.target cfbDecryptFinalCode (Spec.Sm4.cfbDecryptFinalContract AArch64.abi 3264) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.cfbDecryptFinal_framed) (by decide)

theorem cfbDecryptFinalCode_noResidue : NoResidue cfbDecryptFinalCode (Spec.Sm4.cfbDecryptFinalContract AArch64.abi 3264) 0 :=
  noResidue_of_doneG cfbDecryptFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Sm4.cfbDecryptFinalApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_ofb_sm4`. -/
abbrev ofbSm4Code : Prog isa := Impl.Sm4.AArch64.Fn.ofbSm4

theorem ofbSm4Code_verified : Verified AArch64.target ofbSm4Code (Spec.Sm4.ofbContract AArch64.abi 112) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.Sm4e.ofb_framed) (by decide)

theorem ofbSm4Code_noResidue : NoResidue ofbSm4Code (Spec.Sm4.ofbContract AArch64.abi 112) 0 :=
  noResidue_of_doneG ofbSm4Code_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Sm4.ofbApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_ofb`. -/
abbrev ofbCode : Prog isa := Impl.Sm4.AArch64.Fn.ofb

theorem ofbCode_verified : Verified AArch64.target ofbCode (Spec.Sm4.ofbContract AArch64.abi 3264) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.ofb_framed) (by decide)

theorem ofbCode_noResidue : NoResidue ofbCode (Spec.Sm4.ofbContract AArch64.abi 3264) 0 :=
  noResidue_of_doneG ofbCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Sm4.ofbApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_ofb_final_sm4`. -/
abbrev ofbFinalSm4Code : Prog isa := Impl.Sm4.AArch64.Fn.ofbFinalSm4

theorem ofbFinalSm4Code_verified : Verified AArch64.target ofbFinalSm4Code (Spec.Sm4.ofbFinalContract AArch64.abi 112) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.Sm4e.ofbFinal_framed) (by decide)

theorem ofbFinalSm4Code_noResidue : NoResidue ofbFinalSm4Code (Spec.Sm4.ofbFinalContract AArch64.abi 112) 0 :=
  noResidue_of_doneG ofbFinalSm4Code_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Sm4.ofbFinalApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_sm4_ofb_final`. -/
abbrev ofbFinalCode : Prog isa := Impl.Sm4.AArch64.Fn.ofbFinal

theorem ofbFinalCode_verified : Verified AArch64.target ofbFinalCode (Spec.Sm4.ofbFinalContract AArch64.abi 3264) :=
  Clears.Verified.withClears (Proof.Sm4.AArch64.ofbFinal_framed) (by decide)

theorem ofbFinalCode_noResidue : NoResidue ofbFinalCode (Spec.Sm4.ofbFinalContract AArch64.abi 3264) 0 :=
  noResidue_of_doneG ofbFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Sm4.ofbFinalApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.ModesResidue.cbcEncryptChainedSm4Code_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.cbcEncryptChainedSm4
      (Spec.Sm4.cbcEncryptChainedContract AArch64.abi 112) 0 :=
  ⟨Proof.Sm4.AArch64.ModesResidue.cbcEncryptChainedSm4Code_verified,
    Proof.Sm4.AArch64.ModesResidue.cbcEncryptChainedSm4Code_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.cbcEncryptChained
      (Spec.Sm4.cbcEncryptChainedContract AArch64.abi 3264) 0 :=
  ⟨Proof.Sm4.AArch64.ModesResidue.cbcEncryptChainedCode_verified,
    Proof.Sm4.AArch64.ModesResidue.cbcEncryptChainedCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.ModesResidue.cbcDecryptChainedSm4Code_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.cbcDecryptChainedSm4
      (Spec.Sm4.cbcDecryptChainedContract AArch64.abi 224) 0 :=
  ⟨Proof.Sm4.AArch64.ModesResidue.cbcDecryptChainedSm4Code_verified,
    Proof.Sm4.AArch64.ModesResidue.cbcDecryptChainedSm4Code_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.cbcDecryptChained
      (Spec.Sm4.cbcDecryptChainedContract AArch64.abi 3264) 0 :=
  ⟨Proof.Sm4.AArch64.ModesResidue.cbcDecryptChainedCode_verified,
    Proof.Sm4.AArch64.ModesResidue.cbcDecryptChainedCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.ModesResidue.cfbEncryptSm4Code_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.cfbEncryptSm4
      (Spec.Sm4.cfbEncryptContract AArch64.abi 112) 0 :=
  ⟨Proof.Sm4.AArch64.ModesResidue.cfbEncryptSm4Code_verified,
    Proof.Sm4.AArch64.ModesResidue.cfbEncryptSm4Code_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.ModesResidue.cfbEncryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.cfbEncrypt
      (Spec.Sm4.cfbEncryptContract AArch64.abi 3264) 0 :=
  ⟨Proof.Sm4.AArch64.ModesResidue.cfbEncryptCode_verified,
    Proof.Sm4.AArch64.ModesResidue.cfbEncryptCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.ModesResidue.cfbDecryptSm4Code_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.cfbDecryptSm4
      (Spec.Sm4.cfbDecryptContract AArch64.abi 224) 0 :=
  ⟨Proof.Sm4.AArch64.ModesResidue.cfbDecryptSm4Code_verified,
    Proof.Sm4.AArch64.ModesResidue.cfbDecryptSm4Code_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.ModesResidue.cfbDecryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.cfbDecrypt
      (Spec.Sm4.cfbDecryptContract AArch64.abi 3264) 0 :=
  ⟨Proof.Sm4.AArch64.ModesResidue.cfbDecryptCode_verified,
    Proof.Sm4.AArch64.ModesResidue.cfbDecryptCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.ModesResidue.cfbEncryptFinalSm4Code_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.cfbEncryptFinalSm4
      (Spec.Sm4.cfbEncryptFinalContract AArch64.abi 112) 0 :=
  ⟨Proof.Sm4.AArch64.ModesResidue.cfbEncryptFinalSm4Code_verified,
    Proof.Sm4.AArch64.ModesResidue.cfbEncryptFinalSm4Code_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.ModesResidue.cfbEncryptFinalCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.cfbEncryptFinal
      (Spec.Sm4.cfbEncryptFinalContract AArch64.abi 3264) 0 :=
  ⟨Proof.Sm4.AArch64.ModesResidue.cfbEncryptFinalCode_verified,
    Proof.Sm4.AArch64.ModesResidue.cfbEncryptFinalCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.ModesResidue.cfbDecryptFinalSm4Code_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.cfbDecryptFinalSm4
      (Spec.Sm4.cfbDecryptFinalContract AArch64.abi 112) 0 :=
  ⟨Proof.Sm4.AArch64.ModesResidue.cfbDecryptFinalSm4Code_verified,
    Proof.Sm4.AArch64.ModesResidue.cfbDecryptFinalSm4Code_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.ModesResidue.cfbDecryptFinalCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.cfbDecryptFinal
      (Spec.Sm4.cfbDecryptFinalContract AArch64.abi 3264) 0 :=
  ⟨Proof.Sm4.AArch64.ModesResidue.cfbDecryptFinalCode_verified,
    Proof.Sm4.AArch64.ModesResidue.cfbDecryptFinalCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.ModesResidue.ofbSm4Code_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.ofbSm4
      (Spec.Sm4.ofbContract AArch64.abi 112) 0 :=
  ⟨Proof.Sm4.AArch64.ModesResidue.ofbSm4Code_verified,
    Proof.Sm4.AArch64.ModesResidue.ofbSm4Code_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.ModesResidue.ofbCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.ofb
      (Spec.Sm4.ofbContract AArch64.abi 3264) 0 :=
  ⟨Proof.Sm4.AArch64.ModesResidue.ofbCode_verified,
    Proof.Sm4.AArch64.ModesResidue.ofbCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.ModesResidue.ofbFinalSm4Code_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.ofbFinalSm4
      (Spec.Sm4.ofbFinalContract AArch64.abi 112) 0 :=
  ⟨Proof.Sm4.AArch64.ModesResidue.ofbFinalSm4Code_verified,
    Proof.Sm4.AArch64.ModesResidue.ofbFinalSm4Code_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.ModesResidue.ofbFinalCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Fn.ofbFinal
      (Spec.Sm4.ofbFinalContract AArch64.abi 3264) 0 :=
  ⟨Proof.Sm4.AArch64.ModesResidue.ofbFinalCode_verified,
    Proof.Sm4.AArch64.ModesResidue.ofbFinalCode_noResidue⟩

end VG.Proof.Sm4.AArch64.ModesResidue
