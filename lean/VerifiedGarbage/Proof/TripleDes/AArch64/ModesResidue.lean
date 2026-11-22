module

public import VerifiedGarbage.Impl.TripleDes.AArch64.Fn
public meta import VerifiedGarbage.Impl.TripleDes.AArch64.Fn
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Impl.Scrub.AArch64
public meta import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Impl.TripleDes.AArch64.BitsliceAlloc
public meta import VerifiedGarbage.Impl.TripleDes.AArch64.BitsliceAlloc
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public import VerifiedGarbage.Proof.Framework.AArch64.Simd
public meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.Framework.AArch64.Simd64
public meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.AddrArith
public meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Rc2.AArch64.BlockIO
public meta import VerifiedGarbage.Proof.Rc2.AArch64.BlockIO
public import VerifiedGarbage.Proof.Rc2.AArch64.Cipher
public meta import VerifiedGarbage.Proof.Rc2.AArch64.Cipher
public import VerifiedGarbage.Proof.Rc2.AArch64.MemOps
public meta import VerifiedGarbage.Proof.Rc2.AArch64.MemOps
public import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Verified
public meta import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Verified
public import VerifiedGarbage.Proof.TripleDes.AArch64.Box
public meta import VerifiedGarbage.Proof.TripleDes.AArch64.Box
public import VerifiedGarbage.Proof.TripleDes.AArch64.CbcTables
public meta import VerifiedGarbage.Proof.TripleDes.AArch64.CbcTables
public import VerifiedGarbage.Proof.TripleDes.AArch64.CbcVerified
public meta import VerifiedGarbage.Proof.TripleDes.AArch64.CbcVerified
public import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalVerified
public meta import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
public meta import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
public import VerifiedGarbage.Proof.TripleDes.AArch64.Frame
public meta import VerifiedGarbage.Proof.TripleDes.AArch64.Frame
public import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Correct
public meta import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Correct
public import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Verified
public meta import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Verified
public import VerifiedGarbage.Proof.TripleDes.AArch64.Permutation
public meta import VerifiedGarbage.Proof.TripleDes.AArch64.Permutation
public import VerifiedGarbage.Proof.TripleDes.AArch64.RoundBody
public meta import VerifiedGarbage.Proof.TripleDes.AArch64.RoundBody
public import VerifiedGarbage.Proof.TripleDes.AArch64.ShortCbc
public meta import VerifiedGarbage.Proof.TripleDes.AArch64.ShortCbc
public import VerifiedGarbage.Proof.TripleDes.AArch64.ShortCfb
public meta import VerifiedGarbage.Proof.TripleDes.AArch64.ShortCfb
public import VerifiedGarbage.Proof.TripleDes.AArch64.ShortEcb
public meta import VerifiedGarbage.Proof.TripleDes.AArch64.ShortEcb
public import VerifiedGarbage.Proof.TripleDes.AArch64.VerifiedBlock
public meta import VerifiedGarbage.Proof.TripleDes.AArch64.VerifiedBlock
public import VerifiedGarbage.Proof.TripleDes.Bytes
public meta import VerifiedGarbage.Proof.TripleDes.Bytes
public import VerifiedGarbage.Proof.TripleDes.Permutation
public meta import VerifiedGarbage.Proof.TripleDes.Permutation
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalLit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalLit
import VerifiedGarbage.Proof.TripleDes.AArch64.FbLit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FbLit
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Lit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Lit

/-!
# Triple DES on AArch64 returns without secret residue

Triple DES's ECB, CBC, CFB64, CFB8 and OFB functions run in frames of 464 to
1120 bytes whose scratch words they zero (`withStackScratchWiped`). The
analysis of the window's bytes (`rtaintG`) finds every byte of those frames
the same in both runs on return, so they need no clearing of the stack
(`noResidue_of_doneG`), only of what they leave in their registers, `x9` and
`v31` among them where the analysis finds them secret.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.ModesResidue

open VG VG.AArch64 VG.Impl.Scrub.AArch64 VG.AArch64.RTaintG

/-- `vg_triple_des_ecb_encrypt`. -/
abbrev ecbEncryptCode : Prog isa := Impl.TripleDes.AArch64.Fn.ecbEncrypt

theorem ecbEncryptCode_verified : Verified AArch64.target ecbEncryptCode (Spec.TripleDes.ecbContract AArch64.abi .encrypt 1024) :=
  Clears.Verified.withClears (Proof.TripleDes.AArch64.ecb_framed Proof.TripleDes.AArch64.Short.ecbEncrypt_verified) (by decide)

theorem ecbEncryptCode_noResidue : NoResidue ecbEncryptCode (Spec.TripleDes.ecbContract AArch64.abi .encrypt 1024) 0 :=
  noResidue_of_doneG ecbEncryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.TripleDes.ecbEncryptApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_ecb_decrypt`. -/
abbrev ecbDecryptCode : Prog isa := Impl.TripleDes.AArch64.Fn.ecbDecrypt

theorem ecbDecryptCode_verified : Verified AArch64.target ecbDecryptCode (Spec.TripleDes.ecbContract AArch64.abi .decrypt 1024) :=
  Clears.Verified.withClears (Proof.TripleDes.AArch64.ecb_framed Proof.TripleDes.AArch64.Short.ecbDecrypt_verified) (by decide)

theorem ecbDecryptCode_noResidue : NoResidue ecbDecryptCode (Spec.TripleDes.ecbContract AArch64.abi .decrypt 1024) 0 :=
  noResidue_of_doneG ecbDecryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.TripleDes.ecbDecryptApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_cbc_encrypt_chained`. -/
abbrev cbcEncryptChainedCode : Prog isa := Impl.TripleDes.AArch64.Fn.cbcEncryptChained

theorem cbcEncryptChainedCode_verified : Verified AArch64.target cbcEncryptChainedCode (Spec.TripleDes.cbcEncryptChainedContract AArch64.abi 464) :=
  Clears.Verified.withClears (Proof.TripleDes.AArch64.TablesCbc.framed) (by decide)

theorem cbcEncryptChainedCode_noResidue : NoResidue cbcEncryptChainedCode (Spec.TripleDes.cbcEncryptChainedContract AArch64.abi 464) 0 :=
  noResidue_of_doneG cbcEncryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.TripleDes.cbcEncryptChainedApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_cbc_decrypt_chained`. -/
abbrev cbcDecryptChainedCode : Prog isa := Impl.TripleDes.AArch64.Fn.cbcDecryptChained

theorem cbcDecryptChainedCode_verified : Verified AArch64.target cbcDecryptChainedCode (Spec.TripleDes.cbcDecryptChainedContract AArch64.abi 1120) :=
  Clears.Verified.withClears (Proof.TripleDes.AArch64.Short.Cbc.cbcDecryptChained_framed) (by decide)

theorem cbcDecryptChainedCode_noResidue : NoResidue cbcDecryptChainedCode (Spec.TripleDes.cbcDecryptChainedContract AArch64.abi 1120) 0 :=
  noResidue_of_doneG cbcDecryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.TripleDes.cbcDecryptChainedApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_cfb64_encrypt`. -/
abbrev cfbEncryptCode : Prog isa := Impl.TripleDes.AArch64.Fn.cfbEncrypt

theorem cfbEncryptCode_verified : Verified AArch64.target cfbEncryptCode (Spec.TripleDes.cfbEncryptContract AArch64.abi 560) :=
  Clears.Verified.withClears (Proof.TripleDes.AArch64.cfbEncrypt_framed) (by decide)

theorem cfbEncryptCode_noResidue : NoResidue cfbEncryptCode (Spec.TripleDes.cfbEncryptContract AArch64.abi 560) 0 :=
  noResidue_of_doneG cfbEncryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.TripleDes.cfbEncryptApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_cfb64_decrypt`. -/
abbrev cfbDecryptCode : Prog isa := Impl.TripleDes.AArch64.Fn.cfbDecrypt

theorem cfbDecryptCode_verified : Verified AArch64.target cfbDecryptCode (Spec.TripleDes.cfbDecryptContract AArch64.abi 1120) :=
  Clears.Verified.withClears (Proof.TripleDes.AArch64.Short.Cbc.Cfb.cfb64Decrypt_framed) (by decide)

theorem cfbDecryptCode_noResidue : NoResidue cfbDecryptCode (Spec.TripleDes.cfbDecryptContract AArch64.abi 1120) 0 :=
  noResidue_of_doneG cfbDecryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.TripleDes.cfbDecryptApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_cfb64_encrypt_final`. -/
abbrev cfbEncryptFinalCode : Prog isa := Impl.TripleDes.AArch64.Fn.cfbEncryptFinal

theorem cfbEncryptFinalCode_verified : Verified AArch64.target cfbEncryptFinalCode (Spec.TripleDes.cfbEncryptFinalContract AArch64.abi 560) :=
  Clears.Verified.withClears (Proof.TripleDes.AArch64.cfbEncryptFinal_framed) (by decide)

theorem cfbEncryptFinalCode_noResidue : NoResidue cfbEncryptFinalCode (Spec.TripleDes.cfbEncryptFinalContract AArch64.abi 560) 0 :=
  noResidue_of_doneG cfbEncryptFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.TripleDes.cfbEncryptFinalApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_cfb64_decrypt_final`. -/
abbrev cfbDecryptFinalCode : Prog isa := Impl.TripleDes.AArch64.Fn.cfbDecryptFinal

theorem cfbDecryptFinalCode_verified : Verified AArch64.target cfbDecryptFinalCode (Spec.TripleDes.cfbDecryptFinalContract AArch64.abi 560) :=
  Clears.Verified.withClears (Proof.TripleDes.AArch64.cfbDecryptFinal_framed) (by decide)

theorem cfbDecryptFinalCode_noResidue : NoResidue cfbDecryptFinalCode (Spec.TripleDes.cfbDecryptFinalContract AArch64.abi 560) 0 :=
  noResidue_of_doneG cfbDecryptFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.TripleDes.cfbDecryptFinalApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_cfb8_encrypt`. -/
abbrev cfb8EncryptCode : Prog isa := Impl.TripleDes.AArch64.Fn.cfb8Encrypt

theorem cfb8EncryptCode_verified : Verified AArch64.target cfb8EncryptCode (Spec.TripleDes.cfb8EncryptContract AArch64.abi 560) :=
  Clears.Verified.withClears (Proof.TripleDes.AArch64.cfb8Encrypt_framed) (by decide)

theorem cfb8EncryptCode_noResidue : NoResidue cfb8EncryptCode (Spec.TripleDes.cfb8EncryptContract AArch64.abi 560) 0 :=
  noResidue_of_doneG cfb8EncryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.TripleDes.cfb8EncryptApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_cfb8_decrypt`. -/
abbrev cfb8DecryptCode : Prog isa := Impl.TripleDes.AArch64.Fn.cfb8Decrypt

theorem cfb8DecryptCode_verified : Verified AArch64.target cfb8DecryptCode (Spec.TripleDes.cfb8DecryptContract AArch64.abi 560) :=
  Clears.Verified.withClears (Proof.TripleDes.AArch64.cfb8Decrypt_framed) (by decide)

theorem cfb8DecryptCode_noResidue : NoResidue cfb8DecryptCode (Spec.TripleDes.cfb8DecryptContract AArch64.abi 560) 0 :=
  noResidue_of_doneG cfb8DecryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.TripleDes.cfb8DecryptApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_ofb`. -/
abbrev ofbCode : Prog isa := Impl.TripleDes.AArch64.Fn.ofb

theorem ofbCode_verified : Verified AArch64.target ofbCode (Spec.TripleDes.ofbContract AArch64.abi 560) :=
  Clears.Verified.withClears (Proof.TripleDes.AArch64.ofb_framed) (by decide)

theorem ofbCode_noResidue : NoResidue ofbCode (Spec.TripleDes.ofbContract AArch64.abi 560) 0 :=
  noResidue_of_doneG ofbCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.TripleDes.ofbApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- `vg_triple_des_ofb_final`. -/
abbrev ofbFinalCode : Prog isa := Impl.TripleDes.AArch64.Fn.ofbFinal

theorem ofbFinalCode_verified : Verified AArch64.target ofbFinalCode (Spec.TripleDes.ofbFinalContract AArch64.abi 560) :=
  Clears.Verified.withClears (Proof.TripleDes.AArch64.ofbFinal_framed) (by decide)

theorem ofbFinalCode_noResidue : NoResidue ofbFinalCode (Spec.TripleDes.ofbFinalContract AArch64.abi 560) 0 :=
  noResidue_of_doneG ofbFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.TripleDes.ofbFinalApi.sig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.TripleDes.AArch64.ModesResidue.ecbEncryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.TripleDes.AArch64.Fn.ecbEncrypt
      (Spec.TripleDes.ecbContract AArch64.abi Spec.TripleDes.Direction.encrypt 1024) 0 :=
  ⟨Proof.TripleDes.AArch64.ModesResidue.ecbEncryptCode_verified,
    Proof.TripleDes.AArch64.ModesResidue.ecbEncryptCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.TripleDes.AArch64.ModesResidue.ecbDecryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.TripleDes.AArch64.Fn.ecbDecrypt
      (Spec.TripleDes.ecbContract AArch64.abi Spec.TripleDes.Direction.decrypt 1024) 0 :=
  ⟨Proof.TripleDes.AArch64.ModesResidue.ecbDecryptCode_verified,
    Proof.TripleDes.AArch64.ModesResidue.ecbDecryptCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.TripleDes.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.TripleDes.AArch64.Fn.cbcEncryptChained
      (Spec.TripleDes.cbcEncryptChainedContract AArch64.abi 464) 0 :=
  ⟨Proof.TripleDes.AArch64.ModesResidue.cbcEncryptChainedCode_verified,
    Proof.TripleDes.AArch64.ModesResidue.cbcEncryptChainedCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.TripleDes.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.TripleDes.AArch64.Fn.cbcDecryptChained
      (Spec.TripleDes.cbcDecryptChainedContract AArch64.abi 1120) 0 :=
  ⟨Proof.TripleDes.AArch64.ModesResidue.cbcDecryptChainedCode_verified,
    Proof.TripleDes.AArch64.ModesResidue.cbcDecryptChainedCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.TripleDes.AArch64.ModesResidue.cfbEncryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.TripleDes.AArch64.Fn.cfbEncrypt
      (Spec.TripleDes.cfbEncryptContract AArch64.abi 560) 0 :=
  ⟨Proof.TripleDes.AArch64.ModesResidue.cfbEncryptCode_verified,
    Proof.TripleDes.AArch64.ModesResidue.cfbEncryptCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.TripleDes.AArch64.ModesResidue.cfbDecryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.TripleDes.AArch64.Fn.cfbDecrypt
      (Spec.TripleDes.cfbDecryptContract AArch64.abi 1120) 0 :=
  ⟨Proof.TripleDes.AArch64.ModesResidue.cfbDecryptCode_verified,
    Proof.TripleDes.AArch64.ModesResidue.cfbDecryptCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.TripleDes.AArch64.ModesResidue.cfbEncryptFinalCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.TripleDes.AArch64.Fn.cfbEncryptFinal
      (Spec.TripleDes.cfbEncryptFinalContract AArch64.abi 560) 0 :=
  ⟨Proof.TripleDes.AArch64.ModesResidue.cfbEncryptFinalCode_verified,
    Proof.TripleDes.AArch64.ModesResidue.cfbEncryptFinalCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.TripleDes.AArch64.ModesResidue.cfbDecryptFinalCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.TripleDes.AArch64.Fn.cfbDecryptFinal
      (Spec.TripleDes.cfbDecryptFinalContract AArch64.abi 560) 0 :=
  ⟨Proof.TripleDes.AArch64.ModesResidue.cfbDecryptFinalCode_verified,
    Proof.TripleDes.AArch64.ModesResidue.cfbDecryptFinalCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.TripleDes.AArch64.ModesResidue.cfb8EncryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.TripleDes.AArch64.Fn.cfb8Encrypt
      (Spec.TripleDes.cfb8EncryptContract AArch64.abi 560) 0 :=
  ⟨Proof.TripleDes.AArch64.ModesResidue.cfb8EncryptCode_verified,
    Proof.TripleDes.AArch64.ModesResidue.cfb8EncryptCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.TripleDes.AArch64.ModesResidue.cfb8DecryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.TripleDes.AArch64.Fn.cfb8Decrypt
      (Spec.TripleDes.cfb8DecryptContract AArch64.abi 560) 0 :=
  ⟨Proof.TripleDes.AArch64.ModesResidue.cfb8DecryptCode_verified,
    Proof.TripleDes.AArch64.ModesResidue.cfb8DecryptCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.TripleDes.AArch64.ModesResidue.ofbCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.TripleDes.AArch64.Fn.ofb
      (Spec.TripleDes.ofbContract AArch64.abi 560) 0 :=
  ⟨Proof.TripleDes.AArch64.ModesResidue.ofbCode_verified,
    Proof.TripleDes.AArch64.ModesResidue.ofbCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.TripleDes.AArch64.ModesResidue.ofbFinalCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.TripleDes.AArch64.Fn.ofbFinal
      (Spec.TripleDes.ofbFinalContract AArch64.abi 560) 0 :=
  ⟨Proof.TripleDes.AArch64.ModesResidue.ofbFinalCode_verified,
    Proof.TripleDes.AArch64.ModesResidue.ofbFinalCode_noResidue⟩

end VG.Proof.TripleDes.AArch64.ModesResidue
