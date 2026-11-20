module

public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Idea.AArch64.CbcVerified
public meta import VerifiedGarbage.Proof.Idea.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Idea.AArch64.FbVerified
public meta import VerifiedGarbage.Proof.Idea.AArch64.FbVerified
public import VerifiedGarbage.Proof.Idea.AArch64.FbFinalVerified
public meta import VerifiedGarbage.Proof.Idea.AArch64.FbFinalVerified
public import VerifiedGarbage.Impl.Residue.AArch64
public meta import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Idea.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Idea.AArch64.ModesLit
import VerifiedGarbage.Proof.Idea.AArch64.FbFinalLit
meta import VerifiedGarbage.Proof.Idea.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# IDEA's modes on AArch64 return without secret residue

IDEA's CBC, CFB64 and OFB functions run in a frame of 208 bytes whose
scratch words they zero (`withStackScratchWiped 208 .x4 26`). The analysis of
the window's bytes (`rtaintG`) finds every byte of it the same in both runs
on return, so they need no clearing of the stack (`noResidue_of_doneG`), only
of the general-purpose registers they leave secret, `x9` among them.
-/

@[expose] public section

namespace VG.Proof.Idea.AArch64.ModesResidue

open VG VG.AArch64 VG.Impl.Residue.AArch64 VG.AArch64.RTaintG

abbrev cbcEncryptChainedCode : Prog isa :=
  withClears [.x3, .x4, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14] [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cbcEncryptChained)

theorem cbcEncryptChainedCode_verified : Verified AArch64.target cbcEncryptChainedCode (Spec.Idea.cbcEncryptChainedContract AArch64.abi 208) :=
  Clears.Verified.withClears cbcEncryptChained_framed (by decide)

theorem cbcEncryptChainedCode_noResidue : NoResidue cbcEncryptChainedCode (Spec.Idea.cbcEncryptChainedContract AArch64.abi 208) 0 :=
  noResidue_of_doneG cbcEncryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Idea.cbcChainedSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

abbrev cbcDecryptChainedCode : Prog isa :=
  withClears [.x3, .x4, .x6, .x7, .x8, .x9, .x10, .x11, .x12] [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cbcDecryptChained)

theorem cbcDecryptChainedCode_verified : Verified AArch64.target cbcDecryptChainedCode (Spec.Idea.cbcDecryptChainedContract AArch64.abi 208) :=
  Clears.Verified.withClears cbcDecryptChained_framed (by decide)

theorem cbcDecryptChainedCode_noResidue : NoResidue cbcDecryptChainedCode (Spec.Idea.cbcDecryptChainedContract AArch64.abi 208) 0 :=
  noResidue_of_doneG cbcDecryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Idea.cbcChainedSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

abbrev cfbEncryptCode : Prog isa :=
  withClears [.x3, .x4, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14] [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cfbEncrypt)

theorem cfbEncryptCode_verified : Verified AArch64.target cfbEncryptCode (Spec.Idea.cfbEncryptContract AArch64.abi 208) :=
  Clears.Verified.withClears cfbEncrypt_framed (by decide)

theorem cfbEncryptCode_noResidue : NoResidue cfbEncryptCode (Spec.Idea.cfbEncryptContract AArch64.abi 208) 0 :=
  noResidue_of_doneG cfbEncryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Idea.cfbSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

abbrev cfbDecryptCode : Prog isa :=
  withClears [.x3, .x4, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14] [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cfbDecrypt)

theorem cfbDecryptCode_verified : Verified AArch64.target cfbDecryptCode (Spec.Idea.cfbDecryptContract AArch64.abi 208) :=
  Clears.Verified.withClears cfbDecrypt_framed (by decide)

theorem cfbDecryptCode_noResidue : NoResidue cfbDecryptCode (Spec.Idea.cfbDecryptContract AArch64.abi 208) 0 :=
  noResidue_of_doneG cfbDecryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Idea.cfbSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

abbrev cfbEncryptFinalCode : Prog isa :=
  withClears [.x3, .x4, .x6, .x7, .x9, .x10, .x11, .x12, .x13, .x14] [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cfbEncryptFinal)

theorem cfbEncryptFinalCode_verified : Verified AArch64.target cfbEncryptFinalCode (Spec.Idea.cfbEncryptFinalContract AArch64.abi 208) :=
  Clears.Verified.withClears cfbEncryptFinal_framed (by decide)

theorem cfbEncryptFinalCode_noResidue : NoResidue cfbEncryptFinalCode (Spec.Idea.cfbEncryptFinalContract AArch64.abi 208) 0 :=
  noResidue_of_doneG cfbEncryptFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Idea.cfbFinalSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

abbrev cfbDecryptFinalCode : Prog isa :=
  withClears [.x3, .x4, .x6, .x7, .x9, .x10, .x11, .x12, .x13, .x14] [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cfbDecryptFinal)

theorem cfbDecryptFinalCode_verified : Verified AArch64.target cfbDecryptFinalCode (Spec.Idea.cfbDecryptFinalContract AArch64.abi 208) :=
  Clears.Verified.withClears cfbDecryptFinal_framed (by decide)

theorem cfbDecryptFinalCode_noResidue : NoResidue cfbDecryptFinalCode (Spec.Idea.cfbDecryptFinalContract AArch64.abi 208) 0 :=
  noResidue_of_doneG cfbDecryptFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Idea.cfbFinalSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

abbrev ofbCode : Prog isa :=
  withClears [.x3, .x4, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14] [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.ofb)

theorem ofbCode_verified : Verified AArch64.target ofbCode (Spec.Idea.ofbContract AArch64.abi 208) :=
  Clears.Verified.withClears ofb_framed (by decide)

theorem ofbCode_noResidue : NoResidue ofbCode (Spec.Idea.ofbContract AArch64.abi 208) 0 :=
  noResidue_of_doneG ofbCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Idea.ofbSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

abbrev ofbFinalCode : Prog isa :=
  withClears [.x3, .x4, .x6, .x7, .x9, .x10, .x11, .x12, .x13, .x14] [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.ofbFinal)

theorem ofbFinalCode_verified : Verified AArch64.target ofbFinalCode (Spec.Idea.ofbFinalContract AArch64.abi 208) :=
  Clears.Verified.withClears ofbFinal_framed (by decide)

theorem ofbFinalCode_noResidue : NoResidue ofbFinalCode (Spec.Idea.ofbFinalContract AArch64.abi 208) 0 :=
  noResidue_of_doneG ofbFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Idea.ofbFinalSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed :
    VerifiedScrubbed AArch64.target Proof.Idea.AArch64.ModesResidue.cbcEncryptChainedCode
      (Spec.Idea.cbcEncryptChainedContract AArch64.abi 208) 0 :=
  ⟨Proof.Idea.AArch64.ModesResidue.cbcEncryptChainedCode_verified,
    Proof.Idea.AArch64.ModesResidue.cbcEncryptChainedCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed :
    VerifiedScrubbed AArch64.target Proof.Idea.AArch64.ModesResidue.cbcDecryptChainedCode
      (Spec.Idea.cbcDecryptChainedContract AArch64.abi 208) 0 :=
  ⟨Proof.Idea.AArch64.ModesResidue.cbcDecryptChainedCode_verified,
    Proof.Idea.AArch64.ModesResidue.cbcDecryptChainedCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.ModesResidue.cfbEncryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Proof.Idea.AArch64.ModesResidue.cfbEncryptCode
      (Spec.Idea.cfbEncryptContract AArch64.abi 208) 0 :=
  ⟨Proof.Idea.AArch64.ModesResidue.cfbEncryptCode_verified,
    Proof.Idea.AArch64.ModesResidue.cfbEncryptCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.ModesResidue.cfbDecryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Proof.Idea.AArch64.ModesResidue.cfbDecryptCode
      (Spec.Idea.cfbDecryptContract AArch64.abi 208) 0 :=
  ⟨Proof.Idea.AArch64.ModesResidue.cfbDecryptCode_verified,
    Proof.Idea.AArch64.ModesResidue.cfbDecryptCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.ModesResidue.cfbEncryptFinalCode_scrubbed :
    VerifiedScrubbed AArch64.target Proof.Idea.AArch64.ModesResidue.cfbEncryptFinalCode
      (Spec.Idea.cfbEncryptFinalContract AArch64.abi 208) 0 :=
  ⟨Proof.Idea.AArch64.ModesResidue.cfbEncryptFinalCode_verified,
    Proof.Idea.AArch64.ModesResidue.cfbEncryptFinalCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.ModesResidue.cfbDecryptFinalCode_scrubbed :
    VerifiedScrubbed AArch64.target Proof.Idea.AArch64.ModesResidue.cfbDecryptFinalCode
      (Spec.Idea.cfbDecryptFinalContract AArch64.abi 208) 0 :=
  ⟨Proof.Idea.AArch64.ModesResidue.cfbDecryptFinalCode_verified,
    Proof.Idea.AArch64.ModesResidue.cfbDecryptFinalCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.ModesResidue.ofbCode_scrubbed :
    VerifiedScrubbed AArch64.target Proof.Idea.AArch64.ModesResidue.ofbCode
      (Spec.Idea.ofbContract AArch64.abi 208) 0 :=
  ⟨Proof.Idea.AArch64.ModesResidue.ofbCode_verified,
    Proof.Idea.AArch64.ModesResidue.ofbCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.ModesResidue.ofbFinalCode_scrubbed :
    VerifiedScrubbed AArch64.target Proof.Idea.AArch64.ModesResidue.ofbFinalCode
      (Spec.Idea.ofbFinalContract AArch64.abi 208) 0 :=
  ⟨Proof.Idea.AArch64.ModesResidue.ofbFinalCode_verified,
    Proof.Idea.AArch64.ModesResidue.ofbFinalCode_noResidue⟩

end VG.Proof.Idea.AArch64.ModesResidue
