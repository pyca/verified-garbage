module

public import VerifiedGarbage.Impl.Idea.AArch64.Fn
public meta import VerifiedGarbage.Impl.Idea.AArch64.Fn
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Idea.AArch64.CbcVerified
public meta import VerifiedGarbage.Proof.Idea.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Idea.AArch64.FbVerified
public meta import VerifiedGarbage.Proof.Idea.AArch64.FbVerified
public import VerifiedGarbage.Proof.Idea.AArch64.FbFinalVerified
public meta import VerifiedGarbage.Proof.Idea.AArch64.FbFinalVerified
public import VerifiedGarbage.Impl.Scrub.AArch64
public meta import VerifiedGarbage.Impl.Scrub.AArch64
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
public import VerifiedGarbage.Proof.Framework.TaintCTAll
public meta import VerifiedGarbage.Proof.Framework.TaintCTAll

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

open VG VG.AArch64 VG.Impl.Scrub.AArch64 VG.AArch64.RTaintG

abbrev cbcEncryptChainedCode : Prog isa := Impl.Idea.AArch64.Fn.cbcEncryptChained

theorem cbcEncryptChainedCode_verified : Verified AArch64.target cbcEncryptChainedCode (Spec.Idea.cbcEncryptChainedContract AArch64.abi 208) :=
  Clears.Verified.withClears cbcEncryptChained_framed (by decide)

/-- The residue analyses of the functions' code, in one kernel evaluation
(`taint_decide_ct_all`), which analyses the code they share once. -/
theorem residue :
    (rtaintG 208).Ends (RTaintB.init, some (0, 0, [])) Impl.Idea.AArch64.Fn.cbcEncryptChained (doneG 208 0 []) ∧
    (rtaintG 208).Ends (RTaintB.init, some (0, 0, [])) Impl.Idea.AArch64.Fn.cbcDecryptChained (doneG 208 0 []) ∧
    (rtaintG 208).Ends (RTaintB.init, some (0, 0, [])) Impl.Idea.AArch64.Fn.cfbEncrypt (doneG 208 0 []) ∧
    (rtaintG 208).Ends (RTaintB.init, some (0, 0, [])) Impl.Idea.AArch64.Fn.cfbDecrypt (doneG 208 0 []) ∧
    (rtaintG 208).Ends (RTaintB.init, some (0, 0, [])) Impl.Idea.AArch64.Fn.cfbEncryptFinal (doneG 208 0 []) ∧
    (rtaintG 208).Ends (RTaintB.init, some (0, 0, [])) Impl.Idea.AArch64.Fn.cfbDecryptFinal (doneG 208 0 []) ∧
    (rtaintG 208).Ends (RTaintB.init, some (0, 0, [])) Impl.Idea.AArch64.Fn.ofb (doneG 208 0 []) ∧
    (rtaintG 208).Ends (RTaintB.init, some (0, 0, [])) Impl.Idea.AArch64.Fn.ofbFinal (doneG 208 0 []) := by
  taint_decide_ct_all

theorem cbcEncryptChainedCode_noResidue : NoResidue cbcEncryptChainedCode (Spec.Idea.cbcEncryptChainedContract AArch64.abi 208) 0 :=
  noResidue_of_doneG cbcEncryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Idea.cbcChainedSig) (by decide) (by decide) (Nat.le_refl _)) residue.1

abbrev cbcDecryptChainedCode : Prog isa := Impl.Idea.AArch64.Fn.cbcDecryptChained

theorem cbcDecryptChainedCode_verified : Verified AArch64.target cbcDecryptChainedCode (Spec.Idea.cbcDecryptChainedContract AArch64.abi 208) :=
  Clears.Verified.withClears cbcDecryptChained_framed (by decide)

theorem cbcDecryptChainedCode_noResidue : NoResidue cbcDecryptChainedCode (Spec.Idea.cbcDecryptChainedContract AArch64.abi 208) 0 :=
  noResidue_of_doneG cbcDecryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Idea.cbcChainedSig) (by decide) (by decide) (Nat.le_refl _)) residue.2.1

abbrev cfbEncryptCode : Prog isa := Impl.Idea.AArch64.Fn.cfbEncrypt

theorem cfbEncryptCode_verified : Verified AArch64.target cfbEncryptCode (Spec.Idea.cfbEncryptContract AArch64.abi 208) :=
  Clears.Verified.withClears cfbEncrypt_framed (by decide)

theorem cfbEncryptCode_noResidue : NoResidue cfbEncryptCode (Spec.Idea.cfbEncryptContract AArch64.abi 208) 0 :=
  noResidue_of_doneG cfbEncryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Idea.cfbSig) (by decide) (by decide) (Nat.le_refl _)) residue.2.2.1

abbrev cfbDecryptCode : Prog isa := Impl.Idea.AArch64.Fn.cfbDecrypt

theorem cfbDecryptCode_verified : Verified AArch64.target cfbDecryptCode (Spec.Idea.cfbDecryptContract AArch64.abi 208) :=
  Clears.Verified.withClears cfbDecrypt_framed (by decide)

theorem cfbDecryptCode_noResidue : NoResidue cfbDecryptCode (Spec.Idea.cfbDecryptContract AArch64.abi 208) 0 :=
  noResidue_of_doneG cfbDecryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Idea.cfbSig) (by decide) (by decide) (Nat.le_refl _)) residue.2.2.2.1

abbrev cfbEncryptFinalCode : Prog isa := Impl.Idea.AArch64.Fn.cfbEncryptFinal

theorem cfbEncryptFinalCode_verified : Verified AArch64.target cfbEncryptFinalCode (Spec.Idea.cfbEncryptFinalContract AArch64.abi 208) :=
  Clears.Verified.withClears cfbEncryptFinal_framed (by decide)

theorem cfbEncryptFinalCode_noResidue : NoResidue cfbEncryptFinalCode (Spec.Idea.cfbEncryptFinalContract AArch64.abi 208) 0 :=
  noResidue_of_doneG cfbEncryptFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Idea.cfbFinalSig) (by decide) (by decide) (Nat.le_refl _)) residue.2.2.2.2.1

abbrev cfbDecryptFinalCode : Prog isa := Impl.Idea.AArch64.Fn.cfbDecryptFinal

theorem cfbDecryptFinalCode_verified : Verified AArch64.target cfbDecryptFinalCode (Spec.Idea.cfbDecryptFinalContract AArch64.abi 208) :=
  Clears.Verified.withClears cfbDecryptFinal_framed (by decide)

theorem cfbDecryptFinalCode_noResidue : NoResidue cfbDecryptFinalCode (Spec.Idea.cfbDecryptFinalContract AArch64.abi 208) 0 :=
  noResidue_of_doneG cfbDecryptFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Idea.cfbFinalSig) (by decide) (by decide) (Nat.le_refl _)) residue.2.2.2.2.2.1

abbrev ofbCode : Prog isa := Impl.Idea.AArch64.Fn.ofb

theorem ofbCode_verified : Verified AArch64.target ofbCode (Spec.Idea.ofbContract AArch64.abi 208) :=
  Clears.Verified.withClears ofb_framed (by decide)

theorem ofbCode_noResidue : NoResidue ofbCode (Spec.Idea.ofbContract AArch64.abi 208) 0 :=
  noResidue_of_doneG ofbCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Idea.ofbSig) (by decide) (by decide) (Nat.le_refl _)) residue.2.2.2.2.2.2.1

abbrev ofbFinalCode : Prog isa := Impl.Idea.AArch64.Fn.ofbFinal

theorem ofbFinalCode_verified : Verified AArch64.target ofbFinalCode (Spec.Idea.ofbFinalContract AArch64.abi 208) :=
  Clears.Verified.withClears ofbFinal_framed (by decide)

theorem ofbFinalCode_noResidue : NoResidue ofbFinalCode (Spec.Idea.ofbFinalContract AArch64.abi 208) 0 :=
  noResidue_of_doneG ofbFinalCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Idea.ofbFinalSig) (by decide) (by decide) (Nat.le_refl _)) residue.2.2.2.2.2.2.2

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Idea.AArch64.Fn.cbcEncryptChained
      (Spec.Idea.cbcEncryptChainedContract AArch64.abi 208) 0 :=
  ⟨Proof.Idea.AArch64.ModesResidue.cbcEncryptChainedCode_verified,
    Proof.Idea.AArch64.ModesResidue.cbcEncryptChainedCode_noResidue, fun ty _ h => by cases ty <;> cases h⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Idea.AArch64.Fn.cbcDecryptChained
      (Spec.Idea.cbcDecryptChainedContract AArch64.abi 208) 0 :=
  ⟨Proof.Idea.AArch64.ModesResidue.cbcDecryptChainedCode_verified,
    Proof.Idea.AArch64.ModesResidue.cbcDecryptChainedCode_noResidue, fun ty _ h => by cases ty <;> cases h⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.ModesResidue.cfbEncryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Idea.AArch64.Fn.cfbEncrypt
      (Spec.Idea.cfbEncryptContract AArch64.abi 208) 0 :=
  ⟨Proof.Idea.AArch64.ModesResidue.cfbEncryptCode_verified,
    Proof.Idea.AArch64.ModesResidue.cfbEncryptCode_noResidue, fun ty _ h => by cases ty <;> cases h⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.ModesResidue.cfbDecryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Idea.AArch64.Fn.cfbDecrypt
      (Spec.Idea.cfbDecryptContract AArch64.abi 208) 0 :=
  ⟨Proof.Idea.AArch64.ModesResidue.cfbDecryptCode_verified,
    Proof.Idea.AArch64.ModesResidue.cfbDecryptCode_noResidue, fun ty _ h => by cases ty <;> cases h⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.ModesResidue.cfbEncryptFinalCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Idea.AArch64.Fn.cfbEncryptFinal
      (Spec.Idea.cfbEncryptFinalContract AArch64.abi 208) 0 :=
  ⟨Proof.Idea.AArch64.ModesResidue.cfbEncryptFinalCode_verified,
    Proof.Idea.AArch64.ModesResidue.cfbEncryptFinalCode_noResidue, fun ty _ h => by cases ty <;> cases h⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.ModesResidue.cfbDecryptFinalCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Idea.AArch64.Fn.cfbDecryptFinal
      (Spec.Idea.cfbDecryptFinalContract AArch64.abi 208) 0 :=
  ⟨Proof.Idea.AArch64.ModesResidue.cfbDecryptFinalCode_verified,
    Proof.Idea.AArch64.ModesResidue.cfbDecryptFinalCode_noResidue, fun ty _ h => by cases ty <;> cases h⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.ModesResidue.ofbCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Idea.AArch64.Fn.ofb
      (Spec.Idea.ofbContract AArch64.abi 208) 0 :=
  ⟨Proof.Idea.AArch64.ModesResidue.ofbCode_verified,
    Proof.Idea.AArch64.ModesResidue.ofbCode_noResidue, fun ty _ h => by cases ty <;> cases h⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Idea.AArch64.ModesResidue.ofbFinalCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Idea.AArch64.Fn.ofbFinal
      (Spec.Idea.ofbFinalContract AArch64.abi 208) 0 :=
  ⟨Proof.Idea.AArch64.ModesResidue.ofbFinalCode_verified,
    Proof.Idea.AArch64.ModesResidue.ofbFinalCode_noResidue, fun ty _ h => by cases ty <;> cases h⟩

end VG.Proof.Idea.AArch64.ModesResidue
