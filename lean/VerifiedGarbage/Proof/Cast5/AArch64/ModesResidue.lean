module

public import VerifiedGarbage.Impl.Cast5.AArch64.Fn
public meta import VerifiedGarbage.Impl.Cast5.AArch64.Fn
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Cast5.AArch64.CbcVerified
public meta import VerifiedGarbage.Proof.Cast5.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
public meta import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalVerified
public meta import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.TblModesVerified
public meta import VerifiedGarbage.Proof.Cast5.AArch64.TblModesVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.FbResidue
public meta import VerifiedGarbage.Proof.Cast5.AArch64.FbResidue
public import VerifiedGarbage.Proof.Cast5.Rounds
public meta import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Proof.Cast5.CfbFinal
public meta import VerifiedGarbage.Proof.Cast5.CfbFinal
public import VerifiedGarbage.Impl.Scrub.AArch64
public meta import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub
public meta import VerifiedGarbage.Impl.Scrub.AArch64.Scrub
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubSel
public meta import VerifiedGarbage.Proof.Framework.AArch64.ScrubSel
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalLit
meta import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
meta import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# CAST5's CBC and CFB64 modes on AArch64 return without secret residue

The analysis of the window's bytes (`rtaintG`) finds, on return:

* `vg_cast5_cbc_decrypt_chained` and `vg_cast5_cfb64_decrypt`, which run
  their frame of 224 bytes from tables (`Tbl`), with every byte of it the
  same in both runs: they clear only their registers.
* `vg_cast5_cbc_encrypt_chained`, `vg_cast5_cfb64_encrypt` and the two
  `_final` functions, in a frame of 112 bytes whose scratch words they zero,
  with only its last granule (bytes 96–111 of the window) possibly differing:
  they clear their registers as CAST5-OFB does (`FbResidue.ofbCleared`), then
  zero that granule (`scrubSel 112 [6]`).
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64.ModesResidue

open VG VG.AArch64 VG.Impl.Scrub.AArch64 VG.AArch64.RTaintF VG.AArch64.RTaintG
  VG.Proof.Cast5.AArch64.FbResidue

/-! ## From tables, in 224 bytes -/

abbrev tblCleared (c : Prog isa) : Prog isa := Impl.Cast5.AArch64.Fn.tblCleared c

abbrev cbcDecryptChainedCode : Prog isa := Impl.Cast5.AArch64.Fn.cbcDecryptChained

theorem cbcDecryptChainedCode_verified :
    Verified AArch64.target cbcDecryptChainedCode (Spec.Cast5.cbcDecryptChainedContract AArch64.abi 224) :=
  Clears.Verified.withClears (Proof.Cast5.cbcDecryptChained_keyed Proof.Cast5.AArch64.Tbl.cbcDecryptChained_framed)
    (by decide)

theorem cbcDecryptChainedCode_noResidue :
    NoResidue cbcDecryptChainedCode (Spec.Cast5.cbcDecryptChainedContract AArch64.abi 224) 0 :=
  noResidue_of_doneG cbcDecryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Cast5.cbcChainedSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

abbrev cfbDecryptCode : Prog isa := Impl.Cast5.AArch64.Fn.cfbDecrypt

theorem cfbDecryptCode_verified :
    Verified AArch64.target cfbDecryptCode (Spec.Cast5.cfbDecryptContract AArch64.abi 224) :=
  Clears.Verified.withClears (Proof.Cast5.cfbDecrypt_keyed Proof.Cast5.AArch64.Tbl.cfbDecrypt_framed) (by decide)

theorem cfbDecryptCode_noResidue :
    NoResidue cfbDecryptCode (Spec.Cast5.cfbDecryptContract AArch64.abi 224) 0 :=
  noResidue_of_doneG cfbDecryptCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Cast5.cfbSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

/-! ## In 112 bytes, with the last granule zeroed -/

theorem cbcEncryptChainedScrubOk : ScrubOk (Spec.Cast5.cbcEncryptChainedContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) 112 :=
  scrubOk_consts (sig := Spec.Cast5.cbcChainedSig) (c₀ := (Impl.Cast5.s1234Sym, Impl.Cast5.s1234)) (cs := [])
    (W := 112) (by decide) (by decide) (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key → Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      obtain ⟨h₁, h₂⟩ := h key hk
      exact ⟨(cbcBlocksAt_of0 hb.2.2 (Nat.le_refl _)).trans h₁,
        (bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)).trans h₂⟩

abbrev cbcEncryptChainedBase : Prog isa := Impl.Cast5.AArch64.Fn.cbcEncryptChainedBase

abbrev cbcEncryptChainedCode : Prog isa := Impl.Cast5.AArch64.Fn.cbcEncryptChained

theorem cbcEncryptChainedBase_verified : Verified AArch64.target cbcEncryptChainedBase (Spec.Cast5.cbcEncryptChainedContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) :=
  Clears.Verified.withClears_of (Proof.Cast5.cbcEncryptChained_keyed Proof.Cast5.AArch64.cbcEncryptChained_framed)
    (fun hq hm hx => post_consts.mpr (Clears.post_congr (post_consts.mp hq) hm hx)) (by decide)

theorem cfbEncryptScrubOk : ScrubOk (Spec.Cast5.cfbEncryptContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) 112 :=
  scrubOk_consts (sig := Spec.Cast5.cfbSig) (c₀ := (Impl.Cast5.s1234Sym, Impl.Cast5.s1234)) (cs := [])
    (W := 112) (by decide) (by decide) (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key → Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      obtain ⟨h₁, h₂⟩ := h key hk
      exact ⟨(cbcBlocksAt_of0 hb.2.2 (Nat.le_refl _)).trans h₁,
        (bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)).trans h₂⟩

abbrev cfbEncryptBase : Prog isa := Impl.Cast5.AArch64.Fn.cfbEncryptBase

abbrev cfbEncryptCode : Prog isa := Impl.Cast5.AArch64.Fn.cfbEncrypt

theorem cfbEncryptBase_verified : Verified AArch64.target cfbEncryptBase (Spec.Cast5.cfbEncryptContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) :=
  Clears.Verified.withClears_of (Proof.Cast5.cfbEncrypt_keyed Proof.Cast5.AArch64.cfbEncrypt_framed)
    (fun hq hm hx => post_consts.mpr (Clears.post_congr (post_consts.mp hq) hm hx)) (by decide)

theorem cfbEncryptFinalScrubOk : ScrubOk (Spec.Cast5.cfbEncryptFinalContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) 112 :=
  scrubOk_consts (sig := Spec.Cast5.cfbFinalSig) (c₀ := (Impl.Cast5.s1234Sym, Impl.Cast5.s1234)) (cs := [])
    (W := 112) (by decide) (by decide) (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      obtain ⟨h₁, h₂⟩ := h key hk
      exact ⟨(bytesAt_of0 hb.2.2 (Nat.le_of_eq (Nat.mul_one _).symm)).trans h₁,
        (bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)).trans h₂⟩

abbrev cfbEncryptFinalBase : Prog isa := Impl.Cast5.AArch64.Fn.cfbEncryptFinalBase

abbrev cfbEncryptFinalCode : Prog isa := Impl.Cast5.AArch64.Fn.cfbEncryptFinal

theorem cfbEncryptFinalBase_verified : Verified AArch64.target cfbEncryptFinalBase (Spec.Cast5.cfbEncryptFinalContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) :=
  Clears.Verified.withClears_of (Proof.Cast5.cfbEncryptFinal_keyed Proof.Cast5.AArch64.cfbEncryptFinal_framed)
    (fun hq hm hx => post_consts.mpr (Clears.post_congr (post_consts.mp hq) hm hx)) (by decide)

theorem cfbDecryptFinalScrubOk : ScrubOk (Spec.Cast5.cfbDecryptFinalContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) 112 :=
  scrubOk_consts (sig := Spec.Cast5.cfbFinalSig) (c₀ := (Impl.Cast5.s1234Sym, Impl.Cast5.s1234)) (cs := [])
    (W := 112) (by decide) (by decide) (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      obtain ⟨h₁, h₂⟩ := h key hk
      exact ⟨(bytesAt_of0 hb.2.2 (Nat.le_of_eq (Nat.mul_one _).symm)).trans h₁,
        (bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)).trans h₂⟩

abbrev cfbDecryptFinalBase : Prog isa := Impl.Cast5.AArch64.Fn.cfbDecryptFinalBase

abbrev cfbDecryptFinalCode : Prog isa := Impl.Cast5.AArch64.Fn.cfbDecryptFinal

theorem cfbDecryptFinalBase_verified : Verified AArch64.target cfbDecryptFinalBase (Spec.Cast5.cfbDecryptFinalContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) :=
  Clears.Verified.withClears_of (Proof.Cast5.cfbDecryptFinal_keyed Proof.Cast5.AArch64.cfbDecryptFinal_framed)
    (fun hq hm hx => post_consts.mpr (Clears.post_congr (post_consts.mp hq) hm hx)) (by decide)

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Cast5.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Cast5.AArch64.Fn.cbcEncryptChained
      (Spec.Cast5.cbcEncryptChainedContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) 0 :=
  AArch64.Scrub.verifiedScrubbedSel (P₀ := 0) cbcEncryptChainedBase_verified ⟨by decide, by decide, by decide⟩ (by decide) cbcEncryptChainedScrubOk
    (fun _ _ _ _ _ hb => by simp at hb) ⟨_, by taint_decide_ct⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Cast5.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Cast5.AArch64.Fn.cbcDecryptChained
      (Spec.Cast5.cbcDecryptChainedContract AArch64.abi 224) 0 :=
  ⟨Proof.Cast5.AArch64.ModesResidue.cbcDecryptChainedCode_verified,
    Proof.Cast5.AArch64.ModesResidue.cbcDecryptChainedCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Cast5.AArch64.ModesResidue.cfbEncryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Cast5.AArch64.Fn.cfbEncrypt
      (Spec.Cast5.cfbEncryptContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) 0 :=
  AArch64.Scrub.verifiedScrubbedSel (P₀ := 0) cfbEncryptBase_verified ⟨by decide, by decide, by decide⟩ (by decide) cfbEncryptScrubOk
    (fun _ _ _ _ _ hb => by simp at hb) ⟨_, by taint_decide_ct⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Cast5.AArch64.ModesResidue.cfbDecryptCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Cast5.AArch64.Fn.cfbDecrypt
      (Spec.Cast5.cfbDecryptContract AArch64.abi 224) 0 :=
  ⟨Proof.Cast5.AArch64.ModesResidue.cfbDecryptCode_verified,
    Proof.Cast5.AArch64.ModesResidue.cfbDecryptCode_noResidue⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Cast5.AArch64.ModesResidue.cfbEncryptFinalCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Cast5.AArch64.Fn.cfbEncryptFinal
      (Spec.Cast5.cfbEncryptFinalContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) 0 :=
  AArch64.Scrub.verifiedScrubbedSel (P₀ := 0) cfbEncryptFinalBase_verified ⟨by decide, by decide, by decide⟩ (by decide) cfbEncryptFinalScrubOk
    (fun _ _ _ _ _ hb => by simp at hb) ⟨_, by taint_decide_ct⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Cast5.AArch64.ModesResidue.cfbDecryptFinalCode_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Cast5.AArch64.Fn.cfbDecryptFinal
      (Spec.Cast5.cfbDecryptFinalContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) 0 :=
  AArch64.Scrub.verifiedScrubbedSel (P₀ := 0) cfbDecryptFinalBase_verified ⟨by decide, by decide, by decide⟩ (by decide) cfbDecryptFinalScrubOk
    (fun _ _ _ _ _ hb => by simp at hb) ⟨_, by taint_decide_ct⟩

end VG.Proof.Cast5.AArch64.ModesResidue
