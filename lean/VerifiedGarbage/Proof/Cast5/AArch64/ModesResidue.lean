module

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
public import VerifiedGarbage.Impl.Residue.AArch64
public meta import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub
public meta import VerifiedGarbage.Impl.Residue.AArch64.Scrub
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
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
  zero that granule (`withScrubG 112 [6]`).
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64.ModesResidue

open VG VG.AArch64 VG.Impl.Residue.AArch64 VG.AArch64.RTaintF VG.AArch64.RTaintG
  VG.Proof.Cast5.AArch64.FbResidue

/-! ## From tables, in 224 bytes -/

abbrev tblCleared (c : Prog isa) : Prog isa :=
  withClears [.x6, .x8, .x9] [.v0, .v1, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22,
    .v23, .v24, .v25, .v26, .v27] (some .x6) c

abbrev cbcDecryptChainedCode : Prog isa :=
  tblCleared (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x5 28 Impl.Cast5.AArch64.Tbl.cbcDecryptChained)

theorem cbcDecryptChainedCode_verified :
    Verified AArch64.target cbcDecryptChainedCode (Spec.Cast5.cbcDecryptChainedContract AArch64.abi 224) :=
  Clears.Verified.withClears (Proof.Cast5.cbcDecryptChained_keyed Proof.Cast5.AArch64.Tbl.cbcDecryptChained_framed)
    (by decide)

theorem cbcDecryptChainedCode_noResidue :
    NoResidue cbcDecryptChainedCode (Spec.Cast5.cbcDecryptChainedContract AArch64.abi 224) 0 :=
  noResidue_of_doneG cbcDecryptChainedCode_verified ⟨by decide, by decide, by decide⟩
    (sp_of_pre (sig := Spec.Cast5.cbcChainedSig) (by decide) (by decide) (Nat.le_refl _)) ⟨_, by taint_decide_ct⟩

abbrev cfbDecryptCode : Prog isa :=
  tblCleared (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x5 28 Impl.Cast5.AArch64.Tbl.cfbDecrypt)

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

abbrev cbcEncryptChainedBase : Prog isa :=
  ofbCleared (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cbcEncryptChained)

abbrev cbcEncryptChainedCode : Prog isa := withScrubG 112 [6] cbcEncryptChainedBase

theorem cbcEncryptChainedBase_verified : Verified AArch64.target cbcEncryptChainedBase (Spec.Cast5.cbcEncryptChainedContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) :=
  Clears.Verified.withClears_of (Proof.Cast5.cbcEncryptChained_keyed Proof.Cast5.AArch64.cbcEncryptChained_framed)
    (fun hq hm hx => post_consts.mpr (Clears.post_congr (post_consts.mp hq) hm hx)) (by decide)

theorem cbcEncryptChainedCode_verified : Verified AArch64.target cbcEncryptChainedCode (Spec.Cast5.cbcEncryptChainedContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) :=
  RTaintG.Verified.withScrubG cbcEncryptChainedBase_verified ⟨by decide, by decide, by decide⟩ (by decide) cbcEncryptChainedScrubOk

theorem cbcEncryptChainedCode_noResidue : NoResidue cbcEncryptChainedCode (Spec.Cast5.cbcEncryptChainedContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) 0 :=
  noResidue_withScrubG (P₀ := 0) cbcEncryptChainedBase_verified ⟨by decide, by decide, by decide⟩ cbcEncryptChainedScrubOk.sp
    (fun _ _ _ _ _ hb => by simp at hb) ⟨_, by taint_decide_ct⟩

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

abbrev cfbEncryptBase : Prog isa :=
  ofbCleared (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cfbEncrypt)

abbrev cfbEncryptCode : Prog isa := withScrubG 112 [6] cfbEncryptBase

theorem cfbEncryptBase_verified : Verified AArch64.target cfbEncryptBase (Spec.Cast5.cfbEncryptContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) :=
  Clears.Verified.withClears_of (Proof.Cast5.cfbEncrypt_keyed Proof.Cast5.AArch64.cfbEncrypt_framed)
    (fun hq hm hx => post_consts.mpr (Clears.post_congr (post_consts.mp hq) hm hx)) (by decide)

theorem cfbEncryptCode_verified : Verified AArch64.target cfbEncryptCode (Spec.Cast5.cfbEncryptContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) :=
  RTaintG.Verified.withScrubG cfbEncryptBase_verified ⟨by decide, by decide, by decide⟩ (by decide) cfbEncryptScrubOk

theorem cfbEncryptCode_noResidue : NoResidue cfbEncryptCode (Spec.Cast5.cfbEncryptContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) 0 :=
  noResidue_withScrubG (P₀ := 0) cfbEncryptBase_verified ⟨by decide, by decide, by decide⟩ cfbEncryptScrubOk.sp
    (fun _ _ _ _ _ hb => by simp at hb) ⟨_, by taint_decide_ct⟩

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

abbrev cfbEncryptFinalBase : Prog isa :=
  ofbCleared (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cfbEncryptFinal)

abbrev cfbEncryptFinalCode : Prog isa := withScrubG 112 [6] cfbEncryptFinalBase

theorem cfbEncryptFinalBase_verified : Verified AArch64.target cfbEncryptFinalBase (Spec.Cast5.cfbEncryptFinalContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) :=
  Clears.Verified.withClears_of (Proof.Cast5.cfbEncryptFinal_keyed Proof.Cast5.AArch64.cfbEncryptFinal_framed)
    (fun hq hm hx => post_consts.mpr (Clears.post_congr (post_consts.mp hq) hm hx)) (by decide)

theorem cfbEncryptFinalCode_verified : Verified AArch64.target cfbEncryptFinalCode (Spec.Cast5.cfbEncryptFinalContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) :=
  RTaintG.Verified.withScrubG cfbEncryptFinalBase_verified ⟨by decide, by decide, by decide⟩ (by decide) cfbEncryptFinalScrubOk

theorem cfbEncryptFinalCode_noResidue : NoResidue cfbEncryptFinalCode (Spec.Cast5.cfbEncryptFinalContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) 0 :=
  noResidue_withScrubG (P₀ := 0) cfbEncryptFinalBase_verified ⟨by decide, by decide, by decide⟩ cfbEncryptFinalScrubOk.sp
    (fun _ _ _ _ _ hb => by simp at hb) ⟨_, by taint_decide_ct⟩

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

abbrev cfbDecryptFinalBase : Prog isa :=
  ofbCleared (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cfbDecryptFinal)

abbrev cfbDecryptFinalCode : Prog isa := withScrubG 112 [6] cfbDecryptFinalBase

theorem cfbDecryptFinalBase_verified : Verified AArch64.target cfbDecryptFinalBase (Spec.Cast5.cfbDecryptFinalContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) :=
  Clears.Verified.withClears_of (Proof.Cast5.cfbDecryptFinal_keyed Proof.Cast5.AArch64.cfbDecryptFinal_framed)
    (fun hq hm hx => post_consts.mpr (Clears.post_congr (post_consts.mp hq) hm hx)) (by decide)

theorem cfbDecryptFinalCode_verified : Verified AArch64.target cfbDecryptFinalCode (Spec.Cast5.cfbDecryptFinalContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) :=
  RTaintG.Verified.withScrubG cfbDecryptFinalBase_verified ⟨by decide, by decide, by decide⟩ (by decide) cfbDecryptFinalScrubOk

theorem cfbDecryptFinalCode_noResidue : NoResidue cfbDecryptFinalCode (Spec.Cast5.cfbDecryptFinalContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112) 0 :=
  noResidue_withScrubG (P₀ := 0) cfbDecryptFinalBase_verified ⟨by decide, by decide, by decide⟩ cfbDecryptFinalScrubOk.sp
    (fun _ _ _ _ _ hb => by simp at hb) ⟨_, by taint_decide_ct⟩

end VG.Proof.Cast5.AArch64.ModesResidue
