import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtUnit
import VerifiedGarbage.Proof.Bignum.CrtExp

/-!
# RSA with the CRT on AArch64: the window's table

In a prime's workspace at `P` (`X`, `w_X` words, `R = 2^(64 w_X)`), with
`Y ≡ R` and `[aXc] ≡ x R`: `tabBuild` writes the table `T_j ≡ x^j R` after
the arrays (`tabBuild_ok`), and `tabSelect` reads entry `v` into `[aT]` by a
masked selection from every entry (`tabSel_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop)

/-! ## The prime's workspace -/

/-- What the exponentiation keeps in the workspace at `P` (`w_X` words) and
its table: the prime `X` (and its low word, for `-X⁻¹`), and `Xc`. -/
structure CExpCtx (t : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) : Prop where
  good : Good t P (slot wx 8) wx minv
  scrT : Scr t P (slot wx 8 + tabBytes wx)
  n : wv t.mem P (slot wx aN) wx = X
  inv : ((word t.mem P (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  x : wv t.mem P (slot wx Crt.aXc) wx = Xc

theorem CExpCtx.ld {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) {i : Nat} (hi : i < 32) : InRegions (t.rd ++ t.wr) (off P (8 * i)) 8 :=
  hc.good.scr.ld (by have := hdr_lt_slot wx 8 hi; omega_arith)

theorem CExpCtx.st {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) {i : Nat} (hi : i < 32) : InRegions t.wr (off P (8 * i)) 8 :=
  hc.good.scr.st (by have := hdr_lt_slot wx 8 hi; omega_arith)

/-- What changes only within the exponentiation's ranges keeps the context. -/
theorem CExpCtx.of_frm {t t' : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hf : Frm P (crtExpRanges wx) t.mem t'.mem) (hwr : t'.wr = t.wr)
    (h0 : t'.gpr .x0 = t.gpr .x0) : CExpCtx t' P wx minv X Xc := by
  have hn := hc.scrT.nowrap
  have rN := crtExpRanges_arr wx (j := aN) (by decide) (by decide) (by decide) (by decide) (by decide)
  have rX := crtExpRanges_arr wx (j := Crt.aXc) (by decide) (by decide) (by decide) (by decide) (by decide)
  have lN := slot_le (w := wx) (show aN < 8 by decide)
  have lX := slot_le (w := wx) (show Crt.aXc < 8 by decide)
  have hh : ∀ i < 17, word t'.mem P (8 * i) = word t.mem P (8 * i) := fun i hi =>
    hf.word_eq (fun r hr => Or.inl (by have := crtExpRanges_ok wx r hr; omega_arith))
      (by have := hdr_lt_slot wx 8 (show i < 32 by omega_arith); omega_arith)
  exact ⟨⟨hc.good.scr.congr hwr, h0.trans hc.good.x0,
    ⟨(hh _ (by decide)).trans hc.good.hdr.hw, (hh _ (by decide)).trans hc.good.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega_arith)).trans (hc.good.hdr.harr j hj)⟩⟩, hc.scrT.congr hwr,
    by rw [hf.wv_eq (fun r hr => by have := rN r hr; omega_arith) (by omega_arith)]; exact hc.n,
    by rw [hf.word_eq (fun r hr => by have := rN r hr; omega_arith) (by omega_arith)]; exact hc.inv,
    by rw [hf.wv_eq (fun r hr => by have := rX r hr; omega_arith) (by omega_arith)]; exact hc.x⟩

theorem CExpCtx.of_win {t t' : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hf : Frm P (crtWinRanges wx) t.mem t'.mem) (hwr : t'.wr = t.wr)
    (h0 : t'.gpr .x0 = t.gpr .x0) : CExpCtx t' P wx minv X Xc :=
  hc.of_frm (hf.mono (crtWinRanges_sub wx)) hwr h0

/-! ## The table's entries -/

/-- A left shift by 3: times 8. -/
theorem shl3_ofNat {n : Nat} (h : 8 * n < 2 ^ 64) : BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (8 * n) := by
  rw [shl_ofNat (by rw [Nat.mul_comm]; exact h), Nat.mul_comm]; rfl

/-- `sEnt` moves up an entry. -/
theorem nextEnt_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hw : wx < 2 ^ 30) {e : Nat} (he : word t.mem P (8 * Crt.sEnt) = off P e) :
    WP isa nextEnt t fun t' => t'.mem = t.mem.writeW (off P (8 * Crt.sEnt)) (off P (e + 8 * (wx + 2))) ∧
      Keep [.x3, .x4] t t' := by
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t' => t'.mem = t.mem.writeW (off P (8 * Crt.sEnt))
    (off P (e + 8 * (wx + 2)))) ?_ (by decide) (by decide) (by decide +kernel)) fun t' ⟨h, k⟩ => ⟨h, k⟩
  unfold nextEnt
  brun [hc.good.x0, hdr_enc (show Crt.sEnt < 32 by decide), hdr_enc (show sW < 32 by decide),
    hc.ld (i := Crt.sEnt) (by decide), hc.ld (i := sW) (by decide), hc.st (i := Crt.sEnt) (by decide), he,
    hc.good.hdr.hw, ofNat_add_ofNat, shl3_ofNat (show 8 * (wx + 2) < 2 ^ 64 by omega)]

/-- `toEnt a`: entry `j`, at `sEnt`, `:= [a]`. -/
theorem toEnt_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) {a j : Nat} (ha : a < 8) (hj : j < 16)
    (he : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + j))) :
    WP isa (seqs (toEnt a)) t fun t' => wv t'.mem P (slot wx (8 + j)) wx = wv t.mem P (slot wx a) wx ∧
      Outside P (slot wx (8 + j)) (8 * wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  have hT := ent_le wx hj
  have sa := slot_le (w := wx) ha
  have sp := slot_sep (w := wx) (show a ≠ 8 + j by omega_arith)
  unfold toEnt
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x12, .x16, .x17] (Q := fun t₁ => t₁.gpr .x12 = BitVec.ofNat 64 wx ∧
      t₁.gpr .x16 = off P (slot wx a) ∧ t₁.gpr .x17 = off P (slot wx (8 + j)) ∧ t₁.mem = t.mem)
    (by brun [hc.good.x0, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt ha), hdr_enc (show Crt.sEnt < 32 by decide),
      hc.ld (i := sArr a) (sArr_lt ha), hc.ld (i := Crt.sEnt) (by decide), hc.ld (i := sW) (by decide),
      hc.good.hdr.harr a ha, he, hc.good.hdr.hw]) rfl rfl rfl) fun t₁ ⟨⟨h12, h16, h17, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hc.scrT.congr k₁.wr
  refine WP.mono (copyWords_ok h16 h17 h12 (by omega_arith) (by omega_arith) (by omega_arith)
    (fun i hi => hs₁.ld (by omega_arith)) (fun i hi => hs₁.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off P (by omega_arith)]; omega_arith))
    fun t' ⟨hv, _, ho', _, _, k⟩ => ⟨by rw [hv, hm₁], by rw [hm₁] at ho'; exact ho', (k₁.trans k).mono (by decide)⟩

/-! ## Reading an entry -/

/-- The selection's start: `sEnt := sTab`, `sJ := 0`. -/
theorem selInit_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) (ht : word t.mem P (8 * Crt.sTab) = off P (slot wx 8)) :
    WP isa (.block [ldh .x3 Crt.sTab, sth .x3 Crt.sEnt, movi .x3 0, sth .x3 Crt.sJ]) t fun t' =>
      t'.mem = (t.mem.writeW (off P (8 * Crt.sEnt)) (off P (slot wx 8))).writeW (off P (8 * Crt.sJ))
        (BitVec.ofNat 64 0) ∧ Keep [.x3] t t' := by
  refine WP.keep [.x3] ?_ (by decide) (by decide) (by decide +kernel)
  brun [hc.good.x0, hdr_enc (show Crt.sTab < 32 by decide), hdr_enc (show Crt.sEnt < 32 by decide),
    hdr_enc (show Crt.sJ < 32 by decide), hc.ld (i := Crt.sTab) (by decide), ht,
    hc.st (i := Crt.sEnt) (by decide), hc.st (i := Crt.sJ) (by decide)]
  rfl

/-- The instructions that start reading entry `j`: its mask and the
selection's bases. -/
def selHead : List Instr :=
  [ldh .x3 Crt.sJ, ldh .x4 Crt.sNib, .logic .eor .x .x3 .x3 .x4, movi .x4 1, .subs .x .x3 .x3 .x4, movi .x7 0] ++
    borrowMask ++ [ldh .x12 sW, ldh .x16 Crt.sEnt, ldh .x17 (sArr Crt.aT), mov .x14 .x12]

theorem ofNat64_xor_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    decide (BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b = 0) = decide (a = b) :=
  decide_eq_decide.mpr (xor_eq_zero_iff.trans (ofNat64_inj ha hb))

/-- An entry's mask and the selection's bases. -/
theorem selHead_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) {j v : Nat} (hj : j < 16) (hv : v < 16)
    (hJ : word t.mem P (8 * Crt.sJ) = BitVec.ofNat 64 j) (hN : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v)
    (hE : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + j))) :
    WP isa (.block selHead) t fun t' =>
      (t'.gpr .x15 = mask (decide (j = v)) ∧ t'.gpr .x14 = BitVec.ofNat 64 wx ∧
      t'.gpr .x16 = off P (slot wx (8 + j)) ∧ t'.gpr .x17 = off P (slot wx Crt.aT) ∧ t'.mem = t.mem) ∧
      Keep [.x3, .x4, .x7, .x12, .x14, .x15, .x16, .x17] t t' := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [selHead, borrowMask, hc.good.x0, hdr_enc (show Crt.sJ < 32 by decide), hdr_enc (show Crt.sNib < 32 by decide),
    hdr_enc (show sW < 32 by decide), hdr_enc (show Crt.sEnt < 32 by decide),
    hdr_enc (sArr_lt (show Crt.aT < 8 by decide)), hc.ld (i := Crt.sJ) (by decide),
    hc.ld (i := Crt.sNib) (by decide), hc.ld (i := sW) (by decide), hc.ld (i := Crt.sEnt) (by decide),
    hc.ld (i := sArr Crt.aT) (by decide), hJ, hN, hE, hc.good.hdr.hw, hc.good.hdr.harr Crt.aT (by decide),
    subs_one_c, csel_mask', Bool.not_not, ofNat64_xor_eq (show j < 2 ^ 64 by omega) (show v < 2 ^ 64 by omega)]

/-- The entry's index up, and `x4 := j + 1 - 16`. -/
theorem selEnd_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) {j : Nat} (hj : j < 16) (hJ : word t.mem P (8 * Crt.sJ) = BitVec.ofNat 64 j) :
    WP isa (.block [ldh .x3 Crt.sJ, .addImm .x .x3 .x3 1, sth .x3 Crt.sJ, .subImm .x .x4 .x3 16]) t fun t' =>
      (t'.mem = t.mem.writeW (off P (8 * Crt.sJ)) (BitVec.ofNat 64 (j + 1)) ∧
      ((t'.gpr .x4).toNat ≠ 0 ↔ j + 1 ≠ 16)) ∧ Keep [.x3, .x4] t t' := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [hc.good.x0, hdr_enc (show Crt.sJ < 32 by decide), hc.ld (i := Crt.sJ) (by decide),
    hc.st (i := Crt.sJ) (by decide), hJ, ofNat_add_ofNat]
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j + 1 < 2 ^ 64 by omega)]
  omega

/-- After `j` entries of the selection of entry `v` from `t₀`. -/
structure TabSelInv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc v : Nat) (j : Nat) (t : State) :
    Prop where
  ctx : CExpCtx t P wx minv X Xc
  nib : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v
  ent : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + j))
  idx : word t.mem P (8 * Crt.sJ) = BitVec.ofNat 64 j
  val : wv t.mem P (slot wx Crt.aT) wx =
    if v < j then wv t₀.mem P (slot wx (8 + v)) wx else wv t₀.mem P (slot wx Crt.aT) wx
  frm : Frm P (selRanges wx) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

/-- The selection's loop body, as a list. -/
def selBody : List (Prog isa) :=
  [.block selHead, selLoop, nextEnt,
    .block [ldh .x3 Crt.sJ, .addImm .x .x3 .x3 1, sth .x3 Crt.sJ, .subImm .x .x4 .x3 16]]

theorem tabSelect_eq : tabSelect = [.block [ldh .x3 Crt.sTab, sth .x3 Crt.sEnt, movi .x3 0, sth .x3 Crt.sJ],
    .loop (seqs selBody) (.nonzero .x .x4)] := rfl

/-- Entry `j` of the selection. -/
theorem selStep_ok {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v j : Nat}
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 16) (hj : j < 16) (hI : TabSelInv t₀ P wx minv X Xc v j t) :
    WP isa (seqs selBody) t fun t' =>
      TabSelInv t₀ P wx minv X Xc v (j + 1) t' ∧ ((t'.gpr .x4).toNat ≠ 0 ↔ j + 1 ≠ 16) := by
  have hc := hI.ctx
  have hn := hc.scrT.nowrap
  have hE := ent_le wx hj
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have hTE := slot_sep (w := wx) (show Crt.aT ≠ 8 + j by unfold Crt.aT; omega_arith)
  have hE8 := slot_mono wx (show 8 ≤ 8 + j by omega_arith)
  simp only [selBody, seqs]
  refine WP.seq (WP.mono (selHead_ok hc hj hv hI.idx hI.nib hI.ent)
    fun t₁ ⟨⟨h15, h14, h16, h17, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hc.scrT.congr k₁.wr
  refine WP.seq (WP.mono (selLoop_ok hs₁ h16 h17 h14 h15 (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith)) fun t₂ ⟨hsel₂, o₂, k₂⟩ => ?_)
  have f₂ : Frm P (selRanges wx) t₁.mem t₂.mem :=
    Frm.of_outside (o₂.mono (o' := slot wx Crt.aT) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_arith))
      (by simp [selRanges])
  have hc₂ : CExpCtx t₂ P wx minv X Xc :=
    hc.of_win ((by rw [hm₁]; exact Frm.refl _ _ _ : Frm P (crtWinRanges wx) t.mem t₁.mem).trans
      (f₂.mono (selRanges_sub wx))) (k₂.wr.trans k₁.wr) ((k₂.gpr .x0 (by decide)).trans (k₁.gpr .x0 (by decide)))
  have hh₂ : ∀ k < 32, word t₂.mem P (8 * k) = word t.mem P (8 * k) := fun k hk => by
    rw [o₂.word (by have := hdr_lt_slot wx Crt.aT hk; omega_arith) (by omega_arith), hm₁]
  refine WP.seq (WP.mono (nextEnt_ok (e := slot wx (8 + j)) hc₂ hw' (by rw [hh₂ _ (by decide)]; exact hI.ent))
    fun t₃ ⟨hm₃, k₃⟩ => ?_)
  have o₃ := writeW_outside t₂.mem P (d := 8 * Crt.sEnt) (off P (slot wx (8 + j) + 8 * (wx + 2))) (by decide)
  rw [← hm₃] at o₃
  have f₃ : Frm P (selRanges wx) t₂.mem t₃.mem := Frm.of_outside o₃ (by simp [selRanges])
  have hc₃ := hc₂.of_win (f₃.mono (selRanges_sub wx)) k₃.wr (k₃.gpr .x0 (by decide))
  refine WP.mono (selEnd_ok hc₃ hj (by
    rw [hm₃, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₂ _ (by decide)]; exact hI.idx))
    fun t' ⟨⟨hm', hz'⟩, k'⟩ => ⟨?_, hz'⟩
  have o₄ := writeW_outside t₃.mem P (d := 8 * Crt.sJ) (BitVec.ofNat 64 (j + 1)) (by decide)
  rw [← hm'] at o₄
  have f₄ : Frm P (selRanges wx) t₃.mem t'.mem := Frm.of_outside o₄ (by simp [selRanges])
  have hTv : wv t'.mem P (slot wx Crt.aT) wx = wv t₂.mem P (slot wx Crt.aT) wx := by
    rw [o₄.wv (by have := hdr_lt_slot wx Crt.aT (show Crt.sJ < 32 by decide); omega_arith) (by omega_arith),
      o₃.wv (by have := hdr_lt_slot wx Crt.aT (show Crt.sEnt < 32 by decide); omega_arith) (by omega_arith)]
  have hEv : wv t.mem P (slot wx (8 + j)) wx = wv t₀.mem P (slot wx (8 + j)) wx :=
    hI.frm.wv_eq (fun r hr => by
      have := hdr_lt_slot wx (8 + j) (show 31 < 32 by decide)
      simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega_arith
      · simp only [Crt.sEnt, sFn]; omega_arith
      · simp only [Crt.sJ, sFn]; omega_arith) (by omega_arith)
  refine ⟨hc₃.of_win (f₄.mono (selRanges_sub wx)) k'.wr (k'.gpr .x0 (by decide)), ?_, ?_, ?_, ?_,
    ((((hI.frm.trans (by rw [hm₁]; exact Frm.refl _ _ _)).trans f₂).trans f₃).trans f₄),
    ((((hI.keep.trans k₁).trans k₂).trans k₃).trans k').mono (by decide)⟩
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hm₃,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₂ _ (by decide)]; exact hI.nib
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hm₃, word_writeW_self, ← slot_succ,
      Nat.add_assoc]
  · rw [hm', word_writeW_self]
  · rw [hTv, hsel₂, hm₁, hI.val]
    by_cases hjv : j = v
    · subst hjv
      simp only [decide_true, ↓reduceIte, Nat.lt_succ_self]
      exact hEv
    · simp only [hjv, decide_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hvj : v < j
      · simp only [hvj, ↓reduceIte, show v < j + 1 by omega_arith]
      · simp only [hvj, ↓reduceIte, show ¬ v < j + 1 by omega_arith]

/-- The selection: `[aT] := T_v`. -/
theorem tabSel_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 16)
    (ht : word t.mem P (8 * Crt.sTab) = off P (slot wx 8)) (hN : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (seqs tabSelect) t fun t' => CExpCtx t' P wx minv X Xc ∧
      wv t'.mem P (slot wx Crt.aT) wx = wv t.mem P (slot wx (8 + v)) wx ∧
      Frm P (selRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  rw [tabSelect_eq]
  simp only [seqs]
  refine WP.seq (WP.mono (selInit_ok hc ht) fun t₁ ⟨hm₁, k₁⟩ => ?_)
  have o1 := writeW_outside t.mem P (d := 8 * Crt.sEnt) (off P (slot wx 8)) (by decide)
  have o2 := writeW_outside (t.mem.writeW (off P (8 * Crt.sEnt)) (off P (slot wx 8))) P (d := 8 * Crt.sJ)
    (BitVec.ofNat 64 0) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm P (selRanges wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [selRanges])).trans (Frm.of_outside o2 (by simp [selRanges]))
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have h₁ : TabSelInv t₁ P wx minv X Xc v 0 t₁ := by
    refine ⟨hc.of_win (f₁.mono (selRanges_sub wx)) k₁.wr (k₁.gpr .x0 (by decide)), ?_, ?_, ?_, by simp,
      Frm.refl _ _ _, Keep.refl _ _⟩
    · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hN
    · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hm₁, word_writeW_self]
  refine WP.mono (count_loop (cr := .x4) (n := 16) (by decide) (TabSelInv t₁ P wx minv X Xc v)
    (fun j hj s hI => selStep_ok hw hw' hv hj hI) h₁) fun t' hI => ?_
  have hEv : wv t₁.mem P (slot wx (8 + v)) wx = wv t.mem P (slot wx (8 + v)) wx :=
    f₁.wv_eq (fun r hr => by
      have := slot_mono wx (show 8 ≤ 8 + v by omega_arith)
      simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega_arith
      · simp only [Crt.sEnt, sFn]; have := hdr_lt_slot wx 8 (show 31 < 32 by decide); omega_arith
      · simp only [Crt.sJ, sFn]; have := hdr_lt_slot wx 8 (show 31 < 32 by decide); omega_arith)
      (by have := ent_le wx hv; omega_arith)
  refine ⟨hI.ctx, by rw [hI.val]; simp only [hv, ↓reduceIte]; exact hEv, f₁.trans hI.frm,
    (k₁.trans hI.keep).mono (by decide)⟩

end VG.Proof.Bignum.AArch64
