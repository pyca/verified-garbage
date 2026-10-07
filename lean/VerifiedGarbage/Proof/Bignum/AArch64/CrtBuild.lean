import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab

/-!
# RSA with the CRT on AArch64: building the window's table

`tabBuild` writes the table after the prime's arrays: `T_0 := Y ≡ R`,
`T_1 := [aXc] ≡ x R` (`tabPre_ok`), and `T_i := T_(i-1) [aXc] R⁻¹` for `i`
from 2 to 15 (`buildStep_ok`), counted down in `sBit` (`tabBuild_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop)

/-- The count in `sBit` decremented, into `x3`. -/
theorem crtBitEnd_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc b : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hb : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) :
    WP isa (.block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]) t
      fun t' => (t'.mem = t.mem.writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b - 1)) ∧
        t'.gpr .x3 = BitVec.ofNat 64 (b - 1)) ∧ Keep [.x3] t t' := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [hc.good.x0, hdr_enc (show Crt.sBit < 32 by decide), hc.ld (i := Crt.sBit) (by decide),
    hc.st (i := Crt.sBit) (by decide), hb, VG.Offset.ofNat_sub_ofNat hb1]

/-- The count's register, not zero iff the count is not. -/
theorem cnt_ne {b : Nat} (hb : b < 2 ^ 64) : (BitVec.ofNat 64 b).toNat ≠ 0 ↔ b ≠ 0 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

/-! ## The table -/

/-- The table's base, past the last array, into `sTab` and `sEnt`. -/
theorem tabInit_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hw : wx < 2 ^ 30) :
    WP isa (.block [ldh .x3 (sArr aOne), ldh .x4 sW, .addImm .x .x4 .x4 2, .lsl .x .x4 .x4 3, .add .x .x3 .x3 .x4,
      sth .x3 Crt.sTab, sth .x3 Crt.sEnt]) t fun t' =>
      t'.mem = (t.mem.writeW (off P (8 * Crt.sTab)) (off P (slot wx 8))).writeW (off P (8 * Crt.sEnt))
        (off P (slot wx 8)) ∧ Keep [.x3, .x4] t t' := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [hc.good.x0, hdr_enc (sArr_lt (show aOne < 8 by decide)), hdr_enc (show sW < 32 by decide),
    hdr_enc (show Crt.sTab < 32 by decide), hdr_enc (show Crt.sEnt < 32 by decide),
    hc.ld (i := sArr aOne) (by decide), hc.ld (i := sW) (by decide), hc.st (i := Crt.sTab) (by decide),
    hc.st (i := Crt.sEnt) (by decide), hc.good.hdr.harr aOne (by decide), hc.good.hdr.hw, ofNat_add_ofNat,
    shl3_ofNat (show 8 * (wx + 2) < 2 ^ 64 by omega), ← slot_succ]
  rfl

/-- `sBit := 14`, the count of the table's products. -/
theorem cnt14_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) :
    WP isa (.block [movi .x3 14, sth .x3 Crt.sBit]) t fun t' =>
      t'.mem = t.mem.writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 14) ∧ Keep [.x3] t t' := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [hc.good.x0, hdr_enc (show Crt.sBit < 32 by decide), hc.st (i := Crt.sBit) (by decide)]
  rfl

/-- After `i` of the table's products from `t₀`: entries `0 … i + 1`
written, `T ≡ x^(i+1) R` the last. -/
structure BuildInv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) (Q : Prop) (x : Nat)
    (i : Nat) (t : State) : Prop where
  ctx : CExpCtx t P wx minv X Xc
  tab : word t.mem P (8 * Crt.sTab) = off P (slot wx 8)
  ent : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + (i + 1)))
  cnt : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (14 - i)
  tlt : wv t.mem P (slot wx Crt.aT) wx < X
  tval : Q → wv t.mem P (slot wx Crt.aT) wx % X = x ^ (i + 1) * 2 ^ (64 * wx) % X
  elt : ∀ j < i + 2, wv t.mem P (slot wx (8 + j)) wx < X
  eval : Q → ∀ j < i + 2, wv t.mem P (slot wx (8 + j)) wx % X = x ^ j * 2 ^ (64 * wx) % X
  frm : Frm P (buildRanges wx) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

/-- A product of the table's build. -/
def tabBody (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [mul Crt.aT Crt.aT Crt.aXc, nextEnt] ++ (toEnt Crt.aT ++
    [.block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]])

/-- The table's product `i`. -/
theorem buildStep_ok (M : Mont) {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hXN : Xc < X)
    (hXc : Q → Xc % X = x * 2 ^ (64 * wx) % X) {i : Nat} (hi : i < 14)
    (hI : BuildInv t₀ P wx minv X Xc Q x i t) :
    WP isa (seqs (tabBody M.mm)) t
      fun t' => BuildInv t₀ P wx minv X Xc Q x (i + 1) t' ∧ ((t'.gpr .x3).toNat ≠ 0 ↔ i + 1 ≠ 14) := by
  have hc := hI.ctx
  have hn := hc.scrT.nowrap
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  unfold tabBody
  refine wp_seqs_append (by simp) (by simp [toEnt]) ?_
  simp only [seqs]
  -- `T := T Xc`.
  refine WP.seq (WP.mono (M.mm_ok (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) hc.good (Nat.le_refl _) hw
    (by omega_arith) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hc.x, hc.n]; exact hXN)) fun t₁ ⟨_, hlt₁, hm₁, ha₁, k₁⟩ => ?_)
  rw [hc.n] at hlt₁
  rw [hc.n, hc.x] at hm₁
  have f₁ : Frm P (buildRanges wx) t.mem t₁.mem := Frm.of_arrays ha₁ (by simp [buildRanges])
  have hc₁ := hc.of_frm (f₁.mono (buildRanges_sub wx)) k₁.wr (k₁.gpr .x0 (by decide))
  have he₁ : ∀ j < 16, wv t₁.mem P (slot wx (8 + j)) wx = wv t.mem P (slot wx (8 + j)) wx := fun j hj =>
    ha₁.wv_eq (fun k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      have := slot_mono wx (show 8 ≤ 8 + j by omega_arith)
      rcases hk with rfl | rfl | rfl
      · exact Or.inr (by have := slot_le (w := wx) (show aAcc < 8 by decide); omega_arith)
      · exact Or.inr (by have := slot_le (w := wx) (show aTmp < 8 by decide); omega_arith)
      · exact Or.inr (by omega_arith)) (by have := ent_le wx hj; omega_arith)
  -- `sEnt` up.
  refine WP.mono (nextEnt_ok (e := slot wx (8 + (i + 1))) hc₁ hw' (by rw [ha₁.hslot (by decide)]; exact hI.ent))
    fun t₂ ⟨hm₂, k₂⟩ => ?_
  have o₂ := writeW_outside t₁.mem P (d := 8 * Crt.sEnt) (off P (slot wx (8 + (i + 1)) + 8 * (wx + 2))) (by decide)
  rw [← hm₂] at o₂
  have f₂ : Frm P (buildRanges wx) t₁.mem t₂.mem := Frm.of_outside o₂ (by simp [buildRanges])
  have hc₂ := hc₁.of_frm (f₂.mono (buildRanges_sub wx)) k₂.wr (k₂.gpr .x0 (by decide))
  have hT₂ : wv t₂.mem P (slot wx Crt.aT) wx = wv t₁.mem P (slot wx Crt.aT) wx :=
    o₂.wv (by have := hdr_lt_slot wx Crt.aT (show Crt.sEnt < 32 by decide); omega_arith) (by omega_arith)
  have he₂ : ∀ j < 16, wv t₂.mem P (slot wx (8 + j)) wx = wv t₁.mem P (slot wx (8 + j)) wx := fun j hj =>
    o₂.wv (by have := hdr_lt_slot wx (8 + j) (show Crt.sEnt < 32 by decide); omega_arith)
      (by have := ent_le wx hj; omega_arith)
  -- Entry `i + 2 := T`.
  refine wp_seqs_append (by simp [toEnt]) (by simp) ?_
  refine WP.mono (toEnt_ok hc₂ hw hw' (a := Crt.aT) (j := i + 2) (by decide) (by omega_arith) (by
    rw [hm₂, word_writeW_self, ← slot_succ]; rfl)) fun t₃ ⟨hv₃, o₃, k₃⟩ => ?_
  have hE := ent_le wx (show i + 2 < 16 by omega_arith)
  have hE8 := slot_mono wx (show 8 ≤ 8 + (i + 2) by omega_arith)
  have f₃ : Frm P (buildRanges wx) t₂.mem t₃.mem :=
    Frm.of_outside (o₃.mono (o' := slot wx 8) (n' := tabBytes wx) hE8 (by omega_arith)) (by simp [buildRanges])
  have hc₃ := hc₂.of_frm (f₃.mono (buildRanges_sub wx)) k₃.wr (k₃.gpr .x0 (by decide))
  have hh₃ : ∀ k < 32, word t₃.mem P (8 * k) = word t₂.mem P (8 * k) := fun k hk =>
    o₃.word (by have := hdr_lt_slot wx (8 + (i + 2)) hk; omega_arith) (by omega_arith)
  have hT8 : slot wx Crt.aT + 8 * (wx + 2) ≤ slot wx (8 + (i + 2)) := by
    have := slot_mono wx (show Crt.aT + 1 ≤ 8 + (i + 2) by unfold Crt.aT; omega_arith)
    rw [slot_succ] at this; omega_arith
  have hT₃ : wv t₃.mem P (slot wx Crt.aT) wx = wv t₂.mem P (slot wx Crt.aT) wx :=
    o₃.wv (by omega_arith) (by omega_arith)
  simp only [seqs]
  -- The count.
  refine WP.mono (crtBitEnd_ok hc₃ (b := 14 - i) (by rw [hh₃ _ (by decide), hm₂,
    hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), ha₁.hslot (by decide)]; exact hI.cnt) (by omega_arith))
    fun t' ⟨⟨hm', h3'⟩, k'⟩ => ⟨?_, by rw [h3', cnt_ne (by omega_arith)]; omega_arith⟩
  have o₄ := writeW_outside t₃.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 (14 - i - 1)) (by decide)
  rw [← hm'] at o₄
  have f₄ : Frm P (buildRanges wx) t₃.mem t'.mem := Frm.of_outside o₄ (by simp [buildRanges])
  have hT' : wv t'.mem P (slot wx Crt.aT) wx = wv t₁.mem P (slot wx Crt.aT) wx := by
    rw [o₄.wv (by have := hdr_lt_slot wx Crt.aT (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith), hT₃,
      hT₂]
  have hE' : ∀ j < 16, wv t'.mem P (slot wx (8 + j)) wx = wv t₃.mem P (slot wx (8 + j)) wx := fun j hj =>
    o₄.wv (by have := hdr_lt_slot wx (8 + j) (show Crt.sBit < 32 by decide); omega_arith)
      (by have := ent_le wx hj; omega_arith)
  -- Entries other than `i + 2` are kept by `toEnt`.
  have hEo : ∀ j < 16, j ≠ i + 2 → wv t₃.mem P (slot wx (8 + j)) wx = wv t.mem P (slot wx (8 + j)) wx :=
    fun j hj hne => by
      have := slot_sep (w := wx) (show 8 + j ≠ 8 + (i + 2) by omega_arith)
      rw [o₃.wv (by omega_arith) (by have := ent_le wx hj; omega_arith), he₂ j hj, he₁ j hj]
  have hTv : Q → wv t₁.mem P (slot wx Crt.aT) wx % X = x ^ (i + 1 + 1) * 2 ^ (64 * wx) % X := fun hq =>
    mont_mulT (E := i + 1) (v := 1) hR (hI.tval hq) (by rw [Nat.pow_one]; exact hXc hq) hm₁
  refine ⟨hc₃.of_frm (f₄.mono (buildRanges_sub wx)) k'.wr (k'.gpr .x0 (by decide)), ?_, ?_, ?_, by rw [hT']; exact hlt₁,
    fun hq => by rw [hT']; exact hTv hq, fun j hj => ?_, fun hq j hj => ?_,
    (((hI.frm.trans f₁).trans f₂).trans f₃).trans f₄, ((((hI.keep.trans k₁).trans k₂).trans k₃).trans k').mono
      (by decide)⟩
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₃ _ (by decide), hm₂,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), ha₁.hslot (by decide)]; exact hI.tab
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₃ _ (by decide), hm₂, word_writeW_self,
      ← slot_succ]
    rfl
  · rw [hm', word_writeW_self]; congr 1
  · rw [hE' j (by omega_arith)]
    by_cases hj2 : j = i + 2
    · subst hj2; rw [hv₃, hT₂]; exact hlt₁
    · rw [hEo j (by omega_arith) hj2]; exact hI.elt j (by omega_arith)
  · rw [hE' j (by omega_arith)]
    by_cases hj2 : j = i + 2
    · subst hj2; rw [hv₃, hT₂]; exact hTv hq
    · rw [hEo j (by omega_arith) hj2]; exact hI.eval hq j (by omega_arith)

/-- The table's first two entries, `T` and the count. -/
def tabPre : List (Prog isa) :=
  [.block [ldh .x3 (sArr aOne), ldh .x4 sW, .addImm .x .x4 .x4 2, .lsl .x .x4 .x4 3, .add .x .x3 .x3 .x4,
    sth .x3 Crt.sTab, sth .x3 Crt.sEnt]] ++ (toEnt aY ++ ([nextEnt] ++
    (toEnt Crt.aXc ++ (copyArr Crt.aT Crt.aXc ++ [.block [movi .x3 14, sth .x3 Crt.sBit]]))))

/-- The table's products. -/
def tabLoop (mul : Nat → Nat → Nat → Prog isa) : Prog isa := .loop (seqs (tabBody mul)) (.nonzero .x .x3)

theorem tabBuild_eq (mul : Nat → Nat → Nat → Prog isa) : tabBuild mul = tabPre ++ [tabLoop mul] := by
  simp [tabBuild, tabPre, tabLoop, tabBody]

/-- The table's first two entries: `T_0 := Y ≡ R`, `T_1 := [aXc] ≡ x R`. -/
theorem tabPre_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} (hc : CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hXN : Xc < X) (hXc : Q → Xc % X = x * 2 ^ (64 * wx) % X) (hY : wv t.mem P (slot wx aY) wx < X)
    (hYv : Q → wv t.mem P (slot wx aY) wx % X = 2 ^ (64 * wx) % X) :
    WP isa (seqs tabPre) t (BuildInv t P wx minv X Xc Q x 0) := by
  have hn := hc.scrT.nowrap
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have hX0 := slot_le (w := wx) (show Crt.aXc < 8 by decide)
  have hE0 := ent_le wx (show 0 < 16 by decide)
  have hE1 := ent_le wx (show 1 < 16 by decide)
  have h8 := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  unfold tabPre
  refine wp_seqs_append (by simp) (by simp [toEnt]) ?_
  simp only [seqs]
  -- The base.
  refine WP.mono (tabInit_ok hc hw') fun t₁ ⟨hm₁, k₁⟩ => ?_
  have o1 := writeW_outside t.mem P (d := 8 * Crt.sTab) (off P (slot wx 8)) (by decide)
  have o2 := writeW_outside (t.mem.writeW (off P (8 * Crt.sTab)) (off P (slot wx 8))) P (d := 8 * Crt.sEnt)
    (off P (slot wx 8)) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm P (buildRanges wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [buildRanges])).trans (Frm.of_outside o2 (by simp [buildRanges]))
  have hc₁ := hc.of_frm (f₁.mono (buildRanges_sub wx)) k₁.wr (k₁.gpr .x0 (by decide))
  -- `T_0 := Y`.
  refine wp_seqs_append (by simp [toEnt]) (by simp) ?_
  refine WP.mono (toEnt_ok hc₁ hw hw' (a := aY) (j := 0) (by decide) (by decide) (by
    rw [hm₁, word_writeW_self])) fun t₂ ⟨hv₂, o₃, k₂⟩ => ?_
  have f₂ : Frm P (buildRanges wx) t₁.mem t₂.mem :=
    Frm.of_outside (o₃.mono (o' := slot wx 8) (n' := tabBytes wx) (Nat.le_refl _) (by omega_arith))
      (by simp [buildRanges])
  have hc₂ := hc₁.of_frm (f₂.mono (buildRanges_sub wx)) k₂.wr (k₂.gpr .x0 (by decide))
  have hh₂ : ∀ k < 32, word t₂.mem P (8 * k) = word t₁.mem P (8 * k) := fun k hk =>
    o₃.word (by have := hdr_lt_slot wx (8 + 0) hk; omega_arith) (by omega_arith)
  -- `sEnt` up.
  refine wp_seqs_append (by simp) (by simp [toEnt]) ?_
  simp only [seqs]
  refine WP.mono (nextEnt_ok (e := slot wx 8) hc₂ hw' (by rw [hh₂ _ (by decide), hm₁, word_writeW_self]))
    fun t₃ ⟨hm₃, k₃⟩ => ?_
  have o₄ := writeW_outside t₂.mem P (d := 8 * Crt.sEnt) (off P (slot wx 8 + 8 * (wx + 2))) (by decide)
  rw [← hm₃] at o₄
  have f₃ : Frm P (buildRanges wx) t₂.mem t₃.mem := Frm.of_outside o₄ (by simp [buildRanges])
  have hc₃ := hc₂.of_frm (f₃.mono (buildRanges_sub wx)) k₃.wr (k₃.gpr .x0 (by decide))
  -- `T_1 := Xc`.
  refine wp_seqs_append (by simp [toEnt]) (by simp [copyArr]) ?_
  refine WP.mono (toEnt_ok hc₃ hw hw' (a := Crt.aXc) (j := 1) (by decide) (by decide) (by
    rw [hm₃, word_writeW_self, ← slot_succ])) fun t₄ ⟨hv₄, o₅, k₄⟩ => ?_
  have hE01 := slot_sep (w := wx) (show 8 + 0 ≠ 8 + 1 by decide)
  have f₄ : Frm P (buildRanges wx) t₃.mem t₄.mem :=
    Frm.of_outside (o₅.mono (o' := slot wx 8) (n' := tabBytes wx) (slot_mono wx (by decide)) (by omega_arith))
      (by simp [buildRanges])
  have hc₄ := hc₃.of_frm (f₄.mono (buildRanges_sub wx)) k₄.wr (k₄.gpr .x0 (by decide))
  have hh₄ : ∀ k < 32, word t₄.mem P (8 * k) = word t₃.mem P (8 * k) := fun k hk =>
    o₅.word (by have := hdr_lt_slot wx (8 + 1) hk; omega_arith) (by omega_arith)
  -- `T := Xc`.
  refine wp_seqs_append (by simp [copyArr]) (by simp) ?_
  refine WP.mono (copyArr_ok hc₄.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := Crt.aT)
    (a := Crt.aXc) (by decide) (by decide) (by decide)) fun t₅ ⟨hv₅, o₆, k₅⟩ => ?_
  have f₅ : Frm P (buildRanges wx) t₄.mem t₅.mem :=
    Frm.of_outside (o₆.mono (o' := slot wx Crt.aT) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_arith))
      (by simp [buildRanges])
  have hc₅ := hc₄.of_frm (f₅.mono (buildRanges_sub wx)) k₅.wr (k₅.gpr .x0 (by decide))
  have hh₅ : ∀ k < 32, word t₅.mem P (8 * k) = word t₄.mem P (8 * k) := fun k hk =>
    o₆.word (by have := hdr_lt_slot wx Crt.aT hk; omega_arith) (by omega_arith)
  have hT8 : ∀ j, slot wx Crt.aT + 8 * (wx + 2) ≤ slot wx (8 + j) := fun j => by
    have := slot_mono wx (show 8 ≤ 8 + j by omega_arith); omega_arith
  simp only [seqs]
  -- The count.
  refine WP.mono (cnt14_ok hc₅) fun t₆ ⟨hm₆, k₆⟩ => ?_
  have o₇ := writeW_outside t₅.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 14) (by decide)
  rw [← hm₆] at o₇
  have f₆ : Frm P (buildRanges wx) t₅.mem t₆.mem := Frm.of_outside o₇ (by simp [buildRanges])
  have hc₆ := hc₅.of_frm (f₆.mono (buildRanges_sub wx)) k₆.wr (k₆.gpr .x0 (by decide))
  have f06 : Frm P (buildRanges wx) t.mem t₆.mem := ((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).trans f₆
  have k06 : Keep mmRegs t t₆ := (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).mono (by decide)
  -- Entries 0 and 1, and `T`, at `t₆`.
  have hX₄ : wv t₄.mem P (slot wx Crt.aXc) wx = Xc := hc₄.x
  have e0 : wv t₆.mem P (slot wx (8 + 0)) wx = wv t.mem P (slot wx aY) wx := by
    rw [o₇.wv (by have := hdr_lt_slot wx (8 + 0) (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith),
      o₆.wv (by have := hT8 0; omega_arith) (by omega_arith),
      o₅.wv (by omega_arith) (by omega_arith),
      o₄.wv (by have := hdr_lt_slot wx (8 + 0) (show Crt.sEnt < 32 by decide); omega_arith) (by omega_arith), hv₂]
    exact f₁.wv_eq (buildRanges_y wx) (by omega_arith)
  have e1 : wv t₆.mem P (slot wx (8 + 1)) wx = Xc := by
    rw [o₇.wv (by have := hdr_lt_slot wx (8 + 1) (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith),
      o₆.wv (by have := hT8 1; omega_arith) (by omega_arith), hv₄]
    exact hc₃.x
  have eT : wv t₆.mem P (slot wx Crt.aT) wx = Xc := by
    rw [o₇.wv (by have := hdr_lt_slot wx Crt.aT (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith), hv₅,
      hX₄]
  refine ⟨hc₆, ?_, ?_, ?_, by rw [eT]; exact hXN, fun hq => by rw [eT, Nat.zero_add, Nat.pow_one]; exact hXc hq,
    fun j hj => ?_, fun hq j hj => ?_, f06, k06⟩
  · rw [hm₆, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₅ _ (by decide), hh₄ _ (by decide), hm₃,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₂ _ (by decide), hm₁,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm₆, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₅ _ (by decide), hh₄ _ (by decide), hm₃,
      word_writeW_self, ← slot_succ]
  · rw [hm₆, word_writeW_self]
  · rcases (show j = 0 ∨ j = 1 by omega_arith) with rfl | rfl
    · rw [e0]; exact hY
    · rw [e1]; exact hXN
  · rcases (show j = 0 ∨ j = 1 by omega_arith) with rfl | rfl
    · rw [e0, hYv hq, Nat.pow_zero, Nat.one_mul]
    · rw [e1, Nat.pow_one]; exact hXc hq

/-- The table: `T_0 := Y ≡ R`, `T_1 := [aXc] ≡ x R` and `T_i := T_(i-1) [aXc] R⁻¹`. -/
theorem tabBuild_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} (hc : CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X)
    (hXN : Xc < X) (hXc : Q → Xc % X = x * 2 ^ (64 * wx) % X) (hY : wv t.mem P (slot wx aY) wx < X)
    (hYv : Q → wv t.mem P (slot wx aY) wx % X = 2 ^ (64 * wx) % X) :
    WP isa (seqs (tabBuild M.mm)) t fun t' => CExpCtx t' P wx minv X Xc ∧ CTab t'.mem P wx X Q x ∧
      wv t'.mem P (slot wx aY) wx = wv t.mem P (slot wx aY) wx ∧
      (∀ k < 32, k ≠ Crt.sTab → k ≠ Crt.sEnt → k ≠ Crt.sBit → word t'.mem P (8 * k) = word t.mem P (8 * k)) ∧
      Frm P (crtExpRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  rw [tabBuild_eq]
  refine wp_seqs_append (by simp [tabPre]) (by simp) (WP.mono (tabPre_ok hc hw hw' hXN hXc hY hYv) fun t₆ h₀ => ?_)
  simp only [seqs, tabLoop]
  refine WP.mono (count_loop (cr := .x3) (n := 14) (by decide) (BuildInv t P wx minv X Xc Q x)
    (fun i hi s hI => buildStep_ok M hw hw' hR hXN hXc hi hI) h₀) fun t' hI => ?_
  refine ⟨hI.ctx, ⟨hI.tab, fun j hj => hI.elt j (by omega_arith), fun hq j hj => hI.eval hq j (by omega_arith)⟩,
    hI.frm.wv_eq (buildRanges_y wx) (by omega_arith),
    fun k hk h1 h2 h3 => hI.frm.word_eq (fun r hr => by
      simp only [buildRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      have := hdr_lt_slot wx 0 hk
      have := slot_le (w := wx) (show aAcc < 8 by decide)
      have := slot_mono wx (show 0 ≤ aAcc by decide)
      have := slot_mono wx (show aAcc ≤ aTmp by decide)
      have := slot_mono wx (show aTmp ≤ Crt.aT by decide)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Crt.sTab, Crt.sEnt, Crt.sBit, sFn] at * <;> omega_arith) (by omega_arith),
    hI.frm.mono (buildRanges_sub wx), hI.keep⟩

end VG.Proof.Bignum.AArch64
