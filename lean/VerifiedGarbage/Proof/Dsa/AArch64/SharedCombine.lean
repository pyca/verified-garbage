module
public import VerifiedGarbage.Impl.Dsa.AArch64.SharedPower
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
public import VerifiedGarbage.Proof.Dsa.SharedPower
import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucket
import VerifiedGarbage.Proof.Dsa.AArch64.PublicSelect
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The product of the buckets' powers

`combine` multiplies the buckets from the seventh down into `Y`, and each
of those products into `X`: `X` ends as the product of `bucket_d^d`, which
one more multiplication by 1 takes out of Montgomery form, into `[aT]`. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.SharedPower VG.Proof.Dsa.Shared

/-- What the products keep from `s`: the table, the arrays they do not
write, and the header's slots but the digit's and the count's. -/
structure CmbKeep (s : State) (P : Addr) (wx : Nat) (t : State) : Prop where
  ent : ∀ j < 16, wv t.mem P (slot wx (8 + j)) wx = wv s.mem P (slot wx (8 + j)) wx
  arr : ∀ j < 8, j ≠ aAcc → j ≠ aTmp → j ≠ aY → j ≠ Crt.aT → j ≠ aX →
    wv t.mem P (slot wx j) wx = wv s.mem P (slot wx j) wx
  hdr : ∀ i < 32, i ≠ Crt.sNib → i ≠ Crt.sBit → word t.mem P (8 * i) = word s.mem P (8 * i)
  frm : Frm P (workRanges wx) s.mem t.mem
  keep : Keep mmRegs s t

theorem CmbKeep.refl (s : State) (P : Addr) (wx : Nat) : CmbKeep s P wx s :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, Frm.refl _ _ _, Keep.refl _ _⟩

theorem CmbKeep.trans {s t u : State} {P : Addr} {wx : Nat} (h : CmbKeep s P wx t) (k : CmbKeep t P wx u) :
    CmbKeep s P wx u :=
  ⟨fun j hj => (k.ent j hj).trans (h.ent j hj),
    fun j hj h1 h2 h3 h4 h5 => (k.arr j hj h1 h2 h3 h4 h5).trans (h.arr j hj h1 h2 h3 h4 h5),
    fun i hi h1 h2 => (k.hdr i hi h1 h2).trans (h.hdr i hi h1 h2), h.frm.trans k.frm,
    (h.keep.trans k.keep).mono (by decide)⟩

/-- Changes to the arrays the products write. -/
theorem CmbKeep.of_arrays {s t : State} {P : Addr} {wx : Nat} {js : List Nat}
    (ha : Arrays P wx js s.mem t.mem) (hjs : ∀ j ∈ js, j = aAcc ∨ j = aTmp ∨ j = aY ∨ j = Crt.aT ∨ j = aX)
    (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) (hk : Keep mmRegs s t) : CmbKeep s P wx t := by
  have h8 : ∀ j ∈ js, j < 8 := fun j hj => by
    rcases hjs j hj with rfl | rfl | rfl | rfl | rfl <;> decide
  exact ⟨fun j hj => arr_ent ha h8 hn hj,
    fun j hj h1 h2 h3 h4 h5 => ha.wv_of_not_mem hj (fun hm => by
      rcases hjs j hm with h | h | h | h | h
      exacts [h1 h, h2 h, h3 h, h4 h, h5 h]) (by omega_arith),
    fun i hi _ _ => ha.hslot hi, arrays_work ha h8, hk⟩

/-- A store to the digit's slot or the count's. -/
theorem CmbKeep.of_slot {s t : State} {P : Addr} {wx i : Nat} {v : BitVec 64}
    (hm : t.mem = s.mem.writeW (off P (8 * i)) v) (hi : i = Crt.sNib ∨ i = Crt.sBit)
    (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) (hk : Keep mmRegs s t) : CmbKeep s P wx t := by
  have hi17 : 17 ≤ i ∧ i < 32 := by rcases hi with rfl | rfl <;> decide
  have ho : Outside P 136 120 s.mem t.mem := by rw [hm]; exact fn_outside _ P _ hi17.1 hi17.2
  exact ⟨fun j hj => fn_ent ho hn hj, fun j hj _ _ _ _ _ => fn_arr ho hn hj,
    fun k hk h1 h2 => by
      rw [hm, hdrStore_hdr _ _ _ hi17.2 hk (by rcases hi with rfl | rfl <;> [exact Ne.symm h1; exact Ne.symm h2])],
    fn_work ho, hk⟩

/-- The context through changes to arrays that are neither the modulus nor `[aXc]`. -/
theorem ctx_of_arrays {s t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc : Nat} {js : List Nat}
    (hc : CExpCtx s P wx minv N Xc) (ha : Arrays P wx js s.mem t.mem) (hN : aN ∉ js) (hX : Crt.aXc ∉ js)
    (hwr : t.wr = s.wr) (h0 : t.gpr .x0 = s.gpr .x0) : CExpCtx t P wx minv N Xc := by
  have hn := hc.scrT.nowrap
  have hnZ : P.toNat + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  have hw := hc.good.scr.nowrap
  exact ⟨⟨hc.good.scr.congr hwr, h0.trans hc.good.x0, ha.hdr hc.good.hdr⟩, hc.scrT.congr hwr,
    (ha.wv_of_not_mem (by decide) hN hnZ).trans hc.n,
    by
      rw [ha.word_eq (fun k hk => by
        have := slot_sep (w := wx) (show aN ≠ k from fun e => hN (e ▸ hk)); omega_arith)
        (by have := slot_le (w := wx) (show aN < 8 by decide); omega_arith)]
      exact hc.inv,
    (ha.wv_of_not_mem (by decide) hX hnZ).trans hc.x⟩

/-! ## What the constant-time proofs need between the steps

The steps' lemmas below state, after each step, the fact the next step's
constant-time lemma starts from (`FGood`, `FSel`), then the rest of the run:
the correctness lemmas forget these facts, and the constant-time proofs
(`SharedPowerCT`) read them off. -/

/-- The workspace's context, for a multiplication or a copy. -/
def FGood (P : Addr) (wx : Nat) (t : State) : Prop := ∃ mi, Good t P (slot wx 8) wx mi

/-- The direct selection's hypotheses for the entry `v`. -/
def FSel (P : Addr) (wx v : Nat) (t : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc : Nat), CExpCtx t P wx mi X Xc ∧ 2 ≤ wx ∧ wx < 2 ^ 30 ∧ v < 16 ∧
    word t.mem P (8 * Crt.sTab) = off P (slot wx 8) ∧ word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v

/-- `[aT] := T_(b0 + 7)`, directly. -/
theorem pick_steps {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc b0 : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hoff : b0 = 0 ∨ b0 = 8)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    {K : State → Prop} (hK : ∀ t, CExpCtx t P wx minv N Xc ∧
      wv t.mem P (slot wx Crt.aT) wx = wv s.mem P (slot wx (8 + (b0 + 7))) wx ∧ CmbKeep s P wx t → K t) :
    WP isa (.block [movi .x3 (b0 + 7), sth .x3 Crt.sNib]) s fun u => FSel P wx (b0 + 7) u ∧
      WP isa VG.Impl.Dsa.AArch64.PublicPower.select u K := by
  have hn := hc.scrT.nowrap
  have hv : b0 + 7 < 16 := by omega_using [hoff]
  have hT := slot_le (w := wx) (show Crt.aT < 8 by decide)
  refine (WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off P (8 * Crt.sNib))
      (BitVec.ofNat 64 (b0 + 7))) (by
    rcases hoff with rfl | rfl <;>
    · brun [hc.good.x0, hdr_enc (show Crt.sNib < 32 by decide), hc.st (i := Crt.sNib) (by decide)]
      rfl) (by rcases hoff with rfl | rfl <;> rfl) rfl (by rcases hoff with rfl | rfl <;> rfl))
    fun s₁ ⟨hm₁, k₁⟩ => ?_)
  have k₁' : Keep mmRegs s s₁ := k₁.mono (by decide)
  have c₁ : CmbKeep s P wx s₁ := CmbKeep.of_slot hm₁ (Or.inl rfl) hn k₁'
  have hc₁ := ctx_of_fn hc (by rw [hm₁]; exact fn_outside _ P _ (by decide) (by decide)) k₁.wr
    (k₁.gpr .x0 (by decide))
  have ht₁ := (c₁.hdr _ (by decide) (by decide) (by decide)).trans ht
  have hn₁ : word s₁.mem P (8 * Crt.sNib) = BitVec.ofNat 64 (b0 + 7) := by rw [hm₁, word_writeW_self]
  refine ⟨⟨minv, N, Xc, hc₁, hw, hw', hv, ht₁, hn₁⟩, ?_⟩
  refine WP.mono (PublicPower.select_ok hc₁ hw hw' hv ht₁ hn₁) fun t ⟨hct, hT', o₂, k₂⟩ => hK t ?_
  have a₂ : Arrays P wx [Crt.aT] s₁.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self _) o₂ (Nat.le_refl _) (by omega_arith)
  exact ⟨hct, by rw [hT', c₁.ent _ hv], c₁.trans (CmbKeep.of_arrays a₂ (by simp) hn k₂)⟩

/-- `[aT] := T_(b0 + 7)`, directly. -/
theorem pick_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc b0 : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hoff : b0 = 0 ∨ b0 = 8)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8)) :
    WP isa (pick b0 7) s fun t => CExpCtx t P wx minv N Xc ∧
      wv t.mem P (slot wx Crt.aT) wx = wv s.mem P (slot wx (8 + (b0 + 7))) wx ∧ CmbKeep s P wx t :=
  WP.seq (WP.mono (pick_steps hc hw hw' hoff ht fun _ h => h) fun _ h => h.2)

/-- After `i` buckets below the seventh: `Y` their product with it, and
`X` the product of those products. -/
structure CmbInv (s : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (N Xc g : Nat) (b : Nat → Nat) (i : Nat)
    (t : State) : Prop where
  ctx : CExpCtx t P wx minv N Xc
  ylt : wv t.mem P (slot wx aY) wx < N
  y : wv t.mem P (slot wx aY) wx % N = g ^ cy b i * 2 ^ (64 * wx) % N
  xlt : wv t.mem P (slot wx aX) wx < N
  x : wv t.mem P (slot wx aX) wx % N = g ^ cx b i * 2 ^ (64 * wx) % N
  cnt : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (6 - i)
  kept : CmbKeep s P wx t

def cmbBody (mul : Nat → Nat → Nat → Prog isa) (b0 : Nat) : Prog isa :=
  seqs [.block [ldh .x3 Crt.sBit, .addImm .x .x3 .x3 b0, sth .x3 Crt.sNib], VG.Impl.Dsa.AArch64.PublicPower.select,
    mul aY aY Crt.aT, mul aX aX aY, .block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]]

theorem cmbStep_steps (M : Mont) {s t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc g b0 i : Nat}
    {b : Nat → Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) N)
    (hoff : b0 = 0 ∨ b0 = 8) (hi : i < 6)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hlt : ∀ d < 8, d ≠ 0 → wv s.mem P (slot wx (8 + (b0 + d))) wx < N)
    (hb : ∀ d < 8, d ≠ 0 → wv s.mem P (slot wx (8 + (b0 + d))) wx % N = g ^ b d * 2 ^ (64 * wx) % N)
    (hI : CmbInv s P wx minv N Xc g b i t)
    {K : State → Prop} (hK : ∀ t', CmbInv s P wx minv N Xc g b (i + 1) t' ∧
      ((t'.gpr .x3).toNat ≠ 0 ↔ i + 1 ≠ 6) → K t') :
    WP isa (.block [ldh .x3 Crt.sBit, .addImm .x .x3 .x3 b0, sth .x3 Crt.sNib]) t fun s₁ =>
      FSel P wx (b0 + (6 - i)) s₁ ∧ WP isa VG.Impl.Dsa.AArch64.PublicPower.select s₁ fun s₂ =>
      FGood P wx s₂ ∧ WP isa (M.mm aY aY Crt.aT) s₂ fun s₃ =>
      FGood P wx s₃ ∧ WP isa (M.mm aX aX aY) s₃ fun s₄ =>
      FGood P wx s₄ ∧ WP isa (.block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]) s₄ K := by
  have hn := hI.ctx.scrT.nowrap
  have hnZ : P.toNat + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  have hv : b0 + (6 - i) < 16 := by omega_using [hoff, hi]
  have hT := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have hc := hI.ctx
  -- The bucket's index.
  refine (WP.mono (WP.keep [.x3] (Q := fun u => u.mem = t.mem.writeW (off P (8 * Crt.sNib))
      (BitVec.ofNat 64 (b0 + (6 - i)))) (by
    rcases hoff with rfl | rfl <;>
    · brun [hc.good.x0, hdr_enc (show Crt.sBit < 32 by decide), hdr_enc (show Crt.sNib < 32 by decide),
        hc.ld (i := Crt.sBit) (by decide), hc.st (i := Crt.sNib) (by decide), hI.cnt, ofNat_add_ofNat]
      refine congrArg (t.mem.writeW _) (congrArg (BitVec.ofNat 64) ?_)
      omega_arith) (by rcases hoff with rfl | rfl <;> rfl) rfl (by rcases hoff with rfl | rfl <;> rfl))
    fun s₁ ⟨hm₁, k₁⟩ => ?_)
  have o₁ : Outside P 136 120 t.mem s₁.mem := by rw [hm₁]; exact fn_outside _ P _ (by decide) (by decide)
  have c₁ : CmbKeep t P wx s₁ := CmbKeep.of_slot hm₁ (Or.inl rfl) hn (k₁.mono (by decide))
  have hc₁ := ctx_of_fn hc o₁ k₁.wr (k₁.gpr .x0 (by decide))
  -- The bucket.
  have ht₁ := (c₁.hdr _ (by decide) (by decide) (by decide)).trans
    ((hI.kept.hdr _ (by decide) (by decide) (by decide)).trans ht)
  have hn₁ : word s₁.mem P (8 * Crt.sNib) = BitVec.ofNat 64 (b0 + (6 - i)) := by rw [hm₁, word_writeW_self]
  refine ⟨⟨minv, N, Xc, hc₁, hw, hw', hv, ht₁, hn₁⟩, ?_⟩
  refine (WP.mono (PublicPower.select_ok hc₁ hw hw' hv ht₁ hn₁) fun s₂ ⟨hc₂, hT₂, o₂, k₂⟩ => ⟨⟨minv, hc₂.good⟩, ?_⟩)
  have a₂ : Arrays P wx [Crt.aT] s₁.mem s₂.mem :=
    Arrays.of_outside (List.mem_singleton_self _) o₂ (Nat.le_refl _) (by omega_arith)
  have c₂ : CmbKeep s₁ P wx s₂ := CmbKeep.of_arrays a₂ (by simp) hn k₂
  have hTv : wv s₂.mem P (slot wx Crt.aT) wx = wv s.mem P (slot wx (8 + (b0 + (6 - i)))) wx := by
    rw [hT₂, c₁.ent _ hv, hI.kept.ent _ hv]
  have hY₂ : wv s₂.mem P (slot wx aY) wx = wv t.mem P (slot wx aY) wx := by
    rw [a₂.wv_of_not_mem (by decide) (by decide) hnZ, fn_arr o₁ hn (by decide)]
  have hX₂ : wv s₂.mem P (slot wx aX) wx = wv t.mem P (slot wx aX) wx := by
    rw [a₂.wv_of_not_mem (by decide) (by decide) hnZ, fn_arr o₁ hn (by decide)]
  -- `Y := Y T`.
  refine (WP.mono (M.mm_ok (o := aY) (a := aY) (b := Crt.aT) hc₂.good (Nat.le_refl _) hw (by omega_arith)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₂.inv
    (by rw [hc₂.n, hTv]; exact hlt _ (by omega_arith) (by omega_arith)))
    fun s₃ ⟨hg₃, hlt₃, hm₃, a₃, k₃⟩ => ⟨⟨minv, hg₃⟩, ?_⟩)
  rw [hc₂.n] at hlt₃ hm₃
  have c₃ : CmbKeep s₂ P wx s₃ := CmbKeep.of_arrays a₃ (by simp) hn k₃
  have hc₃ := ctx_of_arrays hc₂ a₃ (by decide) (by decide) k₃.wr (k₃.gpr .x0 (by decide))
  have hYv₃ : wv s₃.mem P (slot wx aY) wx % N = g ^ cy b (i + 1) * 2 ^ (64 * wx) % N :=
    mont_mulT hR (hY₂ ▸ hI.y) (hTv ▸ hb _ (by omega_arith) (by omega_arith)) hm₃
  have hX₃ : wv s₃.mem P (slot wx aX) wx = wv t.mem P (slot wx aX) wx := by
    rw [a₃.wv_of_not_mem (by decide) (by decide) hnZ, hX₂]
  -- `X := X Y`.
  refine (WP.mono (M.mm_ok (o := aX) (a := aX) (b := aY) hc₃.good (Nat.le_refl _) hw (by omega_arith)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₃.inv
    (by rw [hc₃.n]; exact hlt₃)) fun s₄ ⟨hg₄, hlt₄, hm₄, a₄, k₄⟩ => ⟨⟨minv, hg₄⟩, ?_⟩)
  rw [hc₃.n] at hlt₄ hm₄
  have c₄ : CmbKeep s₃ P wx s₄ := CmbKeep.of_arrays a₄ (by simp) hn k₄
  have hc₄ := ctx_of_arrays hc₃ a₄ (by decide) (by decide) k₄.wr (k₄.gpr .x0 (by decide))
  have hXv₄ : wv s₄.mem P (slot wx aX) wx % N = g ^ cx b (i + 1) * 2 ^ (64 * wx) % N :=
    mont_mulT hR (hX₃ ▸ hI.x) hYv₃ hm₄
  have hY₄ : wv s₄.mem P (slot wx aY) wx = wv s₃.mem P (slot wx aY) wx :=
    a₄.wv_of_not_mem (by decide) (by decide) hnZ
  have c04 : CmbKeep t P wx s₄ := ((c₁.trans c₂).trans c₃).trans c₄
  -- The count.
  refine WP.mono (crtBitEnd_ok hc₄ (b := 6 - i)
    ((a₄.hslot (by decide)).trans ((a₃.hslot (by decide)).trans ((a₂.hslot (by decide)).trans
      ((by rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)] :
        word s₁.mem P (8 * Crt.sBit) = word t.mem P (8 * Crt.sBit)).trans hI.cnt)))) (by omega_arith))
    fun t' ⟨⟨hm', h3⟩, k'⟩ => hK t' ?_
  have o' : Outside P 136 120 s₄.mem t'.mem := by rw [hm']; exact fn_outside _ P _ (by decide) (by decide)
  have c' : CmbKeep s₄ P wx t' := CmbKeep.of_slot hm' (Or.inr rfl) hn (k'.mono (by decide))
  refine ⟨⟨ctx_of_fn hc₄ o' k'.wr (k'.gpr .x0 (by decide)), ?_, ?_, ?_, ?_, ?_,
    hI.kept.trans (c04.trans c')⟩, ?_⟩
  · rw [fn_arr o' hn (by decide), hY₄]; exact hlt₃
  · rw [fn_arr o' hn (by decide), hY₄]; exact hYv₃
  · rw [fn_arr o' hn (by decide)]; exact hlt₄
  · rw [fn_arr o' hn (by decide)]; exact hXv₄
  · rw [hm', word_writeW_self, Nat.sub_sub]
  · rw [h3, cnt_ne (by omega_arith)]
    omega_arith

theorem cmbStep_ok (M : Mont) {s t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc g b0 i : Nat}
    {b : Nat → Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) N)
    (hoff : b0 = 0 ∨ b0 = 8) (hi : i < 6)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hlt : ∀ d < 8, d ≠ 0 → wv s.mem P (slot wx (8 + (b0 + d))) wx < N)
    (hb : ∀ d < 8, d ≠ 0 → wv s.mem P (slot wx (8 + (b0 + d))) wx % N = g ^ b d * 2 ^ (64 * wx) % N)
    (hI : CmbInv s P wx minv N Xc g b i t) :
    WP isa (cmbBody M.mm b0) t fun t' => CmbInv s P wx minv N Xc g b (i + 1) t' ∧
      ((t'.gpr .x3).toNat ≠ 0 ↔ i + 1 ≠ 6) := by
  unfold cmbBody
  simp only [seqs]
  exact WP.seq (WP.mono (cmbStep_steps M hw hw' hR hoff hi ht hlt hb hI fun _ h => h) fun _ h =>
    WP.seq (WP.mono h.2 fun _ h => WP.seq (WP.mono h.2 fun _ h => WP.seq (WP.mono h.2 fun _ h => h.2))))

theorem combine_eq (mul : Nat → Nat → Nat → Prog isa) (b0 : Nat) : combine mul b0 =
    seqs ([pick b0 7] ++ (Crt.copyArr aY Crt.aT ++ (Crt.copyArr aX Crt.aT ++
      ([.block [movi .x3 6, sth .x3 Crt.sBit], .loop (cmbBody mul b0) (.nonzero .x .x3),
        mul Crt.aT aX aOne] : List (Prog isa))))) := rfl

/-- The seventh bucket into `Y` and `X`, and the count: the start of the
loop over the six buckets below, with what the constant-time proof needs
after each step. -/
theorem combineHead_steps {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc g b0 : Nat}
    {b : Nat → Nat} (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hoff : b0 = 0 ∨ b0 = 8)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hlt : ∀ d < 8, d ≠ 0 → wv s.mem P (slot wx (8 + (b0 + d))) wx < N)
    (hb : ∀ d < 8, d ≠ 0 → wv s.mem P (slot wx (8 + (b0 + d))) wx % N = g ^ b d * 2 ^ (64 * wx) % N)
    {K : State → Prop} (hK : ∀ t, CmbInv s P wx minv N Xc g b 0 t → K t) :
    WP isa (.block [movi .x3 (b0 + 7), sth .x3 Crt.sNib]) s fun u => FSel P wx (b0 + 7) u ∧
      WP isa VG.Impl.Dsa.AArch64.PublicPower.select u fun s₁ => FGood P wx s₁ ∧
      WP isa (seqs (Crt.copyArr aY Crt.aT)) s₁ fun s₂ => FGood P wx s₂ ∧
      WP isa (seqs (Crt.copyArr aX Crt.aT)) s₂ fun s₃ => FGood P wx s₃ ∧
      WP isa (.block [movi .x3 6, sth .x3 Crt.sBit]) s₃ K := by
  have hn := hc.scrT.nowrap
  have hnZ : P.toNat + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  refine pick_steps hc hw hw' hoff ht fun s₁ ⟨hc₁, hT₁, c₁⟩ => ⟨⟨minv, hc₁.good⟩, ?_⟩
  refine WP.mono (copyArr_ok hc₁.good (Nat.le_refl _)
    (by omega_arith) (by omega_arith) (o := aY) (a := Crt.aT) (by decide) (by decide) (by decide))
    fun s₂ ⟨hY₂, o₂, k₂⟩ => ?_
  have a₂ : Arrays P wx [aY] s₁.mem s₂.mem :=
    Arrays.of_outside (List.mem_singleton_self _) o₂ (Nat.le_refl _) (by omega_arith)
  have c₂ : CmbKeep s₁ P wx s₂ := CmbKeep.of_arrays a₂ (by simp) hn k₂
  have hc₂ := ctx_of_arrays hc₁ a₂ (by decide) (by decide) k₂.wr (k₂.gpr .x0 (by decide))
  refine ⟨⟨minv, hc₂.good⟩, ?_⟩
  refine WP.mono (copyArr_ok hc₂.good (Nat.le_refl _)
    (by omega_arith) (by omega_arith) (o := aX) (a := Crt.aT) (by decide) (by decide) (by decide))
    fun s₃ ⟨hX₃, o₃, k₃⟩ => ?_
  have a₃ : Arrays P wx [aX] s₂.mem s₃.mem :=
    Arrays.of_outside (List.mem_singleton_self _) o₃ (Nat.le_refl _) (by omega_arith)
  have c₃ : CmbKeep s₂ P wx s₃ := CmbKeep.of_arrays a₃ (by simp) hn k₃
  have hc₃ := ctx_of_arrays hc₂ a₃ (by decide) (by decide) k₃.wr (k₃.gpr .x0 (by decide))
  refine ⟨⟨minv, hc₃.good⟩, ?_⟩
  -- The count.
  refine WP.mono (WP.keep [.x3] (Q := fun v => v.mem = s₃.mem.writeW (off P (8 * Crt.sBit))
      (BitVec.ofNat 64 6)) (by
    brun [hc₃.good.x0, hdr_enc (show Crt.sBit < 32 by decide), hc₃.st (i := Crt.sBit) (by decide)]
    rfl) rfl rfl rfl) fun s₄ ⟨hm₄, k₄⟩ => hK s₄ ?_
  have o₄ : Outside P 136 120 s₃.mem s₄.mem := by rw [hm₄]; exact fn_outside _ P _ (by decide) (by decide)
  have c₄ : CmbKeep s₃ P wx s₄ := CmbKeep.of_slot hm₄ (Or.inr rfl) hn (k₄.mono (by decide))
  have c04 : CmbKeep s P wx s₄ := ((c₁.trans c₂).trans c₃).trans c₄
  have hTs : wv s₁.mem P (slot wx Crt.aT) wx % N = g ^ b 7 * 2 ^ (64 * wx) % N := by
    rw [hT₁]; exact hb 7 (by decide) (by decide)
  have hTl : wv s₁.mem P (slot wx Crt.aT) wx < N := by rw [hT₁]; exact hlt 7 (by decide) (by decide)
  have hT₂ : wv s₂.mem P (slot wx Crt.aT) wx = wv s₁.mem P (slot wx Crt.aT) wx :=
    a₂.wv_of_not_mem (by decide) (by decide) hnZ
  have hY₄ : wv s₄.mem P (slot wx aY) wx = wv s₁.mem P (slot wx Crt.aT) wx := by
    rw [fn_arr o₄ hn (by decide), a₃.wv_of_not_mem (by decide) (by decide) hnZ, hY₂]
  have hX₄ : wv s₄.mem P (slot wx aX) wx = wv s₁.mem P (slot wx Crt.aT) wx := by
    rw [fn_arr o₄ hn (by decide), hX₃, hT₂]
  exact ⟨ctx_of_fn hc₃ o₄ k₄.wr (k₄.gpr .x0 (by decide)), by rw [hY₄]; exact hTl, by rw [hY₄]; exact hTs,
    by rw [hX₄]; exact hTl, by rw [hX₄]; exact hTs, by rw [hm₄, word_writeW_self], c04⟩

/-- The product of `bucket_d^d` over the seven buckets after entry `b0`,
whose exponents of `g` are `b d`: `[aT] := g^(Σ d · b d)`, out of Montgomery
form. -/
theorem combine_ok (M : Mont) {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc g b0 : Nat}
    {b : Nat → Nat} (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) N) (hN : 1 < N) (hoff : b0 = 0 ∨ b0 = 8)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hlt : ∀ d < 8, d ≠ 0 → wv s.mem P (slot wx (8 + (b0 + d))) wx < N)
    (hb : ∀ d < 8, d ≠ 0 → wv s.mem P (slot wx (8 + (b0 + d))) wx % N = g ^ b d * 2 ^ (64 * wx) % N)
    (hone : wv s.mem P (slot wx aOne) wx = 1) :
    WP isa (combine M.mm b0) s fun t => CExpCtx t P wx minv N Xc ∧
      wv t.mem P (slot wx Crt.aT) wx =
        g ^ (b 1 + 2 * b 2 + 3 * b 3 + 4 * b 4 + 5 * b 5 + 6 * b 6 + 7 * b 7) % N ∧
      CmbKeep s P wx t := by
  have hn := hc.scrT.nowrap
  rw [combine_eq]
  refine wp_seqs_append (by simp) (by simp [Crt.copyArr]) ?_
  simp only [seqs]
  unfold pick
  refine WP.seq (WP.mono (combineHead_steps hc hw hw' hoff ht hlt hb (b := b) (g := g) fun s₄ I0 => ?_)
    fun _ h => WP.mono h.2 fun _ h => wp_seqs_append (by simp [Crt.copyArr]) (by simp [Crt.copyArr])
      (WP.mono h.2 fun _ h => wp_seqs_append (by simp [Crt.copyArr]) (by simp) (WP.mono h.2 fun _ h =>
        WP.seq h.2)))
  -- The six buckets below.
  refine WP.seq (WP.mono (count_loop (cr := .x3) (n := 6) (by decide) (CmbInv s P wx minv N Xc g b)
    (fun i hi t hI => cmbStep_ok M hw hw' hR hoff hi ht hlt hb hI) I0) fun s₅ hI => ?_)
  -- Out of Montgomery form.
  have hone₅ : wv s₅.mem P (slot wx aOne) wx = 1 :=
    (hI.kept.arr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hone
  refine WP.mono (M.mm_ok (o := Crt.aT) (a := aX) (b := aOne) hI.ctx.good (Nat.le_refl _) hw (by omega_arith)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hI.ctx.inv
    (by rw [hI.ctx.n, hone₅]; exact hN)) fun t ⟨_, hltt, hmt, at', kt⟩ => ?_
  rw [hI.ctx.n] at hltt hmt
  rw [hone₅] at hmt
  have hres := VG.Proof.Dsa.mont_decode hR hI.x hmt
  rw [Nat.mod_eq_of_lt hltt, cx_six] at hres
  exact ⟨ctx_of_arrays hI.ctx at' (by decide) (by decide) kt.wr (kt.gpr .x0 (by decide)), hres,
    hI.kept.trans (CmbKeep.of_arrays at' (by simp) hn kt)⟩

end VG.Proof.Dsa.AArch64.SharedPower
