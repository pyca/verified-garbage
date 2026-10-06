import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.CrtRedc
import VerifiedGarbage.Proof.Bignum.CrtMath

/-!
# RSA with the CRT on AArch64: `x R_X^(-K) mod X`

`redc j`, in a prime's workspace (`X`, `w_X` words, `R = 2^(64 w_X)`):
the number `x` of the modulus' array `j` (`w` words) in chunks of `w_X`
words, `x = Σ x_k R^k`, is reduced as `A := (A R⁻¹ + x_k R⁻¹) mod X` for
each chunk from the lowest: `A R^K ≡ x (mod X)` for `K = ⌈w / w_X⌉`
(`redc_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop)

/-- The prime `X` and the number 1 in its workspace, and `-X⁻¹`. -/
structure XVals (t : State) (B : Addr) (o wx : Nat) (minv : BitVec 64) (X : Nat) : Prop where
  n : wv t.mem (off B o) (slot wx Public.aN) wx = X
  inv : ((word t.mem (off B o) (slot wx Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  one : wv t.mem (off B o) (slot wx Public.aOne) wx = 1

theorem XVals.of_frm {s t : State} {B : Addr} {o wx : Nat} {minv : BitVec 64} {X : Nat}
    (h : XVals s B o wx minv X) (hn : (off B o).toNat + slot wx 8 ≤ 2 ^ 64) (hw : 1 ≤ wx)
    (hf : Frm (off B o) (redcRanges wx) s.mem t.mem) : XVals t B o wx minv X := by
  have rN := redcRanges_arr wx (j := Public.aN) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have rO := redcRanges_arr wx (j := Public.aOne) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have lN := slot_le (w := wx) (show Public.aN < 8 by decide)
  have lO := slot_le (w := wx) (show Public.aOne < 8 by decide)
  exact ⟨by rw [hf.wv_eq (fun r hr => by have := rN r hr; omega) (by omega)]; exact h.n,
    by rw [hf.word_eq (fun r hr => by have := rN r hr; omega) (by omega)]; exact h.inv,
    by rw [hf.wv_eq (fun r hr => by have := rO r hr; omega) (by omega)]; exact h.one⟩

/-- A store to a prime's header slot `i`, at offsets of `B`. -/
theorem store_off (m : Mem) (B : Addr) (o d : Nat) (v : BitVec 64) :
    m.writeW (off B (o + d)) v = m.writeW (off (off B o) d) v := by rw [off_off]

/-- `redc`'s start: `A := 0`, the source at array `j` of the modulus' and
all `w` words left. -/
theorem redcHead_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30) {j : Nat} (hj : j < 8) :
    WP isa (.seq (zeroArr aXc) (.block [ldh .x5 sLink, ldw .x3 .x5 (sArr j), sth .x3 sSrc, ldw .x3 .x5 sW,
        sth .x3 sRem])) s fun t =>
      SubCtx t B Z o w wx minv ∧ wv t.mem (off B o) (slot wx aXc) wx = 0 ∧
      word t.mem (off B o) (8 * sSrc) = off B (slot w j) ∧ word t.mem (off B o) (8 * sRem) = BitVec.ofNat 64 w ∧
      Frm (off B o) (redcRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hg := hc.good
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have rok := redcRanges_ok wx
  refine WP.seq (WP.mono (zeroArr_ok hg (Nat.le_refl _) (by omega) (show aXc < 8 by decide))
    fun s₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have f₁ : Frm (off B o) (redcRanges wx) s.mem s₁.mem := Frm.of_outside ho₁ (by simp [redcRanges])
  have hc₁ := hc.of_frm f₁ rok k₁.wr (k₁.gpr .x0 (by decide))
  have hA : wv s₁.mem (off B o) (slot wx aXc) wx = 0 :=
    (wv_eq_zero_iff _ _ _ _).mpr fun q hq => (wv_eq_zero_iff _ _ _ _).mp hz₁ q (by omega)
  have o1 := writeW_outside s₁.mem (off B o) (d := 8 * sSrc) (off B (slot w j)) (by decide)
  have hW : (s₁.mem.writeW (off B (o + 8 * sSrc)) (off B (slot w j))).readW (off B (8 * sW)) 64 =
      BitVec.ofNat 64 w := by
    rw [store_off]
    exact ((Frm.of_outside (rs := [(8 * sSrc, 8)]) o1 (by simp)).word_below (L := slot wx 8)
      (fun r hr => by rw [List.mem_singleton.mp hr]; unfold sSrc sFn slot hdrBytes; omega) (by omega)
      (by unfold slot hdrBytes at hi; omega) (by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)).trans
      hc₁.nw
  refine WP.mono (WP.keep [.x3, .x5] (Q := fun t => t.mem = (s₁.mem.writeW (off (off B o) (8 * sSrc))
      (off B (slot w j))).writeW (off (off B o) (8 * sRem)) (BitVec.ofNat 64 w))
    (by brun [ldw, hc₁.x0, hdr_enc (show sLink < 32 by decide), hdr_enc (sArr_lt hj), hdr_enc (show sSrc < 32 by decide),
      hdr_enc (show sW < 32 by decide), hdr_enc (show sRem < 32 by decide), hc₁.ld' (show sLink < 32 by decide),
      hc₁.link', hc₁.ldn (sArr_lt hj), hc₁.narr j hj, hc₁.st' (show sSrc < 32 by decide),
      hc₁.ldn (show sW < 32 by decide), hW, hc₁.st' (show sRem < 32 by decide)]) rfl rfl rfl)
    fun t ⟨hm, k₂⟩ => ?_
  have o2 := writeW_outside (s₁.mem.writeW (off (off B o) (8 * sSrc)) (off B (slot w j))) (off B o)
    (d := 8 * sRem) (BitVec.ofNat 64 w) (by decide)
  rw [← hm] at o2
  have f₂ : Frm (off B o) (redcRanges wx) s₁.mem t.mem :=
    (Frm.of_outside o1 (by simp [redcRanges])).trans (Frm.of_outside o2 (by simp [redcRanges]))
  have hc₂ := hc₁.of_frm f₂ rok k₂.wr (k₂.gpr .x0 (by decide))
  refine ⟨hc₂, ?_, ?_, ?_, f₁.trans f₂, (k₁.trans k₂).mono (by decide)⟩
  · have := hdr_lt_slot wx aXc (show 31 < 32 by decide)
    have := slot_le (w := wx) (show aXc < 8 by decide)
    rw [o2.wv (by unfold sRem sFn; omega) (by omega), o1.wv (by unfold sSrc sFn; omega) (by omega)]
    exact hA
  · rw [o2.word (by unfold sSrc sRem sFn; omega) (by unfold sSrc sFn; omega)]
    exact word_writeW_self _ _ _ _
  · rw [hm]; exact word_writeW_self _ _ _ _

/-- A chunk into its array: at most `w_X` words. -/
def redcLoad : List (Prog isa) := [
  zeroArr aChunk,
  .block [ldh .x3 sRem, ldh .x12 sW, .subs .x .x4 .x3 .x12, .csel .x .x12 .x12 .x3, ldh .x16 sSrc,
    ldh .x17 (sArr aChunk)],
  copyWords]

/-- The words left and the source advanced, and `A := A R⁻¹ + c R⁻¹`. -/
def redcAcc (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  .block [sth .x16 sSrc, ldh .x3 sRem, .sub .x .x3 .x3 .x12, sth .x3 sRem],
  mul aXc aXc Public.aOne,
  mul aT aChunk Public.aOne,
  addMod aXc aXc aT,
  .block [ldh .x3 sRem]]

theorem redc_eq (mul : Nat → Nat → Nat → Prog isa) (j : Nat) :
    redc mul j = [zeroArr aXc,
      .block [ldh .x5 sLink, ldw .x3 .x5 (sArr j), sth .x3 sSrc, ldw .x3 .x5 sW, sth .x3 sRem],
      .loop (seqs (redcLoad ++ redcAcc mul)) (.nonzero .x .x3)] := rfl

/-- `subs` and `csel` of two numbers: the smaller. -/
theorem csel_min {r c : Nat} (hr : r < 2 ^ 64) (hc : c < 2 ^ 64) :
    (if decide (2 ^ 64 ≤ (BitVec.ofNat 64 r).toNat + (~~~BitVec.ofNat 64 c).toNat + (true).toNat) = true
      then BitVec.ofNat 64 c else BitVec.ofNat 64 r) = BitVec.ofNat 64 (min r c) := by
  have e : (~~~BitVec.ofNat 64 c).toNat = 2 ^ 64 - 1 - c := by
    rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
  rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, Bool.toNat_true]
  split <;> rename_i h <;> simp only [decide_eq_true_eq] at h <;> congr 1 <;> omega

/-- A chunk of `r` words left (at least 1), at offset `e` of `B`, into the
chunk array: `min r w_X` words, the rest zero. -/
theorem redcLoad_ok {t : State} {B : Addr} {Z o w wx j : Nat} {minv : BitVec 64}
    (hc : SubCtx t B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30) (hj : j < 8)
    {r e : Nat} (hr1 : 1 ≤ r) (hj0 : slot w j ≤ e) (hre : e + 8 * r ≤ slot w j + 8 * w)
    (hrem : word t.mem (off B o) (8 * sRem) = BitVec.ofNat 64 r)
    (hsrc : word t.mem (off B o) (8 * sSrc) = off B e) :
    WP isa (seqs redcLoad) t fun t' =>
      SubCtx t' B Z o w wx minv ∧ t'.gpr .x12 = BitVec.ofNat 64 (min r wx) ∧
      t'.gpr .x16 = off B (e + 8 * min r wx) ∧
      wv t'.mem (off B o) (slot wx aChunk) wx = wv t.mem B e (min r wx) ∧
      word t'.mem (off B o) (8 * sRem) = BitVec.ofNat 64 r ∧ word t'.mem (off B o) (8 * sSrc) = off B e ∧
      wv t'.mem (off B o) (slot wx aXc) wx = wv t.mem (off B o) (slot wx aXc) wx ∧
      Frm (off B o) (redcRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have hsl := slot_le (w := w) hj
  have rok := redcRanges_ok wx
  have hC := slot_le (w := wx) (show aChunk < 8 by decide)
  have hC0 := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
  simp only [redcLoad, seqs]
  refine WP.seq (WP.mono (zeroArr_ok hc.good (Nat.le_refl _) (by omega) (show aChunk < 8 by decide))
    fun t₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have f₁ : Frm (off B o) (redcRanges wx) t.mem t₁.mem := Frm.of_outside ho₁ (by simp [redcRanges])
  have hc₁ := hc.of_frm f₁ rok k₁.wr (k₁.gpr .x0 (by decide))
  have hrem₁ : word t₁.mem B (o + 8 * sRem) = BitVec.ofNat 64 r := by
    rw [← word_off, ho₁.word (by unfold sRem sFn; omega) (by unfold sRem sFn; omega)]; exact hrem
  have hsrc₁ : word t₁.mem B (o + 8 * sSrc) = off B e := by
    rw [← word_off, ho₁.word (by unfold sSrc sFn; omega) (by unfold sSrc sFn; omega)]; exact hsrc
  -- `x12 := min r w_X`, and the pointers.
  refine WP.seq (WP.mono (WP.keep [.x3, .x4, .x12, .x16, .x17] (Q := fun t₂ =>
      t₂.gpr .x12 = BitVec.ofNat 64 (min r wx) ∧ t₂.gpr .x16 = off B e ∧
      t₂.gpr .x17 = off (off B o) (slot wx aChunk) ∧ t₂.mem = t₁.mem)
    (by brun [hc₁.x0, hdr_enc (show sRem < 32 by decide), hdr_enc (show sW < 32 by decide),
      hdr_enc (show sSrc < 32 by decide), hdr_enc (sArr_lt (show aChunk < 8 by decide)),
      hc₁.ld' (show sRem < 32 by decide), hc₁.ld' (show sW < 32 by decide), hc₁.ld' (show sSrc < 32 by decide),
      hc₁.ld' (sArr_lt (show aChunk < 8 by decide)), hrem₁, hc₁.hw', hsrc₁, hc₁.harr' (show aChunk < 8 by decide),
      csel_min (show r < 2 ^ 64 by omega) (show wx < 2 ^ 64 by omega), Nat.min_comm wx r, off_off])
    (by decide) (by decide) (by decide +kernel))
    fun t₄ ⟨⟨h12₄, hsi₄, hbx₄, hm₄⟩, k₄⟩ => ?_)
  have hcnt : 1 ≤ min r wx := by omega
  have hcnt' : min r wx ≤ wx := Nat.min_le_right _ _
  have hcr : min r wx ≤ r := Nat.min_le_left _ _
  have hs₄ := hc₁.scr.congr k₄.wr
  have hgs₄ := hc₁.good.scr.congr k₄.wr
  have hL : o + slot wx 8 ≤ 2 ^ 64 := by omega
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  refine WP.mono (copyWords_ok (S := B) (eS := e) (D := off B o) (eD := slot wx aChunk) (w := min r wx) hsi₄ hbx₄
    h12₄ hcnt (by omega) (by omega)
    (fun i hi' => hs₄.ld (by omega)) (fun i hi' => hgs₄.st (by omega))
    (fun i hi' b hb => Or.inr (by
      rcases ofs_rebase B (off B (e + 8 * i) + BitVec.ofNat 64 b) ho64 with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [ofs_off B (by omega)] at h1; omega
      · omega))) fun t₅ ⟨hv₅, _, ho₅, h16₅, _, k₅⟩ => ?_
  have f₅ : Frm (off B o) (redcRanges wx) t₁.mem t₅.mem := by
    rw [← hm₄]; exact Frm.of_outside (ho₅.mono (o' := slot wx aChunk) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega))
      (by simp [redcRanges])
  have hc₅ := hc₁.of_frm f₅ rok (by rw [k₅.wr, k₄.wr]) ((k₄.trans k₅).gpr .x0 (by decide))
  refine ⟨hc₅, (k₅.gpr .x12 (by decide)).trans h12₄, h16₅, ?_, ?_, ?_, ?_, f₁.trans f₅,
    ((k₁.trans k₄).trans k₅).mono (by decide)⟩
  · have hz : wv t₅.mem (off B o) (slot wx aChunk + 8 * min r wx) (wx - min r wx) = 0 :=
      (wv_eq_zero_iff _ _ _ _).mpr fun q hq => by
        rw [ho₅.word (by omega) (by omega), hm₄, show slot wx aChunk + 8 * min r wx + 8 * q =
          slot wx aChunk + 8 * (min r wx + q) by omega]
        exact (wv_eq_zero_iff _ _ _ _).mp hz₁ _ (by omega)
    rw [wv_split _ _ _ (show min r wx + (wx - min r wx) = wx by omega), hv₅, hz, Nat.mul_zero, Nat.add_zero, hm₄,
      f₁.wv_below (fun r hr => (rok r hr).2) hL ho64 (by omega)]
  · rw [ho₅.word (by unfold sRem sFn; omega) (by unfold sRem sFn; omega), hm₄, word_off]; exact hrem₁
  · rw [ho₅.word (by unfold sSrc sFn; omega) (by unfold sSrc sFn; omega), hm₄, word_off]; exact hsrc₁
  · have sp := slot_sep (w := wx) (show aXc ≠ aChunk by decide)
    have := slot_le (w := wx) (show aXc < 8 by decide)
    rw [ho₅.wv (by omega) (by omega), hm₄, ho₁.wv (by omega) (by omega)]

/-- `M.mm o a 1`, `[o] R ≡ [a]`, in a prime's workspace. -/
theorem mmOne_ok (M : Mont) {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X : Nat}
    (hc : SubCtx t B Z o w wx minv) (hv : XVals t B o wx minv X) (hw2 : 2 ≤ wx) (hw30 : wx < 2 ^ 30)
    (hX1 : 1 < X) {d a : Nat} (hd : d < 8) (ha : a < 8) (d1 : d ≠ Public.aAcc) (d2 : d ≠ Public.aTmp)
    (d3 : a ≠ Public.aAcc) (d5 : a ≠ Public.aTmp) (hr : (slot wx d, 8 * (wx + 2)) ∈ redcRanges wx) :
    WP isa (M.mm d a Public.aOne) t fun t' => SubCtx t' B Z o w wx minv ∧ XVals t' B o wx minv X ∧
      wv t'.mem (off B o) (slot wx d) wx < X ∧
      wv t'.mem (off B o) (slot wx d) wx * 2 ^ (64 * wx) % X = wv t.mem (off B o) (slot wx a) wx % X ∧
      Arrays (off B o) wx [Public.aAcc, Public.aTmp, d] t.mem t'.mem ∧
      Frm (off B o) (redcRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.good.scr.nowrap
  refine WP.mono (M.mm_ok hc.good (Nat.le_refl _) hw2 (by omega) hd ha (by decide) d1 d2 d3 (by decide) hv.inv
    (by rw [hv.one, hv.n]; exact hX1) d5 (by decide)) fun t' ⟨_, hlt, hm, har, k⟩ => ?_
  rw [hv.n] at hlt hm
  rw [hv.one, Nat.mul_one] at hm
  have hf : Frm (off B o) (redcRanges wx) t.mem t'.mem := Frm.of_arrays har fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · simp [redcRanges]
    · simp [redcRanges]
    · exact hr
  exact ⟨hc.of_frm hf (redcRanges_ok wx) k.wr (k.gpr .x0 (by decide)), hv.of_frm (by omega) (by omega) hf, hlt, hm,
    har, hf, k⟩

/-- The words left and the source advanced by the chunk's `c` words, and
`A := A R⁻¹ + x_k R⁻¹ mod X`; `x3` the words left. -/
theorem redcAcc_ok (M : Mont) {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X : Nat}
    (hc : SubCtx t B Z o w wx minv) (hv : XVals t B o wx minv X) (hw2 : 2 ≤ wx) (hwx : wx ≤ w)
    (hw30 : w < 2 ^ 30) (hX1 : 1 < X) {r e c : Nat} (hcr : c ≤ r)
    (h12 : t.gpr .x12 = BitVec.ofNat 64 c) (h16 : t.gpr .x16 = off B (e + 8 * c))
    (hrem : word t.mem (off B o) (8 * sRem) = BitVec.ofNat 64 r) :
    WP isa (seqs (redcAcc M.mm)) t fun t' => SubCtx t' B Z o w wx minv ∧ XVals t' B o wx minv X ∧
      word t'.mem (off B o) (8 * sRem) = BitVec.ofNat 64 (r - c) ∧
      word t'.mem (off B o) (8 * sSrc) = off B (e + 8 * c) ∧ t'.gpr .x3 = BitVec.ofNat 64 (r - c) ∧
      wv t'.mem (off B o) (slot wx aXc) wx < X ∧
      (∃ A' T, A' * 2 ^ (64 * wx) % X = wv t.mem (off B o) (slot wx aXc) wx % X ∧
        T * 2 ^ (64 * wx) % X = wv t.mem (off B o) (slot wx aChunk) wx % X ∧
        wv t'.mem (off B o) (slot wx aXc) wx = (A' + T) % X) ∧
      Frm (off B o) (redcRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.good.scr.nowrap
  have hi := hc.hi
  have rok := redcRanges_ok wx
  have hX : ∀ v : BitVec 64, (t.mem.writeW (off B (o + 8 * sSrc)) v).readW (off B (o + 8 * sRem)) 64 =
      BitVec.ofNat 64 r := fun v => by
    rw [store_off, ← off_off]
    exact (hdrStore_hdr t.mem (off B o) v (by decide) (by decide) (by decide)).trans hrem
  simp only [redcAcc, seqs]
  -- The words left and the source.
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t₁ => t₁.mem = (t.mem.writeW (off (off B o) (8 * sSrc))
      (off B (e + 8 * c))).writeW (off (off B o) (8 * sRem)) (BitVec.ofNat 64 (r - c)))
    (by brun [hc.x0, h16, h12, hdr_enc (show sSrc < 32 by decide), hdr_enc (show sRem < 32 by decide),
      hc.st' (show sSrc < 32 by decide), hc.ld' (show sRem < 32 by decide), hc.st' (show sRem < 32 by decide), hX,
      VG.Offset.ofNat_sub_ofNat hcr, off_off]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨hm₁, k₁⟩ => ?_)
  have o1 := writeW_outside t.mem (off B o) (d := 8 * sSrc) (off B (e + 8 * c)) (by decide)
  have o2 := writeW_outside (t.mem.writeW (off (off B o) (8 * sSrc)) (off B (e + 8 * c))) (off B o)
    (d := 8 * sRem) (BitVec.ofNat 64 (r - c)) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm (off B o) (redcRanges wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [redcRanges])).trans (Frm.of_outside o2 (by simp [redcRanges]))
  have hc₁ := hc.of_frm f₁ rok k₁.wr (k₁.gpr .x0 (by decide))
  have hv₁ := hv.of_frm (by omega) (by omega) f₁
  have hrem₁ : word t₁.mem (off B o) (8 * sRem) = BitVec.ofNat 64 (r - c) := by
    rw [hm₁]; exact word_writeW_self _ _ _ _
  have hsrc₁ : word t₁.mem (off B o) (8 * sSrc) = off B (e + 8 * c) := by
    rw [o2.word (by unfold sSrc sRem sFn; omega) (by unfold sSrc sFn; omega)]; exact word_writeW_self _ _ _ _
  have hXc₁ : wv t₁.mem (off B o) (slot wx aXc) wx = wv t.mem (off B o) (slot wx aXc) wx := by
    have := hdr_lt_slot wx aXc (show 31 < 32 by decide)
    have := slot_le (w := wx) (show aXc < 8 by decide)
    rw [o2.wv (by unfold sRem sFn; omega) (by omega), o1.wv (by unfold sSrc sFn; omega) (by omega)]
  have hCh₁ : wv t₁.mem (off B o) (slot wx aChunk) wx = wv t.mem (off B o) (slot wx aChunk) wx := by
    have := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
    have := slot_le (w := wx) (show aChunk < 8 by decide)
    rw [o2.wv (by unfold sRem sFn; omega) (by omega), o1.wv (by unfold sSrc sFn; omega) (by omega)]
  -- `A' := A R⁻¹`, `T := c R⁻¹`, `A := A' + T mod X`.
  refine WP.seq (WP.mono (mmOne_ok M hc₁ hv₁ hw2 (by omega) hX1 (d := aXc) (a := aXc) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [redcRanges]))
    fun t₂ ⟨hc₂, hv₂, hlt₂, hm₂, ha₂, f₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (mmOne_ok M hc₂ hv₂ hw2 (by omega) hX1 (d := aT) (a := aChunk) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [redcRanges]))
    fun t₃ ⟨hc₃, hv₃, hlt₃, hm₃, ha₃, f₃, k₃⟩ => ?_)
  have hn₁ : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := hn
  have hXc₃ : wv t₃.mem (off B o) (slot wx aXc) wx = wv t₂.mem (off B o) (slot wx aXc) wx :=
    ha₃.wv_of_not_mem (by decide) (by decide) hn₁
  have hCh₂ : wv t₂.mem (off B o) (slot wx aChunk) wx = wv t₁.mem (off B o) (slot wx aChunk) wx :=
    ha₂.wv_of_not_mem (by decide) (by decide) hn₁
  refine WP.seq (WP.mono (addMod_ok hc₃.good.scr hc₃.x0 hc₃.hdr (Nat.le_refl _) hw2 (by omega)
    (o := aXc) (a := aXc) (b := aT) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [hv₃.n, hXc₃]; exact hlt₂) (by rw [hv₃.n]; exact hlt₃))
    fun t₄ ⟨hval₄, ha₄, k₄⟩ => ?_)
  rw [hv₃.n] at hval₄
  have f₄ : Frm (off B o) (redcRanges wx) t₃.mem t₄.mem := Frm.of_arrays ha₄ fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> simp [redcRanges]
  have hc₄ := hc₃.of_frm f₄ rok k₄.wr (k₄.gpr .x0 (by decide))
  have hv₄ := hv₃.of_frm (by omega) (by omega) f₄
  have hrem₄ : word t₄.mem (off B o) (8 * sRem) = BitVec.ofNat 64 (r - c) := by
    rw [ha₄.hslot (by decide), ha₃.hslot (by decide), ha₂.hslot (by decide)]; exact hrem₁
  have hsrc₄ : word t₄.mem (off B o) (8 * sSrc) = off B (e + 8 * c) := by
    rw [ha₄.hslot (by decide), ha₃.hslot (by decide), ha₂.hslot (by decide)]; exact hsrc₁
  have hrem₄' : word t₄.mem B (o + 8 * sRem) = BitVec.ofNat 64 (r - c) := by rw [← word_off]; exact hrem₄
  refine WP.mono (WP.keep [.x3] (Q := fun t' => t'.gpr .x3 = BitVec.ofNat 64 (r - c) ∧ t'.mem = t₄.mem)
    (by brun [hc₄.x0, hdr_enc (show sRem < 32 by decide), hc₄.ld' (show sRem < 32 by decide), hrem₄'])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h3, hm'⟩, k'⟩ => ?_
  have f' : Frm (off B o) (redcRanges wx) t₄.mem t'.mem := by rw [hm']; exact Frm.refl _ _ _
  refine ⟨hc₄.of_frm f' rok k'.wr (k'.gpr .x0 (by decide)), hv₄.of_frm (by omega) (by omega) f',
    by rw [hm']; exact hrem₄, by rw [hm']; exact hsrc₄, h3, ?_,
    ⟨wv t₂.mem (off B o) (slot wx aXc) wx, wv t₃.mem (off B o) (slot wx aT) wx, ?_, ?_, by rw [hm', hval₄, hXc₃]⟩,
    (((f₁.trans f₂).trans f₃).trans f₄).trans f', ((((k₁.trans k₂).trans k₃).trans k₄).trans k').mono (by decide)⟩
  · rw [hm', hval₄]; exact Nat.mod_lt _ (by omega)
  · rw [hm₂, hXc₁]
  · rw [hm₃, hCh₂, hCh₁]

/-- After `k` chunks: `A R^k ≡ x mod R^k`. -/
structure RInv (s : State) (B : Addr) (Z o w wx j : Nat) (minv : BitVec 64) (X k : Nat) (t : State) : Prop where
  ctx : SubCtx t B Z o w wx minv
  xv : XVals t B o wx minv X
  rem : word t.mem (off B o) (8 * sRem) = BitVec.ofNat 64 (w - lowW w wx k)
  src : word t.mem (off B o) (8 * sSrc) = off B (slot w j + 8 * lowW w wx k)
  lt : wv t.mem (off B o) (slot wx aXc) wx < X
  val : wv t.mem (off B o) (slot wx aXc) wx * (2 ^ (64 * wx)) ^ k % X = wv s.mem B (slot w j) (lowW w wx k) % X
  frm : Frm (off B o) (redcRanges wx) s.mem t.mem
  keep : Keep mmRegs s t

theorem redcStep_ok (M : Mont) {s t : State} {B : Addr} {Z o w wx j : Nat} {minv : BitVec 64} {X k : Nat}
    (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30) (hX1 : 1 < X) (hj : j < 8)
    (hk : k < (w + wx - 1) / wx) (hI : RInv s B Z o w wx j minv X k t) :
    WP isa (seqs (redcLoad ++ redcAcc M.mm)) t fun t' =>
      RInv s B Z o w wx j minv X (k + 1) t' ∧ ((t'.gpr .x3).toNat ≠ 0 ↔ k + 1 ≠ (w + wx - 1) / wx) := by
  have hkw : k * wx < w := (lt_chunks (by omega)).mp hk
  have hk1 : k + 1 = (w + wx - 1) / wx ↔ w ≤ (k + 1) * wx := by
    have := (lt_chunks (k := k + 1) (w := w) (wx := wx) (by omega)); omega
  have hlw : lowW w wx k = k * wx := Nat.min_eq_right (by omega)
  have hlw1 : lowW w wx (k + 1) = k * wx + min (w - k * wx) wx := by
    unfold lowW; rw [Nat.add_mul, Nat.one_mul]; omega
  have hn := hI.ctx.scr.nowrap
  have hi := hI.ctx.hi
  have hlo := hI.ctx.lo
  have hsl := slot_le (w := w) hj
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hrem0 := hI.rem
  have hsrc0 := hI.src
  have hval0 := hI.val
  rw [hlw] at hrem0 hsrc0 hval0
  refine wp_seqs_append (by simp [redcLoad]) (by simp [redcAcc])
    (WP.mono (redcLoad_ok hI.ctx hw2 hwx hw30 hj (r := w - k * wx) (e := slot w j + 8 * (k * wx)) (by omega)
      (by omega) (by omega) hrem0 hsrc0) fun t₁ ⟨hc₁, h12₁, h16₁, hch₁, hrem₁, hsrc₁, hXc₁, f₁, k₁⟩ => ?_)
  have hv₁ := hI.xv.of_frm (by have := hc₁.good.scr.nowrap; omega) (by omega) f₁
  refine WP.mono (redcAcc_ok M hc₁ hv₁ hw2 hwx hw30 hX1 (Nat.min_le_left _ _) h12₁ h16₁ hrem₁)
    fun t' ⟨hc', hv', hrem', hsrc', h3', hlt', ⟨A', T, hA', hT, hval'⟩, f', k'⟩ => ⟨?_, ?_⟩
  · have hL : o + slot wx 8 ≤ 2 ^ 64 := by omega
    have hsrcv : wv t.mem B (slot w j + 8 * (k * wx)) (min (w - k * wx) wx) =
        wv s.mem B (slot w j + 8 * (k * wx)) (min (w - k * wx) wx) :=
      hI.frm.wv_below (fun r hr => (redcRanges_ok wx r hr).2) hL (by omega) (by omega)
    refine ⟨hc', hv', by rw [hrem', hlw1]; congr 1; omega, by rw [hsrc', hlw1]; congr 1; omega, hlt', ?_,
      hI.frm.trans (f₁.trans f'), ((hI.keep.trans k₁).trans k').mono (by decide)⟩
    rw [hval', hlw1, wv_split _ _ _ rfl]
    have hpow : (2 ^ (64 * wx)) ^ k = 2 ^ (64 * (k * wx)) := by
      rw [← Nat.pow_mul, Nat.mul_assoc, Nat.mul_comm wx k]
    have := VG.Proof.Bignum.redc_step (k := k) (L := wv s.mem B (slot w j) (k * wx)) hA' hT
      (by rw [hXc₁]; exact hval0)
    rw [this, hch₁, hsrcv, hpow, Nat.mul_comm (2 ^ _)]
  · rw [h3', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ne_eq, ne_eq, hk1, Nat.add_mul, Nat.one_mul]
    omega

/-- `redc j`: `A R^K ≡ x (mod X)` for the `w` words `x` of the modulus'
array `j`, `K = ⌈w / w_X⌉`. -/
theorem redc_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X : Nat}
    (hc : SubCtx s B Z o w wx minv) (hv : XVals s B o wx minv X) (hw2 : 2 ≤ wx) (hwx : wx ≤ w)
    (hw30 : w < 2 ^ 30) (hX1 : 1 < X) {j : Nat} (hj : j < 8) :
    WP isa (seqs (redc M.mm j)) s fun t => SubCtx t B Z o w wx minv ∧ XVals t B o wx minv X ∧
      wv t.mem (off B o) (slot wx aXc) wx < X ∧
      wv t.mem (off B o) (slot wx aXc) wx * 2 ^ (64 * wx * ((w + wx - 1) / wx)) % X =
        wv s.mem B (slot w j) w % X ∧
      Frm (off B o) (redcRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  rw [redc_eq]
  refine WP.assoc (WP.seq (WP.mono (redcHead_ok hc hw2 hwx hw30 hj)
    fun t₁ ⟨hc₁, hz₁, hsrc₁, hrem₁, f₁, k₁⟩ => ?_))
  have hn := hc.good.scr.nowrap
  have hK : 0 < (w + wx - 1) / wx := (lt_chunks (k := 0) (by omega)).mpr (by omega)
  have hl0 : lowW w wx 0 = 0 := by simp [lowW]
  refine WP.mono (count_loop (cr := .x3) hK (RInv s B Z o w wx j minv X)
    (fun k hk t hI => redcStep_ok M hw2 hwx hw30 hX1 hj hk hI)
    ⟨hc₁, hv.of_frm hn (by omega) f₁, by rw [hl0, Nat.sub_zero]; exact hrem₁,
      by rw [hl0, Nat.mul_zero, Nat.add_zero]; exact hsrc₁, by rw [hz₁]; omega,
      by rw [hz₁, hl0]; rfl, f₁, k₁⟩) fun t hI => ?_
  have hlK : lowW w wx ((w + wx - 1) / wx) = w := by
    unfold lowW
    have := (lt_chunks (k := (w + wx - 1) / wx) (w := w) (wx := wx) (by omega)).not.mp (Nat.lt_irrefl _)
    omega
  have hv' := hI.val
  rw [hlK, ← Nat.pow_mul] at hv'
  exact ⟨hI.ctx, hI.xv, hI.lt, hv', hI.frm, hI.keep⟩

end VG.Proof.Bignum.AArch64
