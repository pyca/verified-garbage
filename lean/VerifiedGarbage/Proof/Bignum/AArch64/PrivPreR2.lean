module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Impl.Rsa.AArch64.PrivPre
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
public import VerifiedGarbage.Proof.Bignum.PrimeR2
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `vg_rsa_private_precompute` on AArch64: `R_X² mod X`

`r2X` in a prime's workspace (`r2X_ok`): `R² mod n` reduced modulo `X` by
`Crt.redc` and then by `R_X⁻¹` (`rzLoop_ok`) is `2^(64 e)` (`r2_reduced`)
when `X` divides `n`, doubled (`dLoop_ok`) and squared (`sq6_ok`) to
`2^(128 w_X)`, as `Proof/Bignum/PrimeR2.lean` counts them; and `maskCopy`, a
copy of words and-ed with a mask (`maskCopy_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.PrivPre

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.PrivPre
open VG.Impl.Bignum.Crt (aXc aChunk aT sLink sSrc sRem)
open VG.Impl.Rsa.AArch64.Crt (copyArr addMod ldw redc)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop eval_nonzero ne_zero_iff)

/-- What `r2X` changes in the prime's workspace: `redc`'s, `Y`, and the
slots `sBit` and `sV`. -/
def r2Ranges (wx : Nat) : List (Nat × Nat) :=
  redcRanges wx ++ [(slot wx aY, 8 * (wx + 2)), (8 * Crt.sBit, 8), (8 * Crt.sV, 8)]

theorem r2Ranges_ok (wx : Nat) : ∀ r ∈ r2Ranges wx, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 := by
  intro r hr
  simp only [r2Ranges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | rfl | rfl | rfl
  · exact redcRanges_ok wx r hr
  · have := slot_le (w := wx) (show aY < 8 by decide)
    have := hdr_lt_slot wx aY (show 31 < 32 by decide)
    simp only; omega_arith
  · simp only [Crt.sBit, sFn, slot, hdrBytes]; omega_using []
  · simp only [Crt.sV, sFn, slot, hdrBytes]; omega_using []

/-- The prime's `X`, `-X⁻¹` and 1 are kept. -/
theorem r2Ranges_arr (wx : Nat) {j : Nat} (hj : j = aN ∨ j = aOne) :
    ∀ r ∈ r2Ranges wx, slot wx j + 8 * (wx + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot wx j := by
  intro r hr
  simp only [r2Ranges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  have := hdr_lt_slot wx j (show 31 < 32 by decide)
  rcases hr with hr | rfl | rfl | rfl
  · rcases hj with rfl | rfl
    · exact redcRanges_arr wx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r hr
    · exact redcRanges_arr wx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r hr
  · rcases hj with rfl | rfl
    · exact slot_sep (w := wx) (show aN ≠ aY by decide)
    · exact slot_sep (w := wx) (show aOne ≠ aY by decide)
  · simp only [Crt.sBit, sFn] at *; omega_using [this]
  · simp only [Crt.sV, sFn] at *; omega_using [this]

theorem XVals.of_r2 {s t : State} {B : Addr} {o wx : Nat} {minv : BitVec 64} {X : Nat}
    (h : XVals s B o wx minv X) (hn : (off B o).toNat + slot wx 8 ≤ 2 ^ 64)
    (hf : Frm (off B o) (r2Ranges wx) s.mem t.mem) : XVals t B o wx minv X := by
  have rN := r2Ranges_arr wx (j := aN) (Or.inl rfl)
  have rO := r2Ranges_arr wx (j := aOne) (Or.inr rfl)
  have lN := slot_le (w := wx) (show aN < 8 by decide)
  have lO := slot_le (w := wx) (show aOne < 8 by decide)
  exact ⟨by rw [hf.wv_eq (fun r hr => by have := rN r hr; omega_using [this]) (by omega_using [hn, lN])]; exact h.n,
    by rw [hf.word_eq (fun r hr => by have := rN r hr; omega_using [this]) (by omega_using [hn, lN])]; exact h.inv,
    by rw [hf.wv_eq (fun r hr => by have := rO r hr; omega_using [this]) (by omega_using [hn, lO])]; exact h.one⟩

/-! ## The counts -/

/-- `gtTest`: whether `2 w_X < e`. -/
theorem gtTest_ok {t : State} {e wx : Nat} (he : e < 2 ^ 62) (hwx : wx < 2 ^ 62)
    (h3 : t.gpr .x3 = BitVec.ofNat 64 e) (h13 : t.gpr .x13 = BitVec.ofNat 64 wx) (h7 : t.gpr .x7 = 0)
    (h8 : t.gpr .x8 = 1) :
    WP isa (.block gtTest) t fun t' =>
      (t'.gpr .x4 = (if e ≤ 2 * wx then 0 else 1) ∧ t'.mem = t.mem) ∧ Keep [.x4, .x6] t t' := by
  refine WP.keep [.x4, .x6] (Q := fun t' => t'.gpr .x4 = (if e ≤ 2 * wx then 0 else 1) ∧ t'.mem = t.mem)
    (by brun [gtTest, h3, h13, h7, h8, shl_ofNat (show wx * 2 ^ 1 < 2 ^ 64 by omega_using [hwx]),
      show wx * 2 ^ 1 = 2 * wx by omega_using [], subs_ge (show 2 * wx < 2 ^ 64 by omega_using [hwx]) (show e < 2 ^ 64 by omega_using [he]),
      decide_eq_true_eq])
    (by decide) (by decide) (by decide +kernel)

/-- After `redc`: `e₀ = 2 w - K w_X` into slot `sV` and `x3`, and whether
`2 w_X < e₀` into `x4`. -/
theorem r2Head_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30) :
    WP isa (.seq (.block r2Load) (.seq kLoop (.block eInit))) s fun t =>
      t.mem = s.mem.writeW (off (off B o) (8 * Crt.sV)) (BitVec.ofNat 64 (r2E0 w wx)) ∧
      t.gpr .x3 = BitVec.ofNat 64 (r2E0 w wx) ∧ t.gpr .x4 = (if r2E0 w wx ≤ 2 * wx then 0 else 1) ∧
      t.gpr .x13 = BitVec.ofNat 64 wx ∧ t.gpr .x7 = 0 ∧ t.gpr .x8 = 1 ∧
      Keep [.x3, .x4, .x5, .x6, .x7, .x8, .x12, .x13] s t := by
  obtain ⟨hK1, hK2⟩ := kBounds (w := w) (by omega_using [hw2] : 1 ≤ wx)
  refine WP.seq (WP.mono (WP.keep [.x3, .x5, .x7, .x8, .x12] (Q := fun t => t.gpr .x5 = BitVec.ofNat 64 wx ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x3 = BitVec.ofNat 64 0 ∧ t.gpr .x7 = 0 ∧ t.gpr .x8 = 1 ∧
      t.mem = s.mem)
    (by brun [r2Load, ldw, hc.x0, hdr_enc (show sLink < 32 by decide), hdr_enc (show sW < 32 by decide),
      hc.ld' (show sLink < 32 by decide), hc.link', hc.ldn (show sW < 32 by decide), hc.nw,
      hc.ld' (show sW < 32 by decide), hc.hw'])
    (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h5, h12, h3, h7, h8, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (kLoop_ok (by omega_using [hw2]) (by omega_using [hwx, hK2]) (by omega_using [hwx, hw30]) h5 h12 h3 h7 h8)
    fun s₂ ⟨h3₂, hm₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have e₂ : ∀ r, r = .x5 ∨ r = .x7 ∨ r = .x8 ∨ r = .x12 → s₂.gpr r = s₁.gpr r := fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl <;> exact k₂.gpr _ (by decide)
  have hsub : BitVec.ofNat 64 (2 * w) - BitVec.ofNat 64 ((w + wx - 1) / wx * wx) =
      BitVec.ofNat 64 (r2E0 w wx) := VG.Offset.ofNat_sub_ofNat (by omega_using [hwx, hK2])
  have hE : r2E0 w wx ≤ 2 * w := by unfold r2E0; omega_using []
  have hc₂ : SubCtx s₂ B Z o w wx minv := hc.of_frm (rs := []) (by rw [hm₂, hm₁]; exact Frm.refl _ _ _) (by simp)
    k12.wr (k12.gpr .x0 (by decide))
  unfold eInit
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x13] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (r2E0 w wx) ∧
      t.gpr .x13 = BitVec.ofNat 64 wx ∧ t.mem = s.mem.writeW (off (off B o) (8 * Crt.sV)) (BitVec.ofNat 64 (r2E0 w wx)))
    (by brun [h3₂, e₂ .x5 (by simp), e₂ .x12 (by simp), h5, h12, hc₂.x0,
      shl_ofNat (show w * 2 ^ 1 < 2 ^ 64 by omega_using [hw30]), show w * 2 ^ 1 = 2 * w by omega_using [], hsub,
      hdr_enc (show Crt.sV < 32 by decide), hc₂.st' (show Crt.sV < 32 by decide), hm₂, hm₁, off_off])
    (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨⟨h3₃, h13₃, hm₃⟩, k₃⟩ => ?_
  have h7₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr .x7 (by decide), e₂ .x7 (by simp), h7]
  have h8₃ : s₃.gpr .x8 = 1 := by rw [k₃.gpr .x8 (by decide), e₂ .x8 (by simp), h8]
  refine WP.mono (gtTest_ok (by omega_using [hw30, hE]) (by omega_using [hwx, hw30]) h3₃ h13₃ h7₃ h8₃) fun t ⟨⟨h4, hm⟩, k⟩ => ?_
  exact ⟨hm.trans hm₃, by rw [k.gpr .x3 (by decide)]; exact h3₃, h4, by rw [k.gpr .x13 (by decide)]; exact h13₃,
    by rw [k.gpr .x7 (by decide)]; exact h7₃, by rw [k.gpr .x8 (by decide)]; exact h8₃,
    ((k12.trans k₃).trans k).mono (by decide)⟩

/-! ## The further reductions -/

/-- After `j` further reductions from `s₀`: `A R_X^(K + j) ≡ x`, and
`e₀ - j w_X` in slot `sV`. -/
structure RzInv (s₀ : State) (B : Addr) (Z o w wx : Nat) (minv : BitVec 64) (X x j : Nat) (t : State) : Prop where
  ctx : SubCtx t B Z o w wx minv
  xv : XVals t B o wx minv X
  lt : wv t.mem (off B o) (slot wx aXc) wx < X
  val : wv t.mem (off B o) (slot wx aXc) wx * 2 ^ (64 * wx * ((w + wx - 1) / wx + j)) % X = x % X
  e : word t.mem (off B o) (8 * Crt.sV) = BitVec.ofNat 64 (r2E0 w wx - j * wx)
  frm : Frm (off B o) (r2Ranges wx) s₀.mem t.mem
  keep : Keep mmRegs s₀ t

/-- A further reduction. -/
theorem rzStep_ok (M : Mont) {s₀ t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x j : Nat}
    (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30) (hX1 : 1 < X) (hj : j < r2Z w wx)
    (hI : RzInv s₀ B Z o w wx minv X x j t) :
    WP isa (zBody M.mm) t fun t' =>
      RzInv s₀ B Z o w wx minv X x (j + 1) t' ∧ ((t'.gpr .x4).toNat ≠ 0 ↔ j + 1 ≠ r2Z w wx) := by
  have hn := hI.ctx.scr.nowrap
  have hz1 : (j + 1) * wx ≤ r2E0 w wx - wx - 1 :=
    (Nat.le_div_iff_mul_le (by omega_using [hw2])).mp (by unfold r2Z at hj; omega_using [hj])
  have hE : r2E0 w wx ≤ 2 * w := by unfold r2E0; omega_using []
  have hjw : j * wx + wx = (j + 1) * wx := by rw [Nat.add_mul, Nat.one_mul]
  refine WP.seq (WP.mono (mmOne_ok M hI.ctx hI.xv hw2 (by omega_using [hwx, hw30]) hX1 (d := aXc) (a := aXc) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [redcRanges]))
    fun t₁ ⟨hc₁, hv₁, hlt₁, hm₁, _, f₁, k₁⟩ => ?_)
  have f₁' : Frm (off B o) (r2Ranges wx) t.mem t₁.mem := f₁.mono (fun r hr => List.mem_append_left _ hr)
  have he₁ : word t₁.mem B (o + 8 * Crt.sV) = BitVec.ofNat 64 (r2E0 w wx - j * wx) := by
    rw [← word_off, f₁.word_eq (fun r hr => by
      have := redcRanges_ok wx r hr
      simp only [redcRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      have := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Crt.sV, sSrc, sRem, sFn, slot, hdrBytes, aAcc, aTmp, aXc, aChunk, aT] at * <;> omega_using [])
      (by have := hc₁.hi; unfold Crt.sV sFn slot hdrBytes at *; omega_using [])]
    exact hI.e
  have hsub : BitVec.ofNat 64 (r2E0 w wx - j * wx) - BitVec.ofNat 64 wx =
      BitVec.ofNat 64 (r2E0 w wx - (j + 1) * wx) := by
    rw [VG.Offset.ofNat_sub_ofNat (by omega_using [hz1, hjw])]; congr 1; omega_using [hjw]
  unfold zTail
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x7, .x8, .x13] (Q := fun t₂ =>
      t₂.gpr .x3 = BitVec.ofNat 64 (r2E0 w wx - (j + 1) * wx) ∧ t₂.gpr .x13 = BitVec.ofNat 64 wx ∧
      t₂.gpr .x7 = 0 ∧ t₂.gpr .x8 = 1 ∧
      t₂.mem = t₁.mem.writeW (off (off B o) (8 * Crt.sV)) (BitVec.ofNat 64 (r2E0 w wx - (j + 1) * wx)))
    (by brun [hc₁.x0, hdr_enc (show Crt.sV < 32 by decide), hdr_enc (show sW < 32 by decide),
      hc₁.ld' (show Crt.sV < 32 by decide), hc₁.ld' (show sW < 32 by decide), he₁, hc₁.hw', hsub,
      hc₁.st' (show Crt.sV < 32 by decide), off_off])
    (by decide) (by decide) (by decide +kernel)) fun t₂ ⟨⟨h3₂, h13₂, h7₂, h8₂, hm₂⟩, k₂⟩ => ?_
  refine WP.mono (gtTest_ok (by omega_using [hw30, hE]) (by omega_using [hwx, hw30]) h3₂ h13₂ h7₂ h8₂) fun t' ⟨⟨h4, hm'⟩, k'⟩ => ?_
  have o₂ := writeW_outside t₁.mem (off B o) (d := 8 * Crt.sV) (BitVec.ofNat 64 (r2E0 w wx - (j + 1) * wx))
    (by decide)
  rw [← hm₂, ← hm'] at o₂
  have f₂ : Frm (off B o) (r2Ranges wx) t₁.mem t'.mem := Frm.of_outside o₂ (by simp [r2Ranges])
  have k12 := (k₁.trans k₂).trans k'
  have hc' := hc₁.of_frm f₂ (r2Ranges_ok wx) (k₂.trans k').wr ((k₂.trans k').gpr .x0 (by decide))
  have hXc : wv t'.mem (off B o) (slot wx aXc) wx = wv t₁.mem (off B o) (slot wx aXc) wx := by
    have := hdr_lt_slot wx aXc (show 31 < 32 by decide)
    have := slot_le (w := wx) (show aXc < 8 by decide)
    exact o₂.wv (by unfold Crt.sV sFn; omega_arith) (by have := hc'.hi; unfold slot hdrBytes at *; omega_arith)
  refine ⟨⟨hc', XVals.of_r2 hv₁ hc₁.good.scr.nowrap f₂, by rw [hXc]; exact hlt₁, ?_, by rw [hm', hm₂]; exact word_writeW_self _ _ _ _,
    (hI.frm.trans f₁').trans f₂, (hI.keep.trans k12).mono (by decide)⟩, ?_⟩
  · rw [hXc, show (w + wx - 1) / wx + (j + 1) = (w + wx - 1) / wx + j + 1 by omega_using []]
    exact r2_step hm₁ hI.val
  · rw [h4]
    have hst := r2Z_step (w := w) (wx := wx) (j := j) (by omega_using [hw2]) hj
    split <;> rename_i h
    · exact ⟨fun h' => absurd rfl h', fun h' => absurd (by omega_using [hj, hst, h']) (show ¬ 2 * wx < r2E0 w wx - (j + 1) * wx by omega_using [h])⟩
    · exact ⟨fun _ => by omega_using [hst, h], fun _ => by decide⟩

/-- The further reductions, while more than `2 w_X` words are left. -/
theorem rzLoop_ok (M : Mont) {s₀ t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat}
    (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30) (hX1 : 1 < X) (hI : RzInv s₀ B Z o w wx minv X x 0 t)
    (h4 : t.gpr .x4 = if r2E0 w wx ≤ 2 * wx then 0 else 1) :
    WP isa (.ite (.nonzero .x .x4) (.loop (zBody M.mm) (.nonzero .x .x4)) (.block [])) t
      (RzInv s₀ B Z o w wx minv X x (r2Z w wx)) := by
  have hp := r2Z_pos (w := w) (wx := wx) (by omega_using [hw2])
  by_cases hz : 2 * wx < r2E0 w wx
  · refine WP.ite true (by rw [eval_nonzero, h4, ite_eq_right_iff.mpr (fun h => absurd h (by omega_using [hz]))]; rfl) (fun _ => ?_) (by simp)
    exact count_loop (cr := .x4) (hp.mpr hz) (RzInv s₀ B Z o w wx minv X x)
      (fun j hj t h => rzStep_ok M hw2 hwx hw30 hX1 hj h) hI
  · have h0 : r2Z w wx = 0 := by omega_using [hp, hz]
    refine WP.ite false (by rw [eval_nonzero, h4, ite_eq_left_iff.mpr (fun h => absurd (by omega_using [hz]) h)]; rfl) (by simp) (fun _ => ?_)
    rw [h0]; exact WP.block_nil hI

/-! ## The doublings and squarings -/

/-- `cntBlk`: the doublings into slot `sBit` and `x3`, and whether six
squarings follow into slot `sV`. -/
theorem cnt_ok {t : State} {B : Addr} {Z o w wx e : Nat} {minv : BitVec 64} (hc : SubCtx t B Z o w wx minv)
    (hwx : wx < 2 ^ 30) (he2 : e ≤ 2 * wx)
    (he : word t.mem (off B o) (8 * Crt.sV) = BitVec.ofNat 64 e) :
    WP isa (.block cntBlk) t fun t' =>
      (t'.gpr .x3 = BitVec.ofNat 64 (if e ≤ wx then 64 * (wx - e) + wx else 64 * (2 * wx - e)) ∧
        t'.mem = (t.mem.writeW (off (off B o) (8 * Crt.sBit))
          (BitVec.ofNat 64 (if e ≤ wx then 64 * (wx - e) + wx else 64 * (2 * wx - e)))).writeW
          (off (off B o) (8 * Crt.sV)) (if e ≤ wx then (1 : BitVec 64) else 0#64)) ∧
      Keep [.x3, .x4, .x5, .x6, .x7, .x8, .x13] t t' := by
  have he' : word t.mem B (o + 8 * Crt.sV) = BitVec.ofNat 64 e := by rw [← word_off]; exact he
  have z0 : BitVec.setWidth 64 0#16 = 0#64 := by decide
  have z1 : BitVec.setWidth 64 1#16 = (1 : BitVec 64) := by decide
  by_cases hle : e ≤ wx
  · have hA : (BitVec.setWidth 64 0#16 + BitVec.ofNat 64 wx - BitVec.ofNat 64 e) <<< 6 + BitVec.ofNat 64 wx =
        BitVec.ofNat 64 (64 * (wx - e) + wx) := by
      rw [z0, BitVec.zero_add, VG.Offset.ofNat_sub_ofNat hle, shl_ofNat (by omega_using [hwx]), ← BitVec.ofNat_add]
      congr 1; omega_using []
    simp only [hle, ite_true]
    refine WP.keep [.x3, .x4, .x5, .x6, .x7, .x8, .x13] (Q := fun t' =>
      t'.gpr .x3 = BitVec.ofNat 64 (64 * (wx - e) + wx) ∧
      t'.mem = (t.mem.writeW (off (off B o) (8 * Crt.sBit)) (BitVec.ofNat 64 (64 * (wx - e) + wx))).writeW
        (off (off B o) (8 * Crt.sV)) (1 : BitVec 64))
      (by brun [cntBlk, hc.x0, hdr_enc (show Crt.sV < 32 by decide), hdr_enc (show sW < 32 by decide),
        hdr_enc (show Crt.sBit < 32 by decide), hc.ld' (show Crt.sV < 32 by decide),
        hc.ld' (show sW < 32 by decide), he', hc.hw', hc.st' (show Crt.sBit < 32 by decide),
        hc.st' (show Crt.sV < 32 by decide), subs_ge (show wx < 2 ^ 64 by omega_using [hwx]) (show e < 2 ^ 64 by omega_using [hwx, he2]),
        decide_eq_true hle, hA, z1, off_off])
      (by decide) (by decide) (by decide +kernel)
  · have hA : (BitVec.ofNat 64 wx + BitVec.ofNat 64 wx - BitVec.ofNat 64 e) <<< 6 =
        BitVec.ofNat 64 (64 * (2 * wx - e)) := by
      rw [← BitVec.ofNat_add, VG.Offset.ofNat_sub_ofNat (by omega_using [he2]), shl_ofNat (by omega_using [hwx])]
      congr 1; omega_using []
    simp only [hle, ite_false]
    refine WP.keep [.x3, .x4, .x5, .x6, .x7, .x8, .x13] (Q := fun t' =>
      t'.gpr .x3 = BitVec.ofNat 64 (64 * (2 * wx - e)) ∧
      t'.mem = (t.mem.writeW (off (off B o) (8 * Crt.sBit)) (BitVec.ofNat 64 (64 * (2 * wx - e)))).writeW
        (off (off B o) (8 * Crt.sV)) 0#64)
      (by brun [cntBlk, hc.x0, hdr_enc (show Crt.sV < 32 by decide), hdr_enc (show sW < 32 by decide),
        hdr_enc (show Crt.sBit < 32 by decide), hc.ld' (show Crt.sV < 32 by decide),
        hc.ld' (show sW < 32 by decide), he', hc.hw', hc.st' (show Crt.sBit < 32 by decide),
        hc.st' (show Crt.sV < 32 by decide), subs_ge (show wx < 2 ^ 64 by omega_using [hwx]) (show e < 2 ^ 64 by omega_using [hwx, he2]),
        decide_eq_false hle, hA, z0, off_off])
      (by decide) (by decide) (by decide +kernel)

/-- After `j` of the `c` doublings of `Y₀` from `s₀`. -/
structure DInv (s₀ : State) (B : Addr) (Z o w wx : Nat) (minv : BitVec 64) (v : BitVec 64) (X Y₀ c j : Nat)
    (t : State) : Prop where
  ctx : SubCtx t B Z o w wx minv
  xv : XVals t B o wx minv X
  y : wv t.mem (off B o) (slot wx aY) wx = Y₀ * 2 ^ j % X
  cnt : word t.mem (off B o) (8 * Crt.sBit) = BitVec.ofNat 64 (c - j)
  sv : word t.mem (off B o) (8 * Crt.sV) = v
  frm : Frm (off B o) (r2Ranges wx) s₀.mem t.mem
  keep : Keep mmRegs s₀ t

/-- A doubling. -/
theorem dStep_ok {s₀ t : State} {B : Addr} {Z o w wx : Nat} {minv v : BitVec 64} {X Y₀ c j : Nat}
    (hw2 : 2 ≤ wx) (hwx : wx < 2 ^ 30) (hX1 : 1 < X) (hc : c < 2 ^ 40) (hj : j < c)
    (hI : DInv s₀ B Z o w wx minv v X Y₀ c j t) :
    WP isa r2Body t fun t' => DInv s₀ B Z o w wx minv v X Y₀ c (j + 1) t' ∧ ((t'.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ c) := by
  have hg := hI.ctx.good
  have hn' : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := hg.scr.nowrap
  have hylt : wv t.mem (off B o) (slot wx aY) wx < X := by rw [hI.y]; exact Nat.mod_lt _ (by omega_using [hX1])
  refine WP.seq (WP.mono (addMod_ok hg.scr hg.x0 hg.hdr (Nat.le_refl _) hw2 (by omega_using [hwx]) (o := aY) (a := aY) (b := aY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hI.xv.n]; exact hylt) (by rw [hI.xv.n]; exact hylt)) fun t₁ ⟨hv₁, ha₁, k₁⟩ => ?_)
  rw [hI.xv.n, hI.y] at hv₁
  have f₁ : Frm (off B o) (r2Ranges wx) t.mem t₁.mem := Frm.of_arrays ha₁ (by simp [r2Ranges, redcRanges])
  have hc₁ := hI.ctx.of_frm f₁ (r2Ranges_ok wx) k₁.wr (k₁.gpr .x0 (by decide))
  have hc₁' : word t₁.mem B (o + 8 * Crt.sBit) = BitVec.ofNat 64 (c - j) := by
    rw [← word_off, ha₁.hslot (by decide)]; exact hI.cnt
  have hsub : BitVec.ofNat 64 (c - j) - 1#64 = BitVec.ofNat 64 (c - (j + 1)) := by
    rw [show (1#64) = BitVec.ofNat 64 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_using [hj])]; congr 1
  refine WP.mono (WP.keep [.x3] (Q := fun t' => t'.mem = t₁.mem.writeW (off (off B o) (8 * Crt.sBit))
      (BitVec.ofNat 64 (c - (j + 1))) ∧ t'.gpr .x3 = BitVec.ofNat 64 (c - (j + 1))) (by
    brun [hc₁.x0, hdr_enc (show Crt.sBit < 32 by decide), hc₁.ld' (show Crt.sBit < 32 by decide),
      hc₁.st' (show Crt.sBit < 32 by decide), hc₁', hsub, off_off])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨hm', h3'⟩, k'⟩ => ?_
  have o' := writeW_outside t₁.mem (off B o) (d := 8 * Crt.sBit) (BitVec.ofNat 64 (c - (j + 1))) (by decide)
  rw [← hm'] at o'
  have f' : Frm (off B o) (r2Ranges wx) t₁.mem t'.mem := Frm.of_outside o' (by simp [r2Ranges])
  have hc' := hc₁.of_frm f' (r2Ranges_ok wx) k'.wr (k'.gpr .x0 (by decide))
  refine ⟨⟨hc', XVals.of_r2 hI.xv hn' (f₁.trans f'), ?_, by rw [hm', word_writeW_self],
    by rw [o'.word (by unfold Crt.sV Crt.sBit sFn; omega_using []) (by unfold Crt.sV sFn; omega_using []), ha₁.hslot (by decide)]
       exact hI.sv,
    (hI.frm.trans f₁).trans f', (hI.keep.trans (k₁.trans k')).mono (by decide)⟩, ?_⟩
  · have := hdr_lt_slot wx aY (show 31 < 32 by decide)
    have := slot_le (w := wx) (show aY < 8 by decide)
    rw [o'.wv (by unfold Crt.sBit sFn; omega_arith) (by omega_using [hn', this]), hv₁, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two,
      Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, ← Nat.mul_two]
  · rw [h3', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hc])]
    omega_using [hj]

theorem eval_nz_ofNat' {t : State} {r : Reg} {n : Nat} (h : t.gpr r = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    isa.eval (.nonzero .x r) t = some (decide (n ≠ 0)) := by
  rw [eval_nonzero, ne_zero_iff, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- The doublings, `c` of them (none if `c = 0`), from `Y₀ < X`. -/
theorem dLoop_ok {s₀ t : State} {B : Addr} {Z o w wx : Nat} {minv v : BitVec 64} {X Y₀ c : Nat}
    (hw2 : 2 ≤ wx) (hwx : wx < 2 ^ 30) (hX1 : 1 < X) (hc : c < 2 ^ 40)
    (hI : DInv s₀ B Z o w wx minv v X Y₀ c 0 t) (h3 : t.gpr .x3 = BitVec.ofNat 64 c) :
    WP isa (.ite (.nonzero .x .x3) (.loop r2Body (.nonzero .x .x3)) (.block [])) t
      (DInv s₀ B Z o w wx minv v X Y₀ c c) := by
  by_cases hc0 : c = 0
  · subst hc0
    refine WP.ite false (by rw [eval_nz_ofNat' h3 (by omega_using [])]; rfl) (by simp) (fun _ => WP.block_nil hI)
  · refine WP.ite true (by rw [eval_nz_ofNat' h3 (by omega_using [hc])]; simp [hc0]) (fun _ => ?_) (by simp)
    exact count_loop (cr := .x3) (by omega_using [hc0]) (DInv s₀ B Z o w wx minv v X Y₀ c)
      (fun j hj t h => dStep_ok hw2 hwx hX1 hc hj h) hI

/-- Before a squaring from `s₀`: `Y = 2^(64 w_X + t) mod X` if `P`. -/
structure SInv (s₀ : State) (B : Addr) (Z o w wx : Nat) (minv : BitVec 64) (X : Nat) (P : Prop) (t : Nat)
    (u : State) : Prop where
  ctx : SubCtx u B Z o w wx minv
  xv : XVals u B o wx minv X
  lt : wv u.mem (off B o) (slot wx aY) wx < X
  y : P → wv u.mem (off B o) (slot wx aY) wx = 2 ^ (64 * wx + t) % X
  frm : Frm (off B o) (r2Ranges wx) s₀.mem u.mem
  keep : Keep mmRegs s₀ u

/-- A Montgomery squaring: `2^(64 w_X + t) ↦ 2^(64 w_X + 2 t)`. -/
theorem sqStep_ok (M : Mont) {s₀ u : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X : Nat} {P : Prop}
    {t : Nat} (hw2 : 2 ≤ wx) (hwx : wx < 2 ^ 30) (hodd : P → X % 2 = 1) (hI : SInv s₀ B Z o w wx minv X P t u) :
    WP isa (M.mm aY aY aY) u (SInv s₀ B Z o w wx minv X P (2 * t)) := by
  have hg := hI.ctx.good
  refine WP.mono (M.mm_ok hg (Nat.le_refl _) hw2 (by omega_using [hwx]) (o := aY) (a := aY) (b := aY) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hI.xv.inv (by rw [hI.xv.n]; exact hI.lt))
    fun u' ⟨_, hlt, hm, ha, k⟩ => ?_
  rw [hI.xv.n] at hlt hm
  have f : Frm (off B o) (r2Ranges wx) u.mem u'.mem := Frm.of_arrays ha (by simp [r2Ranges, redcRanges])
  exact ⟨hI.ctx.of_frm f (r2Ranges_ok wx) k.wr (k.gpr .x0 (by decide)), XVals.of_r2 hI.xv hg.scr.nowrap f, hlt,
    fun hp => r2_square (hodd hp) (hI.y hp) hlt hm, hI.frm.trans f, (hI.keep.trans k).mono (by decide)⟩

/-- Six squarings: `2^(64 w_X + w_X) ↦ 2^(128 w_X)`. -/
theorem sq6_ok (M : Mont) {s₀ u : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X : Nat} {P : Prop}
    (hw2 : 2 ≤ wx) (hwx : wx < 2 ^ 30) (hodd : P → X % 2 = 1) (hI : SInv s₀ B Z o w wx minv X P wx u) :
    WP isa (seqs [M.mm aY aY aY, M.mm aY aY aY, M.mm aY aY aY, M.mm aY aY aY, M.mm aY aY aY, M.mm aY aY aY]) u
      (SInv s₀ B Z o w wx minv X P (64 * wx)) := by
  simp only [seqs]
  refine WP.seq (WP.mono (sqStep_ok M hw2 hwx hodd hI) fun u₁ h₁ => ?_)
  refine WP.seq (WP.mono (sqStep_ok M hw2 hwx hodd h₁) fun u₂ h₂ => ?_)
  refine WP.seq (WP.mono (sqStep_ok M hw2 hwx hodd h₂) fun u₃ h₃ => ?_)
  refine WP.seq (WP.mono (sqStep_ok M hw2 hwx hodd h₃) fun u₄ h₄ => ?_)
  refine WP.seq (WP.mono (sqStep_ok M hw2 hwx hodd h₄) fun u₅ h₅ => ?_)
  refine WP.mono (sqStep_ok M hw2 hwx hodd h₅) fun u₆ h₆ => ?_
  rw [show 64 * wx = 2 * (2 * (2 * (2 * (2 * (2 * wx))))) by omega_using []]
  exact h₆

/-! ## `r2X` -/

/-- `zLoop`: the further reductions, while more than `2 w_X` words are left. -/
abbrev zLoop (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .ite (.nonzero .x .x4) (.loop (zBody mul) (.nonzero .x .x4)) (.block [])

/-- `dLoop`: the doublings. -/
abbrev dLoop : Prog isa := .ite (.nonzero .x .x3) (.loop r2Body (.nonzero .x .x3)) (.block [])

/-- The squarings, if `e ≤ w_X`. -/
abbrev sq6 (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .ite (.nonzero .x .x3) (seqs [mul aY aY aY, mul aY aY aY, mul aY aY aY, mul aY aY aY, mul aY aY aY,
    mul aY aY aY]) (.block [])

theorem r2X_eq (mul : Nat → Nat → Nat → Prog isa) : r2X mul =
    (redc mul aR2 ++ ([.block r2Load, kLoop, .block eInit] : List (Prog isa))) ++ (([zLoop mul] : List (Prog isa)) ++
    ((copyArr aY aXc ++ ([.block cntBlk] : List (Prog isa))) ++
      (([dLoop] : List (Prog isa)) ++ ([.block [ldh .x3 Crt.sV], sq6 mul] : List (Prog isa))))) := by
  simp only [r2X, List.append_assoc, List.cons_append, List.nil_append]

theorem mod_pow_mul {A X a c : Nat} (h : A % X = 2 ^ a % X) : A * 2 ^ c % X = 2 ^ (a + c) % X := by
  rw [Nat.mul_mod, h, ← Nat.mul_mod, Nat.pow_add]

/-- `redc` of `R² mod n` and `e₀`: `A R_X^K ≡ R² mod n`, and whether further
reductions follow. -/
theorem r2A_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X : Nat}
    (hc : SubCtx s B Z o w wx minv) (hv : XVals s B o wx minv X) (hw2 : 2 ≤ wx) (hwx : wx ≤ w)
    (hw30 : w < 2 ^ 30) (hX1 : 1 < X) :
    WP isa (seqs (redc M.mm aR2 ++ ([.block r2Load, kLoop, .block eInit] : List (Prog isa)))) s fun t =>
      RzInv s B Z o w wx minv X (wv s.mem B (slot w aR2) w) 0 t ∧
      t.gpr .x4 = (if r2E0 w wx ≤ 2 * wx then 0 else 1) := by
  have hn : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := hc.good.scr.nowrap
  refine wp_seqs_append (by simp [redc]) (by simp) ?_
  refine WP.mono (redc_ok M hc hv hw2 hwx hw30 hX1 (j := aR2) (by decide))
    fun t₁ ⟨hc₁, hv₁, hlt₁, hval₁, f₁, k₁⟩ => ?_
  refine WP.mono (r2Head_ok hc₁ hw2 hwx hw30) fun t₂ ⟨hm₂, _, h4₂, _, _, _, k₂⟩ => ⟨?_, h4₂⟩
  have o₂ := writeW_outside t₁.mem (off B o) (d := 8 * Crt.sV) (BitVec.ofNat 64 (r2E0 w wx)) (by decide)
  rw [← hm₂] at o₂
  have f₂ : Frm (off B o) (r2Ranges wx) t₁.mem t₂.mem := Frm.of_outside o₂ (by simp [r2Ranges])
  have f₁' : Frm (off B o) (r2Ranges wx) s.mem t₁.mem := f₁.mono (fun r hr => List.mem_append_left _ hr)
  have hXc₂ : wv t₂.mem (off B o) (slot wx aXc) wx = wv t₁.mem (off B o) (slot wx aXc) wx := by
    have := hdr_lt_slot wx aXc (show 31 < 32 by decide)
    have := slot_le (w := wx) (show aXc < 8 by decide)
    exact o₂.wv (by unfold Crt.sV sFn; omega_arith) (by omega_using [hn, this])
  exact ⟨hc₁.of_frm f₂ (r2Ranges_ok wx) k₂.wr (k₂.gpr .x0 (by decide)), XVals.of_r2 hv₁ hn f₂,
    by rw [hXc₂]; exact hlt₁, by rw [hXc₂, Nat.add_zero]; exact hval₁,
    by rw [hm₂, word_writeW_self, Nat.zero_mul, Nat.sub_zero], f₁'.trans f₂, (k₁.trans k₂).mono (by decide)⟩

/-- `Y := A` and the counts, after the further reductions. -/
theorem r2B_ok {s₀ t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat}
    (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30) (hZ : RzInv s₀ B Z o w wx minv X x (r2Z w wx) t) :
    WP isa (seqs (copyArr aY aXc ++ ([.block cntBlk] : List (Prog isa)))) t fun u =>
      DInv s₀ B Z o w wx minv (if r2E w wx ≤ wx then (1 : BitVec 64) else 0#64) X
        (wv t.mem (off B o) (slot wx aXc) wx) (r2C w wx) 0 u ∧ u.gpr .x3 = BitVec.ofNat 64 (r2C w wx) := by
  have hn : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := hZ.ctx.good.scr.nowrap
  obtain ⟨hE1, hE2, hE3⟩ := r2E_spec (w := w) (wx := wx) (by omega_using [hw2]) hwx
  refine wp_seqs_append (by simp [copyArr]) (by simp) ?_
  refine WP.mono (copyArr_ok hZ.ctx.good (Nat.le_refl _) (by omega_using [hw2]) (by omega_using [hwx, hw30]) (o := aY) (a := aXc) (by decide)
    (by decide) (by decide)) fun t₄ ⟨hv₄, ho₄, k₄⟩ => ?_
  have f₄ : Frm (off B o) (r2Ranges wx) t.mem t₄.mem :=
    Frm.of_outside (ho₄.mono (o' := slot wx aY) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_using []))
      (by simp [r2Ranges])
  have hc₄ := hZ.ctx.of_frm f₄ (r2Ranges_ok wx) k₄.wr (k₄.gpr .x0 (by decide))
  have he₄ : word t₄.mem (off B o) (8 * Crt.sV) = BitVec.ofNat 64 (r2E w wx) := by
    rw [ho₄.word (Or.inl (hdr_lt_slot wx aY (show Crt.sV < 32 by decide))) (by unfold Crt.sV sFn; omega_using [])]
    exact hZ.e
  simp only [seqs]
  refine WP.mono (cnt_ok hc₄ (by omega_using [hwx, hw30]) hE2 he₄) fun t₅ ⟨⟨h3₅, hm₅⟩, k₅⟩ => ?_
  have hAX : wv t.mem (off B o) (slot wx aXc) wx < X := hZ.lt
  have o₅a := writeW_outside t₄.mem (off B o) (d := 8 * Crt.sBit) (BitVec.ofNat 64 (r2C w wx)) (by decide)
  have o₅b := writeW_outside (t₄.mem.writeW (off (off B o) (8 * Crt.sBit)) (BitVec.ofNat 64 (r2C w wx)))
    (off B o) (d := 8 * Crt.sV) (if r2E w wx ≤ wx then (1 : BitVec 64) else 0#64) (by decide)
  have eC : (if r2E w wx ≤ wx then 64 * (wx - r2E w wx) + wx else 64 * (2 * wx - r2E w wx)) = r2C w wx := rfl
  rw [eC] at h3₅ hm₅
  rw [← hm₅] at o₅b
  have f₅ : Frm (off B o) (r2Ranges wx) t₄.mem t₅.mem :=
    (Frm.of_outside o₅a (by simp [r2Ranges])).trans (Frm.of_outside o₅b (by simp [r2Ranges]))
  have hc₅ := hc₄.of_frm f₅ (r2Ranges_ok wx) k₅.wr (k₅.gpr .x0 (by decide))
  have hY₅ : wv t₅.mem (off B o) (slot wx aY) wx = wv t.mem (off B o) (slot wx aXc) wx := by
    have := hdr_lt_slot wx aY (show 31 < 32 by decide)
    have := slot_le (w := wx) (show aY < 8 by decide)
    rw [o₅b.wv (by unfold Crt.sV sFn; omega_arith) (by omega_using [hn, this]), o₅a.wv (by unfold Crt.sBit sFn; omega_arith) (by omega_using [hn, this]), hv₄]
  have hcnt₅ : word t₅.mem (off B o) (8 * Crt.sBit) = BitVec.ofNat 64 (r2C w wx) := by
    rw [o₅b.word (by unfold Crt.sV Crt.sBit sFn; omega_using []) (by unfold Crt.sBit sFn; omega_using []), word_writeW_self]
  have hfl₅ : word t₅.mem (off B o) (8 * Crt.sV) = if r2E w wx ≤ wx then (1 : BitVec 64) else 0#64 := by
    rw [hm₅, word_writeW_self]
  exact ⟨⟨hc₅, XVals.of_r2 hZ.xv hn (f₄.trans f₅), by rw [hY₅, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hAX],
    by rw [hcnt₅, Nat.sub_zero], hfl₅, (hZ.frm.trans f₄).trans f₅, ((hZ.keep.trans k₄).trans k₅).mono (by decide)⟩,
    h3₅⟩

/-- The squarings, if `e ≤ w_X`, from `Y = 2^(64 e + c)` (if `P`). -/
theorem r2Tail_ok (M : Mont) {s₀ t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X A : Nat} {P : Prop}
    (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30) (hX1 : 1 < X) (hodd : P → X % 2 = 1)
    (hD : DInv s₀ B Z o w wx minv (if r2E w wx ≤ wx then (1 : BitVec 64) else 0#64) X A (r2C w wx) (r2C w wx) t)
    (hval : P → wv t.mem (off B o) (slot wx aY) wx = 2 ^ (64 * r2E w wx + r2C w wx) % X) :
    WP isa (seqs [.block [ldh .x3 Crt.sV], sq6 M.mm]) t fun u => SubCtx u B Z o w wx minv ∧
      XVals u B o wx minv X ∧ (P → wv u.mem (off B o) (slot wx aY) wx = 2 ^ (128 * wx) % X) ∧
      Frm (off B o) (r2Ranges wx) s₀.mem u.mem ∧ Keep mmRegs s₀ u := by
  have hdbl := r2_doubled (w := w) (wx := wx) (by omega_using [hw2]) hwx
  have hfl₆ : word t.mem B (o + 8 * Crt.sV) = (if r2E w wx ≤ wx then (1 : BitVec 64) else 0#64) := by
    rw [← word_off]; exact hD.sv
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun u => u.gpr .x3 = (if r2E w wx ≤ wx then (1 : BitVec 64) else 0#64) ∧
      u.mem = t.mem)
    (by brun [hD.ctx.x0, hdr_enc (show Crt.sV < 32 by decide), hD.ctx.ld' (show Crt.sV < 32 by decide), hfl₆])
    (by decide) (by decide) (by decide +kernel)) fun t₇ ⟨⟨h3₇, hm₇⟩, k₇⟩ => ?_)
  have hc₇ : SubCtx t₇ B Z o w wx minv := hD.ctx.of_frm (rs := []) (by rw [hm₇]; exact Frm.refl _ _ _) (by simp)
    k₇.wr (k₇.gpr .x0 (by decide))
  have hS : SInv s₀ B Z o w wx minv X P (if r2E w wx ≤ wx then wx else 64 * wx) t₇ :=
    ⟨hc₇, ⟨by rw [hm₇]; exact hD.xv.n, by rw [hm₇]; exact hD.xv.inv, by rw [hm₇]; exact hD.xv.one⟩,
      by rw [hm₇, hD.y]; exact Nat.mod_lt _ (by omega_using [hX1]),
      fun hp => by rw [hm₇, hval hp, hdbl]; split <;> rename_i h <;> [rfl; (congr 2; omega_using [])],
      by rw [hm₇]; exact hD.frm, (hD.keep.trans k₇).mono (by decide)⟩
  by_cases hle : r2E w wx ≤ wx
  · simp only [hle, ite_true] at h3₇ hS
    refine WP.ite true (by rw [eval_nonzero, h3₇]; rfl) (fun _ => ?_) (by simp)
    refine WP.mono (sq6_ok M hw2 (by omega_using [hwx, hw30]) hodd hS) fun u hu => ⟨hu.ctx, hu.xv, fun hp => by
      rw [hu.y hp]; congr 2; omega_using [], hu.frm, hu.keep⟩
  · simp only [hle, ite_false] at h3₇ hS
    refine WP.ite false (by rw [eval_nonzero, h3₇]; rfl) (by simp) (fun _ => WP.block_nil ?_)
    exact ⟨hS.ctx, hS.xv, fun hp => by rw [hS.y hp]; congr 2; omega_using [], hS.frm, hS.keep⟩

/-- `r2X`: `Y := R_X² mod X` when `X` is odd and `R² mod n ≡ 2^(128 w)`
modulo it (`P`), as when `X` divides `n`. -/
theorem r2X_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X : Nat} {P : Prop}
    (hc : SubCtx s B Z o w wx minv) (hv : XVals s B o wx minv X) (hw2 : 2 ≤ wx) (hwx : wx ≤ w)
    (hw30 : w < 2 ^ 30) (hX1 : 1 < X)
    (hP : P → X % 2 = 1 ∧ wv s.mem B (slot w aR2) w % X = 2 ^ (128 * w) % X) :
    WP isa (seqs (r2X M.mm)) s fun t => SubCtx t B Z o w wx minv ∧ XVals t B o wx minv X ∧
      (P → wv t.mem (off B o) (slot wx aY) wx = 2 ^ (128 * wx) % X) ∧
      Frm (off B o) (r2Ranges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hC : r2C w wx < 2 ^ 40 := by
    have := r2C_le (w := w) (wx := wx) (by omega_using [hw2]) hwx; omega_using [hwx, hw30, this]
  rw [r2X_eq]
  refine wp_seqs_append (by simp [redc]) (by simp) ?_
  refine WP.mono (r2A_ok M hc hv hw2 hwx hw30 hX1) fun t₂ ⟨hZ0, h4₂⟩ => ?_
  refine wp_seqs_append (by simp) (by simp [copyArr]) ?_
  refine WP.mono (rzLoop_ok M hw2 hwx hw30 hX1 hZ0 h4₂) fun t₃ hZ => ?_
  refine wp_seqs_append (by simp [copyArr]) (by simp) ?_
  refine WP.mono (r2B_ok hw2 hwx hw30 hZ) fun t₅ ⟨hD0, h3₅⟩ => ?_
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (dLoop_ok hw2 (by omega_using [hwx, hw30]) hX1 hC hD0 h3₅) fun t₆ hD => ?_
  refine r2Tail_ok M hw2 hwx hw30 hX1 (fun hp => (hP hp).1) hD fun hp => ?_
  obtain ⟨hodd, hx⟩ := hP hp
  have hr := r2_reduced (A := wv t₃.mem (off B o) (slot wx aXc) wx) (by omega_using [hw2]) hwx hodd (by rw [hZ.val, hx])
  rw [hD.y, mod_pow_mul hr]

/-! ## `maskCopy` -/

structure MCInv (s₀ : State) (S D : Addr) (eS eD : Nat) (j : Nat) (t : State) : Prop where
  keep : Keep [.x3, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off S (eS + 8 * j)
  x17 : t.gpr .x17 = off D (eD + 8 * j)
  done : ∀ i < j, word t.mem D (eD + 8 * i) = word s₀.mem S (eS + 8 * i) &&& s₀.gpr .x15
  frame : Outside D eD (8 * j) s₀.mem t.mem

theorem mcStep_ok {s₀ : State} {S D : Addr} {eS eD w : Nat} (hD : eD + 8 * w ≤ 2 ^ 64)
    (hrd : ∀ j < w, InRegions (s₀.rd ++ s₀.wr) (off S (eS + 8 * j)) 8)
    (hwr : ∀ j < w, InRegions s₀.wr (off D (eD + 8 * j)) 8)
    (hsep : ∀ j < w, ∀ b < 8, ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * w ≤ ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b))
    {j : Nat} (hj : j < w) {t : State} (hI : MCInv s₀ S D eS eD j t) :
    WP isa (.block ([ld .x3 .x16, .logic .and .x .x3 .x3 .x15, st .x3 .x17, next .x16, next .x17] ++
        ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => MCInv s₀ S D eS eD (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hld : InRegions (t.rd ++ t.wr) (off S (eS + 8 * j)) 8 := by
    rw [hI.keep.rd, hI.keep.wr]; exact hrd j hj
  have hst : InRegions t.wr (off D (eD + 8 * j)) 8 := by rw [hI.keep.wr]; exact hwr j hj
  have hv : word t.mem S (eS + 8 * j) = word s₀.mem S (eS + 8 * j) :=
    Mem.readW_congr fun b hb => hI.frame _ (by have := hsep j hj b hb; omega_using [hj, this])
  have h15 : t.gpr .x15 = s₀.gpr .x15 := hI.keep.gpr .x15 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off D (eD + 8 * j)) (word s₀.mem S (eS + 8 * j) &&& s₀.gpr .x15) ∧
      t₁.gpr .x16 = off S (eS + 8 * j + 8) ∧ t₁.gpr .x17 = off D (eD + 8 * j + 8))
    (by brun [hI.x16, hI.x17, hld, hst, h15, hv]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨hm, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  refine ⟨((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], fun i hi => ?_, ?_⟩
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [(writeW_outside t.mem D _ (by omega_using [hD, hj])).word (by omega_using [hi]) (by omega_arith)]; exact hI.done i hi
    · exact word_writeW_self _ _ _ _
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem D _ (by omega_using [hD, hj]) x (by omega_using [hx'])]
    exact hI.frame x (by omega_using [hx'])

/-- `maskCopy`: the `w` words at `S + eS` (`x16`) and-ed with `x15` to
`D + eD` (`x17`), which they do not overlap, changing only those. -/
theorem maskCopy_ok {s : State} {S D : Addr} {eS eD w : Nat}
    (h16 : s.gpr .x16 = off S eS) (h17 : s.gpr .x17 = off D eD) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hD : eD + 8 * w ≤ 2 ^ 64)
    (hrd : ∀ j < w, InRegions (s.rd ++ s.wr) (off S (eS + 8 * j)) 8)
    (hwr : ∀ j < w, InRegions s.wr (off D (eD + 8 * j)) 8)
    (hsep : ∀ j < w, ∀ b < 8, ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * w ≤ ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b)) :
    WP isa maskCopy s fun t =>
      (∀ i < w, word t.mem D (eD + 8 * i) = word s.mem S (eS + 8 * i) &&& s.gpr .x15) ∧
      Outside D eD (8 * w) s.mem t.mem ∧ t.gpr .x16 = off S (eS + 8 * w) ∧
      t.gpr .x17 = off D (eD + 8 * w) ∧ Keep [.x3, .x14, .x16, .x17] s t := by
  unfold maskCopy
  refine WP.seq (WP.mono (WP.keep [.x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.mem = s.mem)
    (by brun [h12]) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h14, hm₁⟩, k₁⟩ => ?_)
  have h0 : MCInv s₁ S D eS eD 0 s₁ :=
    ⟨Keep.refl _ _, by rw [k₁.gpr .x16 (by decide), h16]; rfl, by rw [k₁.gpr .x17 (by decide), h17]; rfl,
      fun i hi => absurd hi (Nat.not_lt_zero _), Outside.refl _ _ _ _⟩
  have e15 : s₁.gpr .x15 = s.gpr .x15 := k₁.gpr .x15 (by decide)
  refine WP.mono (wp_countdown (N := w) (by omega_using [hw']) (by omega_using [hw]) (MCInv s₁ S D eS eD)
    (fun j hj t hI _ => mcStep_ok hD (by rw [k₁.rd, k₁.wr]; exact hrd) (by rw [k₁.wr]; exact hwr) hsep hj hI)
    h0 h14) fun t hI => ?_
  refine ⟨fun i hi => by rw [hI.done i hi, hm₁, e15], by rw [← hm₁]; exact hI.frame, hI.x16, hI.x17,
    (k₁.trans hI.keep).mono (by decide)⟩

/-- Words copied and-ed with a mask: the number, or 0. -/
theorem wv_mask {m m' : Mem} {S D : Addr} {eS eD : Nat} {c : Bool} :
    ∀ {n : Nat}, (∀ i < n, word m' D (eD + 8 * i) = word m S (eS + 8 * i) &&& mask c) →
      wv m' D eD n = if c then wv m S eS n else 0
  | 0, _ => by cases c <;> rfl
  | n + 1, h => by
    rw [wv, wv, wv_mask fun i hi => h i (by omega_using [hi]), h n (by omega_using []), and_mask_toNat]
    cases c <;> simp

end VG.Proof.Bignum.AArch64.PrivPre
