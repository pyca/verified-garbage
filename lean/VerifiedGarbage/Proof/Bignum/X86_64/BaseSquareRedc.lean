module

import VerifiedGarbage.Proof.Framework.OmegaNear
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcRow
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcStep
import VerifiedGarbage.Proof.Bignum.X86_64.BaseSquareRow
public import VerifiedGarbage.Impl.Bignum.X86_64.BaseSquare

/-!
# The baseline square's Montgomery reduction (x86-64)

`BaseSquare.redc`: the `2 w` words of a square at `A` reduced row by row
into the `w + 2` words at `A + 8 w`, `R T = X + q m` (`redc_ok`), as
`AdxSquare.redc` does, with `-m⁻¹`, `w`, the modulus' base and the end of the
rows in `xmm15`, `xmm0`, `xmm2` and `xmm3`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.BaseSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.BaseSquare VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- The low quadword that `movq r64, xmm` reads after `movq xmm, r64`. -/
theorem movq_lo (v : BitVec 64) : ((0 : BitVec 64) ++ v).extractLsb' 0 64 = v := by
  ext i h; simp only [BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_append]; simp [h]

theorem imul_redcU (a b : BitVec 64) : BitVec.ofInt 64 (a.toInt * b.toInt) = AdxSquare.redcU a b := by
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt, AdxSquare.redcU]
  apply BitVec.eq_of_toNat_eq
  simp

theorem head_ok {s : State} {B : Addr} {Z e : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (he : e + 8 ≤ Z) (hx : s.xmm .xmm15 = (0 : BitVec 64) ++ minv) :
    WP isa (.block head) s fun t =>
      t.gpr .rdx = AdxSquare.redcU (word s.mem B e) minv ∧ t.mem = s.mem ∧ Keep [.rdx, .rax] s t := by
  refine WP.mono (WP.keep [.rdx, .rax] (Q := fun t =>
    t.gpr .rdx = AdxSquare.redcU (word s.mem B e) minv ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  unfold head
  xrun [State.ea, at0, h8, hs.ld he, hx, movq_lo, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
    execImul, imul_redcU]

/-- The rows' end: the flags of `r8 = eT`, `eT` from `xmm3`. -/
theorem endTest_ok {s : State} {B : Addr} {e eT : Nat} (h8 : s.gpr .r8 = off B e)
    (hx : s.xmm .xmm3 = (0 : BitVec 64) ++ off B eT) (he : e < 2 ^ 64) (heT : eT < 2 ^ 64) :
    WP isa (.block [.movqR .rax .xmm3, .alu .cmp .r8 (.reg .rax)]) s fun t =>
      t.zf = some (decide (e = eT)) ∧ t.mem = s.mem ∧ t.gpr .r8 = off B e ∧ Keep [.rax, .r8] s t := by
  refine WP.mono (WP.keep [.rax, .r8] (Q := fun t => t.zf = some (decide (e = eT)) ∧ t.mem = s.mem ∧
    t.gpr .r8 = off B e) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [h8, hx, movq_lo, off_sub_beq B he heT]

/-- One row of the reduction, as `AdxSquare.redcRow_ok`'s, its end the
flags of `e + 8 = eT`. -/
theorem redcRow_ok {s : State} {B : Addr} {Z e eN eT w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eN)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 w) (hx15 : s.xmm .xmm15 = (0 : BitVec 64) ++ minv)
    (hx3 : s.xmm .xmm3 = (0 : BitVec 64) ++ off B eT) (heT : eT < Z)
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 31) (hwn : w < n) (heZ : e + 8 * n ≤ Z) (hsep : eN + 8 * w ≤ e)
    (hinv : ((word s.mem B eN).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa redcRow s fun t => ∃ u < 2 ^ 64,
      2 ^ 64 * (wv t.mem B (e + 8) (n - 1) + 2 ^ (64 * w) * (t.gpr .r10).toNat) =
        wv s.mem B e n + 2 ^ (64 * w) * (s.gpr .r10).toNat + u * wv s.mem B eN w ∧
      ((s.gpr .r10).toNat ≤ 1 → (t.gpr .r10).toNat ≤ 1) ∧
      Outside B e (8 * (w + 1)) s.mem t.mem ∧ t.gpr .r8 = off B (e + 8) ∧
      t.zf = some (decide (e + 8 = eT)) ∧
      Keep [.rdx, .rax, .rsi, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx, .r10, .r8] s t := by
  have hn := hs.nowrap
  unfold redcRow
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (head_ok hs h8 (by omega_near) hx15))
    fun s₁ ⟨⟨hdx, hm₁, k₁⟩, hx₁, _⟩ => ?_)
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (row_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans h8)
    ((k₁.gpr (by decide)).trans h9) ((k₁.gpr (by decide)).trans hbp) (by omega_near) (by omega_near)
    (by omega_near) (by omega_near) (by omega_near))) fun s₂ ⟨⟨hv, ho, h14, k₂⟩, hx₂, _⟩ => ?_)
  rw [hm₁, hdx] at hv
  rw [hm₁] at ho
  have k12 := k₁.trans k₂
  have hlow := AdxSquare.redc_low (by omega_near) hinv hv
  have top : word s₂.mem B (e + 8 * w) = word s.mem B (e + 8 * w) := ho.word (by omega_near) (by omega_near)
  have c10 : s₂.gpr .r10 = s.gpr .r10 := k12.gpr (by decide)
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (AdxSquare.redcTail_ok (hs.congr k12.2.2)
    ((k12.gpr (by decide)).trans h8) h14 (by omega_near))) fun s₃ ⟨⟨lo, hm₃, ht, hc, h8₃, k₃⟩, hx₃, _⟩ => ?_)
  rw [top, c10] at ht
  rw [c10] at hc
  have out₃ : Outside B (e + 8 * w) 8 s₂.mem s₃.mem := by
    rw [hm₃]; exact writeW_outside _ _ _ (by omega_near)
  have allout : Outside B e (8 * (w + 1)) s.mem s₃.mem :=
    (ho.mono (o' := e) (n' := 8 * (w + 1)) (Nat.le_refl _) (by omega_near)).trans
      (out₃.mono (o' := e) (n' := 8 * (w + 1)) (by omega_near) (by omega_near))
  have low₃ : word s₃.mem B e = 0 := (out₃.word (by omega_near) (by omega_near)).trans hlow
  have pre₃ : wv s₃.mem B e w = wv s₂.mem B e w := out₃.wv (by omega_near) (by omega_near)
  have top₃ : word s₃.mem B (e + 8 * w) = lo := by rw [hm₃, word_writeW_self]
  have high₃ : wv s₃.mem B (e + 8 * w + 8) (n - (w + 1)) =
      wv s.mem B (e + 8 * w + 8) (n - (w + 1)) := allout.wv (by omega_near) (by omega_near)
  have eq : wv s₃.mem B e n + 2 ^ (64 * w) * 2 ^ 64 * (s₃.gpr .r10).toNat =
      wv s.mem B e n + 2 ^ (64 * w) * (s.gpr .r10).toNat +
        (AdxSquare.redcU (word s.mem B e) minv).toNat * wv s.mem B eN w := by
    rw [AdxSquare.wv_at_word _ _ _ _ _ hwn, AdxSquare.wv_at_word s.mem _ _ _ _ hwn, pre₃, top₃, high₃]
    grind
  have shifted : wv s₃.mem B e n = 2 ^ 64 * wv s₃.mem B (e + 8) (n - 1) := by
    rw [show n = (n - 1) + 1 by omega_near, wv_low, low₃]
    simp
  rw [shifted] at eq
  have k123 := k12.trans k₃
  have hx₃' : s₃.xmm .xmm3 = (0 : BitVec 64) ++ off B eT := by rw [hx₃, hx₂, hx₁, hx3]
  refine WP.mono (endTest_ok h8₃ hx₃' (by omega_near) (by omega_near)) fun t ⟨hz, hm, h8', kt⟩ => ?_
  refine ⟨(AdxSquare.redcU (word s.mem B e) minv).toNat, (AdxSquare.redcU (word s.mem B e) minv).isLt, ?_, ?_, ?_,
    h8', hz, (k123.trans kt).mono (by decide)⟩
  · rw [hm, kt.gpr (by decide)]
    grind
  · rw [kt.gpr (by decide)]; exact hc
  · rw [hm]; exact allout

/-- After reduction rows `0, …, i - 1` from `s₀`, of the square's `2 w`
words at `A`, with the modulus at `eN`. -/
structure RedcInv (s₀ : State) (B : Addr) (Z A eN w : Nat) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rdx, .rax, .rsi, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx, .r10, .r8] s₀ t
  xmm : t.xmm = s₀.xmm
  r8 : t.gpr .r8 = off B (A + 8 * i)
  carry : (t.gpr .r10).toNat ≤ 1
  out : Outside B A (16 * w) s₀.mem t.mem
  val : ∃ q < 2 ^ (64 * i),
    2 ^ (64 * i) * (wv t.mem B (A + 8 * i) (2 * w - i) + 2 ^ (64 * w) * (t.gpr .r10).toNat) =
      wv s₀.mem B A (2 * w) + q * wv s₀.mem B eN w

theorem redcStep_ok {s₀ t : State} {B : Addr} {Z A eN w i : Nat} {minv : BitVec 64}
    (h9 : s₀.gpr .r9 = off B eN) (hbp : s₀.gpr .rbp = BitVec.ofNat 64 w)
    (hx15 : s₀.xmm .xmm15 = (0 : BitVec 64) ++ minv) (hx3 : s₀.xmm .xmm3 = (0 : BitVec 64) ++ off B (A + 8 * w))
    (hA : A + 16 * w + 16 ≤ Z) (hsep : eN + 8 * w ≤ A) (hw1 : 1 ≤ w) (hw : w < 2 ^ 31) (hi : i < w)
    (hinv : ((word s₀.mem B eN).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hI : RedcInv s₀ B Z A eN w i t) :
    WP isa redcRow t fun t' => t'.zf = some (decide (i + 1 = w)) ∧ RedcInv s₀ B Z A eN w (i + 1) t' := by
  have hn := hI.scr.nowrap
  have kp := hI.keep
  have hN : wv t.mem B eN w = wv s₀.mem B eN w := hI.out.wv (by omega_near) (by omega_near)
  have hN0 : word t.mem B eN = word s₀.mem B eN := hI.out.word (by omega_near) (by omega_near)
  refine WP.mono (WP.vecKeep (by decide) (redcRow_ok (n := 2 * w - i) (eT := A + 8 * w) hI.scr hI.r8
    ((kp.gpr (by decide)).trans h9) ((kp.gpr (by decide)).trans hbp) (by rw [hI.xmm]; exact hx15)
    (by rw [hI.xmm]; exact hx3) (by omega_near) hw1 hw (by omega_near) (by omega_near) (by omega_near) (by rw [hN0]; exact hinv)))
    fun t' ⟨⟨u, hu, hv, hc, ho, h8', hz, kt⟩, hx', _⟩ => ⟨?_, ?_⟩
  · rw [hz]
    congr 1
    exact decide_eq_decide.mpr (by omega_near)
  rw [hN, show A + 8 * i + 8 = A + 8 * (i + 1) by omega_near, show 2 * w - i - 1 = 2 * w - (i + 1) by omega_near] at hv
  refine ⟨hI.scr.congr kt.2.2, (kp.trans kt).mono (by decide), hx'.trans hI.xmm, ?_, hc hI.carry, ?_, ?_⟩
  · rw [h8']; congr 1
  · exact hI.out.trans (ho.mono (o' := A) (n' := 16 * w) (by omega_near) (by omega_near))
  · obtain ⟨q, hq, heq⟩ := hI.val
    refine ⟨q + 2 ^ (64 * i) * u, ?_, ?_⟩
    · rw [pow64_succ]
      exact AdxSquare.digit_bound hq hu
    · rw [pow64_succ]
      grind

/-- `redc`: `R T = X + q m` for the square `X` at `A` and the result `T`,
its `w + 2` words at `A + 8 w`. -/
theorem redc_ok {s : State} {B : Addr} {Z A eN w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B A) (hx0 : s.xmm .xmm0 = (0 : BitVec 64) ++ BitVec.ofNat 64 w)
    (hx2 : s.xmm .xmm2 = (0 : BitVec 64) ++ off B eN) (hx15 : s.xmm .xmm15 = (0 : BitVec 64) ++ minv)
    (hx3 : s.xmm .xmm3 = (0 : BitVec 64) ++ off B (A + 8 * w))
    (hA : A + 16 * w + 16 ≤ Z) (hsep : eN + 8 * w ≤ A) (hw1 : 1 ≤ w) (hw : w < 2 ^ 31)
    (hinv : ((word s.mem B eN).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa redc s fun t =>
      (∃ q < 2 ^ (64 * w), 2 ^ (64 * w) * wv t.mem B (A + 8 * w) (w + 2) =
        wv s.mem B A (2 * w) + q * wv s.mem B eN w) ∧
      Outside B A (16 * w + 16) s.mem t.mem ∧ t.gpr .r8 = off B (A + 8 * w) ∧ t.xmm = s.xmm ∧
      Keep [.rdx, .rax, .rsi, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx, .r10, .r8, .r9, .rbp] s t := by
  have hn := hs.nowrap
  unfold redc
  have init : WP isa (.block [.movqR .r9 .xmm2, .movqR .rbp .xmm0, .mov32 .r10 (.imm 0)]) s fun t =>
      t.gpr .r9 = off B eN ∧ t.gpr .rbp = BitVec.ofNat 64 w ∧ t.gpr .r10 = 0 ∧ t.mem = s.mem ∧
        Keep [.r9, .rbp, .r10] s t := by
    refine WP.mono (WP.keep [.r9, .rbp, .r10] (Q := fun t => t.gpr .r9 = off B eN ∧
      t.gpr .rbp = BitVec.ofNat 64 w ∧ t.gpr .r10 = 0 ∧ t.mem = s.mem) ?_ rfl)
      fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
    xrun [hx0, hx2, movq_lo, RegUpd.xmm_setReg]
  refine WP.seq (WP.mono (WP.vecKeep (by decide) init) fun s₁ ⟨⟨h9, hbp, h10, hm₁, k₁⟩, hx₁, _⟩ => ?_)
  rw [← hm₁] at hinv
  have I0 : RedcInv s₁ B Z A eN w 0 s₁ := by
    refine ⟨hs.congr k₁.2.2, Keep.refl _ _, rfl, by simpa using (k₁.gpr (by decide)).trans h8, by simp [h10],
      Outside.refl _ _ _ _, 0, by decide, ?_⟩
    simp [h10]
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := w) (by omega_near) (RedcInv s₁ B Z A eN w)
    (fun i _ hi t h => redcStep_ok h9 hbp (by rw [hx₁]; exact hx15) (by rw [hx₁]; exact hx3) hA hsep hw1 hw hi
      hinv h) (fun _ h => h) I0) fun s₂ hI => ?_)
  refine WP.mono (WP.vecKeep (by decide) (AdxSquare.redcFinish_ok hI.scr hI.r8
    ((hI.keep.gpr (by decide)).trans hbp) (by omega_near))) fun t ⟨⟨hv, ho, kt⟩, hxt, _⟩ => ?_
  obtain ⟨q, hq, heq⟩ := hI.val
  rw [show 2 * w - w = w by omega_near, hm₁] at heq
  have o₁ := hI.out
  rw [hm₁] at o₁
  refine ⟨⟨q, hq, ?_⟩, ?_, ?_, ?_, ((k₁.trans hI.keep).trans kt).mono (by decide)⟩
  · rw [hv]; exact heq
  · exact (o₁.mono (o' := A) (n' := 16 * w + 16) (Nat.le_refl _) (by omega_near)).trans
      (ho.mono (o' := A) (n' := 16 * w + 16) (by omega_near) (by omega_near))
  · rw [kt.gpr (by decide)]; exact hI.r8
  · rw [hxt, hI.xmm, hx₁]

end VG.Proof.Bignum.X86_64.BaseSquare
