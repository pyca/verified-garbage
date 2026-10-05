import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontSetup
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec

/-!
# A candidate on x86-64: the rest of `montSetup`

`R mod c` into `aY` (`msY_ok`), copied into `aR1`; `c − R mod c` into `aRm1`
(`msRm1_ok`); the number of uniform witnesses, `checksW w`, into `kChecks`
(`msChecks_ok`); and all of `montSetup` (`montSetup_ok`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- `c − [aR1]` into `aRm1`, both extra arrays. -/
theorem msRm1_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hXZ : slot w aRm1 + 8 * (w + 2) ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hlt : wv s.mem B (slot w aR1) w < wv s.mem B (slot w aN) w) :
    WP isa (seqs [.block (([.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN)))] : List Instr) ++ extBase aR1 .r10 ++
        extBase aRm1 .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr)),
      wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .r8 .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
        .store (ix .rsi .r14) .rax, cfToRbp]]) s fun t =>
      wv t.mem B (slot w aRm1) w = wv s.mem B (slot w aN) w - wv s.mem B (slot w aR1) w ∧
      Outside B (slot w aRm1) (8 * w) s.mem t.mem ∧ Keep [.rax, .rbp, .rsi, .r8, .r10, .r12, .r14] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have e1 : slot w aR1 + 8 * (w + 2) = slot w aRm1 := by unfold slot aR1 aRm1; omega
  have e0 : slot w aN + 8 * (w + 2) ≤ slot w aR1 := by unfold slot aN aR1; omega
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12, .r8] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r8 = off B (slot w aN) ∧
      t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hg.hdr.hw,
      hg.hdr.harr aN (by decide)]) rfl) fun s₁ ⟨⟨h12, h8, hm₁⟩, k₁⟩ => ?_
  have hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine WP.mono (extBase_ok hg₁ hZ hw' (j := aR1) (by decide) (r := .r10) (by decide) rfl rfl)
    fun s₂ ⟨h10, hm₂, k₂⟩ => ?_
  have hg₂ : Good s₂ B Z w mi := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, by rw [hm₂]; exact hg₁.hdr⟩
  refine WP.mono (extBase_ok hg₂ hZ hw' (j := aRm1) (by decide) (r := .rsi) (by decide) rfl rfl)
    fun s₃ ⟨hsi, hm₃, k₃⟩ => ?_
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask false ∧ t.mem = s₃.mem) (by xrun) rfl)
    fun s₄ ⟨⟨hbp, hm₄⟩, k₄⟩ => ?_
  have k24 := (k₂.trans k₃).trans k₄
  have hs₄ := (hg₂.scr.congr k₃.2.2).congr k₄.2.2
  have hm₄' : s₄.mem = s.mem := by rw [hm₄, hm₃, hm₂, hm₁]
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw'
    (SubInv s₄ B Z (slot w aN) (slot w aR1) (slot w aRm1))
    (fun t h14 hm k _ => ⟨hs₄.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, by rw [k.gpr (by decide)]; exact hbp, by simp [wv]⟩⟩)
    (fun j _ hj t hI => subStep_ok ((k24.gpr (by decide)).trans h8)
      ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans h10)) ((k₄.gpr (by decide)).trans hsi)
      ((k24.gpr (by decide)).trans h12) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hj hI))
    fun t hI => ?_
  obtain ⟨b, -, hv⟩ := hI.val
  rw [hm₄'] at hv
  have hb : b = false := by
    cases b
    · rfl
    · have := wv_lt t.mem B (slot w aRm1) w
      have := wv_lt s.mem B (slot w aN) w
      simp only [Bool.toNat_true, Nat.mul_one] at hv; omega
  subst hb
  simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
  refine ⟨by omega, by rw [← hm₄']; exact hI.out, (((k₁.trans k24).trans hI.keep)).mono (by decide)⟩

theorem cmp_imm_cf {x k : Nat} (hx : x < 2 ^ 63) (hk : k < 2 ^ 31) :
    decide ((BitVec.ofNat 64 x).toNat < (BitVec.signExtend 64 (BitVec.ofNat 32 k)).toNat) = decide (x < k) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have : (BitVec.signExtend 64 (BitVec.ofNat 32 k)).toNat = k := by
    have hm : (BitVec.ofNat 32 k).msb = false := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp; omega
    rw [BitVec.signExtend_eq_setWidth_of_msb_false hm, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [this]

/-- One comparison of the chain choosing `checksW`, after `pre` (which
leaves `w` in `rcx`): `rax := v`, and on to `rest` unless `w < k`. -/
theorem chkStep_ok {t : State} {w v k : Nat} {pre : List Instr} {rest : Prog isa} {Q : State → Prop}
    (hpre : WP isa (.block pre) t fun t' => t'.gpr .rcx = BitVec.ofNat 64 w ∧ t'.mem = t.mem ∧ Keep [.rax, .rcx] t t')
    (hw : w < 2 ^ 63) (hv : v < 2 ^ 31) (hk : k < 2 ^ 31)
    (ht : w < k → ∀ t', t'.gpr .rax = BitVec.ofNat 64 v → t'.mem = t.mem → Keep [.rax, .rcx] t t' → Q t')
    (he : ¬ w < k → ∀ t', t'.gpr .rcx = BitVec.ofNat 64 w → t'.mem = t.mem → Keep [.rax, .rcx] t t' →
      WP isa rest t' Q) :
    WP isa (.seq (.block (pre ++ ([.mov32 .rax (.imm (BitVec.ofNat 32 v)), .alu .cmp .rcx (.imm (BitVec.ofNat 32 k))] : List Instr)))
      (.ite .b (.block []) rest)) t Q := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono hpre fun t₀ ⟨hcx, hm₀, k₀⟩ => ?_
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t' => t'.gpr .rax = BitVec.ofNat 64 v ∧
      t'.cf = some (decide (w < k)) ∧ t'.gpr .rcx = BitVec.ofNat 64 w ∧ t'.mem = t₀.mem) (by
    xrun [hcx]
    refine ⟨?_, cmp_imm_cf hw hk⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]) rfl) fun t₁ ⟨⟨hax, hcf, hcx₁, hm⟩, k₁⟩ => ?_
  have hm' : t₁.mem = t.mem := hm.trans hm₀
  refine WP.ite (decide (w < k)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (ht (by simpa using h) t₁ hax hm' ((k₀.trans k₁).mono (by decide)))
  · exact he (by simpa using h) t₁ hcx₁ hm' ((k₀.trans k₁).mono (by decide))

/-- The chain from `w` in `rcx` on, with no prefix. -/
theorem chkNil {t : State} {w : Nat} (hcx : t.gpr .rcx = BitVec.ofNat 64 w) :
    WP isa (.block []) t fun t' => t'.gpr .rcx = BitVec.ofNat 64 w ∧ t'.mem = t.mem ∧ Keep [.rax, .rcx] t t' :=
  WP.block_nil ⟨hcx, rfl, Keep.refl _ _⟩

/-- The number of uniform witnesses into `kChecks`. -/
theorem msChecks_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi)
    (hZ : slot w 8 ≤ Z) (hw : w < 2 ^ 31) :
    WP isa (seqs [.block [.mov .rcx (.mem (hdr sW)), .mov32 .rax (.imm 27), .alu .cmp .rcx (.imm 5)],
      .ite .b (.block []) (seqs [
        .block [.mov32 .rax (.imm 8), .alu .cmp .rcx (.imm 6)],
        .ite .b (.block []) (seqs [
          .block [.mov32 .rax (.imm 7), .alu .cmp .rcx (.imm 7)],
          .ite .b (.block []) (seqs [
            .block [.mov32 .rax (.imm 6), .alu .cmp .rcx (.imm 8)],
            .ite .b (.block []) (seqs [
              .block [.mov32 .rax (.imm 5), .alu .cmp .rcx (.imm 22)],
              .ite .b (.block []) (seqs [
                .block [.mov32 .rax (.imm 4), .alu .cmp .rcx (.imm 59)],
                .ite .b (.block []) (.block [.mov32 .rax (.imm 3)])])])])])]),
      .block [.store (hdr kChecks) .rax]]) s fun t =>
      t.mem = s.mem.writeW (off B (8 * kChecks)) (BitVec.ofNat 64 (Proof.RsaKeyGen.checksW w)) ∧
      Keep [.rax, .rcx] s t := by
  have hn := hg.scr.nowrap
  have hst : InRegions s.wr (off B (8 * kChecks)) 8 := hg.scr.st (by have := hdr_lt_slot w 8 (show kChecks < 32 by decide); omega)
  have fin : ∀ t', t'.gpr .rax = BitVec.ofNat 64 (Proof.RsaKeyGen.checksW w) → t'.mem = s.mem →
      Keep [.rax, .rcx] s t' → WP isa (.block [.store (hdr kChecks) .rax]) t' fun t =>
        t.mem = s.mem.writeW (off B (8 * kChecks)) (BitVec.ofNat 64 (Proof.RsaKeyGen.checksW w)) ∧
        Keep [.rax, .rcx] s t := by
    intro t' hax hm k
    have hdi : t'.gpr .rdi = B := (k.gpr (by decide)).trans hg.rdi
    have hst' : InRegions t'.wr (off B (8 * kChecks)) 8 := by rw [k.2.2]; exact hst
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B (8 * kChecks))
      (BitVec.ofNat 64 (Proof.RsaKeyGen.checksW w))) (by
      xrun [State.ea, hdr, hdi, hdrOff, hst', hax, hm]) rfl) fun t ⟨h, k'⟩ => ⟨h, (k.trans k').mono (by decide)⟩
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sW)) 8 := hg.scr.ld (by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)
  simp only [seqs]
  refine WP.assoc (WP.seq ?_)
  refine chkStep_ok (w := w) (v := 27) (k := 5) (pre := [.mov .rcx (.mem (hdr sW))]) (WP.mono (WP.keep [.rcx]
    (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 w ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hg.hdr.hw]) rfl) fun t ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k.mono (by decide)⟩)
    (by omega) (by decide) (by decide) (fun h t' hax hm k => fin t' (by rw [hax]; congr 1; simp [Proof.RsaKeyGen.checksW, h]) hm k)
    (fun h₁ t₁ hcx₁ hm₁ k₁ => ?_)
  refine chkStep_ok (w := w) (v := 8) (k := 6) (pre := []) (chkNil hcx₁) (by omega) (by decide) (by decide)
    (fun h t' hax hm k => fin t' (by rw [hax]; congr 1; simp [Proof.RsaKeyGen.checksW, h, h₁]) (hm.trans hm₁) (k₁.trans k |>.mono (by decide)))
    (fun h₂ t₂ hcx₂ hm₂ k₂ => ?_)
  refine chkStep_ok (w := w) (v := 7) (k := 7) (pre := []) (chkNil hcx₂) (by omega) (by decide) (by decide)
    (fun h t' hax hm k => fin t' (by rw [hax]; congr 1; simp [Proof.RsaKeyGen.checksW, h, h₁, h₂])
      ((hm.trans hm₂).trans hm₁) ((k₁.trans k₂).trans k |>.mono (by decide)))
    (fun h₃ t₃ hcx₃ hm₃ k₃ => ?_)
  refine chkStep_ok (w := w) (v := 6) (k := 8) (pre := []) (chkNil hcx₃) (by omega) (by decide) (by decide)
    (fun h t' hax hm k => fin t' (by rw [hax]; congr 1; simp [Proof.RsaKeyGen.checksW, h, h₁, h₂, h₃])
      (((hm.trans hm₃).trans hm₂).trans hm₁) (((k₁.trans k₂).trans k₃).trans k |>.mono (by decide)))
    (fun h₄ t₄ hcx₄ hm₄ k₄ => ?_)
  refine chkStep_ok (w := w) (v := 5) (k := 22) (pre := []) (chkNil hcx₄) (by omega) (by decide) (by decide)
    (fun h t' hax hm k => fin t' (by rw [hax]; congr 1; simp [Proof.RsaKeyGen.checksW, h, h₁, h₂, h₃, h₄])
      ((((hm.trans hm₄).trans hm₃).trans hm₂).trans hm₁) ((((k₁.trans k₂).trans k₃).trans k₄).trans k |>.mono (by decide)))
    (fun h₅ t₅ hcx₅ hm₅ k₅ => ?_)
  refine chkStep_ok (w := w) (v := 4) (k := 59) (pre := []) (chkNil hcx₅) (by omega) (by decide) (by decide)
    (fun h t' hax hm k => fin t' (by rw [hax]; congr 1; simp [Proof.RsaKeyGen.checksW, h, h₁, h₂, h₃, h₄, h₅])
      (((((hm.trans hm₅).trans hm₄).trans hm₃).trans hm₂).trans hm₁)
      (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k |>.mono (by decide)))
    (fun h₆ t₆ hcx₆ hm₆ k₆ => ?_)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 3 ∧ t.mem = t₆.mem) (by xrun) rfl)
    fun t' ⟨⟨hax, hm⟩, k⟩ => fin t' (by rw [hax]; congr 1; simp [Proof.RsaKeyGen.checksW, h₁, h₂, h₃, h₄, h₅, h₆])
      ((((((hm.trans hm₆).trans hm₅).trans hm₄).trans hm₃).trans hm₂).trans hm₁)
      ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k |>.mono (by decide))

end VG.Proof.RsaKeyGen.X86_64
