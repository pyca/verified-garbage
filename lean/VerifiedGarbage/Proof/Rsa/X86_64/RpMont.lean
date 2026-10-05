import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.Bignum.X86_64.PubR2

/-!
# `vg_rsa_recover_primes` on x86-64: Montgomery form

`minvBlk`: `-n⁻¹ mod 2⁶⁴` into its slot (`minvBlk_ok`). `mont`: `R² mod n`
as `vg_rsa_public` computes it, 1, `R mod n` and `n - R mod n`, the
Montgomery forms of 1 and `-1` (`mont_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)
open VG.Proof.Bignum (mont_cancel)

/-- `minvBlk`: `-n⁻¹ mod 2⁶⁴` into `sMinv`, for an odd `n`. -/
theorem minvBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    (hodd : (word s.mem B (slot w aN)).toNat % 2 = 1) :
    WP isa (.block minvBlk) s fun t =>
      ((word t.mem B (slot w aN)).toNat * (word t.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
      Frm B (rg w [] [sMinv]) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have sN := h.sl (j := aN) (by decide)
  have hN0 := hdr_lt_slot w aN (show sMinv < 32 by decide)
  unfold minvBlk
  rw [List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aN (r := .r10) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9)
    fun t₂ ⟨h10, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = word s.mem B (slot w aN) ∧ t.mem = s.mem) (by
    xrun [State.ea, at0, h10, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.ld (d := slot w aN) (by omega), m₂, m₁]) rfl) fun t₃ ⟨⟨hbx, m₃⟩, k₃⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (minv_ok t₃ (by rw [hbx]; exact hodd)) fun t₄ ⟨hi, k₄, m₄⟩ => ?_
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hdi₄ : t₄.gpr .rdi = B := (k14.gpr (by decide)).trans h.rdi
  have hs₄ := h.scr.congr k14.2.2
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = t₄.mem.writeW (off B (8 * sMinv)) (t₄.gpr .r15)) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.st (d := 8 * sMinv) (by simp only [sMinv]; omega)]) rfl)
    fun t ⟨mt, k₅⟩ => ?_
  have o := writeW_outside t₄.mem B (t₄.gpr .r15) (d := 8 * sMinv) (by simp only [sMinv]; omega)
  rw [← mt] at o
  have m4 : t₄.mem = s.mem := m₄.trans m₃
  refine ⟨?_, by rw [← m4]; exact Frm.rg_of_hdr o _ _ (List.mem_singleton_self _), (k14.trans k₅).mono (by decide)⟩
  rw [o.word (Or.inr (by omega)) (by omega), mt, word_writeW_self, m4, ← hbx]
  exact hi

/-- The bases of a subtraction `[c] := [a] - [b]`, `w` and no borrow. -/
theorem subSet_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (a b c : Nat) :
    WP isa (.block (ws ++ base a .r8 ++ base b .r10 ++ base c .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr))) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r8 = off B (slot w a) ∧ t.gpr .r10 = off B (slot w b) ∧
      t.gpr .rsi = off B (slot w c) ∧ t.gpr .rbp = mask false ∧ t.mem = s.mem ∧
      Keep [.r12, .r9, .r8, .r10, .rsi, .rbp] s t := by
  rw [List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  have hdi₁ : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.rdi
  refine WP.mono (base_ok a (r := .r8) (by decide) hdi₁ h9) fun t₂ ⟨h8, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok b (r := .r10) (by decide) ((k₂.gpr (by decide)).trans hdi₁)
    ((k₂.gpr (by decide)).trans h9)) fun t₃ ⟨h10, m₃, k₃⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok c (r := .rsi) (by decide) ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hdi₁))
    ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h9))) fun t₄ ⟨hsi, m₄, k₄⟩ => ?_
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask false ∧ t.mem = t₄.mem) (by xrun) rfl)
    fun t ⟨⟨hbp, mt⟩, k₅⟩ => ⟨?_, ?_, ?_, (k₅.gpr (by decide)).trans hsi, hbp, by rw [mt, m₄, m₃, m₂, m₁],
      ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  · exact (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans
      ((k₂.gpr (by decide)).trans h12)))
  · exact (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans h8))
  · exact (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans h10)

/-- `R` is invertible modulo `n`, and `R mod n`'s value. -/
theorem r_one {Y N R R2 : Nat} (hR : Nat.Coprime R N) (hY : Y < N) (hr2 : R2 % N = R * R % N)
    (h : Y * R % N = R2 * 1 % N) : Y = R % N := by
  rw [← Nat.mod_eq_of_lt hY]
  exact mont_cancel hR (by rw [h, Nat.mul_one, hr2])

/-- `mont`: `R² mod n`, 1, `R mod n` and `n - R mod n`, for the odd `n` in
its array, of `w` words with the top one not zero, and `-n⁻¹` in `sMinv`. -/
theorem mont_ok (M : Mont) {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w)
    (hinv : ((word s.mem B (slot w aN)).toNat * (word s.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (hlo : 2 ^ (64 * (w - 1)) ≤ N) :
    WP isa (seqs (mont M.mm)) s fun t => Ws t B Z w ∧
      wv t.mem B (slot w aR2) w < N ∧ wv t.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aOne) w = 1 ∧ wv t.mem B (slot w aO) w = 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aNg) w = N - 2 ^ (64 * w) % N ∧
      Frm B (rg w [aAcc, aTmp, aR2, aOne, aY, aO, aNg] [sCnt]) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn0 := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have hZ16 : slot w 16 ≤ 2 ^ 64 := by omega
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hN1 : 1 < N := by
    have : 1 ≤ 2 ^ (64 * (w - 1)) := Nat.one_le_two_pow
    have : 2 ^ 64 ≤ 2 ^ (64 * (w - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hNR : N < 2 ^ (64 * w) := hn ▸ wv_lt _ _ _ _
  obtain ⟨minv, hmv⟩ : ∃ v, word s.mem B (8 * sMinv) = v := ⟨_, rfl⟩
  rw [hmv] at hinv
  rw [show mont M.mm = [.block [.mov .r12 (.mem (hdr sW)), .mov .r10 (.mem (hdr (sArr aN)))]] ++
    (r2Steps M ++ [.block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0), .mov .r12 (.mem (hdr sW))],
      setWord aOne .rcx, M.mm aY aR2 aOne, copyA aO aY,
      .block (ws ++ base aN .r8 ++ base aO .r10 ++ base aNg .rsi ++ [.mov32 .rbp (.imm 0)]),
      wordLoop 0 subBody]) from rfl]
  refine wp_seqs_append (by simp) (by simp) ?_
  -- The bases of `n` and `w`.
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => h.scr.ld (by omega)
  refine WP.mono (WP.keep [.r12, .r10] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r10 = off B (slot w aN) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, h.rdi, hdrOff, hl _ (show sW < 32 by decide), hl _ (show sArr aN < 32 by decide), h.hw,
      h.harr aN (by decide)]) rfl) fun t₁ ⟨⟨h12, h10, m₁⟩, k₁⟩ => ?_
  have hw₁ : Ws t₁ B Z w := h.congrG (js := []) (hs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) k₁
    (by decide)
  have hg₁ := hw₁.good
  rw [m₁, hmv] at hg₁
  refine wp_seqs_append (by simp [r2Steps]) (by simp) (WP.mono (r2_ok M hg₁.1 hg₁.2 hw1 (by omega)
    (by rw [m₁]; exact hn) (by rw [m₁]; exact hinv) h12 h10 hodd hlo) fun t₂ ⟨hg₂, hlt, hc, hf₂, k₂⟩ => ?_)
  have hf₂' : Frm B (rg w [aAcc, aTmp, aR2] [sCnt]) t₁.mem t₂.mem := hf₂
  have hw₂ : Ws t₂ B Z w := hw₁.congrG hf₂' (by decide) k₂ (by decide)
  have hN₂ : wv t₂.mem B (slot w aN) w = N := by
    rw [hf₂'.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), m₁, hn]
  have hi₂ : ((word t₂.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hf₂'.rg_word0 hZ16 (by decide) (by decide) (by decide), m₁]; exact hinv
  have hmv₂ : word t₂.mem B (8 * sMinv) = minv := hg₂.hdr.hminv
  simp only [seqs]
  -- 1, 0 and `w`.
  refine WP.seq (WP.mono (WP.keep [.rdx, .rcx, .r12] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 1 ∧
      t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧ t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hw₂.rdi, hdrOff, hw₂.scr.ld (d := 8 * sW) (by simp only [sW]; omega), hw₂.hw]
    ) rfl) fun t₃ ⟨⟨hdx, hcx, h12₃, m₃⟩, k₃⟩ => ?_)
  have hw₃ : Ws t₃ B Z w := hw₂.congrG (js := []) (hs := []) (by rw [m₃]; exact Frm.refl _ _ _) (by simp) k₃
    (by decide)
  have hH₃ : Hdr t₃.mem B w minv := ⟨hw₃.hw, by rw [m₃]; exact hmv₂, fun j hj => hw₃.harr j hj⟩
  refine WP.seq (WP.mono (setWord_ok hw₃.scr hw₃.rdi hH₃ hg₁.2 h12₃ (by omega) (by omega)
    (o := aOne) (by decide) (ri := .rcx) (by decide) (i := 0) (by omega) hcx) fun t₄ ⟨hv₄, o₄, k₄⟩ => ?_)
  rw [hdx, BitVec.toNat_ofNat] at hv₄
  have hf₄ : Frm B (rg w [aOne] []) t₃.mem t₄.mem := Frm.rg_of_out o₄ (Nat.le_refl _) _ _ (by decide)
  have hw₄ : Ws t₄ B Z w := hw₃.congrG hf₄ (by simp) k₄ (by decide)
  have hg₄ := hw₄.good
  have hmv₄ : word t₄.mem B (8 * sMinv) = minv := by
    rw [hf₄.rg_word (by decide) (by simp), m₃, hmv₂]
  rw [hmv₄] at hg₄
  have hN₄ : wv t₄.mem B (slot w aN) w = N := by
    rw [hf₄.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), m₃, hN₂]
  have hi₄ : ((word t₄.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hf₄.rg_word0 hZ16 (by simp) (by decide) (by decide), m₃]; exact hi₂
  have hR2₄ : wv t₄.mem B (slot w aR2) w = wv t₂.mem B (slot w aR2) w := by
    rw [hf₄.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), m₃]
  -- `Y = R mod n`.
  refine WP.seq (WP.mono (M.mm_ok hg₄.1 hg₄.2 hw1 (by omega) (o := aY) (a := aR2) (b := aOne) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hi₄
    (by rw [hv₄, hN₄]; simpa using hN1)) fun t₅ ⟨hg₅, hlt₅, hc₅, ha₅, k₅⟩ => ?_)
  rw [hN₄] at hlt₅
  rw [hN₄, hR2₄, hv₄] at hc₅
  have hY₅ : wv t₅.mem B (slot w aY) w = 2 ^ (64 * w) % N := r_one hR hlt₅ hc (by simpa using hc₅)
  have hf₅ : Frm B (rg w [aAcc, aTmp, aY] []) t₄.mem t₅.mem := Frm.rg_of_arrays ha₅ _ _ (by decide)
  have hw₅ : Ws t₅ B Z w := hw₄.congrG hf₅ (by simp) k₅ (by decide)
  -- `R mod n` into its array.
  refine WP.seq (WP.mono (copyA_ok hw₅ (o := aO) (a := aY) (by decide) (by decide) (by decide))
    fun t₆ ⟨hv₆, o₆, k₆⟩ => ?_)
  have hf₆ : Frm B (rg w [aO] []) t₅.mem t₆.mem := Frm.rg_of_out o₆ (by omega) _ _ (by decide)
  have hw₆ : Ws t₆ B Z w := hw₅.congrG hf₆ (by simp) k₆ (by decide)
  rw [hY₅] at hv₆
  -- `n - R mod n`.
  refine WP.seq (WP.mono (subSet_ok hw₆ aN aO aNg) fun t₇ ⟨h12₇, h8₇, h10₇, hsi₇, hbp₇, m₇, k₇⟩ => ?_)
  have hs₇ := hw₆.scr.congr k₇.2.2
  refine WP.mono (sub_ok hs₇ h8₇ h10₇ hsi₇ h12₇ hbp₇ (by omega) (by omega) (by have := hw₆.sl (j := aN) (by decide); omega)
    (by have := hw₆.sl (j := aO) (by decide); omega) (by have := hw₆.sl (j := aNg) (by decide); omega)
    (by have := slot_far (w := w) (show aNg ≠ aN by decide); omega)
    (by have := slot_far (w := w) (show aNg ≠ aO by decide); omega))
    fun t ⟨c, _, hv, o₈, k₈⟩ => ?_
  have hf₈ : Frm B (rg w [aNg] []) t₆.mem t.mem := by
    rw [← m₇]; exact Frm.rg_of_out o₈ (by omega) _ _ (by decide)
  have k68 := k₇.trans k₈
  have hw₈ : Ws t B Z w := hw₆.congrG hf₈ (by simp) k68 (by decide)
  -- The values, through the later pieces.
  have hO₇ : wv t₆.mem B (slot w aO) w = 2 ^ (64 * w) % N := hv₆
  have hN₆ : wv t₆.mem B (slot w aN) w = N := by
    rw [hf₆.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      hf₅.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hN₄]
  rw [m₇, hO₇, hN₆] at hv
  have hRN : 2 ^ (64 * w) % N < N := Nat.mod_lt _ (by omega)
  have hc0 : c = false := by
    cases c
    · rfl
    · have := wv_lt t.mem B (slot w aNg) w
      simp only [Bool.toNat_true, Nat.mul_one] at hv
      omega
  subst hc0
  simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
  have hR2₆ : wv t₆.mem B (slot w aR2) w = wv t₂.mem B (slot w aR2) w := by
    rw [hf₆.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      hf₅.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hR2₄]
  have hOne₆ : wv t₆.mem B (slot w aOne) w = 1 := by
    rw [hf₆.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega),
      hf₅.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hv₄]
    rfl
  refine ⟨hw₈, ?_, ?_, ?_, ?_, by omega, ?_, ?_⟩
  · rw [hf₈.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hR2₆]; exact hlt
  · rw [hf₈.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hR2₆]; exact hc
  · rw [hf₈.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hOne₆]
  · rw [hf₈.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), hO₇]
  · have hf₂s : Frm B (rg w [aAcc, aTmp, aR2] [sCnt]) s.mem t₂.mem := by rw [← m₁]; exact hf₂'
    have hf₄s : Frm B (rg w [aOne] []) t₂.mem t₄.mem := by rw [← m₃]; exact hf₄
    have := ((hf₂s.rg_trans hf₄s).rg_trans hf₅).rg_trans hf₆
    exact (this.rg_trans hf₈).rg_mono (by decide) (by decide)
  · exact ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k68).mono (by decide)

end VG.Proof.Rsa.X86_64
