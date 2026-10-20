module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWin
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# A candidate on AArch64: Miller–Rabin's exponentiation loops

`WinInv`: after `t` windows of word `k − 1` of `E` (the words from the top),
`y R mod c` and the flag after the `16 (w − k) + t` windows from the top
(`wRun`), the word shifted left by `4 t` in `kV`. `mrWins_ok`: the inner
loop over the word's 16 windows; `mrWord_ok`: one word.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

/-- What the exponentiation changes. -/
def expRanges (w : Nat) : List (Nat × Nat) := winRanges w ++ [(8 * kWords, 8)]

/-- `expRanges`'s ranges, in the header and in the arrays. -/
theorem expRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(8, 8), (184, 8), (208, 8), (240, 8), (232, 8)]
    [(2, 1), (3, 1), (6, 1), (5, 1)] (expRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append,
    expRanges, winRanges, Public.sCnt, Public.aAcc, Public.aTmp, Public.aXm, Public.aY, aAcc, aTmp, aXm, aY, kT0, sFn, sCnt, kG, kV, kWords, kBits, kFlag, kPlen, kT1, kT2] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(6, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(5, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)

theorem expRanges_low (w : Nat) : ∀ r ∈ expRanges w, r.1 + r.2 ≤ slot w aT0 := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact winRanges_low w r hr
  · simp only [List.mem_singleton] at hr; subst hr
    simp only [slot, hdrBytes, aT0, kWords, kT1, sFn]; omega

theorem expRanges_mut (w : Nat) : ∀ r ∈ expRanges w, KMut r := by
  unfold expRanges winRanges; simp only [List.cons_append, List.nil_append]; w_mut

theorem sqRanges_sub (w : Nat) : ∀ r ∈ sqRanges w, r ∈ expRanges w := fun r hr =>
  List.mem_append_left _ (sqRanges_win w r hr)

theorem winRanges_sub (w : Nat) : ∀ r ∈ winRanges w, r ∈ expRanges w := fun _ hr => List.mem_append_left _ hr

theorem expRanges_hdr (w : Nat) {i : Nat} (hi : i = kWords ∨ i = kV ∨ i = kBits ∨ i = kFlag) :
    (8 * i, 8) ∈ expRanges w := by
  rcases hi with rfl | rfl | rfl | rfl <;> simp [expRanges, winRanges]

/-- `MrCtx` survives changes within the exponentiation's ranges. -/
theorem MrCtx.of_exp {s t : State} {B : Addr} {Z w c bm : Nat} {rs : List (Nat × Nat)}
    (hc : MrCtx s B Z w c bm) (hf : Frm B rs s.mem t.mem) (hs : ∀ r ∈ rs, r ∈ expRanges w)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : MrCtx t B Z w c bm :=
  hc.of_frm (hf.mono hs) (expRanges_mut w) k hr
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; w_disj)
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; w_disj)
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; w_disj)
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; w_disj)
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; w_disj)

/-- After `t` windows of word `k − 1`, `W`, of `E`. -/
structure WinInv (B : Addr) (Z w : Nat) (c bm b k : Nat) (W : BitVec 64) (s₀ : State) (t : Nat)
    (s : State) : Prop where
  ctx : MrCtx s B Z w c bm
  tab : TabOK s.mem B w c b
  y : wv s.mem B (slot w aY) w = (wRun c b (mrE c) (16 * w) (16 * (w - k) + t)).1 * 2 ^ (64 * w) % c
  flag : word s.mem B (8 * kFlag) = mask (wRun c b (mrE c) (16 * w) (16 * (w - k) + t)).2
  v : word s.mem B (8 * kV) = W <<< (4 * t)
  bits : word s.mem B (8 * kBits) = BitVec.ofNat 64 (16 - t)
  words : word s.mem B (8 * kWords) = BitVec.ofNat 64 (k - 1)
  frm : Frm B (expRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

/-- One window of word `k − 1`. -/
theorem mrWinStep_ok (M : Mont) {B : Addr} {Z w c bm b k : Nat} {W : BitVec 64} {s₀ s : State}
    (hw128 : w ≤ 128) (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hodd : c % 2 = 1) (hc1 : 1 < c) (hk : 1 ≤ k)
    (hkw : k ≤ w) (hW : W.toNat = mrE c / 2 ^ (64 * (k - 1)) % 2 ^ 64) {j : Nat} (hj : j < 16)
    (hI : WinInv B Z w c bm b k W s₀ j s) :
    WP isa (seqs (mrWin M.mm)) s fun t =>
      WinInv B Z w c bm b k W s₀ (j + 1) t ∧ ((t.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ 16) := by
  have hdig := win_digit hW hj
  refine WP.mono (mrWin_ok M hw128 hEZ hI.ctx hI.tab hodd hc1 hI.y hI.flag hI.v hI.bits (by omega_arith)
    (by omega_arith)) fun t ⟨hct, htt, hyt, hft, hvt, hbt, h3, hfr, kt⟩ => ⟨?_, ?_⟩
  · have e : wRun c b (mrE c) (16 * w) (16 * (w - k) + (j + 1)) =
        wWin c b ((W <<< (4 * j)) >>> 60).toNat
          ((wRun c b (mrE c) (16 * w) (16 * (w - k) + j)).1, (wRun c b (mrE c) (16 * w) (16 * (w - k) + j)).2) := by
      rw [show 16 * (w - k) + (j + 1) = (16 * (w - k) + j) + 1 by omega_arith, wRun, hdig,
        show 16 * w - 1 - (16 * (w - k) + j) = 16 * (k - 1) + (15 - j) by omega_arith]
    refine ⟨hct, htt, by rw [e]; exact hyt, by rw [e]; exact hft, by rw [hvt, shl4_succ], ?_, ?_,
      hI.frm.trans (hfr.mono (winRanges_sub w)), (hI.keep.trans kt).mono (by decide)⟩
    · rw [hbt, show 16 - j - 1 = 16 - (j + 1) by omega_arith]
    · rw [hfr.word_eq (d := 8 * kWords) (by unfold winRanges; w_disj) (by decide)]
      exact hI.words
  · rw [h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

/-- The inner loop: the 16 windows of word `k − 1`. -/
theorem mrWins_ok (M : Mont) {B : Addr} {Z w c bm b k : Nat} {W : BitVec 64} {s₀ s : State}
    (hw128 : w ≤ 128) (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hodd : c % 2 = 1) (hc1 : 1 < c) (hk : 1 ≤ k)
    (hkw : k ≤ w) (hW : W.toNat = mrE c / 2 ^ (64 * (k - 1)) % 2 ^ 64) (h0 : WinInv B Z w c bm b k W s₀ 0 s) :
    WP isa (.loop (seqs (mrWin M.mm)) (.nonzero .x .x3)) s (WinInv B Z w c bm b k W s₀ 16) :=
  count_loop (cr := .x3) (n := 16) (by decide) (WinInv B Z w c bm b k W s₀)
    (fun _ hj _ hI => mrWinStep_ok M hw128 hEZ hodd hc1 hk hkw hW hj hI) h0

/-- After `j` of the `w` words. -/
structure WordInv (B : Addr) (Z w : Nat) (c bm b : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  ctx : MrCtx s B Z w c bm
  tab : TabOK s.mem B w c b
  y : wv s.mem B (slot w aY) w = (wRun c b (mrE c) (16 * w) (16 * j)).1 * 2 ^ (64 * w) % c
  flag : word s.mem B (8 * kFlag) = mask (wRun c b (mrE c) (16 * w) (16 * j)).2
  words : word s.mem B (8 * kWords) = BitVec.ofNat 64 (w - j)
  frm : Frm B (expRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

/-- The word `w − 1 − j` of `E`, as `WinInv` reads it. -/
abbrev wordE (m : Mem) (B : Addr) (w j : Nat) : BitVec 64 := word m B (slot w aE + 8 * (w - j - 1))

/-- The start of a word, after `ws` and `aE`'s base. -/
def wordHead : List Instr :=
  [ldh .x3 kWords, .subImm .x .x3 .x3 1, sth .x3 kWords, .lsl .x .x5 .x3 3, .add .x .x4 .x16 .x5, ld .x5 .x4,
    sth .x5 kV, movi .x6 16, sth .x6 kBits]

/-- The start of word `w − 1 − j`: `kWords := w − 1 − j`, the word into
`kV`, 16 into `kBits`. -/
theorem wordStart_ok {B : Addr} {Z w c bm b : Nat} {s₀ s : State} (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    {j : Nat} (hj : j < w) (hI : WordInv B Z w c bm b s₀ j s) :
    WP isa (.block (ws ++ base aE .x16 ++ wordHead)) s
      fun s₁ => WinInv B Z w c bm b (w - j) (wordE s.mem B w j) s₀ 0 s₁ := by
  have h := hI.ctx.ws
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hw2 := h.w2
  have hZ8 := hI.ctx.good.2
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aE .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have hl : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off B (8 * i)) 8 := fun i hi => hs₂.ld (by omega_arith)
  have hst : ∀ i < 32, InRegions s₂.wr (off B (8 * i)) 8 := fun i hi => hs₂.st (by omega_arith)
  have hWd : word s₂.mem B (8 * kWords) = BitVec.ofNat 64 (w - j) := by rw [m₂, m₁]; exact hI.words
  have hEw : ∀ X, word (s₂.mem.writeW (off B (8 * kWords)) X) B (slot w aE + 8 * (w - j - 1)) = wordE s.mem B w j :=
    fun X => by
      rw [(writeW_outside _ B _ (d := 8 * kWords) (by decide)).word
        (Or.inr (by have := hdr_lt_slot w aE (show kWords < 32 by decide); omega_arith)) (by omega_arith), m₂, m₁]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x6] (Q := fun t => t.mem = ((s₂.mem.writeW (off B (8 * kWords))
      (BitVec.ofNat 64 (w - j - 1))).writeW (off B (8 * kV)) (wordE s.mem B w j)).writeW (off B (8 * kBits))
      (BitVec.ofNat 64 16)) (by
    brun [wordHead, (k12.gpr .x0 (by decide)).trans h.x0, hdr_enc (show kWords < 32 by decide),
      hdr_enc (show kV < 32 by decide), hdr_enc (show kBits < 32 by decide), hl kWords (by decide),
      hst kWords (by decide), hst kV (by decide), hst kBits (by decide), hWd, h16,
      ofNat64_pred (show 1 ≤ w - j by omega_arith) (by omega_arith),
      ofNat_shl3 (show w - j - 1 < 2 ^ 60 by omega_arith), off_add,
      hs₂.ld (d := slot w aE + 8 * (w - j - 1)) (by omega_arith), hEw]
    rfl)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  have hf : Frm B (expRanges w) s.mem t.mem := by
    rw [hm, m₂, m₁]
    exact ((Frm.of_outside (writeW_outside _ B _ (d := 8 * kWords) (by decide))
      (expRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kV)
        (by decide)) (expRanges_hdr w (Or.inr (Or.inl rfl))))).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * kBits) (by decide))
        (expRanges_hdr w (Or.inr (Or.inr (Or.inl rfl)))))
  have hnw : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  refine ⟨hI.ctx.of_exp hf (fun _ h => h) (k12.trans k) (by decide),
    hI.tab.of_low hf (expRanges_low w) hEZ hn, ?_, ?_, ?_, ?_, ?_, hI.frm.trans hf,
    (hI.keep.trans (k12.trans k)).mono (by decide)⟩
  · rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) hnw, hdrStore_wv _ _ _ (by decide) (by decide) hnw,
      hdrStore_wv _ _ _ (by decide) (by decide) hnw, m₂, m₁, hI.y, show 16 * (w - (w - j)) + 0 = 16 * j by omega_arith]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), m₂, m₁, hI.flag,
      show 16 * (w - (w - j)) + 0 = 16 * j by omega_arith]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, Nat.mul_zero,
      BitVec.shiftLeft_zero]
  · rw [hm, word_writeW_self]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self]

/-- The end of word `w − 1 − j`: `x3 := kWords`. -/
theorem wordEnd_ok {B : Addr} {Z w c bm b : Nat} {W : BitVec 64} {s₀ s : State} {j : Nat} (hj : j < w)
    (hB : WinInv B Z w c bm b (w - j) W s₀ 16 s) :
    WP isa (.block [ldh .x3 kWords]) s fun t =>
      WordInv B Z w c bm b s₀ (j + 1) t ∧ ((t.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ w) := by
  have h := hB.ctx.ws
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hw2 := h.w2
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (w - j - 1) ∧ t.mem = s.mem) (by
    brun [h.x0, hdr_enc (show kWords < 32 by decide), h.scr.ld (d := 8 * kWords) (by simp only [kWords, kT1, sFn]; omega),
      hB.words]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ => ⟨?_, ?_⟩
  · have e : 16 * (w - (w - j)) + 16 = 16 * (j + 1) := by omega_arith
    refine ⟨hB.ctx.of_exp (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide),
      by rw [hm]; exact hB.tab, ?_, ?_, ?_, by rw [hm]; exact hB.frm, (hB.keep.trans k).mono (by decide)⟩
    · rw [hm, hB.y, e]
    · rw [hm, hB.flag, e]
    · rw [hm, hB.words, show w - j - 1 = w - (j + 1) by omega_arith]
  · rw [h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

/-- One word of the exponentiation. -/
theorem mrWord_ok (M : Mont) {B : Addr} {Z w c bm b : Nat} {s₀ s : State} (hw128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hE : ECtx s.mem B w c) (hodd : c % 2 = 1) (hc1 : 1 < c) {j : Nat}
    (hj : j < w) (hI : WordInv B Z w c bm b s₀ j s) :
    WP isa (seqs [.block (ws ++ base aE .x16 ++ wordHead), .loop (seqs (mrWin M.mm)) (.nonzero .x .x3),
      .block [ldh .x3 kWords]]) s fun t =>
      WordInv B Z w c bm b s₀ (j + 1) t ∧ ((t.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ w) := by
  have hW : (wordE s.mem B w j).toNat = mrE c / 2 ^ (64 * (w - j - 1)) % 2 ^ 64 := by
    rw [← hE.e]; exact word_of_wv s.mem B (slot w aE) w (by omega_arith)
  simp only [seqs]
  refine WP.seq (WP.mono (wordStart_ok hEZ hj hI) fun s₁ hB0 => ?_)
  exact WP.seq (WP.mono (mrWins_ok M hw128 hEZ hodd hc1 (by omega_arith) (by omega_arith)
    hW hB0) fun s₂ hB => wordEnd_ok hj hB)

end VG.Proof.RsaKeyGen.AArch64
