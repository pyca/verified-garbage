module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWin
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-!
# A candidate on x86-64: Miller–Rabin's exponentiation loops

`WinInv`: after `t` windows of word `k − 1` of `E` (the words from the top),
`y R mod c` and the flag after the `16 (w − k) + t` windows from the top
(`wRun`), the word shifted left by `4 t` in `kV`. `mrWins_ok`: the inner
loop over the word's 16 windows; `mrWord_ok`: one word.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen

/-- What the exponentiation changes. -/
def expRanges (w : Nat) : List (Nat × Nat) := winRanges w ++ [(8 * kWords, 8)]

/-- `expRanges`'s ranges, in the header and in the arrays. -/
theorem expRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(248, 8), (176, 8), (208, 8), (224, 8), (216, 8)]
    [(2, 1), (3, 1), (6, 1), (5, 1)] (expRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append,
    expRanges, winRanges, Public.aAcc, Public.aTmp, Public.aXm, Public.aY, aAcc, aTmp, aXm, aY, kT0, sFn, kG, kV, kWords, kBits, kFlag, kPlen, kT1, kT2] at hr
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

theorem expRanges_low (w : Nat) : ∀ r ∈ expRanges w, r.1 + r.2 ≤ slot w 8 := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact winRanges_low w r hr
  · simp only [List.mem_singleton] at hr; subst hr
    exact hdr_lt_slot w 8 (show kWords < 32 by decide)

theorem sqRanges_sub (w : Nat) : ∀ r ∈ sqRanges w, r ∈ expRanges w := by
  simp only [sqRanges, expRanges, winRanges, List.mem_cons, List.not_mem_nil, or_false, List.mem_append]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp

theorem winRanges_sub (w : Nat) : ∀ r ∈ winRanges w, r ∈ expRanges w := fun _ hr => List.mem_append_left _ hr

/-- After `t` windows of word `k − 1`, `W`, of `E`. -/
structure WinInv (B : Addr) (Z w : Nat) (mi : BitVec 64) (c bm b k : Nat) (W : BitVec 64) (s₀ : State) (t : Nat)
    (s : State) : Prop where
  ctx : MrCtx s B Z w mi c bm
  tab : TabOK s.mem B w c b
  y : wv s.mem B (slot w aY) w = (wRun c b (mrE c) (16 * w) (16 * (w - k) + t)).1 * 2 ^ (64 * w) % c
  flag : word s.mem B (8 * kFlag) = mask (wRun c b (mrE c) (16 * w) (16 * (w - k) + t)).2
  v : word s.mem B (8 * kV) = W <<< (4 * t)
  bits : word s.mem B (8 * kBits) = BitVec.ofNat 64 (16 - t)
  words : word s.mem B (8 * kWords) = BitVec.ofNat 64 (k - 1)
  frm : Frm B (expRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

/-- One window of word `k − 1`. -/
theorem mrWinStep_ok (M : Mont) {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b k : Nat} {W : BitVec 64}
    {s₀ s : State} (hd : MrDims B Z w) (hodd : c % 2 = 1) (hc1 : 1 < c) (hk : 1 ≤ k) (hkw : k ≤ w)
    (hW : W.toNat = mrE c / 2 ^ (64 * (k - 1)) % 2 ^ 64) {j : Nat} (hj : j < 16)
    (hI : WinInv B Z w mi c bm b k W s₀ j s) :
    WP isa (seqs (mrWin M.mm)) s fun t =>
      t.zf = some (decide (j + 1 = 16)) ∧ WinInv B Z w mi c bm b k W s₀ (j + 1) t := by
  have hdig := win_digit hW hj
  refine WP.mono (mrWin_ok M hd hI.ctx hI.tab hodd hc1 hI.y hI.flag hI.v hI.bits (by omega_arith) (by omega_arith))
    fun t ⟨hct, htt, hyt, hft, hvt, hbt, hz, hfr, kt⟩ =>
      ⟨by rw [hz, decide_eq_decide.mpr (show 16 - j - 1 = 0 ↔ j + 1 = 16 by omega_arith)], ?_⟩
  have e : wRun c b (mrE c) (16 * w) (16 * (w - k) + (j + 1)) =
      wWin c b ((W <<< (4 * j)) >>> 60).toNat
        ((wRun c b (mrE c) (16 * w) (16 * (w - k) + j)).1, (wRun c b (mrE c) (16 * w) (16 * (w - k) + j)).2) := by
    rw [show 16 * (w - k) + (j + 1) = (16 * (w - k) + j) + 1 by omega_arith, wRun, hdig,
      show 16 * w - 1 - (16 * (w - k) + j) = 16 * (k - 1) + (15 - j) by omega_arith]
  refine ⟨hct, htt, by rw [e]; exact hyt, by rw [e]; exact hft, by rw [hvt, shl4_succ], ?_, ?_,
    hI.frm.trans (hfr.mono (winRanges_sub w)), (hI.keep.trans kt).mono (by decide)⟩
  · rw [hbt, show 16 - j - 1 = 16 - (j + 1) by omega_arith]
  · rw [hfr.word_eq (d := 8 * kWords) (by simp only [winRanges]; rng_disj) (by unfold kWords kT1 sFn; omega_arith)]
    exact hI.words

/-- The inner loop: the 16 windows of word `k − 1`. -/
theorem mrWins_ok (M : Mont) {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b k : Nat} {W : BitVec 64}
    {s₀ s : State} (hd : MrDims B Z w) (hodd : c % 2 = 1) (hc1 : 1 < c) (hk : 1 ≤ k) (hkw : k ≤ w)
    (hW : W.toNat = mrE c / 2 ^ (64 * (k - 1)) % 2 ^ 64) (h0 : WinInv B Z w mi c bm b k W s₀ 0 s) :
    WP isa (.loop (seqs (mrWin M.mm)) .ne) s (WinInv B Z w mi c bm b k W s₀ 16) :=
  wp_upto (a := 0) (N := 16) (by decide) (WinInv B Z w mi c bm b k W s₀)
    (fun j _ hj s hI => mrWinStep_ok M hd hodd hc1 hk hkw hW hj hI) (fun _ h => h) h0

/-- After `j` of the `w` words. -/
structure WordInv (B : Addr) (Z w : Nat) (mi : BitVec 64) (c bm b : Nat) (s₀ : State) (j : Nat) (s : State) :
    Prop where
  ctx : MrCtx s B Z w mi c bm
  tab : TabOK s.mem B w c b
  y : wv s.mem B (slot w aY) w = (wRun c b (mrE c) (16 * w) (16 * j)).1 * 2 ^ (64 * w) % c
  flag : word s.mem B (8 * kFlag) = mask (wRun c b (mrE c) (16 * w) (16 * j)).2
  words : word s.mem B (8 * kWords) = BitVec.ofNat 64 (w - j)
  frm : Frm B (expRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

theorem expRanges_hdr (w : Nat) {i : Nat} (hi : i = kWords ∨ i = kV ∨ i = kBits ∨ i = kFlag) :
    (8 * i, 8) ∈ expRanges w := by
  rcases hi with rfl | rfl | rfl | rfl <;> simp [expRanges, winRanges]

/-- `MrCtx` survives changes within the exponentiation's ranges. -/
theorem MrCtx.of_exp {s t : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat}
    (hc : MrCtx s B Z w mi c bm) (hd : MrDims B Z w) (hf : Frm B (expRanges w) s.mem t.mem) (hs : Scr t B Z)
    (hdi : t.gpr .rdi = B) : MrCtx t B Z w mi c bm :=
  hc.of_frm hd hf hs hdi (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; rng_disj)
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; rng_disj)
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; rng_disj)
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; rng_disj)
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; rng_disj)

/-- The word `w − 1 − j` of `E`, as `WinInv` reads it. -/
abbrev wordE (m : Mem) (B : Addr) (w j : Nat) : BitVec 64 := word m B (slot w aE + 8 * (w - j - 1))

/-- The start of word `w − 1 − j`: `kWords := w − 1 − j`, the word into
`kV`, 16 into `kBits`. -/
theorem wordStart_ok {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat} {s₀ s : State}
    (hd : MrDims B Z w) {j : Nat} (hj : j < w) (hI : WordInv B Z w mi c bm b s₀ j s) :
    WP isa (.block (([.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1), .store (hdr kWords) .rax] :
        List Instr) ++ extBase aE .rdx ++ ([.mov .rax (.mem (hdr kWords)), .mov .rcx (.mem (ix .rdx .rax)),
        .store (hdr kV) .rcx, .mov32 .rcx (.imm 16), .store (hdr kBits) .rcx] : List Instr))) s
      fun s₁ => WinInv B Z w mi c bm b (w - j) (wordE s.mem B w j) s₀ 0 s₁ := by
  have hg := hI.ctx.good
  have hZ := hd.z
  have hXZ := hd.x
  have hw4 := hd.w4
  have hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hn := hg.scr.nowrap
  have hl : ∀ (t : State), Scr t B Z → ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun t hs i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have hst : ∀ (t : State), Scr t B Z → ∀ i < 32, InRegions t.wr (off B (8 * i)) 8 := fun t hs i hi =>
    hs.st (by have := hdr_lt_slot w 8 hi; omega_arith)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B (8 * kWords))
      (BitVec.ofNat 64 (w - j - 1))) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl s hg.scr kWords (by decide), hst s hg.scr kWords (by decide), hI.words,
      ofNat64_pred (show 1 ≤ w - j by omega_arith) (by omega_arith)]) rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi,
    by rw [hm₁]; exact hg.hdr.store (by decide) (by decide) _⟩
  refine WP.mono (extBase_ok hg₁ hZ hw' (j := aE) (by decide) (r := .rdx) (by decide) rfl rfl)
    fun s₂ ⟨hdx, hm₂, k₂⟩ => ?_
  have hg₂ : Good s₂ B Z w mi := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, by rw [hm₂]; exact hg₁.hdr⟩
  have hWd : word s₂.mem B (8 * kWords) = BitVec.ofNat 64 (w - j - 1) := by rw [hm₂, hm₁, word_writeW_self]
  have hEw : word s₂.mem B (slot w aE + 8 * (w - j - 1)) = wordE s.mem B w j := by
    rw [hm₂, hm₁, (writeW_outside _ B _ (d := 8 * kWords) (by unfold kWords kT1 sFn; omega_arith)).word
      (Or.inr (by have := hdr_lt_slot w aE (show kWords < 32 by decide); omega_arith)) (by
        have := slot_lt24 w (show aE ≤ 24 by decide); omega_arith)]
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem = (s₂.mem.writeW (off B (8 * kV))
      (wordE s.mem B w j)).writeW (off B (8 * kBits)) (BitVec.ofNat 64 16)) (by
    xrun [State.ea, hdr, ix, hg₂.rdi, hdrOff, hl s₂ hg₂.scr kWords (by decide), hst s₂ hg₂.scr kV (by decide),
      hst s₂ hg₂.scr kBits (by decide), hWd, hdx, addr0 rfl rfl,
      hg₂.scr.ld (d := slot w aE + 8 * (w - j - 1)) (by have := aE_fits hd; omega_arith), hEw]
    rfl) rfl) fun t ⟨hm, k⟩ => ?_
  have hf : Frm B (expRanges w) s.mem t.mem := by
    rw [hm, hm₂, hm₁]
    exact ((Frm.of_outside (writeW_outside _ B _ (d := 8 * kWords) (by unfold kWords kT1 sFn; omega_arith))
      (expRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kV)
        (by unfold kV kT0 sFn; omega_arith)) (expRanges_hdr w (Or.inr (Or.inl rfl))))).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * kBits) (by unfold kBits kT2 sFn; omega_arith))
        (expRanges_hdr w (Or.inr (Or.inr (Or.inl rfl)))))
  have hst' := hg₂.scr.congr k.2.2
  have hdi : t.gpr .rdi = B := (k.gpr (by decide)).trans hg₂.rdi
  refine ⟨hI.ctx.of_exp hd hf hst' hdi, hI.tab.of_low hf (expRanges_low w) hw', ?_, ?_, ?_, ?_, ?_,
    hI.frm.trans hf, ((hI.keep.trans k₁).trans (k₂.trans k)).mono (by decide)⟩
  · rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith), hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith),
      hm₂, hm₁, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith), hI.y,
      show 16 * (w - (w - j)) + 0 = 16 * j by omega_arith]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hm₂, hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hI.flag,
      show 16 * (w - (w - j)) + 0 = 16 * j by omega_arith]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, Nat.mul_zero,
      BitVec.shiftLeft_zero]
  · rw [hm, word_writeW_self]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hWd]

/-- The end of word `w − 1 − j`: ZF set after the last. -/
theorem wordEnd_ok {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat} {W : BitVec 64} {s₀ s : State}
    (hd : MrDims B Z w) {j : Nat} (hj : j < w) (hB : WinInv B Z w mi c bm b (w - j) W s₀ 16 s) :
    WP isa (.block [.mov .rax (.mem (hdr kWords)), .alu .test .rax (.reg .rax)]) s fun t =>
      t.zf = some (decide (j + 1 = w)) ∧ WordInv B Z w mi c bm b s₀ (j + 1) t := by
  have hg₂ := hB.ctx.good
  have hn := hg₂.scr.nowrap
  have hZ := hd.z
  have h64 := hd.w128
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kWords)) 8 :=
    hg₂.scr.ld (by have := hdr_lt_slot w 8 (show kWords < 32 by decide); omega_arith)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (j + 1 = w)) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg₂.rdi, hdrOff, hl, hB.words, BitVec.and_self,
      ofNat64_beq_zero (show w - j - 1 < 2 ^ 64 by omega_arith)]
    exact decide_eq_decide.mpr (by omega)) rfl) fun t ⟨⟨hz, hm⟩, k⟩ => ⟨hz, ?_⟩
  have e : 16 * (w - (w - j)) + 16 = 16 * (j + 1) := by omega_arith
  have hft : Frm B [] s.mem t.mem := by rw [hm]; exact Frm.refl _ _ _
  refine ⟨hB.ctx.of_frm hd hft (hg₂.scr.congr k.2.2) ((k.gpr (by decide)).trans hg₂.rdi) (by simp) (by simp) (by simp)
      (by simp) (by simp), by rw [hm]; exact hB.tab, ?_, ?_, ?_, by rw [hm]; exact hB.frm, (hB.keep.trans k).mono (by decide)⟩
  · rw [hm, hB.y, e]
  · rw [hm, hB.flag, e]
  · rw [hm, hB.words, show w - j - 1 = w - (j + 1) by omega_arith]

/-- One word of the exponentiation. -/
theorem mrWord_ok (M : Mont) {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat} {s₀ s : State}
    (hd : MrDims B Z w) (hE : ECtx s.mem B w c) (hodd : c % 2 = 1) (hc1 : 1 < c) {j : Nat} (hj : j < w)
    (hI : WordInv B Z w mi c bm b s₀ j s) :
    WP isa (seqs [
      .block (([.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1), .store (hdr kWords) .rax] : List Instr) ++
        extBase aE .rdx ++ ([.mov .rax (.mem (hdr kWords)), .mov .rcx (.mem (ix .rdx .rax)), .store (hdr kV) .rcx,
        .mov32 .rcx (.imm 16), .store (hdr kBits) .rcx] : List Instr)),
      .loop (seqs (mrWin M.mm)) .ne,
      .block [.mov .rax (.mem (hdr kWords)), .alu .test .rax (.reg .rax)]]) s fun t =>
      t.zf = some (decide (j + 1 = w)) ∧ WordInv B Z w mi c bm b s₀ (j + 1) t := by
  have hW : (wordE s.mem B w j).toNat = mrE c / 2 ^ (64 * (w - j - 1)) % 2 ^ 64 := by
    rw [← hE.e]; exact word_of_wv s.mem B (slot w aE) w (by omega_arith)
  simp only [seqs]
  refine WP.seq (WP.mono (wordStart_ok hd hj hI) fun s₁ hB0 => ?_)
  exact WP.seq (WP.mono (mrWins_ok M hd hodd hc1 (by omega_arith) (by omega_arith)
    hW hB0) fun s₂ hB => wordEnd_ok hd hj hB)

end VG.Proof.RsaKeyGen.X86_64
