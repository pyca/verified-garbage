module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrLoop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# A candidate on AArch64: Miller–Rabin's exponentiation

`mrExpLoop_ok`: from `y = 1` and the table of the witness `b`, the windows
of `E` from the top, then the three squarings of `wEnd`: the flag is
`wEnd`'s.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

theorem setWidth_zero_mask : BitVec.setWidth 64 (0#16) = mask false := rfl

/-- The start of the exponentiation: `kWords := w`, the flag clear. -/
theorem expStart_ok {B : Addr} {Z w c bm b : Nat} {s : State} (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hc : MrCtx s B Z w c bm) (hT : TabOK s.mem B w c b) (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % c) :
    WP isa (.block [ldh .x3 sW, sth .x3 kWords, movi .x3 0, sth .x3 kFlag]) s (WordInv B Z w c bm b s 0) := by
  have h := hc.ws
  have hZ8 := hc.good.2
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => h.scr.ld (by omega_arith)
  have hs : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi => h.scr.st (by omega_arith)
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = (s.mem.writeW (off B (8 * kWords))
      (BitVec.ofNat 64 w)).writeW (off B (8 * kFlag)) (mask false)) (by
    brun [h.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show kWords < 32 by decide),
      hdr_enc (show kFlag < 32 by decide), hl sW (by decide), hs kWords (by decide), hs kFlag (by decide), h.hw,
      setWidth_zero_mask]) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have hf₁ : Frm B (expRanges w) s.mem s₁.mem := by
    rw [hm₁]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * kWords) (by decide))
      (expRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kFlag)
        (by decide)) (expRanges_hdr w (Or.inr (Or.inr (Or.inr rfl)))))
  have hnw : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  refine ⟨hc.of_exp hf₁ (fun _ h => h) k₁ (by decide), hT.of_low hf₁ (expRanges_low w) hEZ hn, ?_, ?_, ?_, hf₁,
    k₁.mono (by decide)⟩
  · rw [hm₁, hdrStore_wv _ _ _ (by decide) (by decide) hnw, hdrStore_wv _ _ _ (by decide) (by decide) hnw,
      hY, Nat.mul_zero]
    simp only [wRun, Nat.one_mul]
  · rw [hm₁, word_writeW_self, Nat.mul_zero]; rfl
  · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, Nat.sub_zero]

/-- `mrLast j` as a squaring of `wEnd`. -/
theorem mrLast_wsq (M : Mont) {s : State} {B : Addr} {Z w c bm : Nat} {st : Nat × Bool} (hw128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hc : MrCtx s B Z w c bm) (hE : ECtx s.mem B w c) (hodd : c % 2 = 1)
    (hc1 : 1 < c) (hY : wv s.mem B (slot w aY) w = st.1 * 2 ^ (64 * w) % c)
    (hP : word s.mem B (8 * kFlag) = mask st.2) {j : Nat} (hj : 1 ≤ j ∧ j ≤ 3) :
    WP isa (seqs (mrLast M.mm j)) s fun t =>
      MrCtx t B Z w c bm ∧ ECtx t.mem B w c ∧
      wv t.mem B (slot w aY) w = (wSq c (decide (j < mrSig c)) st).1 * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (wSq c (decide (j < mrSig c)) st).2 ∧
      Frm B (sqRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.ws.scr.nowrap
  refine WP.mono (mrLast_ok M hw128 hEZ hc hE hodd hc1 hY hP hj) fun t ⟨hct, hyt, hft, hfr, kt⟩ =>
    ⟨hct, hE.of_low hfr (fun r hr => winRanges_low w r (sqRanges_win w r hr)) hEZ hn,
      hyt, by rw [hft, Bool.and_comm]; rfl, hfr, kt⟩

theorem mrExpLoop_eq (mul : Nat → Nat → Nat → Prog isa) : mrExpLoop mul =
    ([.block [ldh .x3 sW, sth .x3 kWords, movi .x3 0, sth .x3 kFlag],
      .loop (seqs [.block (ws ++ base aE .x16 ++ wordHead), .loop (seqs (mrWin mul)) (.nonzero .x .x3),
        .block [ldh .x3 kWords]]) (.nonzero .x .x3)] : List (Prog isa)) ++
    (mrLast mul 1 ++ (mrLast mul 2 ++ mrLast mul 3)) := by
  simp only [mrExpLoop, wordHead, List.append_assoc]

/-- The exponentiation: from `y = 1` (`R mod c` in `aY`) and the table, the
flag of `wEnd` over the windows of `E`. -/
theorem mrExpLoop_ok (M : Mont) {B : Addr} {Z w c bm b : Nat} {s : State} (hw128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hc : MrCtx s B Z w c bm) (hT : TabOK s.mem B w c b)
    (hE : ECtx s.mem B w c) (hodd : c % 2 = 1) (hc1 : 1 < c) (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % c) :
    WP isa (seqs (mrExpLoop M.mm)) s fun t => MrCtx t B Z w c bm ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (wEnd c (wRun c b (mrE c) (16 * w) (16 * w))).2 ∧
      Frm B (expRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.ws.scr.nowrap
  have hw2 := hc.ws.w1
  rw [mrExpLoop_eq]
  refine wp_seqs_append (by simp) (by simp [mrLast]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (expStart_ok hEZ hc hT hY) fun s₁ hI0 => ?_)
  refine WP.mono (count_loop (cr := .x3) (n := w) (by omega_arith) (WordInv B Z w c bm b s)
    (fun j hj t hI => mrWord_ok M hw128 hEZ (hE.of_low hI.frm (expRanges_low w) hEZ hn) hodd hc1 hj hI) hI0)
    fun s₂ hI => ?_
  have hE₂ : ECtx s₂.mem B w c := hE.of_low hI.frm (expRanges_low w) hEZ hn
  generalize hst : wRun c b (mrE c) (16 * w) (16 * w) = st
  have hY₂ : wv s₂.mem B (slot w aY) w = st.1 * 2 ^ (64 * w) % c := by rw [← hst]; exact hI.y
  have hP₂ : word s₂.mem B (8 * kFlag) = mask st.2 := by rw [← hst]; exact hI.flag
  refine wp_seqs_append (by simp [mrLast]) (by simp [mrLast]) (WP.mono (mrLast_wsq M hw128 hEZ hI.ctx hE₂ hodd hc1
    hY₂ hP₂ (j := 1) (by decide)) fun s₃ ⟨hc₃, hE₃, hY₃, hP₃, hf₃, k₃⟩ => ?_)
  refine wp_seqs_append (by simp [mrLast]) (by simp [mrLast]) (WP.mono (mrLast_wsq M hw128 hEZ hc₃ hE₃ hodd hc1
    hY₃ hP₃ (j := 2) (by decide)) fun s₄ ⟨hc₄, hE₄, hY₄, hP₄, hf₄, k₄⟩ => ?_)
  refine WP.mono (mrLast_wsq M hw128 hEZ hc₄ hE₄ hodd hc1 hY₄ hP₄ (j := 3) (by decide))
    fun t ⟨hct, hEt, _, hPt, hft, kt⟩ => ⟨hct, hEt, hPt, ?_, ?_⟩
  · exact ((hI.frm.trans (hf₃.mono (sqRanges_sub w))).trans (hf₄.mono (sqRanges_sub w))).trans
      (hft.mono (sqRanges_sub w))
  · exact (((hI.keep.trans k₃).trans k₄).trans kt).mono (by decide)

end VG.Proof.RsaKeyGen.AArch64
