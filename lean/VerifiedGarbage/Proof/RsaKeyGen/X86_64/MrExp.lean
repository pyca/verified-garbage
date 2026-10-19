module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrLoop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-!
# A candidate on x86-64: Miller–Rabin's exponentiation

`mrExpLoop_ok`: from `y = 1` and the table, the windows of all the words of
`E` and the three squarings after them: the flag of `wEnd`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen

/-- The start of the exponentiation: `kWords := w`, the flag clear. -/
theorem expStart_ok {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat} {s : State}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hT : TabOK s.mem B w c b)
    (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % c) :
    WP isa (.block [.mov .rax (.mem (hdr sW)), .store (hdr kWords) .rax, .mov32 .rax (.imm 0), .store (hdr kFlag) .rax])
      s (WordInv B Z w mi c bm b s 0) := by
  have hg := hc.good
  have hZ := hd.z
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have hs : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi =>
    hg.scr.st (by have := hdr_lt_slot w 8 hi; omega_arith)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = (s.mem.writeW (off B (8 * kWords))
      (BitVec.ofNat 64 w)).writeW (off B (8 * kFlag)) (mask false)) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hs kWords (by decide), hs kFlag (by decide), hg.hdr.hw]
    rfl) rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have hf₁ : Frm B (expRanges w) s.mem s₁.mem := by
    rw [hm₁]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * kWords) (by unfold kWords kT1 sFn; omega_arith))
      (expRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kFlag)
        (by unfold kFlag kPlen sFn; omega_arith)) (expRanges_hdr w (Or.inr (Or.inr (Or.inr rfl)))))
  have hs₁ := hg.scr.congr k₁.2.2
  refine ⟨hc.of_exp hd hf₁ hs₁ ((k₁.gpr (by decide)).trans hg.rdi), hT.of_low hf₁ (expRanges_low w)
    (by have := hd.w128; omega_arith), ?_, ?_, ?_, hf₁, k₁.mono (by decide)⟩
  · rw [hm₁, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith), hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith),
      hY, Nat.mul_zero]
    simp only [wRun, Nat.one_mul]
  · rw [hm₁, word_writeW_self, Nat.mul_zero]; rfl
  · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, Nat.sub_zero]

/-- `mrLast j` as a squaring of `wEnd`. -/
theorem mrLast_wsq (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat} {st : Nat × Bool}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hE : ECtx s.mem B w c) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = st.1 * 2 ^ (64 * w) % c) (hP : word s.mem B (8 * kFlag) = mask st.2)
    {j : Nat} (hj : 1 ≤ j ∧ j ≤ 3) :
    WP isa (seqs (mrLast M.mm j)) s fun t =>
      MrCtx t B Z w mi c bm ∧ ECtx t.mem B w c ∧
      wv t.mem B (slot w aY) w = (wSq c (decide (j < mrSig c)) st).1 * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (wSq c (decide (j < mrSig c)) st).2 ∧
      Frm B (sqRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.good.scr.nowrap
  refine WP.mono (mrLast_ok M hd hc hE hodd hc1 hY hP hj) fun t ⟨hct, hyt, hft, hfr, kt⟩ =>
    ⟨hct, hE.of_low hfr (fun r hr => winRanges_low w r (by
      simp only [sqRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [winRanges, List.mem_cons, List.not_mem_nil, or_false]
      rcases hr with rfl | rfl | rfl | rfl <;> simp)) (by have := aE_fits hd; have := hd.z; omega_arith),
      hyt, by rw [hft, Bool.and_comm]; rfl, hfr, kt⟩

theorem mrExpLoop_eq (mul : Nat → Nat → Nat → Prog isa) : mrExpLoop mul =
    ([.block [.mov .rax (.mem (hdr sW)), .store (hdr kWords) .rax, .mov32 .rax (.imm 0), .store (hdr kFlag) .rax],
      .loop (seqs [
        .block (([.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1), .store (hdr kWords) .rax] : List Instr) ++
          extBase aE .rdx ++ ([.mov .rax (.mem (hdr kWords)), .mov .rcx (.mem (ix .rdx .rax)), .store (hdr kV) .rcx,
          .mov32 .rcx (.imm 16), .store (hdr kBits) .rcx] : List Instr)),
        .loop (seqs (mrWin mul)) .ne,
        .block [.mov .rax (.mem (hdr kWords)), .alu .test .rax (.reg .rax)]]) .ne] : List (Prog isa)) ++
    (mrLast mul 1 ++ (mrLast mul 2 ++ mrLast mul 3)) := by
  simp only [mrExpLoop, List.append_assoc]

/-- The exponentiation: from `y = 1` (`R mod c` in `aY`) and the table, the
flag of `wEnd` over the windows of `E`. -/
theorem mrExpLoop_ok (M : Mont) {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat} {s : State}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hT : TabOK s.mem B w c b) (hE : ECtx s.mem B w c)
    (hodd : c % 2 = 1) (hc1 : 1 < c) (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % c) :
    WP isa (seqs (mrExpLoop M.mm)) s fun t => MrCtx t B Z w mi c bm ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (wEnd c (wRun c b (mrE c) (16 * w) (16 * w))).2 ∧
      Frm B (expRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw4 := hd.w4
  have hn := hc.good.scr.nowrap
  have hEn : B.toNat + slot w aE + 8 * (w + 1) ≤ 2 ^ 64 := by have := aE_fits hd; have := hd.z; omega_arith
  rw [mrExpLoop_eq]
  refine wp_seqs_append (by simp) (by simp [mrLast]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (expStart_ok hd hc hT hY) fun s₁ hI0 => ?_)
  refine WP.mono (wp_upto (a := 0) (N := w) (by omega_arith) (WordInv B Z w mi c bm b s)
    (fun j _ hj t hI => mrWord_ok M hd (hE.of_low hI.frm (expRanges_low w) hEn) hodd hc1 hj hI)
    (fun t hI => hI) hI0) fun s₂ hI => ?_
  have hE₂ : ECtx s₂.mem B w c := hE.of_low hI.frm (expRanges_low w) hEn
  generalize hst : wRun c b (mrE c) (16 * w) (16 * w) = st
  have hY₂ : wv s₂.mem B (slot w aY) w = st.1 * 2 ^ (64 * w) % c := by rw [← hst]; exact hI.y
  have hP₂ : word s₂.mem B (8 * kFlag) = mask st.2 := by rw [← hst]; exact hI.flag
  refine wp_seqs_append (by simp [mrLast]) (by simp [mrLast]) (WP.mono (mrLast_wsq M hd hI.ctx hE₂ hodd hc1 hY₂ hP₂
    (j := 1) (by decide)) fun s₃ ⟨hc₃, hE₃, hY₃, hP₃, hf₃, k₃⟩ => ?_)
  refine wp_seqs_append (by simp [mrLast]) (by simp [mrLast]) (WP.mono (mrLast_wsq M hd hc₃ hE₃ hodd hc1 hY₃ hP₃
    (j := 2) (by decide)) fun s₄ ⟨hc₄, hE₄, hY₄, hP₄, hf₄, k₄⟩ => ?_)
  refine WP.mono (mrLast_wsq M hd hc₄ hE₄ hodd hc1 hY₄ hP₄ (j := 3) (by decide))
    fun t ⟨hct, hEt, _, hPt, hft, kt⟩ => ⟨hct, hEt, hPt, ?_, ?_⟩
  · exact ((hI.frm.trans (hf₃.mono (sqRanges_sub w))).trans (hf₄.mono (sqRanges_sub w))).trans
      (hft.mono (sqRanges_sub w))
  · exact (((hI.keep.trans k₃).trans k₄).trans kt).mono (by decide)

end VG.Proof.RsaKeyGen.X86_64
