module
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Base
public import VerifiedGarbage.Proof.RsaKeyGen.Table

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdStep
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Phase
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# An FFDH parameter candidate on AArch64: `q = (p − 1) / 2`

`halveQ` (`halveQ_ok`): `aN := aN / 2` in place (`halfPass_ok`), and the
evenness of the result or'ed into `fBad`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The flag of an even `q`. -/
def evenFlag (q : Nat) : BitVec 64 := BitVec.ofNat 64 (1 - q % 2)

theorem evenFlag_zero (q : Nat) : evenFlag q = 0 ↔ q % 2 = 1 := by
  unfold evenFlag
  rcases Nat.mod_two_eq_zero_or_one q with h | h <;> rw [h] <;> decide

theorem low_bit_flag (x : BitVec 64) :
    (x &&& BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 1 = BitVec.ofNat 64 (1 - x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, show BitVec.ofNat 64 1 = (1 : BitVec 64) from rfl, and1_toNat,
    show (1 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_ofNat]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- The halving's start: `x16 = x17 = aN`'s base, `x15` all ones. -/
theorem halveHead_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block (ws ++ base aN .x16 ++ [mov .x17 .x16, movi .x7 0, .subImm .x .x15 .x7 1])) s fun t =>
      (t.gpr .x16 = off B (slot w aN) ∧ t.gpr .x17 = off B (slot w aN) ∧ t.gpr .x15 = mask true ∧
        t.gpr .x12 = BitVec.ofNat 64 w ∧ t.mem = s.mem) ∧ Keep mmRegs s t := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aN .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  refine WP.mono (WP.keep [.x17, .x7, .x15] (Q := fun t => t.gpr .x16 = off B (slot w aN) ∧
      t.gpr .x17 = off B (slot w aN) ∧ t.gpr .x15 = mask true ∧ t.mem = s₂.mem) (by
    brun [h16, imm16 (show 0 < 65536 by decide)]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨a, b, c, d⟩, k₃⟩ => ?_
  exact ⟨⟨a, b, c, (k₃.gpr .x12 (by decide)).trans ((k₂.gpr .x12 (by decide)).trans h12), by rw [d, m₂, m₁]⟩,
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `halveQ`: `q := c / 2` in `aN`, and its evenness or'ed into `fBad`. -/
theorem halveQ_ok {s : State} {p : PP} {w c : Nat} {v : BitVec 64} (h : PSt p w s)
    (hc : wv s.mem p.B (slot w aN) w = c) (hv : word s.mem p.B (8 * fBad) = v) :
    WP isa (seqs halveQ) s fun t =>
      PSt p w t ∧ wv t.mem p.B (slot w aN) w = c / 2 ∧ word t.mem p.B (8 * fBad) = v ||| evenFlag (c / 2) ∧
        Frm p.B [(slot w aN, 8 * (w + 2)), (8 * fBad, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have hw1 := hws.w1
  have hw2 := hws.w2
  have h256 := hws.h256
  have sN := hws.sl (show aN < 16 by decide)
  unfold halveQ
  rw [List.cons_append]
  refine wp_seqs_append (a := _ :: halfPass) (by simp) (by simp) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (halveHead_ok hws) fun s₁ ⟨⟨h16, h17, h15, h12, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (halfPass_ok (mb := true) (hs.congr k₁.wr) h16 h17 h15 h12 hw1 (by omega) (by omega) (by omega)
    (.inl rfl)) fun s₂ ⟨hv₂, o₂, k₂⟩ => ?_
  simp only [ite_true] at hv₂
  rw [hm₁, hc] at hv₂
  rw [hm₁] at o₂
  have f₂a : Frm p.B [(slot w aN, 8 * (w + 2))] s.mem s₂.mem :=
    Frm.of_outside (o₂.mono (o' := slot w aN) (n' := 8 * (w + 2)) (by omega) (by omega)) (by simp)
  have f₂ : Frm p.B [(slot w aN, 8 * (w + 2)), (8 * fBad, 8)] s.mem s₂.mem := f₂a.mono (by simp)
  have k12 := k₁.trans k₂
  have hmut : ∀ r ∈ [(slot w aN, 8 * (w + 2)), (8 * fBad, 8)], KMut r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [KMut.ofSlot _ _ _, KMut.hdr (by decide)]
  have pmut : ∀ r ∈ [(slot w aN, 8 * (w + 2)), (8 * fBad, 8)], PMut r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [PMut.ofSlot _ _ _, PMut.hdr (by decide)]
  have zz : ∀ r ∈ [(slot w aN, 8 * (w + 2)), (8 * fBad, 8)], r.1 + r.2 ≤ p.Z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [fBad] <;> omega
  have hws₂ : Ws s₂ p.B p.Z w := hws.congr' f₂ hmut k12 (by decide)
  have hb₂ : word s₂.mem p.B (8 * fBad) = v := by
    rw [f₂a.word_eq (d := 8 * fBad) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (hdr_lt_slot w aN (by decide))) (by simp only [fBad]; omega)]
    exact hv
  have hlow : (word s₂.mem p.B (slot w aN)).toNat % 2 = c / 2 % 2 := by
    rw [← hv₂, ← wv_mod64 s₂.mem p.B (slot w aN) (n := w) (by omega), Nat.mod_mod_of_dvd _ (by decide)]
  -- The flag.
  have hblk : WP isa (.block (ws ++ base aN .x16 ++ [ldh .x5 fBad, ld .x3 .x16, movi .x4 1,
      .logic .and .x .x3 .x3 .x4, .logic .eor .x .x3 .x3 .x4, .logic .orr .x .x5 .x5 .x3, sth .x5 fBad])) s₂
      (fun t => t.mem = s₂.mem.writeW (off p.B (8 * fBad)) (v ||| evenFlag (c / 2)) ∧ Keep mmRegs s₂ t) := by
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono hws₂.ws_ok fun s₃ ⟨⟨_, h11, m₃, _⟩, k₃⟩ => ?_
    refine WP.mono (base_ok aN .x16 ((k₃.gpr .x0 (by decide)).trans hws₂.x0) h11) fun s₄ ⟨⟨h16₄, m₄, _⟩, k₄⟩ => ?_
    have hs₄ := hs.congr ((k12.trans k₃).trans k₄).wr
    have h0₄ : s₄.gpr .x0 = p.B := ((k₃.trans k₄).gpr .x0 (by decide)).trans hws₂.x0
    have hfl : (word s₂.mem p.B (slot w aN) &&& BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 1 = evenFlag (c / 2) := by
      rw [low_bit_flag, hlow]; rfl
    refine WP.mono (WP.keep [.x5, .x3, .x4] (Q := fun t =>
        t.mem = s₂.mem.writeW (off p.B (8 * fBad)) (v ||| evenFlag (c / 2))) (by
      brun [h16₄, h0₄, m₄, m₃, hb₂, imm16 (show 1 < 65536 by decide), hdr_enc (show fBad < 32 by decide),
        hs₄.ld (d := 8 * fBad) (by simp only [fBad]; omega), hs₄.st (d := 8 * fBad) (by simp only [fBad]; omega),
        hs₄.ld (d := slot w aN) (by omega), hfl])
      (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₅⟩ => ⟨hm, ((k₃.trans k₄).trans k₅).mono (by decide)⟩
  refine WP.mono hblk fun t ⟨hm, k₃⟩ => ?_
  have f₃' : Frm p.B [(8 * fBad, 8)] s₂.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by simp only [fBad]; omega)) (by simp)
  have f₃ : Frm p.B [(slot w aN, 8 * (w + 2)), (8 * fBad, 8)] s₂.mem t.mem := f₃'.mono (by simp)
  have hf := f₂.trans f₃
  have k13 := k12.trans k₃
  refine ⟨h.step (hws.congr' hf hmut k13 (by decide)) hf pmut zz k13, ?_, by rw [hm, word_writeW_self], hf,
    k13.mono (by decide)⟩
  rw [f₃'.wv_eq (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Or.inr (hdr_lt_slot w aN (by decide))) (by omega)]
  exact hv₂

end VG.Proof.Ffdh.AArch64.ParameterCandidate
