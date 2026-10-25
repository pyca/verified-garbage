module
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Base

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.ModE
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Phase
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# An FFDH parameter candidate on AArch64: the generator's congruence

`residue` (`residue_ok`): `r = c mod e` by RSA's bit-serial reduction of
`aN`'s words from the top (`modWords_ok`), `e` 24 for the generator 2 and 10
for 5, and `fBad := resFlag g r`, zero exactly for `r = 11` (generator 2)
or `r ∈ {3, 7}` (generator 5).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The modulus of the congruence: 10 for the generator 5, 24 for 2. -/
def resMod (g : Nat) : Nat := if 3 ≤ g then 10 else 24

/-- The congruence's flag for the remainder `r`. -/
def resFlag (g : Nat) (r : BitVec 64) : BitVec 64 :=
  if 3 ≤ g then (r ||| BitVec.ofNat 64 4) ^^^ BitVec.ofNat 64 7 else r ^^^ BitVec.ofNat 64 11

theorem resFlag_two {r : Nat} (hr : r < 24) : resFlag 2 (BitVec.ofNat 64 r) = 0 ↔ r = 11 := by
  unfold resFlag
  simp only [show ¬ 3 ≤ 2 by decide, ite_false]
  revert r; decide

theorem resFlag_five {r : Nat} (hr : r < 10) : resFlag 5 (BitVec.ofNat 64 r) = 0 ↔ r = 3 ∨ r = 7 := by
  unfold resFlag
  simp only [show 3 ≤ 5 by decide, ite_true]
  revert r; decide

/-- The congruence's flag is zero exactly for the generator's congruence. -/
theorem resFlag_zero {g c : Nat} (hg : g = 2 ∨ g = 5) :
    resFlag g (BitVec.ofNat 64 (c % resMod g)) = 0 ↔
      (if g = 2 then c % 24 = 11 else g = 5 ∧ (c % 10 = 3 ∨ c % 10 = 7)) := by
  rcases hg with rfl | rfl
  · rw [resFlag_two (by unfold resMod; simp only [show ¬ 3 ≤ 2 by decide, ite_false]; omega_arith)]
    simp [resMod]
  · rw [resFlag_five (by unfold resMod; simp only [show 3 ≤ 5 by decide, ite_true]; omega_arith)]
    simp [resMod]

theorem w8_addr (B : Addr) {d w : Nat} (hw : w < 2 ^ 31) :
    off B d + BitVec.ofNat 64 w <<< 3 = off B (d + 8 * w) := by
  rw [shl_ofNat (show w * 2 ^ 3 < 2 ^ 64 by omega_arith), off_add, show w * 2 ^ 3 = 8 * w by omega_arith]

/-- The reduction's start. -/
theorem residueHead_ok {s : State} {p : PP} {w : Nat} (h : PSt p w s) :
    WP isa (.block (ws ++ base aN .x16 ++ ([.lsl .x .x5 .x12 3, .add .x .x10 .x16 .x5, mov .x14 .x12, ldh .x9 fGen,
      movi .x6 3, .subs .x .x8 .x9 .x6, movi .x13 10, movi .x6 24, .csel .x .x13 .x13 .x6, movi .x3 0, movi .x7 0,
      .subImm .x .x8 .x7 1] : List Instr))) s fun t =>
      (t.gpr .x10 = off p.B (slot w aN + 8 * w) ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧
        t.gpr .x13 = BitVec.ofNat 64 (resMod p.g) ∧ t.gpr .x3 = 0 ∧ t.gpr .x7 = 0 ∧ t.gpr .x8 = mask true ∧
        t.mem = s.mem) ∧ Keep mmRegs s t := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have hw2 := hws.w2
  have hg := h.dims.g
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono hws.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aN .x16 ((k₁.gpr .x0 (by decide)).trans hws.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have h0₂ : s₂.gpr .x0 = p.B := (k12.gpr .x0 (by decide)).trans hws.x0
  have e12 : s₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12
  have hm₂ : s₂.mem = s.mem := m₂.trans m₁
  have hG : s₂.mem.readW (off p.B (8 * fGen)) 64 = BitVec.ofNat 64 p.g := by rw [hm₂]; exact h.args.gen
  have hsel : (if decide (2 ^ 64 ≤ (BitVec.ofNat 64 p.g).toNat + (~~~BitVec.ofNat 64 3).toNat + true.toNat) = true
      then BitVec.ofNat 64 10 else BitVec.ofNat 64 24) = BitVec.ofNat 64 (resMod p.g) := by
    rw [subs_ge (by omega_arith) (by decide)]
    unfold resMod
    by_cases hc : 3 ≤ p.g
    · simp [hc]
    · simp [hc]
  refine WP.mono (WP.keep [.x5, .x10, .x14, .x9, .x6, .x8, .x13, .x3, .x7] (Q := fun t =>
      t.gpr .x10 = off p.B (slot w aN + 8 * w) ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧
        t.gpr .x13 = BitVec.ofNat 64 (resMod p.g) ∧ t.gpr .x3 = 0 ∧ t.gpr .x7 = 0 ∧ t.gpr .x8 = mask true ∧
        t.mem = s.mem) (by
    brun [h16, e12, h0₂, hm₂, w8_addr p.B (d := slot w aN) (w := w) (by omega_arith), hdr_enc (show fGen < 32 by decide),
      hs₂.ld (d := 8 * fGen) (by have := hws.h256; simp only [fGen, sFn]; omega_arith), hG,
      imm16 (show 3 < 65536 by decide), imm16 (show 10 < 65536 by decide), imm16 (show 24 < 65536 by decide),
      imm16 (show 0 < 65536 by decide), hsel, h.args.gen]) (by decide) (by decide) (by decide +kernel)) fun t ⟨hq, k₃⟩ => ⟨hq, (k12.trans k₃).mono (by decide)⟩


/-- The flag, from the remainder in `x3`. -/
theorem residueTail_ok {s : State} {p : PP} {w : Nat} {X : BitVec 64} (h : PSt p w s) (h3 : s.gpr .x3 = X) :
    WP isa (.block [ldh .x9 fGen, movi .x6 3, .subs .x .x8 .x9 .x6, movi .x4 4, .logic .orr .x .x5 .x3 .x4,
      .csel .x .x5 .x5 .x3, movi .x6 7, movi .x7 11, .csel .x .x6 .x6 .x7, .logic .eor .x .x5 .x5 .x6,
      sth .x5 fBad]) s fun t =>
      t.mem = s.mem.writeW (off p.B (8 * fBad)) (resFlag p.g X) ∧ Keep mmRegs s t := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have hg := h.dims.g
  have h256 := hws.h256
  have hgen := h.args.gen
  refine WP.mono (WP.keep [.x9, .x6, .x8, .x4, .x5, .x7] (Q := fun t =>
      t.mem = s.mem.writeW (off p.B (8 * fBad)) (resFlag p.g X)) (by
    rcases hg with hg | hg <;> rw [hg] at hgen ⊢ <;>
    brun [hws.x0, h3, hdr_enc (show fGen < 32 by decide), hdr_enc (show fBad < 32 by decide),
      hs.ld (d := 8 * fGen) (by simp only [fGen, sFn]; omega_arith), hs.st (d := 8 * fBad) (by simp only [fBad]; omega_arith),
      hgen, resFlag, imm16 (show 3 < 65536 by decide), imm16 (show 4 < 65536 by decide),
      imm16 (show 7 < 65536 by decide), imm16 (show 11 < 65536 by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨hm, k⟩ => ⟨hm, k.mono (by decide)⟩

/-- `residue`: the congruence's flag into `fBad`. -/
theorem residue_ok {s : State} {p : PP} {w c : Nat} (h : PSt p w s) (hc : wv s.mem p.B (slot w aN) w = c) :
    WP isa (seqs residue) s fun t =>
      PSt p w t ∧ word t.mem p.B (8 * fBad) = resFlag p.g (BitVec.ofNat 64 (c % resMod p.g)) ∧
      Frm p.B [(8 * fBad, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have hw1 := hws.w1
  have hw2 := hws.w2
  have sN := hws.sl (show aN < 16 by decide)
  have h256 := hws.h256
  simp only [residue, seqs]
  refine WP.seq (WP.mono (residueHead_ok h) fun s₁ ⟨⟨h10, h14, h13, h3, h7, h8, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  refine WP.seq (WP.mono (modWords_ok hs₁ h10 h14 h7 h8 (by omega_arith) (by omega_arith) (by omega_arith) h3
    (by rw [h13, BitVec.toNat_ofNat]; unfold resMod; split <;> decide)) fun s₂ ⟨hr₂, hm₂, k₂⟩ => ?_)
  have e13 : (s₁.gpr .x13).toNat = resMod p.g := by
    rw [h13, BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; unfold resMod; split <;> decide
  rw [e13, hm₁, hc] at hr₂
  have h3₂ : s₂.gpr .x3 = BitVec.ofNat 64 (c % resMod p.g) := by
    have h1 := Nat.mod_lt c (show 0 < resMod p.g by unfold resMod; split <;> decide)
    have h2 : resMod p.g ≤ 24 := by unfold resMod; split <;> decide
    apply BitVec.eq_of_toNat_eq; rw [hr₂, BitVec.toNat_ofNat]; exact (Nat.mod_eq_of_lt (by omega_arith)).symm
  have k12 := k₁.trans k₂
  have st₂ : PSt p w s₂ := h.step (rs := []) (hws.congr' (rs := []) (by rw [hm₂, hm₁]; exact Frm.refl _ _ _)
    (by simp) k12 (by decide)) (by rw [hm₂, hm₁]; exact Frm.refl _ _ _) (by simp) (by simp) k12
  refine WP.mono (residueTail_ok st₂ h3₂) fun t ⟨hm, k₃⟩ => ?_
  have hf : Frm p.B [(8 * fBad, 8)] s.mem t.mem := by
    rw [hm, hm₂, hm₁]; exact Frm.of_outside (writeW_outside _ _ _ (by simp only [fBad]; omega_arith)) (by simp)
  refine ⟨h.step (hws.congr' hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.hdr (by decide))
      ((k12.trans k₃)) (by decide)) hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [fBad]; omega_arith) (k12.trans k₃), ?_, hf,
    (k12.trans k₃).mono (by decide)⟩
  rw [hm, word_writeW_self]

end VG.Proof.Ffdh.AArch64.ParameterCandidate
