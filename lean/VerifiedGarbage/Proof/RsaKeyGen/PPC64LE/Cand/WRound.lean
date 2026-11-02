module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Witness
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCall
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.GeFlag
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on PPC64LE: a witness's round

`passed_ok`: after a passing round, one more witness (`hIdx`), and
`hStat := 1` once there are at least 17 (from 1) of them and `hChecks`
uniform ones, else 4. `round_ok`: the round (`roundCall_ok`) and its outcome,
`hStat := 2` for a failure.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Witness (passed hUni)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth hIdx hChecks hStat)
open VG.Proof.MillerRabin.PPC64LE.Search (geFlag_ok Prep RcPost Kept keeps_word roundCall_ok)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl arr)
open VG.Proof.Bignum (slot)

/-- The status after a passing round. -/
abbrev statOf (I U ch : Nat) : Nat := if 17 ≤ I + 1 ∧ ch ≤ U then 1 else 4

theorem stat_val (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) :
    BitVec.ofNat 64 4 - (BitVec.ofNat 64 b &&& BitVec.ofNat 64 a) * BitVec.ofNat 64 3 =
      BitVec.ofNat 64 (if a = 1 ∧ b = 1 then 1 else 4) := by
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;>
    decide

/-- The registers `passed` writes. -/
def psRegs : List Reg := [.r0, .r3, .r4, .r5, .r7]

/-- `passed`: `hIdx := I + 1`, and `hStat := statOf I U ch` for `U` uniform
witnesses of `ch` needed. -/
theorem passed_ok {s : State} {B : Addr} {Z I U ch : Nat} (hs : Scr s B Z) (h31 : s.gpr .r31 = B) (hZ : 256 ≤ Z)
    (hI : word s.mem B (8 * hIdx) = BitVec.ofNat 64 I) (hU : word s.mem B (8 * hUni) = BitVec.ofNat 64 U)
    (hch : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch) (hI' : I + 1 < 2 ^ 63) (hU' : U < 2 ^ 63)
    (hch' : ch < 2 ^ 63) :
    WP isa (.block passed) s fun t =>
      (t.mem = (s.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 (I + 1))).writeW (off B (8 * hStat))
        (BitVec.ofNat 64 (statOf I U ch))) ∧ Keep psRegs s t := by
  have hnw := hs.nowrap
  unfold passed
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  simp only [hIdx, hUni, hChecks, hStat] at hI hU hch ⊢
  refine WP.mono (WP.keep [.r3, .r4] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 (I + 1) ∧
      t.gpr .r4 = BitVec.ofNat 64 17 ∧ t.mem = s.mem.writeW (off B 176) (BitVec.ofNat 64 (I + 1))) (by
    simp only [ldh, sth]
    prun [h31, hI, hs.ld (d := 176) (n := 8) (by omega), hs.st (d := 176) (n := 8) (by omega),
      BitVec.ofNat_add_ofNat]) (by decide)) fun t₁ ⟨⟨a3, a4, m₁⟩, k₁⟩ => ?_
  refine WP.mono (geFlag_ok a3 a4 (by omega) (by decide)) fun t₂ ⟨⟨b5, m₂⟩, k₂⟩ => ?_
  have hs₂ := hs.congr (k₁.trans k₂).wr
  have h31₂ : t₂.gpr .r31 = B := by rw [(k₁.trans k₂).gpr _ (by decide), h31]
  have rU : t₂.mem.readW (off B 16) 64 = BitVec.ofNat 64 U := by
    rw [m₂, m₁, Mem.readW_writeW_sep (Offset.sep B (by omega) (by omega) (by omega)) (by decide)]; exact hU
  have rC : t₂.mem.readW (off B 168) 64 = BitVec.ofNat 64 ch := by
    rw [m₂, m₁, Mem.readW_writeW_sep (Offset.sep B (by omega) (by omega) (by omega)) (by decide)]; exact hch
  refine WP.mono (WP.keep [.r3, .r4, .r7] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 U ∧
      t.gpr .r4 = BitVec.ofNat 64 ch ∧ t.gpr .r7 = t₂.gpr .r5 ∧ t.mem = t₂.mem) (by
    simp only [ldh]
    prun [h31₂, hs₂.ld (d := 16) (n := 8) (by omega), hs₂.ld (d := 168) (n := 8) (by omega), rU, rC]
    exact BitVec.add_zero _) (by decide)) fun t₃ ⟨⟨c3, c4, c7, m₃⟩, k₃⟩ => ?_
  refine WP.mono (geFlag_ok c3 c4 (by omega) hch') fun t₄ ⟨⟨d5, m₄⟩, k₄⟩ => ?_
  have K := ((k₁.trans k₂).trans k₃).trans k₄
  have hs₄ := hs.congr K.wr
  have h31₄ : t₄.gpr .r31 = B := by rw [K.gpr _ (by decide), h31]
  have d7 : t₄.gpr .r7 = BitVec.ofNat 64 (if 17 ≤ I + 1 then 1 else 0) := by
    rw [k₄.gpr _ (by decide), c7, b5]
  refine WP.mono (WP.keep [.r4, .r5] (Q := fun t => t.mem = t₄.mem.writeW (off B 160)
      (BitVec.ofNat 64 (statOf I U ch))) (by
    simp only [sth]
    prun [h31₄, d5, d7, hs₄.st (d := 160) (n := 8) (by omega)]
    have e : (4#64 - (BitVec.ofNat 64 (if ch ≤ U then 1 else 0) &&& BitVec.ofNat 64 (if 16 ≤ I then 1 else 0)) *
        3#64 : BitVec 64) = BitVec.ofNat 64 (statOf I U ch) := by
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl,
        stat_val _ _ (by split <;> omega) (by split <;> omega)]
      unfold statOf
      by_cases e1 : 16 ≤ I <;> by_cases e2 : ch ≤ U <;> simp [e1, e2] <;> omega
    rw [e]) (by decide)) fun t ⟨tm, kt⟩ => ⟨?_, (K.trans kt).mono (by simp [psRegs])⟩
  rw [tm, m₄, m₃, m₂, m₁]

/-- A header word the round keeps. -/
theorem kept_hdr {w d : Nat} (hd : d + 8 ≤ 256) (hk : ∀ k ∈ [23, 26, 29, 30, 1], d + 8 ≤ 8 * k ∨ 8 * k + 8 ≤ d) :
    ∀ i, d ≤ i → i < d + 8 → Kept w i := by
  intro i h1 h2
  refine ⟨fun k hk' => by have := hk k hk'; omega, fun j hj => .inl ?_, .inl ?_⟩
  · have : 256 ≤ slot w j := by rw [slot_lin]; omega
    omega
  · have : 256 ≤ slot w 11 := by rw [slot_lin]; omega
    omega

/-- What a witness's round leaves. -/
structure RdPost (s : State) (B : Addr) (L w c a I U ch : Nat) (t : State) : Prop where
  prep : Prep t B L w c
  stat : word t.mem B (8 * hStat) =
    BitVec.ofNat 64 (if Proof.MillerRabin.Round.round c a then statOf I U ch else 2)
  idx : word t.mem B (8 * hIdx) = BitVec.ofNat 64 (if Proof.MillerRabin.Round.round c a then I + 1 else I)
  hdr : ∀ d, d + 8 ≤ 256 → (∀ k ∈ [23, 26, 29, 30, 1, 20, 22], d + 8 ≤ 8 * k ∨ 8 * k + 8 ≤ d) →
    word t.mem B d = word s.mem B d
  frame : Frame [⟨B, 8 * L⟩, below s.sp 176] s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  cs : ∀ r ∈ preserved, r ∉ Pub.montRegs → r ∉ psRegs → t.gpr r = s.gpr r

theorem round_ok (R : RoundImpl) {s : State} {B : Addr} {L w c a I U ch : Nat} (h : Prep s B L w c)
    (ha : arr s.mem B w 4 = a) (hac : a < c)
    (hsp : 176 ≤ s.sp.toNat) (hstk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩)
    (hI : word s.mem B (8 * hIdx) = BitVec.ofNat 64 I) (hU : word s.mem B (8 * hUni) = BitVec.ofNat 64 U)
    (hch : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch) (hI' : I + 1 < 2 ^ 63) (hU' : U < 2 ^ 63)
    (hch' : ch < 2 ^ 63) :
    WP isa (VG.Impl.RsaKeyGen.PPC64LE.Witness.round R.name R.code) s (RdPost s B L w c a I U ch) := by
  have e := h.env
  have hZ := e.hZ
  rw [slot_lin] at hZ
  unfold VG.Impl.RsaKeyGen.PPC64LE.Witness.round
  refine WP.seq (WP.mono (roundCall_ok R h ha hac hsp hstk) fun u hu => ?_)
  have kw : ∀ d, d + 8 ≤ 256 → (∀ k ∈ [23, 26, 29, 30, 1], d + 8 ≤ 8 * k ∨ 8 * k + 8 ≤ d) →
      word u.mem B d = word s.mem B d := fun d hd hk => keeps_word hu.keeps (by omega) (kept_hdr hd hk)
  have hsu := e.hs.congr hu.wr
  have h31 : u.gpr .r31 = B := hu.prep.env.h31
  refine WP.ite _ (eval_zero_ofNat _ _ (by split <;> decide) hu.r3) (fun hz => ?_) (fun hz => ?_)
  · have hr : Proof.MillerRabin.Round.round c a = false := by
      by_contra hc; simp [hc] at hz
    refine WP.mono (WP.keep [.r3] (Q := fun t => t.mem = u.mem.writeW (off B (8 * hStat)) (BitVec.ofNat 64 2)) (by
      simp only [sth, hStat]; prun [h31, hsu.st (d := 160) (n := 8) (by omega)]) (by decide)) fun t ⟨tm, kt⟩ => ?_
    have wo := writeW_outside u.mem B (d := 8 * hStat) (BitVec.ofNat 64 2) (by simp only [hStat]; omega)
    have hL := hu.prep.env.hZ
    rw [slot_lin] at hL
    have hnw := hsu.nowrap
    refine ⟨hu.prep.keep (hu.prep.env.keep kt (by decide)) (fun d hd => ?_) (fun j hj => ?_), ?_, ?_, ?_, ?_,
      kt.rd.trans hu.rd, kt.wr.trans hu.wr, kt.sp.trans hu.sp, fun r hr h1 h2 => ?_⟩
    · rw [tm]
      have s0 : 256 ≤ slot w 0 := by rw [slot_lin]; omega
      have s0' : slot w 0 + 8 ≤ 8 * L := by rw [slot_lin]; omega
      have s27 : 256 ≤ slot w 27 := by rw [slot_lin]; omega
      have s27' : slot w 27 + 8 * w + 8 ≤ 8 * L := by rw [slot_lin]; omega
      rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
      all_goals exact wo.word (by simp only [hStat]; omega) (by omega)
    · rw [tm]
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        exact wo.val32 (by simp only [hStat]; rw [slot_lin]; omega) (by rw [slot_lin]; omega)
    · rw [tm, hr]; exact word_writeW_self _ _ _ _
    · rw [tm, hr, wo.word (by simp only [hStat, hIdx]; omega) (by simp only [hIdx]; omega),
        kw _ (by simp only [hIdx]; omega) (by simp only [hIdx]; decide), hI]; rfl
    · intro d hd hk
      rw [tm, wo.word (by have := hk 20 (by simp); simp only [hStat]; omega) (by omega),
        kw d hd (fun k hk' => hk k (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk' ⊢; omega))]
    · rw [tm]
      exact hu.frame.writeW (r := ⟨B, 8 * L⟩) (by simp) _
        (Offset.contains_base _ (by simp only [hStat]; omega) (by simp only [hStat]; omega))
    · have h3 : r ≠ .r3 := fun e => by subst e; exact h2 (by decide)
      rw [kt.gpr r (by simp [h3]), hu.cs r hr h1]
  · have hr : Proof.MillerRabin.Round.round c a = true := by
      by_contra hc; simp [hc] at hz
    have hL := hu.prep.env.hZ
    rw [slot_lin] at hL
    have hnw := hsu.nowrap
    have kI : word u.mem B (8 * hIdx) = BitVec.ofNat 64 I := by
      rw [kw _ (by simp only [hIdx]; omega) (by simp only [hIdx]; decide), hI]
    have kU : word u.mem B (8 * hUni) = BitVec.ofNat 64 U := by
      rw [kw _ (by simp only [hUni]; omega) (by simp only [hUni]; decide), hU]
    have kC : word u.mem B (8 * hChecks) = BitVec.ofNat 64 ch := by
      rw [kw _ (by simp only [hChecks]; omega) (by simp only [hChecks]; decide), hch]
    refine WP.mono (passed_ok hsu h31 (by omega) kI kU kC hI' hU' hch') fun t ⟨tm, kt⟩ => ?_
    have wo1 := writeW_outside u.mem B (d := 8 * hIdx) (BitVec.ofNat 64 (I + 1)) (by simp only [hIdx]; omega)
    have wo2 := writeW_outside (u.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 (I + 1))) B (d := 8 * hStat)
      (BitVec.ofNat 64 (statOf I U ch)) (by simp only [hStat]; omega)
    refine ⟨hu.prep.keep (hu.prep.env.keep kt (by decide)) (fun d hd => ?_) (fun j hj => ?_), ?_, ?_, ?_, ?_,
      kt.rd.trans hu.rd, kt.wr.trans hu.wr, kt.sp.trans hu.sp, fun r hr h1 h2 => ?_⟩
    · rw [tm]
      have s0 : 256 ≤ slot w 0 := by rw [slot_lin]; omega
      have s0' : slot w 0 + 8 ≤ 8 * L := by rw [slot_lin]; omega
      have s27 : 256 ≤ slot w 27 := by rw [slot_lin]; omega
      have s27' : slot w 27 + 8 * w + 8 ≤ 8 * L := by rw [slot_lin]; omega
      rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
      all_goals rw [wo2.word (by simp only [hStat]; omega) (by omega)]
      all_goals exact wo1.word (by simp only [hIdx]; omega) (by omega)
    · rw [tm]
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        rw [wo2.val32 (by simp only [hStat]; rw [slot_lin]; omega) (by rw [slot_lin]; omega)] <;>
        exact wo1.val32 (by simp only [hIdx]; rw [slot_lin]; omega) (by rw [slot_lin]; omega)
    · rw [tm, hr]; exact word_writeW_self _ _ _ _
    · rw [tm, hr, wo2.word (by simp only [hStat, hIdx]; omega) (by simp only [hIdx]; omega)]
      exact word_writeW_self _ _ _ _
    · intro d hd hk
      have h20 := hk 20 (by simp)
      have h22 := hk 22 (by simp)
      rw [tm, wo2.word (by simp only [hStat]; omega) (by omega), wo1.word (by simp only [hIdx]; omega) (by omega),
        kw d hd (fun k hk' => hk k (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk' ⊢; omega))]
    · rw [tm]
      exact (hu.frame.writeW (r := ⟨B, 8 * L⟩) (by simp) _
        (Offset.contains_base _ (by simp only [hIdx]; omega) (by simp only [hIdx]; omega))).writeW
        (r := ⟨B, 8 * L⟩) (by simp) _
        (Offset.contains_base _ (by simp only [hStat]; omega) (by simp only [hStat]; omega))
    · rw [kt.gpr r h2, hu.cs r hr h1]

end VG.Proof.RsaKeyGen.PPC64LE.Cand
