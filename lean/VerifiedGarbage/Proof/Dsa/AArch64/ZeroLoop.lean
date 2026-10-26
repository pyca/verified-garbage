module
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup

import VerifiedGarbage.Proof.Dsa.AArch64.Significant
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceCount
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! # Fixed-length bytewise zero tests for DSA acceptance masks -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev zeroByte : List Instr := [.ldrb .x3 .x1 0, .logic .orr .x .x8 .x8 .x3,
  .addImm .x .x1 .x1 1, .subImm .x .x9 .x9 1]

theorem zeroByte_ok {s : State} {p : Addr} {n : Nat}
    (hp : s.gpr .x1 = p) (hn : s.gpr .x9 = BitVec.ofNat 64 n)
    (hr : InRegions (s.rd ++ s.wr) p 1) (h1 : 1 ≤ n) (h64 : n < 2 ^ 64) :
    WP isa (.block zeroByte) s fun t =>
      t.gpr .x1 = p + 1 ∧ t.gpr .x9 = BitVec.ofNat 64 (n - 1) ∧
      (t.gpr .x8 = 0 ↔ s.gpr .x8 = 0 ∧ s.mem p = 0) ∧
      (t.gpr .x9 == (0#64)) = decide (n = 1) ∧ t.mem = s.mem ∧ Keep [.x3, .x8, .x1, .x9] s t := by
  have hsub : BitVec.ofNat 64 n - (1#64) = BitVec.ofNat 64 (n - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    simp only [Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide)]
    omega
  have hz : (BitVec.ofNat 64 (n - 1) == (0#64)) = decide (n = 1) := by
    rw [ofNat_beq_zero (by omega), Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    omega
  refine WP.mono (WP.keep [.x3, .x8, .x1, .x9] (Q := fun t =>
    t.gpr .x1 = p + 1 ∧ t.gpr .x9 = BitVec.ofNat 64 (n - 1) ∧
    t.gpr .x8 = s.gpr .x8 ||| (s.mem p).zeroExtend 64 ∧ (t.gpr .x9 == (0#64)) = decide (n = 1) ∧ t.mem = s.mem)
    ?_ rfl rfl rfl) fun t ⟨⟨htp, htn, ht8, htz, htm⟩, hk⟩ => ?_
  · unfold zeroByte
    have hb : ((s.mem p).setWidth 32).setWidth 64 = (s.mem p).zeroExtend 64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.zeroExtend]
      have := (s.mem p).isLt
      omega
    brun [hp, hn, hr, read_one, hb, hsub, hz]
    rfl
  · exact ⟨htp, htn, by rw [ht8]; exact BitVec.or_eq_zero_iff.trans (and_congr Iff.rfl (byte_widen_zero _)), htz, htm, hk⟩

/-- A positive-length zero scan reads every byte, including leading zeros. -/
theorem zeroLoop_ok {s : State} {B p : Addr} {Z : Nat} {bs : List Byte}
    (hp : s.gpr .x1 = p) (hn : s.gpr .x9 = BitVec.ofNat 64 bs.length)
    (hs : Src s B Z p bs) (h1 : 0 < bs.length) (h64 : bs.length < 2 ^ 64) :
    WP isa (.loop (.block zeroByte) (.nonzero .x .x9)) s fun t =>
      (t.gpr .x8 = 0 ↔ s.gpr .x8 = 0 ∧ ∀ b ∈ bs, b = 0) ∧ t.mem = s.mem ∧
      Keep [.x3, .x8, .x1, .x9] s t := by
  let target := s.gpr .x8 = 0 ∧ ∀ b ∈ bs, b = 0
  let Inv := fun n t => ∃ (ptr : Addr) (rest : List Byte),
    rest.length = n ∧ 0 < n ∧ n < 2 ^ 64 ∧ t.gpr .x1 = ptr ∧
    t.gpr .x9 = BitVec.ofNat 64 rest.length ∧ Src t B Z ptr rest ∧
    ((t.gpr .x8 = 0 ∧ ∀ b ∈ rest, b = 0) ↔ target) ∧ t.mem = s.mem ∧
    Keep [.x3, .x8, .x1, .x9] s t
  refine WP.loop (M := isa) (body := .block zeroByte) (c := (.nonzero .x .x9)) Inv ?_ bs.length s ?_
  · intro n u ⟨ptr, rest, hlen, hpos, hbnd, hup, hun, hus, htarget, hum, hku⟩
    cases rest with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons b rest =>
      have hr : InRegions (u.rd ++ u.wr) ptr 1 := by simpa using hus.rd 0 (by simp)
      have hbyte : u.mem ptr = b := by
        have he := hus.val 0 (by simp)
        change u.mem (ptr + 0) = b at he
        exact (congrArg u.mem (BitVec.add_zero ptr)).symm.trans he
      refine WP.mono (zeroByte_ok hup hun hr (by simp) (by omega))
        fun t ⟨htp, htn, ht8, htz, htm, hkt⟩ => ?_
      rw [hbyte] at ht8
      have htarget' : (t.gpr .x8 = 0 ∧ ∀ b ∈ rest, b = 0) ↔ target := by
        rw [ht8, ← htarget]
        simp only [List.mem_cons, forall_eq_or_imp]
        exact and_assoc
      have hk : Keep [.x3, .x8, .x1, .x9] s t := (hku.trans hkt).mono (by decide)
      by_cases he : rest.length = 0
      · left
        refine ⟨?_, ?_, htm.trans hum, hk⟩
        · change some (!(t.gpr .x9 == (0#64))) = some false
          simp only [htz, List.length_cons, he, decide_true, Bool.not_true]
        · simpa only [List.length_eq_zero_iff.mp he, List.not_mem_nil, forall_const, false_implies, implies_true, and_true] using htarget'
      · right
        refine ⟨?_, rest.length, by simp only [List.length_cons] at hlen; omega,
          ptr + 1, rest, rfl, by omega, by simp only [List.length_cons] at hlen; omega,
          htp, ?_, source_tail (hus.congrK (by rw [htm]; exact InScr.refl _ _ _) hkt), htarget', htm.trans hum, hk⟩
        · change some (!(t.gpr .x9 == (0#64))) = some true
          simp only [htz, List.length_cons, Nat.add_eq_right, he, decide_false, Bool.not_false]
        · simpa only [List.length_cons, Nat.add_sub_cancel] using htn
  · exact ⟨p, bs, rfl, h1, h64, hp, hn, hs, Iff.rfl, rfl, Keep.refl _ _⟩

end VG.Proof.Dsa.AArch64
