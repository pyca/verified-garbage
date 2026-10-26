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

/-! # Fixed-length equality scans for DSA signatures and keys -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev equalByte : List Instr := [.ldrb .x3 .x1 0, .ldrb .x10 .x2 0,
  .logic .eor .x .x3 .x3 .x10, .logic .orr .x .x8 .x8 .x3,
  .addImm .x .x1 .x1 1, .addImm .x .x2 .x2 1, .subImm .x .x9 .x9 1]

theorem byte_widen_eq (a b : Byte) : a.zeroExtend 64 = b.zeroExtend 64 ↔ a = b := by
  constructor
  · intro h
    have he := congrArg BitVec.toNat h
    change (a.setWidth 64).toNat = (b.setWidth 64).toNat at he
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (show 2 ^ 8 < 2 ^ 64 by decide)),
      Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (show 2 ^ 8 < 2 ^ 64 by decide))] at he
    exact BitVec.eq_of_toNat_eq he
  · intro h; rw [h]

theorem equalByte_ok {s : State} {p q : Addr} {n : Nat}
    (hp : s.gpr .x1 = p) (hq : s.gpr .x2 = q) (hn : s.gpr .x9 = BitVec.ofNat 64 n)
    (hrp : InRegions (s.rd ++ s.wr) p 1) (hrq : InRegions (s.rd ++ s.wr) q 1)
    (h1 : 1 ≤ n) (h64 : n < 2 ^ 64) :
    WP isa (.block equalByte) s fun t =>
      t.gpr .x1 = p + 1 ∧ t.gpr .x2 = q + 1 ∧ t.gpr .x9 = BitVec.ofNat 64 (n - 1) ∧
      (t.gpr .x8 = 0 ↔ s.gpr .x8 = 0 ∧ s.mem p = s.mem q) ∧
      (t.gpr .x9 == (0#64)) = decide (n = 1) ∧ t.mem = s.mem ∧ Keep [.x3, .x10, .x8, .x1, .x2, .x9] s t := by
  have hsub : BitVec.ofNat 64 n - (1#64) = BitVec.ofNat 64 (n - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    simp only [Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide)]
    omega
  have hz : (BitVec.ofNat 64 (n - 1) == (0#64)) = decide (n = 1) := by
    rw [ofNat_beq_zero (by omega), Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    omega
  refine WP.mono (WP.keep [.x3, .x10, .x8, .x1, .x2, .x9] (Q := fun t =>
    t.gpr .x1 = p + 1 ∧ t.gpr .x2 = q + 1 ∧ t.gpr .x9 = BitVec.ofNat 64 (n - 1) ∧
    t.gpr .x8 = s.gpr .x8 ||| ((s.mem p).zeroExtend 64 ^^^ (s.mem q).zeroExtend 64) ∧
    (t.gpr .x9 == (0#64)) = decide (n = 1) ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨htp, htq, htn, ht8, htz, htm⟩, hk⟩ => ?_
  · unfold equalByte
    have hb (b : Byte) : (b.setWidth 32).setWidth 64 = b.zeroExtend 64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.zeroExtend]
      have := b.isLt
      omega
    brun [hp, hq, hn, hrp, hrq, read_one, hb, hsub, hz]
    exact ⟨rfl, rfl⟩
  · refine ⟨htp, htq, htn, ?_, htz, htm, hk⟩
    rw [ht8]
    exact BitVec.or_eq_zero_iff.trans (and_congr Iff.rfl (BitVec.xor_eq_zero_iff.trans (byte_widen_eq _ _)))

/-- Both buffers are read completely, even after the first unequal byte. -/
theorem equalLoop_ok {s : State} {B p q : Addr} {Z : Nat} {as bs : List Byte}
    (hp : s.gpr .x1 = p) (hq : s.gpr .x2 = q) (hn : s.gpr .x9 = BitVec.ofNat 64 as.length)
    (ha : Src s B Z p as) (hb : Src s B Z q bs) (hlen : as.length = bs.length)
    (h1 : 0 < as.length) (h64 : as.length < 2 ^ 64) :
    WP isa (.loop (.block equalByte) (.nonzero .x .x9)) s fun t =>
      (t.gpr .x8 = 0 ↔ s.gpr .x8 = 0 ∧ as = bs) ∧ t.mem = s.mem ∧
      Keep [.x3, .x10, .x8, .x1, .x2, .x9] s t := by
  let target := s.gpr .x8 = 0 ∧ as = bs
  let Inv := fun n t => ∃ (pa pb : Addr) (aa bb : List Byte),
    aa.length = n ∧ bb.length = n ∧ 0 < n ∧ n < 2 ^ 64 ∧
    t.gpr .x1 = pa ∧ t.gpr .x2 = pb ∧ t.gpr .x9 = BitVec.ofNat 64 aa.length ∧
    Src t B Z pa aa ∧ Src t B Z pb bb ∧
    ((t.gpr .x8 = 0 ∧ aa = bb) ↔ target) ∧ t.mem = s.mem ∧
    Keep [.x3, .x10, .x8, .x1, .x2, .x9] s t
  refine WP.loop (M := isa) (body := .block equalByte) (c := (.nonzero .x .x9)) Inv ?_ as.length s ?_
  · intro n u ⟨pa, pb, aa, bb, hla, hlb, hpos, hbnd, hup, huq, hun, hua, hub, htarget, hum, hku⟩
    cases aa with
    | nil => simp only [List.length_nil] at hla; omega
    | cons a aa =>
      cases bb with
      | nil => simp only [List.length_nil] at hlb; omega
      | cons b bb =>
        have hrp : InRegions (u.rd ++ u.wr) pa 1 := by simpa using hua.rd 0 (by simp)
        have hrq : InRegions (u.rd ++ u.wr) pb 1 := by simpa using hub.rd 0 (by simp)
        have va : u.mem pa = a := by
          have he := hua.val 0 (by simp)
          change u.mem (pa + 0) = a at he
          exact (congrArg u.mem (BitVec.add_zero pa)).symm.trans he
        have vb : u.mem pb = b := by
          have he := hub.val 0 (by simp)
          change u.mem (pb + 0) = b at he
          exact (congrArg u.mem (BitVec.add_zero pb)).symm.trans he
        refine WP.mono (equalByte_ok hup huq hun hrp hrq (by simp) (by omega))
          fun t ⟨htp, htq, htn, ht8, htz, htm, hkt⟩ => ?_
        rw [va, vb] at ht8
        have htarget' : (t.gpr .x8 = 0 ∧ aa = bb) ↔ target := by
          rw [ht8, ← htarget, List.cons.injEq]
          exact and_assoc
        have hk : Keep [.x3, .x10, .x8, .x1, .x2, .x9] s t := (hku.trans hkt).mono (by decide)
        by_cases he : aa.length = 0
        · left
          refine ⟨?_, ?_, htm.trans hum, hk⟩
          · change some (!(t.gpr .x9 == (0#64))) = some false
            simp only [htz, List.length_cons, he, decide_true, Bool.not_true]
          · have heb : bb.length = 0 := by simp only [List.length_cons] at hla hlb; omega
            simpa only [List.length_eq_zero_iff.mp he, List.length_eq_zero_iff.mp heb, and_true] using htarget'
        · right
          refine ⟨?_, aa.length, by simp only [List.length_cons] at hla; omega,
            pa + 1, pb + 1, aa, bb, rfl, by simp only [List.length_cons] at hla hlb; omega,
            by omega, by simp only [List.length_cons] at hla; omega, htp, htq, ?_,
            source_tail (hua.congrK (by rw [htm]; exact InScr.refl _ _ _) hkt),
            source_tail (hub.congrK (by rw [htm]; exact InScr.refl _ _ _) hkt), htarget', htm.trans hum, hk⟩
          · change some (!(t.gpr .x9 == (0#64))) = some true
            simp only [htz, List.length_cons, Nat.add_eq_right, he, decide_false, Bool.not_false]
          · simpa only [List.length_cons, Nat.add_sub_cancel] using htn
  · exact ⟨p, q, as, bs, rfl, hlen.symm, h1, h64, hp, hq, hn, ha, hb, Iff.rfl, rfl, Keep.refl _ _⟩

end VG.Proof.Dsa.AArch64
