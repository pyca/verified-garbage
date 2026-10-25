module

import VerifiedGarbage.Proof.Dsa.AArch64.RandomBorrow
public import VerifiedGarbage.Proof.Dsa.RandomRange
public import VerifiedGarbage.Impl.Dsa.AArch64.Random
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! Correctness of the sampler's right-to-left range check. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

/-- A byte comparison advances both pointers, preserves memory, and computes
both the subtraction borrow and the nonzero accumulator. -/
theorem random_rangeByte_ok {s : State} {p q : Addr} {a b : Byte} {n c : Nat}
    (hp : s.gpr .x2 = p + 1#64) (hq : s.gpr .x12 = q + 1#64)
    (hn : s.gpr .x9 = BitVec.ofNat 64 n) (h8 : s.gpr .x8 = BitVec.ofNat 64 c)
    (hc : c ≤ 1) (hnpos : 0 < n) (hnb : n < 2 ^ 64)
    (hrp : InRegions (s.rd ++ s.wr) p 1) (hrq : InRegions (s.rd ++ s.wr) q 1)
    (ha : s.mem p = a) (hb : s.mem q = b) :
    WP isa (.block Random.rangeByte) s fun t =>
      t.gpr .x2 = p ∧ t.gpr .x12 = q ∧ t.gpr .x9 = BitVec.ofNat 64 (n - 1) ∧
      (t.gpr .x8).toNat = (if a.toNat < b.toNat + c then 1 else 0) ∧
      t.gpr .x10 = s.gpr .x10 ||| a.setWidth 64 ∧
      t.mem = s.mem ∧
      Keep [.x0, .x4, .x2, .x8, .x10, .x12, .x9] s t := by
  have hac : (a.setWidth 64).toNat = a.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := a.isLt; omega)]
  have hbc : (b.setWidth 64).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  have hcc : (BitVec.ofNat 64 c).toNat = c := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hadd : (b.setWidth 64 + BitVec.ofNat 64 c).toNat = b.toNat + c := by
    rw [BitVec.toNat_add, hbc, hcc, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  have hborrow := random_byte_borrow (a.setWidth 64) (b.setWidth 64 + BitVec.ofNat 64 c)
    (by rw [hac]; have := a.isLt; omega) (by rw [hadd]; have := b.isLt; omega)
  rw [hac, hadd] at hborrow
  refine WP.mono (WP.keep [.x0, .x4, .x2, .x8, .x10, .x12, .x9] (Q := fun t =>
      t.gpr .x2 = p ∧ t.gpr .x12 = q ∧ t.gpr .x9 = BitVec.ofNat 64 (n - 1) ∧
      (t.gpr .x8).toNat = (if a.toNat < b.toNat + c then 1 else 0) ∧
      t.gpr .x10 = s.gpr .x10 ||| a.setWidth 64 ∧
      t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨htp, htq, htn, htc, hta, htm⟩, hkt⟩ =>
      ⟨htp, htq, htn, htc, hta, htm, hkt⟩
  unfold Random.rangeByte Random.borrow
  have hpred : BitVec.ofNat 64 n - 1#64 = BitVec.ofNat 64 (n - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hbyte (x : Byte) : (x.setWidth 32).setWidth 64 = x.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := x.isLt
    omega
  brun [hp, hq, hn, h8, BitVec.add_sub_cancel, hrp, hrq, read_one, ha, hb,
    hbyte, hborrow, hpred]

structure RandomRangeInv (s : State) (p q : Addr) (as bs : List Byte) (j : Nat) (t : State) : Prop where
  keep : Keep [.x0, .x4, .x2, .x8, .x10, .x12, .x9] s t
  ptrA : t.gpr .x2 = p + BitVec.ofNat 64 (as.length - j)
  ptrB : t.gpr .x12 = q + BitVec.ofNat 64 (as.length - j)
  count : t.gpr .x9 = BitVec.ofNat 64 (as.length - j)
  borrow : (t.gpr .x8).toNat = VG.Proof.Dsa.randomBorrow (as.drop (as.length - j)) (bs.drop (as.length - j))
  accum : t.gpr .x10 = VG.Proof.Dsa.randomOr (as.drop (as.length - j))
  mem : t.mem = s.mem

/-- The entire right-to-left loop computes the borrow and OR accumulator. -/
theorem random_rangeLoop_ok {s : State} {p q : Addr} {as bs : List Byte}
    (hlen : as.length = bs.length) (hpos : 0 < as.length) (hbound : as.length < 2 ^ 64)
    (hp : s.gpr .x2 = p + BitVec.ofNat 64 as.length)
    (hq : s.gpr .x12 = q + BitVec.ofNat 64 as.length)
    (hn : s.gpr .x9 = BitVec.ofNat 64 as.length)
    (h8 : s.gpr .x8 = 0) (h9 : s.gpr .x10 = 0)
    (hra : ∀ i < as.length, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hrb : ∀ i < as.length, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 i) 1)
    (hva : ∀ i (h : i < as.length), s.mem (p + BitVec.ofNat 64 i) = as[i])
    (hvb : ∀ i (h : i < bs.length), s.mem (q + BitVec.ofNat 64 i) = bs[i]) :
    WP isa (.loop (.block Random.rangeByte) (.nonzero .x .x9)) s fun t =>
      (t.gpr .x8).toNat = VG.Proof.Dsa.randomBorrow as bs ∧
      t.gpr .x10 = VG.Proof.Dsa.randomOr as ∧ t.mem = s.mem ∧
      Keep [.x0, .x4, .x2, .x8, .x10, .x12, .x9] s t := by
  refine WP.mono (wp_countdown (N := as.length) hbound hpos (RandomRangeInv s p q as bs) ?_ ?_ hn) fun t ht => ?_
  · intro j hj t ht hcount
    let i := as.length - (j + 1)
    have hi : i < as.length := by dsimp only [i]; omega
    have hib : i < bs.length := by omega
    have hij : i + 1 = as.length - j := by dsimp only [i]; omega
    have hpa : t.gpr .x2 = (p + BitVec.ofNat 64 i) + 1#64 := by
      change _ = _ + BitVec.ofNat 64 1
      rw [ht.ptrA, BitVec.add_assoc, BitVec.ofNat_add_ofNat, hij]
    have hpb : t.gpr .x12 = (q + BitVec.ofNat 64 i) + 1#64 := by
      change _ = _ + BitVec.ofNat 64 1
      rw [ht.ptrB, BitVec.add_assoc, BitVec.ofNat_add_ofNat, hij]
    have ht8 : t.gpr .x8 = BitVec.ofNat 64
        (VG.Proof.Dsa.randomBorrow (as.drop (as.length - j)) (bs.drop (as.length - j))) := by
      rw [← ht.borrow, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine WP.mono (random_rangeByte_ok (a := as[i]) (b := bs[i]) hpa hpb ht.count ht8 (VG.Proof.Dsa.randomBorrow_le _ _)
      (by omega) (by omega)
      (by rw [ht.keep.rd, ht.keep.wr]; exact hra i hi)
      (by rw [ht.keep.rd, ht.keep.wr]; exact hrb i hi)
      (by rw [ht.mem]; exact hva i hi) (by rw [ht.mem]; exact hvb i hib))
      fun u ⟨hup, huq, hun, hub, hua, hum, hku⟩ => ?_
    refine ⟨⟨(ht.keep.trans hku).mono (by decide), hup, huq, ?_, ?_, ?_, hum.trans ht.mem⟩, ?_⟩
    · rw [hun, show as.length - j - 1 = as.length - (j + 1) by omega]
    · change (u.gpr .x8).toNat = VG.Proof.Dsa.randomBorrow (as.drop i) (bs.drop i)
      rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hib, VG.Proof.Dsa.randomBorrow, hij]
      exact hub
    · change u.gpr .x10 = VG.Proof.Dsa.randomOr (as.drop i)
      rw [List.drop_eq_getElem_cons hi, VG.Proof.Dsa.randomOr, hij, hua, ht.accum]
    · rw [hun, hcount]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
  · refine ⟨Keep.refl _ _, by simpa using hp, by simpa using hq, by simpa using hn, ?_, ?_, rfl⟩
    · rw [Nat.sub_zero, List.drop_length, hlen, List.drop_length, h8]
      rfl
    · simp only [Nat.sub_zero, List.drop_length, VG.Proof.Dsa.randomOr, h9]
  · refine ⟨?_, ?_, ht.mem, ht.keep⟩
    · simpa only [Nat.sub_self, List.drop_zero] using ht.borrow
    · simpa only [Nat.sub_self, List.drop_zero] using ht.accum

/-- Only the combined accept bit is exposed to the following branch. -/
theorem random_rangeFinish_ok {s : State} {a b : Nat}
    (h8 : s.gpr .x8 = BitVec.ofNat 64 (if a < b then 1 else 0))
    (h9 : (s.gpr .x10 == 0) = decide (a = 0)) :
    WP isa (.block Random.rangeFinish) s fun t =>
      t.gpr .x8 = BitVec.ofNat 64 (if 0 < a ∧ a < b then 1 else 0) ∧ t.mem = s.mem ∧
      Keep [.x0, .x8] s t := by
  refine WP.mono (WP.keep [.x0, .x8] (Q := fun t =>
      t.gpr .x8 = BitVec.ofNat 64 (if 0 < a ∧ a < b then 1 else 0) ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun _ ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  unfold Random.rangeFinish
  brun [exec_tst_x, exec_cselc_x, CondCode.holds, State.write, h9, h8]
  by_cases hz : a = 0 <;> by_cases hl : a < b <;> simp [hz, hl]
  rw [ite_eq_left (show 0 < a by omega)]

end VG.Proof.Dsa.AArch64
