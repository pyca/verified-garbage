module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.SearchInit
public import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
public import VerifiedGarbage.Proof.RsaKeyGen.InitWords
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.PPC64LE.InitCommon
import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.SearchInit
meta import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.InitCommon
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Mathlib.Tactic.SplitIfs

/-! # Starting the RSA prime search on PPC64LE: correctness, constant time -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.SearchInit

open VG VG.PPC64LE VG.Proof.Bignum
open VG.Proof.Ffdh.PPC64LE (lt_bit shr_zero)
open VG.Proof.RsaKeyGen.SearchInit
open VG.Impl.Bignum.PPC64LE (countLoop)
open VG.Impl.RsaKeyGen.PPC64LE.SearchInit

/-! ## Validation -/

theorem or_shr_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a >>> 14 ||| BitVec.ofNat 64 b >>> 14 == 0) = decide (a < 2 ^ 14 ∧ b < 2 ^ 14) := by
  have h := or_eq_zero (BitVec.ofNat 64 a >>> 14) (BitVec.ofNat 64 b >>> 14)
  have h1 := Bool.eq_iff_iff.mp (shr_zero (k := 14) ha)
  have h2 := Bool.eq_iff_iff.mp (shr_zero (k := 14) hb)
  simp only [beq_iff_eq, decide_eq_true_eq] at h1 h2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [h, h1, h2]

theorem high_ok (s : State) :
    WP isa (.block high) s fun t =>
      (t.gpr .r12 = s.gpr .r4 >>> 14 ||| s.gpr .r6 >>> 14 ∧ t.mem = s.mem) ∧ Keep [.r11, .r12] s t := by
  refine WP.keep [.r11, .r12] ?_ (by decide +kernel)
  unfold high
  crunr

theorem and7 (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n &&& BitVec.ofNat 64 7 = BitVec.ofNat 64 (n % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `validate`: with both below `2^14`, `r12` is 1 exactly for a valid width
and exponent length. -/
theorem validate_ok (s : State) {L len : Nat} (hx : s.gpr .r4 = BitVec.ofNat 64 L) (hL : L < 2 ^ 14)
    (hy : s.gpr .r6 = BitVec.ofNat 64 len) (hl : len < 2 ^ 14) :
    WP isa (.block validate) s fun t =>
      (t.gpr .r12 = BitVec.ofNat 64 (if initValid L len then 1 else 0) ∧ t.mem = s.mem) ∧
        Keep [.r7, .r8, .r9, .r10, .r11, .r12] s t := by
  refine WP.keep [.r7, .r8, .r9, .r10, .r11, .r12] ?_ (by decide +kernel)
  unfold validate lt
  crunr [hx, hy, List.cons_append, List.nil_append, and7 L (by omega)]
  rw [lt_bit (by omega) (by decide), lt_bit (by omega) (by decide), lt_bit (by omega) (by decide),
    lt_bit (by omega) (by decide), lt_bit (by omega) (by decide)]
  unfold initValid
  split_ifs <;> first | rfl | (exfalso; omega)

/-! ## The four words -/

/-- The state's 32 bytes, which the code may write. -/
def Scr (s : State) (B : Addr) : Prop := ⟨B, 32⟩ ∈ s.wr ∧ B.toNat + 32 ≤ 2 ^ 64

theorem Scr.st {s : State} {B : Addr} (h : Scr s B) (d : Nat) (hd : d + 8 ≤ 32) :
    InRegions s.wr (B + BitVec.ofNat 64 d) 8 :=
  ⟨_, h.1, Offset.contains_base _ hd (by have := h.2; omega)⟩

theorem Scr.st0 {s : State} {B : Addr} (h : Scr s B) : InRegions s.wr B 8 := by
  simpa only [BitVec.add_zero] using h.st 0 (by decide)

theorem Scr.congr {s t : State} {B : Addr} (h : Scr s B) (hw : t.wr = s.wr) : Scr t B := by
  rw [Scr, hw]; exact h

theorem clear_ok {s : State} {B : Addr} (scr : Scr s B) (h3 : s.gpr .r3 = B) :
    WP isa (.block clear) s fun t => t.gpr .r3 = 0 ∧ t.mem = written s.mem B [0, 0, 0, 0] := by
  unfold clear written
  crunr [h3, scr.st0, scr.st 8 (by decide), scr.st 16 (by decide), scr.st 24 (by decide), off]
  rfl

theorem initialize_ok {s : State} {B : Addr} {L k : Nat} (scr : Scr s B) (h3 : s.gpr .r3 = B)
    (h4 : s.gpr .r4 = BitVec.ofNat 64 L) (hL : L ≤ 512) (h9 : s.gpr .r9 = BitVec.ofNat 64 k) (hk : k < 2 ^ 63) :
    WP isa (.block initializeState) s
      fun t => t.gpr .r3 = 1 ∧ t.mem = written s.mem B (initWords L (decide (k = 0))) := by
  have e3 := shl_ofNat L 3 (by omega)
  have e4 := shl_ofNat L 4 (by omega)
  have e5 := shl_ofNat L 5 (by omega)
  have e15 := shl_ofNat L 15 (by omega)
  have hz : (BitVec.ofNat 64 k - BitVec.ofNat 64 1) >>> 63 = BitVec.ofNat 64 (if k = 0 then 1 else 0) := by
    rw [lt_bit hk (by decide)]
    congr 2
    exact propext ⟨fun h => by omega, fun h => by omega⟩
  have e0 : BitVec.ofNat 64 (L * 8) + BitVec.ofNat 64 (32 * L) +
      (BitVec.ofNat 64 (L * 16) + BitVec.ofNat 64 (L * 8)) * BitVec.ofNat 64 (if k = 0 then 1 else 0) =
      BitVec.ofNat 64 (if k = 0 then 64 * L else 40 * L) := by
    rw [add_ofNat, add_ofNat, ← BitVec.ofNat_mul, add_ofNat]
    congr 1
    split <;> omega
  have e32769 : BitVec.ofNat 64 (L * 2 ^ 15) + BitVec.ofNat 64 L = BitVec.ofNat 64 (32769 * L) := by
    rw [add_ofNat]; congr 1; omega
  have e32 : BitVec.ofNat 64 (L * 2 ^ 5) = BitVec.ofNat 64 (32 * L) := by congr 1; omega
  unfold initializeState written initWords
  crunr [h3, h4, h9, e3, e4, e5, e15, hz, e32769, e32, scr.st0, scr.st 8 (by decide),
    scr.st 16 (by decide), scr.st 24 (by decide), off, List.getD_cons_zero, List.getD_cons_succ]
  rw [e0]
  simp only [decide_eq_true_eq]
  rfl

/-! ## Whether the exponent is 3 -/

theorem widen_byte (b : Byte) : BitVec.setWidth 64 (0#0 ++ b) = b.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft,
    Nat.zero_or]

/-- After `j` leading octets. -/
def LeadInv (s : State) (P : Addr) (j : Nat) (u : State) : Prop :=
  u.gpr .r5 = P + BitVec.ofNat 64 j ∧ u.gpr .r9 = orOf (Spec.Rsa.bytesAt s.mem P j) ∧ u.mem = s.mem ∧
    Keep [.r5, .r9, .r10, .r11, .r12] s u

theorem isThree_body {s u : State} {P : Addr} {len j : Nat} (hj : j < len - 1)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (h : LeadInv s P j u) :
    WP isa (.block (([.lbz .r11 .r5 0, .logic .or .r9 .r9 .r11, .addi .r5 .r5 1] : List Instr) ++
      ([.subi .r10 .r10 1] : List Instr))) u fun v =>
      LeadInv s P (j + 1) v ∧ v.gpr .r10 = u.gpr .r10 - BitVec.ofNat 64 1 := by
  obtain ⟨hx5, hx9, hm, k⟩ := h
  have hr : InRegions (u.rd ++ u.wr) (P + BitVec.ofNat 64 j) 1 := by
    rw [k.2.1, k.2.2]; exact hrd j (by omega)
  refine WP.mono (WP.keep [.r5, .r9, .r10, .r11] (Q := fun v =>
      v.gpr .r5 = P + BitVec.ofNat 64 (j + 1) ∧
      v.gpr .r9 = orOf (Spec.Rsa.bytesAt s.mem P j) ||| (u.mem (P + BitVec.ofNat 64 j)).setWidth 64 ∧
      v.mem = u.mem ∧ v.gpr .r10 = u.gpr .r10 - BitVec.ofNat 64 1) ?_ (by decide +kernel))
    fun v ⟨⟨h5, h9, hmv, h10⟩, kv⟩ => ⟨⟨h5, ?_, hmv.trans hm, (k.trans kv).mono (by decide)⟩, h10⟩
  · crunr [hx5, hx9, hr, widen_byte, BitVec.add_assoc, BitVec.ofNat_add, List.cons_append, List.nil_append]
  · rw [h9, bytesAt_succ, orOf_snoc, hm]

theorem sub_one {n : Nat} (h1 : 1 ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat_beq_zero {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  · rintro rfl; rfl

theorem widen_lt (b : Byte) : (b.setWidth 64).toNat < 2 ^ 8 := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (by decide))]
  exact b.isLt

private theorem foldl_or_lt (bs : List Byte) (a : BitVec 64) (ha : a.toNat < 2 ^ 8) :
    (bs.foldl (fun a b => a ||| b.setWidth 64) a).toNat < 2 ^ 8 := by
  induction bs generalizing a with
  | nil => exact ha
  | cons b bs ih =>
    rw [List.foldl_cons]
    exact ih _ (by rw [BitVec.toNat_or]; exact Nat.or_lt_two_pow ha (widen_lt b))

theorem orOf_lt (bs : List Byte) : (orOf bs).toNat < 2 ^ 8 := foldl_or_lt bs 0 (by decide)

/-- The last octet XOR 3, ORed with the leading ones: below `2^8`. -/
theorem isThree_last {s u : State} {P : Addr} {len : Nat} (h1 : 1 ≤ len)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (h : LeadInv s P (len - 1) u) :
    WP isa (.block [.lbz .r11 .r5 0, .li .r12 3, .logic .xor .r11 .r11 .r12, .logic .or .r9 .r9 .r11]) u
      fun t => (t.gpr .r9 = 0 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P len) = 3) ∧
        (t.gpr .r9).toNat < 2 ^ 8 ∧ t.mem = s.mem ∧ Keep [.r5, .r9, .r10, .r11, .r12] s t := by
  obtain ⟨hx5, hx9, hm, k⟩ := h
  have hr : InRegions (u.rd ++ u.wr) (P + BitVec.ofNat 64 (len - 1)) 1 := by
    rw [k.2.1, k.2.2]; exact hrd (len - 1) (by omega)
  refine WP.mono (WP.keep [.r9, .r11, .r12] (Q := fun t => t.gpr .r9 =
      orOf (Spec.Rsa.bytesAt s.mem P (len - 1)) |||
        ((u.mem (P + BitVec.ofNat 64 (len - 1))).setWidth 64 ^^^ 3) ∧ t.mem = u.mem) ?_
      (by decide +kernel)) fun t ⟨⟨h9, hmt⟩, kt⟩ =>
    ⟨?_, ?_, hmt.trans hm, (k.trans kt).mono (by decide)⟩
  · crunr [hx5, hx9, hr, widen_byte]
  · have hb : Spec.Rsa.bytesAt s.mem P len =
        Spec.Rsa.bytesAt s.mem P (len - 1) ++ [s.mem (P + BitVec.ofNat 64 (len - 1))] := by
      rw [← bytesAt_succ, Nat.sub_add_cancel h1]
    rw [h9, hm, hb, os2ip_eq_three]
  · rw [h9, BitVec.toNat_or, BitVec.toNat_xor]
    exact Nat.or_lt_two_pow (orOf_lt _) (Nat.xor_lt_two_pow (widen_lt _) (by decide))

/-- `isThree`: `r9` is 0 iff `e` (`len` octets at `r5`) is 3. -/
theorem isThree_ok {s : State} {P : Addr} {len : Nat} (hp : s.gpr .r5 = P)
    (hl : s.gpr .r6 = BitVec.ofNat 64 len) (h1 : 1 ≤ len) (h8 : len ≤ 8)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) :
    WP isa isThree s fun t =>
      (t.gpr .r9 = 0 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P len) = 3) ∧
        (t.gpr .r9).toNat < 2 ^ 8 ∧ t.mem = s.mem ∧ Keep [.r5, .r9, .r10, .r11, .r12] s t := by
  unfold isThree
  refine WP.seq (WP.mono (WP.keep [.r9, .r10] (Q := fun t =>
      t.gpr .r9 = 0 ∧ t.gpr .r10 = BitVec.ofNat 64 (len - 1) ∧ t.mem = s.mem)
    (by crunr [hl, sub_one h1 (by omega)]) (by decide +kernel)) fun t ⟨⟨h9, h10, hm⟩, k⟩ => ?_)
  have h0 : LeadInv s P 0 t := ⟨by rw [k.gpr (by decide), hp, BitVec.add_zero],
    by rw [h9]; rfl, hm, k.mono (by decide)⟩
  have hloop : WP isa (.ite (.zero .d .r10) (.block [])
      (countLoop .r10 [.lbz .r11 .r5 0, .logic .or .r9 .r9 .r11, .addi .r5 .r5 1])) t
      (LeadInv s P (len - 1)) := by
    refine WP.ite (decide (len - 1 = 0)) (by simp only [VG.PPC64LE.eval, State.read, Size.bits,
        BitVec.setWidth_eq, h10, ofNat_beq_zero (show len - 1 < 2 ^ 64 by omega)]) (fun hz => ?_) (fun hz => ?_)
    · have hz : len - 1 = 0 := of_decide_eq_true hz
      exact WP.block_nil (by rw [hz]; exact h0)
    · have hz : len - 1 ≠ 0 := of_decide_eq_false hz
      exact VG.Proof.Bignum.PPC64LE.wp_countdown (N := len - 1) (by omega) (by omega) (LeadInv s P)
        (fun i hi u hI _ => isThree_body (len := len) hi hrd hI) h0 h10
  exact WP.seq (WP.mono hloop fun u hu => isThree_last h1 hrd hu)

/-! ## The whole initialization -/

/-- The four words written, or zeros. -/
def InitPost (L len : Nat) (m : Mem) (B P : Addr) (t : State) : Prop :=
  if initValid L len then
    t.gpr .r3 = 1 ∧ t.mem = written m B (initWords L (decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m P len) = 3)))
  else t.gpr .r3 = 0 ∧ t.mem = written m B [0, 0, 0, 0]

theorem toNat_eq_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem init_ok {s : State} {B P : Addr} (scr : Scr s B) (h3 : s.gpr .r3 = B) (hp : s.gpr .r5 = P)
    (hrd : (s.gpr .r6).toNat ≤ 8 →
      ∀ i < (s.gpr .r6).toNat, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) :
    WP isa init s (InitPost (s.gpr .r4).toNat (s.gpr .r6).toNat s.mem B P) := by
  have hx := toNat_eq_ofNat (s.gpr .r4)
  have hy := toNat_eq_ofNat (s.gpr .r6)
  unfold init
  refine WP.seq (WP.mono (high_ok s) fun u ⟨⟨h12, hm⟩, k⟩ => ?_)
  have hev : isa.eval (.zero .d .r12) u =
      some (decide ((s.gpr .r4).toNat < 2 ^ 14 ∧ (s.gpr .r6).toNat < 2 ^ 14)) := by
    simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, h12]
    rw [hx, hy, or_shr_zero (BitVec.isLt _) (BitVec.isLt _)]
    simp only [BitVec.toNat_ofNat, BitVec.toNat_mod_cancel]
  by_cases hb : (s.gpr .r4).toNat < 2 ^ 14 ∧ (s.gpr .r6).toNat < 2 ^ 14
  · refine WP.ite true (by rw [hev, decide_eq_true hb]) (fun _ => ?_) (by simp)
    have h4 : u.gpr .r4 = BitVec.ofNat 64 (s.gpr .r4).toNat := (k.gpr (by decide)).trans hx
    have h6 : u.gpr .r6 = BitVec.ofNat 64 (s.gpr .r6).toNat := (k.gpr (by decide)).trans hy
    refine WP.seq (WP.mono (validate_ok u h4 hb.1 h6 hb.2) fun v ⟨⟨h12', hm'⟩, k'⟩ => ?_)
    have kv := k.trans k'
    have scv : Scr v B := scr.congr kv.2.2
    have hv3 : v.gpr .r3 = B := (kv.gpr (by decide)).trans h3
    by_cases hv : initValid (s.gpr .r4).toNat (s.gpr .r6).toNat
    · rw [ite_eq_left hv] at h12'
      refine WP.ite false (by simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, h12']; rfl)
        (by simp) (fun _ => ?_)
      obtain ⟨h32, h512, hmod, h1, h8⟩ := hv
      have hl : v.gpr .r6 = BitVec.ofNat 64 (s.gpr .r6).toNat := (kv.gpr (by decide)).trans hy
      have hru : ∀ i < (s.gpr .r6).toNat, InRegions (v.rd ++ v.wr) (P + BitVec.ofNat 64 i) 1 := by
        rw [kv.2.1, kv.2.2]; exact hrd h8
      refine WP.seq (WP.mono (isThree_ok ((kv.gpr (by decide)).trans hp) hl h1 h8 hru)
        fun z ⟨hzi, hz8, hmz, kz⟩ => ?_)
      have hz9 := toNat_eq_ofNat (z.gpr .r9)
      have hz4 : z.gpr .r4 = BitVec.ofNat 64 (s.gpr .r4).toNat :=
        (kz.gpr (by decide)).trans ((kv.gpr (by decide)).trans hx)
      refine WP.mono (initialize_ok (scv.congr kz.2.2) ((kz.gpr (by decide)).trans hv3) hz4 h512 hz9
        (by omega)) fun t ⟨ht, hmt⟩ => ?_
      unfold InitPost
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h32, h512, hmod, h1, h8⟩)]
      refine ⟨ht, ?_⟩
      rw [hmt, hmz, hm', hm]
      congr 2
      apply decide_eq_decide.mpr
      rw [hm', hm] at hzi
      rw [← hzi]
      exact ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => by rw [h]; rfl⟩
    · rw [ite_eq_right hv] at h12'
      refine WP.ite true (by simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, h12']; rfl)
        (fun _ => WP.mono (clear_ok scv hv3) fun t ⟨ht, hmt⟩ => ?_) (by simp)
      unfold InitPost
      rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
      exact ⟨ht, by rw [hmt, hm', hm]⟩
  · refine WP.ite false (by rw [hev, decide_eq_false hb]) (by simp)
      (fun _ => WP.mono (clear_ok (scr.congr k.2.2) ((k.gpr (by decide)).trans h3)) fun t ⟨ht, hmt⟩ => ?_)
    have hv : ¬initValid (s.gpr .r4).toNat (s.gpr .r6).toNat := by unfold initValid; omega
    unfold InitPost
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
    exact ⟨ht, by rw [hmt, hm]⟩

/-! ## The contract -/

def initPre (s : State) : Prop :=
  s.rd = [⟨s.gpr .r5, (s.gpr .r6).toNat⟩] ∧ s.wr = [⟨s.gpr .r3, 32⟩] ∧
    (s.gpr .r3).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64

def initPost (s t : State) : Prop :=
  match Spec.RsaKeyGen.primeInit (s.gpr .r4).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) with
  | none => ((t.gpr .r3).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .r3) 4 = List.replicate 4 0
  | some values => ((t.gpr .r3).setWidth 32).toNat = 1 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .r3) 4 = values.map (BitVec.ofNat 64)

def initPub (s t : State) : Prop :=
  s.sp = t.sp ∧ s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r5 = t.gpr .r5 ∧
    s.gpr .r6 = t.gpr .r6

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

private theorem result_post {s t : State}
    (h : InitPost (s.gpr .r4).toNat (s.gpr .r6).toNat s.mem (s.gpr .r3) (s.gpr .r5) t) :
    initPost s t := by
  unfold InitPost at h
  unfold initPost
  have hl : (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat).length = (s.gpr .r6).toNat := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  rw [primeInit_eq, hl]
  split at h
  · rename_i hv
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
    refine ⟨by rw [h.1]; rfl, ?_⟩
    rw [h.2, initWords, written_words]
    simp only [List.map_cons, List.map_nil, decide_eq_true_eq]
  · rename_i hv
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
    exact ⟨by rw [h.1]; rfl, by rw [h.2, written_words]; rfl⟩

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨hrd, hwr, hroom, hroome⟩ := h
  have scr : Scr s (s.gpr .r3) := ⟨by rw [hwr]; simp, hroom⟩
  have hreads : (s.gpr .r6).toNat ≤ 8 →
      ∀ i < (s.gpr .r6).toNat, InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 i) 1 :=
    fun _ i hi => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨tr, t, he, hp, k⟩ := WP.keep [.r3, .r5, .r7, .r8, .r9, .r10, .r11, .r12]
    (init_ok scr rfl rfl hreads) (by decide +kernel)
  exact ⟨tr, t, he, abiPreserved_of_keep he k (by decide) (by decide +kernel)
    (by rw [← Code.allInstrs_eq]; decide +kernel), result_post hp⟩

/-- Two runs agree on the arguments. -/
theorem init_agree {s₁ s₂ : State} (h : initPub s₁ s₂) :
    taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6]) s₁ s₂ := by
  obtain ⟨hsp, h3, h4, h5, h6⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem init_constantTime : ConstantTime isa (fun _ => True) initPub init :=
  RelCT.constantTime ((RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ h => init_agree h) (by taint_decide)).mono (fun _ _ h => h.2.2) fun _ _ h => h)

private def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 3 | _ => 0
  lr := 0
  sp := 0x3000
  mem _ := 0
  rd := [⟨0x2000, 3⟩]
  wr := [⟨0x1000, 32⟩]

theorem init_verified : Verified target init (Spec.RsaKeyGen.primeInitContract abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp h₁ h₂
    exact init_constantTime s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hp h₁ h₂
  · sig_implies [Spec.RsaKeyGen.primeInitContract, Spec.RsaKeyGen.primeInitSig,
      initContract, initPre, initPost, initPub, abi, argRegs] [initSat] using initSat

end VG.Proof.RsaKeyGen.PPC64LE.SearchInit
