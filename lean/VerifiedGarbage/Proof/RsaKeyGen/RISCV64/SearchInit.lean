module

public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.SearchInit
public import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
public import VerifiedGarbage.Proof.RsaKeyGen.InitWords
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.SearchInit
meta import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Mathlib.Tactic.SplitIfs

/-! # Starting the RSA prime search on RISC-V: correctness, constant time -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.SearchInit

open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Proof.RsaKeyGen.SearchInit
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Impl.RsaKeyGen.RISCV64.SearchInit

/-! ## Validation -/

/-- `sltu` of small numbers. -/
theorem ltu_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (if BitVec.ofNat 64 a < BitVec.ofNat 64 b then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (if a < b then 1 else 0) := by
  have : (BitVec.ofNat 64 a < BitVec.ofNat 64 b) ↔ a < b := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : a < b
  · simp only [this, h, ↓reduceIte]; rfl
  · simp only [this, h, ↓reduceIte]; rfl

theorem and7 (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n &&& BitVec.ofNat 64 7 = BitVec.ofNat 64 (n % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem toNat_eq_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `validate`: `t3` is 1 exactly for a valid width and exponent length. -/
theorem validate_ok (s : State) :
    WP isa (.block validate) s fun t =>
      (t.gpr .t3 = BitVec.ofNat 64 (if initValid (s.gpr .a1).toNat (s.gpr .a3).toNat then 1 else 0) ∧
        t.mem = s.mem) ∧ Keep [.t0, .t1, .t2, .t3] s t := by
  obtain ⟨L, hL, hx⟩ : ∃ n, n < 2 ^ 64 ∧ s.gpr .a1 = BitVec.ofNat 64 n :=
    ⟨_, (s.gpr .a1).isLt, toNat_eq_ofNat _⟩
  obtain ⟨len, hl, hy⟩ : ∃ n, n < 2 ^ 64 ∧ s.gpr .a3 = BitVec.ofNat 64 n :=
    ⟨_, (s.gpr .a3).isLt, toNat_eq_ofNat _⟩
  rw [hx, hy, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]
  refine WP.keep [.t0, .t1, .t2, .t3] ?_ (by decide +kernel)
  unfold validate
  brun [hx, hy, and7 L hL, ltu_ofNat hL (show 32 < 2 ^ 64 by decide), ltu_ofNat hL (show 513 < 2 ^ 64 by decide),
    ltu_ofNat (show L % 8 < 2 ^ 64 by omega) (show 1 < 2 ^ 64 by decide),
    ltu_ofNat hl (show 1 < 2 ^ 64 by decide), ltu_ofNat hl (show 9 < 2 ^ 64 by decide), exec_li]
  unfold initValid
  split_ifs <;> first | rfl | (exfalso; omega)

/-! ## The four words -/

theorem clear_ok {s : State} {B : Addr} (scr : Scr s B 32) (h0 : s.gpr .a0 = B) :
    WP isa (.block clear) s fun t => t.gpr .a0 = 0 ∧ t.mem = written s.mem B [0, 0, 0, 0] := by
  unfold clear written
  brun [h0, exec_li, scr.st (d := 0) (n := 8) (by decide), scr.st (d := 8) (n := 8) (by decide), scr.st (d := 16) (n := 8) (by decide),
    scr.st (d := 24) (n := 8) (by decide), scr.al8 (d := 0) (by decide) (by decide), scr.al8 (d := 8) (by decide) (by decide),
    scr.al8 (d := 16) (by decide) (by decide), scr.al8 (d := 24) (by decide) (by decide), off]
  simp only [List.getD_cons_zero, List.getD_cons_succ, BitVec.add_zero]
  exact ⟨rfl, rfl⟩

theorem initialize_ok {s : State} {B : Addr} {L k : Nat} (scr : Scr s B 32) (h0 : s.gpr .a0 = B)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 L) (hL : L ≤ 512) (h4 : s.gpr .t4 = BitVec.ofNat 64 k) (hk : k < 2 ^ 64) :
    WP isa (.block initializeState) s
      fun t => t.gpr .a0 = 1 ∧ t.mem = written s.mem B (initWords L (decide (k = 0))) := by
  have e3 := shl_ofNat L 3 (by omega)
  have e4 := shl_ofNat L 4 (by omega)
  have e5 := shl_ofNat L 5 (by omega)
  have e15 := shl_ofNat L 15 (by omega)
  have hz : BitVec.ofNat 64 (if k < 1 then 1 else 0) = BitVec.ofNat 64 (if k = 0 then 1 else 0) := by
    congr 2; exact propext ⟨fun h => by omega, fun h => by omega⟩
  unfold initializeState written initWords
  brun [h0, h1, h4, exec_li, e3, e4, e5, e15, hz, ltu_ofNat hk (show 1 < 2 ^ 64 by decide),
    scr.st (d := 0) (n := 8) (by decide), scr.st (d := 8) (n := 8) (by decide),
    scr.st (d := 16) (n := 8) (by decide), scr.st (d := 24) (n := 8) (by decide),
    scr.al8 (d := 0) (by decide) (by decide), scr.al8 (d := 8) (by decide) (by decide),
    scr.al8 (d := 16) (by decide) (by decide), scr.al8 (d := 24) (by decide) (by decide), off]
  have e0 : BitVec.ofNat 64 (L * 8) + BitVec.ofNat 64 (L * 32) +
      (BitVec.ofNat 64 (L * 16) + BitVec.ofNat 64 (L * 8)) * BitVec.ofNat 64 (if k = 0 then 1 else 0) =
      BitVec.ofNat 64 (if k = 0 then 64 * L else 40 * L) := by
    rw [add_ofNat, add_ofNat, ← BitVec.ofNat_mul, add_ofNat]
    congr 1
    split <;> omega
  have e1 : BitVec.ofNat 64 (L * 32768) + BitVec.ofNat 64 L = BitVec.ofNat 64 (32769 * L) := by
    rw [add_ofNat]; congr 1; omega
  have e2 : BitVec.ofNat 64 (L * 32) = BitVec.ofNat 64 (32 * L) := by congr 1; omega
  rw [e0, e1, e2]
  simp only [List.getD_cons_zero, List.getD_cons_succ, BitVec.add_zero, decide_eq_true_eq]
  refine ⟨?_, ?_⟩ <;> first | trivial | rfl

/-! ## Whether the exponent is 3 -/

theorem read_one (m : Mem) (a : Addr) : m.read a 1 = m a := by
  change (0#0 ++ m a : BitVec (0 + 8)) = m a
  exact BitVec.zero_width_append _ _

/-- After `j` leading octets. -/
def LeadInv (s : State) (P : Addr) (j : Nat) (u : State) : Prop :=
  u.gpr .a2 = P + BitVec.ofNat 64 j ∧ u.gpr .t4 = orOf (Spec.Rsa.bytesAt s.mem P j) ∧ u.mem = s.mem ∧
    Keep [.a2, .t0, .t4, .t5, .t6] s u

theorem isThree_body {s u : State} {P : Addr} {len j : Nat} (hj : j < len - 1)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (h : LeadInv s P j u) :
    WP isa (.block (([.load .b .t6 .a2 0, .logic .or .t4 .t4 .t6, .addi .a2 .a2 1] : List Instr) ++
      ([.addi .t5 .t5 (-1)] : List Instr))) u fun v =>
      LeadInv s P (j + 1) v ∧ v.gpr .t5 = u.gpr .t5 - BitVec.ofNat 64 1 := by
  obtain ⟨hx2, hx4, hm, k⟩ := h
  have hr : InRegions (u.rd ++ u.wr) (P + BitVec.ofNat 64 j) 1 := by
    rw [k.2.1, k.2.2]; exact hrd j (by omega)
  refine WP.mono (WP.keep [.a2, .t4, .t5, .t6] (Q := fun v =>
      v.gpr .a2 = P + BitVec.ofNat 64 (j + 1) ∧
      v.gpr .t4 = orOf (Spec.Rsa.bytesAt s.mem P j) ||| (u.mem (P + BitVec.ofNat 64 j)).setWidth 64 ∧
      v.mem = u.mem ∧ v.gpr .t5 = u.gpr .t5 - BitVec.ofNat 64 1) ?_ (by decide +kernel))
    fun v ⟨⟨h2, h4, hmv, h5⟩, kv⟩ => ⟨⟨h2, ?_, hmv.trans hm, (k.trans kv).mono (by decide)⟩, h5⟩
  · brun [hx2, hx4, hr, read_one]
  · rw [h4, bytesAt_succ, orOf_snoc, hm]

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
    WP isa (.block [.load .b .t6 .a2 0, .li .t0 3, .logic .xor .t6 .t6 .t0, .logic .or .t4 .t4 .t6]) u
      fun t => (t.gpr .t4 = 0 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P len) = 3) ∧
        (t.gpr .t4).toNat < 2 ^ 8 ∧ t.mem = s.mem ∧ Keep [.a2, .t0, .t4, .t5, .t6] s t := by
  obtain ⟨hx2, hx4, hm, k⟩ := h
  have hr : InRegions (u.rd ++ u.wr) (P + BitVec.ofNat 64 (len - 1)) 1 := by
    rw [k.2.1, k.2.2]; exact hrd (len - 1) (by omega)
  refine WP.mono (WP.keep [.t0, .t4, .t6] (Q := fun t => t.gpr .t4 =
      orOf (Spec.Rsa.bytesAt s.mem P (len - 1)) |||
        ((u.mem (P + BitVec.ofNat 64 (len - 1))).setWidth 64 ^^^ BitVec.ofNat 64 3) ∧ t.mem = u.mem) ?_
      (by decide +kernel)) fun t ⟨⟨h4, hmt⟩, kt⟩ =>
    ⟨?_, ?_, hmt.trans hm, (k.trans kt).mono (by decide)⟩
  · brun [hx2, hx4, hr, read_one, exec_li]
  · have hb : Spec.Rsa.bytesAt s.mem P len =
        Spec.Rsa.bytesAt s.mem P (len - 1) ++ [s.mem (P + BitVec.ofNat 64 (len - 1))] := by
      rw [← bytesAt_succ, Nat.sub_add_cancel h1]
    rw [h4, hm, hb, os2ip_eq_three]
    rfl
  · rw [h4, BitVec.toNat_or, BitVec.toNat_xor]
    exact Nat.or_lt_two_pow (orOf_lt _) (Nat.xor_lt_two_pow (widen_lt _) (by decide))

/-- `isThree`: `t4` is 0 iff `e` (`len` octets at `a2`) is 3. -/
theorem isThree_ok {s : State} {P : Addr} {len : Nat} (hp : s.gpr .a2 = P)
    (hl : s.gpr .a3 = BitVec.ofNat 64 len) (h1 : 1 ≤ len) (h8 : len ≤ 8)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) :
    WP isa isThree s fun t =>
      (t.gpr .t4 = 0 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P len) = 3) ∧
        (t.gpr .t4).toNat < 2 ^ 8 ∧ t.mem = s.mem ∧ Keep [.a2, .t0, .t4, .t5, .t6] s t := by
  unfold isThree
  refine WP.seq (WP.mono (WP.keep [.t4, .t5] (Q := fun t =>
      t.gpr .t4 = 0 ∧ t.gpr .t5 = BitVec.ofNat 64 (len - 1) ∧ t.mem = s.mem)
    (by brun [hl, exec_li, sub_one h1 (by omega)]; try rfl) (by decide +kernel)) fun t ⟨⟨h4, h5, hm⟩, k⟩ => ?_)
  have h0 : LeadInv s P 0 t := ⟨by rw [k.gpr (by decide), hp, BitVec.add_zero],
    by rw [h4]; rfl, hm, k.mono (by decide)⟩
  have hloop : WP isa (.ite (.zero .t5) (.block [])
      (countLoop .t5 [.load .b .t6 .a2 0, .logic .or .t4 .t4 .t6, .addi .a2 .a2 1])) t
      (LeadInv s P (len - 1)) := by
    refine WP.ite (decide (len - 1 = 0)) (by
        change some (t.gpr .t5 == 0) = _
        rw [h5, ofNat_beq_zero (show len - 1 < 2 ^ 64 by omega)]) (fun hz => ?_) (fun hz => ?_)
    · have hz : len - 1 = 0 := of_decide_eq_true hz
      exact WP.block_nil (by rw [hz]; exact h0)
    · have hz : len - 1 ≠ 0 := of_decide_eq_false hz
      exact wp_countdown (N := len - 1) (by omega) (by omega) (LeadInv s P)
        (fun i hi u hI _ => isThree_body (len := len) hi hrd hI) h0 h5
  exact WP.seq (WP.mono hloop fun u hu => isThree_last h1 hrd hu)

/-! ## The whole initialization -/

/-- The four words written, or zeros. -/
def InitPost (L len : Nat) (m : Mem) (B P : Addr) (t : State) : Prop :=
  if initValid L len then
    t.gpr .a0 = 1 ∧ t.mem = written m B (initWords L (decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m P len) = 3)))
  else t.gpr .a0 = 0 ∧ t.mem = written m B [0, 0, 0, 0]

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero r) s = some (s.gpr r == 0) := rfl

theorem init_ok {s : State} {B P : Addr} (scr : Scr s B 32) (h0 : s.gpr .a0 = B) (hp : s.gpr .a2 = P)
    (hrd : (s.gpr .a3).toNat ≤ 8 →
      ∀ i < (s.gpr .a3).toNat, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) :
    WP isa init s (InitPost (s.gpr .a1).toNat (s.gpr .a3).toNat s.mem B P) := by
  unfold init
  refine WP.seq (WP.mono (validate_ok s) fun u ⟨⟨h3, hm⟩, k⟩ => ?_)
  have scu : Scr u B 32 := scr.congr k.2.2
  have hu0 : u.gpr .a0 = B := (k.gpr (by decide)).trans h0
  by_cases hv : initValid (s.gpr .a1).toNat (s.gpr .a3).toNat
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hv)] at h3
    refine WP.ite false (by rw [eval_zero, h3]; rfl) (fun h => by cases h) fun _ => ?_
    obtain ⟨h32, h512, hmod, h1, h8⟩ := hv
    have hl : u.gpr .a3 = BitVec.ofNat 64 (s.gpr .a3).toNat := (k.gpr (by decide)).trans (toNat_eq_ofNat _)
    have hru : ∀ i < (s.gpr .a3).toNat, InRegions (u.rd ++ u.wr) (P + BitVec.ofNat 64 i) 1 := by
      rw [k.2.1, k.2.2]; exact hrd h8
    refine WP.seq (WP.mono (isThree_ok ((k.gpr (by decide)).trans hp) hl h1 h8 hru)
      fun z ⟨hzi, hz8, hmz, kz⟩ => ?_)
    have hz1 : z.gpr .a1 = BitVec.ofNat 64 (s.gpr .a1).toNat :=
      (kz.gpr (by decide)).trans ((k.gpr (by decide)).trans (toNat_eq_ofNat _))
    refine WP.mono (initialize_ok (scu.congr kz.2.2) ((kz.gpr (by decide)).trans hu0) hz1 h512
      (toNat_eq_ofNat _) (by omega)) fun t ⟨ht, hmt⟩ => ?_
    unfold InitPost
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h32, h512, hmod, h1, h8⟩)]
    refine ⟨ht, ?_⟩
    rw [hmt, hmz, hm]
    congr 2
    apply decide_eq_decide.mpr
    rw [hm] at hzi
    rw [← hzi]
    exact ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => by rw [h]; rfl⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hv)] at h3
    refine WP.ite true (by rw [eval_zero, h3]; rfl) (fun _ => WP.mono (clear_ok scu hu0) fun t ⟨ht, hmt⟩ => ?_)
      (fun h => by cases h)
    unfold InitPost
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
    exact ⟨ht, by rw [hmt, hm]⟩

/-! ## The contract -/

def initPre (s : State) : Prop :=
  s.rd = [⟨s.gpr .a2, (s.gpr .a3).toNat⟩] ∧ s.wr = [⟨s.gpr .a0, 32⟩] ∧
    (s.gpr .a0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0

def initPost (s t : State) : Prop :=
  match Spec.RsaKeyGen.primeInit (s.gpr .a1).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) with
  | none => ((t.gpr .a0).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .a0) 4 = List.replicate 4 0
  | some values => ((t.gpr .a0).setWidth 32).toNat = 1 ∧
      ∃ first, Spec.Rsa.wordsAt t.mem (s.gpr .a0) 4 =
        (values ++ [first]).map (BitVec.ofNat 64) ∧
        Spec.Entropy.RequestValid (Spec.RsaKeyGen.primeEntropy (s.gpr .a1).toNat) 0 first

def initPub (s t : State) : Prop :=
  s.sp = t.sp ∧ s.gpr .a0 = t.gpr .a0 ∧ s.gpr .a1 = t.gpr .a1 ∧ s.gpr .a2 = t.gpr .a2 ∧
    s.gpr .a3 = t.gpr .a3

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

private theorem result_post {s t : State}
    (h : InitPost (s.gpr .a1).toNat (s.gpr .a3).toNat s.mem (s.gpr .a0) (s.gpr .a2) t) :
    initPost s t := by
  unfold InitPost at h
  unfold initPost
  have hl : (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat).length = (s.gpr .a3).toNat := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  rw [primeInit_eq, hl]
  split at h
  · rename_i hv
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
    refine ⟨by rw [h.1]; rfl, _, ?_, SearchInit.first_valid hv⟩
    rw [h.2, initWords, written_words]
    simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, decide_eq_true_eq]
  · rename_i hv
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
    exact ⟨by rw [h.1]; rfl, by rw [h.2, written_words]; rfl⟩

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨hrd, hwr, hroom, hroome, hal⟩ := h
  have scr : Scr s (s.gpr .a0) 32 := Scr.of_mem (by rw [hwr]; simp) hroom hal
  have hreads : (s.gpr .a3).toNat ≤ 8 →
      ∀ i < (s.gpr .a3).toNat, InRegions (s.rd ++ s.wr) (s.gpr .a2 + BitVec.ofNat 64 i) 1 :=
    fun _ i hi => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨tr, t, he, hp, k⟩ := WP.keep [.a0, .a2, .t0, .t1, .t2, .t3, .t4, .t5, .t6]
    (init_ok scr rfl rfl hreads) (by decide +kernel)
  exact ⟨tr, t, he, abiPreserved_of_keep he k (by decide) (by decide), result_post hp⟩

/-- Two runs agree on the arguments. -/
theorem init_agree {s₁ s₂ : State} (h : initPub s₁ s₂) :
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ := by
  obtain ⟨hsp, h0, h1, h2, h3⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem init_constantTime : ConstantTime isa (fun _ => True) initPub init :=
  RelCT.constantTime ((RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ h => init_agree h) (by taint_decide)).mono (fun _ _ h => h.2.2) fun _ _ h => h)

private def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 3 | _ => 0
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

end VG.Proof.RsaKeyGen.RISCV64.SearchInit
