module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.Cached
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Ffdh.CombBitBytes
import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.Scalar
import VerifiedGarbage.Proof.Bignum.RISCV64.PubOut
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
-- separate module: the cached attempt's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # FFDH's comb on RISC-V: a row's digit

`bit_ok`: bit `k` of x, from its octets, most significant first.
`digit_ok`: the five bits `i + j rows` of row `i`'s digit. -/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64.Cached VG.Impl.Ffdh.RISCV64.Cached.Generate
open VG.Proof.Bignum.RISCV64

theorem eval_ltu' (s : State) (a b : Reg) : isa.eval (.ltu a b) s = some (decide (s.gpr a < s.gpr b)) := rfl

theorem ofNat_lt_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    decide (BitVec.ofNat 64 a < BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem ofNat_shr3 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 3 = BitVec.ofNat 64 (a / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h]
  rw [Nat.mod_eq_of_lt (by omega_arith)]

theorem ofNat_and7 (a : Nat) : BitVec.ofNat 64 a &&& BitVec.ofNat 64 7 = BitVec.ofNat 64 (a % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_mod_of_dvd _ (by decide)]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))).symm

/-- A byte's bit `j`. -/
theorem bit_bv (b : Byte) {j : Nat} (hj : j < 8) :
    (b.setWidth 64 >>> ((BitVec.ofNat 64 j).toNat % 64)) &&& BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (b.toNat / 2 ^ j % 2) := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show j < 64 by omega_arith),
    Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega_arith), Nat.shiftRight_eq_div_pow,
    show (1 : Nat) % 2 ^ 64 = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have : b.toNat / 2 ^ j % 2 ^ 1 < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt this]

/-- `bit`: `t5 :=` bit `k` (`t6`) of x, the `L` octets at `X` (`s8`), `L` in
`s11`; 0 from `8 L` up. -/
theorem bit_ok {s : State} {X : Addr} {xb : List Byte} {k : Nat}
    (h11 : s.gpr .s11 = BitVec.ofNat 64 xb.length) (h6 : s.gpr .t6 = BitVec.ofNat 64 k) (h8 : s.gpr .s8 = X)
    (hrd : ∀ n < xb.length, InRegions (s.rd ++ s.wr) (off X n) 1)
    (hval : ∀ n (h : n < xb.length), s.mem (off X n) = xb[n]) (hk : k < 2 ^ 31) (hL : 8 * xb.length < 2 ^ 31) :
    WP isa bit s fun t =>
      (t.gpr .t5 = BitVec.ofNat 64 (Spec.Rsa.os2ip xb / 2 ^ k % 2) ∧ t.mem = s.mem) ∧ Keep [.t2, .t5] s t := by
  unfold bit
  refine WP.seq (WP.mono (WP.keep [.t2] (Q := fun t => t.gpr .t2 = BitVec.ofNat 64 (8 * xb.length) ∧ t.mem = s.mem)
    (by brun [h11, ofNat_shl3' (show 8 * xb.length < 2 ^ 64 by omega_arith)]) (by rfl) (by rfl))
    fun s₁ ⟨⟨a2, m1⟩, k1⟩ => ?_)
  have g6 : s₁.gpr .t6 = BitVec.ofNat 64 k := (k1.gpr (by decide)).trans h6
  refine WP.ite (decide (k < 8 * xb.length)) (by
      rw [eval_ltu', g6, a2, ofNat_lt_ofNat (by omega_arith) (by omega_arith)]) (fun hb => ?_) (fun hb => ?_)
  · have hb' : k < 8 * xb.length := by simpa using hb
    obtain ⟨n, hn⟩ : ∃ n, n = xb.length - 1 - k / 8 := ⟨_, rfl⟩
    have hidx : n < xb.length := by omega_arith
    have l3 : InRegions (s₁.rd ++ s₁.wr) (X + BitVec.ofNat 64 n) 1 := by
      rw [k1.2.1, k1.2.2]; exact hrd _ hidx
    have v3 : (s₁.mem.read (X + BitVec.ofNat 64 n) 1).setWidth 64 = (xb[n]'hidx).setWidth 64 := by
      rw [Pub.read1_setWidth, m1]; exact congrArg (BitVec.setWidth 64) (hval _ hidx)
    refine WP.mono (WP.keep [.t2, .t5] (Q := fun t =>
        t.gpr .t5 = BitVec.ofNat 64 ((xb[n]'hidx).toNat / 2 ^ (k % 8) % 2) ∧ t.mem = s₁.mem) (by
      brun [g6, (k1.gpr (r := .s11) (by decide)).trans h11, (k1.gpr (r := .s8) (by decide)).trans h8,
        ofNat_shr3 (show k < 2 ^ 64 by omega_arith),
        ofNat_sub'' (show k / 8 ≤ xb.length by omega_arith) (show xb.length < 2 ^ 64 by omega_arith),
        ofNat_sub'' (show 1 ≤ xb.length - k / 8 by omega_arith) (show xb.length - k / 8 < 2 ^ 64 by omega_arith),
        show xb.length - k / 8 - 1 = n by omega_arith, add_ofNat_zero, l3, v3, ofNat_and7, exec_srl_reg,
        bit_bv _ (Nat.mod_lt k (show 0 < 8 by decide))]) (by rfl) (by rfl)) fun t ⟨⟨t5, tm⟩, kt⟩ =>
      ⟨⟨?_, tm.trans m1⟩, (k1.trans kt).mono (by decide)⟩
    rw [t5, CombBitBytes.os2ip_bit xb k hb']
    subst hn; rfl
  · have hb' : ¬ k < 8 * xb.length := by simpa using hb
    refine WP.mono (WP.keep [.t5] (Q := fun t => t.gpr .t5 = BitVec.ofNat 64 0 ∧ t.mem = s₁.mem)
      (by brun [Pub.pub_li0]) (by rfl) (by rfl)) fun t ⟨⟨t5, tm⟩, kt⟩ =>
        ⟨⟨?_, tm.trans m1⟩, (k1.trans kt).mono (by decide)⟩
    rw [t5]
    have hlt : Spec.Rsa.os2ip xb < 2 ^ k :=
      Nat.lt_of_lt_of_le (VG.Proof.Bignum.os2ip_lt xb) (by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega_arith))
    rw [Nat.div_eq_of_lt hlt]

theorem tooth_bv {acc b j : Nat} (hb : b < 2) (hj : j < 5) (ha : acc < 2 ^ j) :
    BitVec.ofNat 64 acc ||| BitVec.ofNat 64 b <<< j = BitVec.ofNat 64 (acc + 2 ^ j * b) := by
  have h2j : 2 ^ j ≤ 16 := Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) (show j ≤ 4 by omega_arith))
    (by decide)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show acc < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show b * 2 ^ j < 2 ^ 64 by
      have : b * 2 ^ j ≤ 1 * 16 := Nat.mul_le_mul (by omega_arith) h2j
      omega_arith),
    Nat.mod_eq_of_lt (show acc + 2 ^ j * b < 2 ^ 64 by
      have : 2 ^ j * b ≤ 16 * 1 := Nat.mul_le_mul h2j (by omega_arith)
      omega_arith),
    Nat.or_comm, Nat.mul_comm b, ← Nat.two_pow_add_eq_or_of_lt ha, Nat.add_comm]

/-- What `bit` reads: the rows (`s7`), and the `L` octets of x at `X`
(`s8`), `L` in `s11`. -/
structure XCtx (s : State) (X : Addr) (xb : List Byte) (rows : Nat) : Prop where
  h11 : s.gpr .s11 = BitVec.ofNat 64 xb.length
  h7 : s.gpr .s7 = BitVec.ofNat 64 rows
  h8 : s.gpr .s8 = X
  hrd : ∀ n < xb.length, InRegions (s.rd ++ s.wr) (off X n) 1
  hval : ∀ n (h : n < xb.length), s.mem (off X n) = xb[n]
  hL : 8 * xb.length < 2 ^ 31

/-- The registers `digit` writes. -/
def digitRegs : List Reg := [.a1, .t2, .t5, .t6]

theorem XCtx.keep {s t : State} {X : Addr} {xb : List Byte} {rows : Nat} (h : XCtx s X xb rows)
    (hm : t.mem = s.mem) (k : Keep digitRegs s t) : XCtx t X xb rows :=
  ⟨(k.gpr (by decide)).trans h.h11, (k.gpr (by decide)).trans h.h7, (k.gpr (by decide)).trans h.h8,
    fun n hn => by rw [k.2.1, k.2.2]; exact h.hrd n hn, fun n hn => by rw [hm]; exact h.hval n hn, h.hL⟩

/-- `tooth j`: `a1 := acc + 2^j` bit `i + j rows` of x, for `acc < 2^j`; `t6`
on to the next tooth's bit. -/
theorem tooth_ok {s : State} {X : Addr} {xb : List Byte} {i rows j acc : Nat} (h : XCtx s X xb rows)
    (h6 : s.gpr .t6 = BitVec.ofNat 64 (i + j * rows)) (hj : j < 5) (hk : i + 5 * rows < 2 ^ 31)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 acc) (ha : acc < 2 ^ j) :
    WP isa (tooth j) s fun t =>
      (t.gpr .a1 = BitVec.ofNat 64 (acc + 2 ^ j * Rsa.FixedBaseComb.bit (Spec.Rsa.os2ip xb) (i + j * rows)) ∧
        t.gpr .t6 = BitVec.ofNat 64 (i + (j + 1) * rows) ∧ XCtx t X xb rows ∧ t.mem = s.mem) ∧
        Keep digitRegs s t := by
  have hjr : j * rows ≤ 4 * rows := Nat.mul_le_mul_right _ (by omega_arith)
  unfold tooth
  refine WP.seq (WP.mono (bit_ok h.h11 h6 h.h8 h.hrd h.hval (by omega_arith) h.hL) fun t ⟨⟨a5, m⟩, k⟩ => ?_)
  have hb : Spec.Rsa.os2ip xb / 2 ^ (i + j * rows) % 2 < 2 := Nat.mod_lt _ (by decide)
  have g1 : t.gpr .a1 = BitVec.ofNat 64 acc := (k.gpr (by decide)).trans h1
  have g6 : t.gpr .t6 = BitVec.ofNat 64 (i + j * rows) := (k.gpr (by decide)).trans h6
  have g7 : t.gpr .s7 = BitVec.ofNat 64 rows := (k.gpr (by decide)).trans h.h7
  have e6 : BitVec.ofNat 64 (i + j * rows) + BitVec.ofNat 64 rows = BitVec.ofNat 64 (i + (j + 1) * rows) := by
    rw [← BitVec.ofNat_add, Nat.succ_mul, Nat.add_assoc]
  have post : ∀ u : State, (u.gpr .a1 = BitVec.ofNat 64 (acc + 2 ^ j *
      Rsa.FixedBaseComb.bit (Spec.Rsa.os2ip xb) (i + j * rows)) ∧
      u.gpr .t6 = BitVec.ofNat 64 (i + (j + 1) * rows) ∧ u.mem = t.mem) ∧ Keep [.t5, .a1, .t6] t u →
      (u.gpr .a1 = BitVec.ofNat 64 (acc + 2 ^ j * Rsa.FixedBaseComb.bit (Spec.Rsa.os2ip xb) (i + j * rows)) ∧
        u.gpr .t6 = BitVec.ofNat 64 (i + (j + 1) * rows) ∧ XCtx u X xb rows ∧ u.mem = s.mem) ∧
        Keep digitRegs s u :=
    fun u ⟨⟨b1, b6, bm⟩, bk⟩ => ⟨⟨b1, b6, h.keep (bm.trans m) ((k.trans bk).mono (by decide)), bm.trans m⟩,
      (k.trans bk).mono (by decide)⟩
  by_cases h0 : j = 0
  · subst h0
    have ha0 : acc = 0 := by omega_arith
    subst ha0
    simp only [ite_true, List.nil_append]
    refine WP.mono (WP.keep [.t5, .a1, .t6] ?_ (by rfl) (by rfl)) post
    brun [a5, g1, g6, g7, e6]
    rw [Nat.zero_add, Nat.one_mul]
    exact BitVec.zero_or
  · simp only [h0, ite_false, List.singleton_append]
    refine WP.mono (WP.keep [.t5, .a1, .t6] ?_ (by rfl) (by rfl)) post
    brun [a5, g1, g6, g7, e6, tooth_bv hb hj ha, show j < 64 by omega_arith]
    rfl

/-- The comb's digit of row `i`, for `rows` rows: `FixedBaseComb.digit` for
`rows = rows bits`. -/
def combDigit (x i rows : Nat) : Nat :=
  Rsa.FixedBaseComb.bit x i + 2 * Rsa.FixedBaseComb.bit x (i + rows) +
    4 * Rsa.FixedBaseComb.bit x (i + 2 * rows) + 8 * Rsa.FixedBaseComb.bit x (i + 3 * rows) +
    16 * Rsa.FixedBaseComb.bit x (i + 4 * rows)

theorem combDigit_eq (bits x i : Nat) :
    combDigit x i (Spec.Rsa.FixedBaseComb.rows bits) = Rsa.FixedBaseComb.digit bits x i := rfl

theorem seqs_teeth : seqs ((List.range 5).map tooth) =
    .seq (tooth 0) (.seq (tooth 1) (.seq (tooth 2) (.seq (tooth 3) (tooth 4)))) := rfl

/-- `digit`: `a1 :=` row `i`'s digit of x, for `i + 1` in `s9`. -/
theorem digit_ok {s : State} {X : Addr} {xb : List Byte} {i rows : Nat} (h : XCtx s X xb rows)
    (h9 : s.gpr .s9 = BitVec.ofNat 64 (i + 1)) (hk : i + 5 * rows < 2 ^ 31) :
    WP isa digit s fun t =>
      (t.gpr .a1 = BitVec.ofNat 64 (combDigit (Spec.Rsa.os2ip xb) i rows) ∧ t.mem = s.mem) ∧
        Keep digitRegs s t := by
  unfold digit
  rw [seqs_teeth]
  have hb := Rsa.FixedBaseComb.bit_lt (Spec.Rsa.os2ip xb)
  refine WP.seq (WP.mono (WP.keep [.a1, .t6] (Q := fun t => t.gpr .a1 = BitVec.ofNat 64 0 ∧
    t.gpr .t6 = BitVec.ofNat 64 (i + 0 * rows) ∧ t.mem = s.mem)
    (by brun [h9, Pub.pub_li0, exec_addi_neg_lit (show 1 ≤ 2048 by decide),
          ofNat_sub'' (show 1 ≤ i + 1 by omega_arith) (show i + 1 < 2 ^ 64 by omega_arith), Nat.add_sub_cancel]
        rw [Nat.zero_mul, Nat.add_zero])
      (by rfl) (by rfl))
    fun t₀ ⟨⟨a0, b0, m0⟩, k0⟩ => ?_)
  have c0 := h.keep m0 (k0.mono (by decide))
  refine WP.seq (WP.mono (tooth_ok (j := 0) c0 b0 (by decide) hk a0 (by decide)) fun t₁ ⟨⟨a1, b1, c1, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (tooth_ok (j := 1) c1 b1 (by decide) hk a1 (by have := hb (i + 0 * rows); omega_arith))
    fun t₂ ⟨⟨a2, b2, c2, m2⟩, k2⟩ => ?_)
  refine WP.seq (WP.mono (tooth_ok (j := 2) c2 b2 (by decide) hk a2
    (by have := hb (i + 0 * rows); have := hb (i + 1 * rows); omega_arith)) fun t₃ ⟨⟨a3, b3, c3, m3⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (tooth_ok (j := 3) c3 b3 (by decide) hk a3
    (by have := hb (i + 0 * rows); have := hb (i + 1 * rows); have := hb (i + 2 * rows); omega_arith))
    fun t₄ ⟨⟨a4, b4, c4, m4⟩, k4⟩ => ?_)
  refine WP.mono (tooth_ok (j := 4) c4 b4 (by decide) hk a4
    (by have := hb (i + 0 * rows); have := hb (i + 1 * rows); have := hb (i + 2 * rows)
        have := hb (i + 3 * rows); omega_arith)) fun t ⟨⟨a5, _, _, m5⟩, k5⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · rw [a5]
    unfold combDigit
    simp only [Nat.zero_add, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.pow_zero, Nat.pow_one,
      show (2 : Nat) ^ 2 = 4 from rfl, show (2 : Nat) ^ 3 = 8 from rfl, show (2 : Nat) ^ 4 = 16 from rfl]
  · rw [m5, m4, m3, m2, m1, m0]
  · have k05 := (((((k0.mono (rs' := digitRegs) (by decide)).trans k1).trans k2).trans k3).trans k4).trans k5
    exact k05.mono (by decide)

end VG.Proof.Ffdh.RISCV64.Cached
