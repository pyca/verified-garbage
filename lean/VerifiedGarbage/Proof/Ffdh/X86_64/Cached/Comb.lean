module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Table
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.CombBitBytes
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.TableLoops
import VerifiedGarbage.Proof.MlKem.X86_64.S4Squeeze

/-! # FFDH key generation from the context on x86-64: the comb

`aY := g^x mod p` from the context's table: for the rows `i` from the top
down, one square and the product with the entry of the digit of row `i`,
which `select` reads by scanning all 32 entries under an equality mask. -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.Cached VG.Impl.Ffdh.X86_64.Cached.Generate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64 (ModCtx)

/-! ## A bit of the scalar -/

theorem shr3 {k : Nat} (_hk : k < 2 ^ 64) : BitVec.ofNat 64 k >>> 3 = BitVec.ofNat 64 (k / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt _hk]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem shl3 {k : Nat} (_hk : 8 * k < 2 ^ 64) : BitVec.ofNat 64 k <<< 3 = BitVec.ofNat 64 (8 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem and7 (k : Nat) : BitVec.ofNat 64 k &&& BitVec.signExtend 64 (7 : BitVec 32) = BitVec.ofNat 64 (k % 8) := by
  rw [show BitVec.signExtend 64 (7 : BitVec 32) = BitVec.ofNat 64 7 from by decide]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem sub_ofNat {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem byteAddr (xp : Addr) {i : Nat} (hi : 1 ≤ i) (hi' : i < 2 ^ 64) :
    xp + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 (-1) = xp + BitVec.ofNat 64 (i - 1) := by
  rw [show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.mul_one, BitVec.add_assoc]
  refine congrArg (xp + ·) (BitVec.eq_of_toNat_eq ?_)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (BitVec.ofInt 64 (-1)).toNat = 2 ^ 64 - 1 by decide]
  omega

theorem byteBit (b : Byte) {j : Nat} (_hj : j < 8) :
    (b.setWidth 64 >>> j) &&& (1 : BitVec 64) = BitVec.ofNat 64 (b.toNat / 2 ^ j % 2) := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (by omega), show (1 : Nat) % 2 ^ 64 = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (a := b.toNat / 2 ^ j % 2 ^ 1) (by omega)]

theorem mod8_64 (k : Nat) : (BitVec.ofNat 64 (k % 8)).toNat % 64 = k % 8 := by
  rw [BitVec.toNat_ofNat]; omega

/-- The bit `k` of a number of `L` bytes past them is 0. -/
theorem os2ip_bit_high (xb : List Byte) {k : Nat} (hk : 8 * xb.length ≤ k) : Spec.Rsa.os2ip xb / 2 ^ k % 2 = 0 := by
  have hlt : Spec.Rsa.os2ip xb < 2 ^ k := by
    have h1 := os2ip_lt xb
    have h2 : 256 ^ xb.length ≤ 2 ^ k := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) hk
    omega
  rw [Nat.div_eq_of_lt hlt]

/-- `rdx :=` bit `k` of `x`, the `L` bytes at `rsi`. -/
theorem bit_ok {s : State} {xp : Addr} {xb : List Byte} {k : Nat} (hax : s.gpr .rax = BitVec.ofNat 64 k)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 xb.length) (hsi : s.gpr .rsi = xp)
    (hrd : ∀ i < xb.length, InRegions (s.rd ++ s.wr) (xp + BitVec.ofNat 64 i) 1)
    (hval : ∀ i (h : i < xb.length), s.mem (xp + BitVec.ofNat 64 i) = xb[i])
    (hk : k < 2 ^ 32) (hL : 8 * xb.length < 2 ^ 32) :
    WP isa bit s fun t => t.gpr .rdx = BitVec.ofNat 64 (Spec.Rsa.os2ip xb / 2 ^ k % 2) ∧ t.mem = s.mem ∧
      Keep [.rax, .rdx, .r8, .r10, .rcx] s t := by
  unfold bit
  refine WP.seq (WP.mono (WP.keep [.rdx, .rax] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 (8 * xb.length) ∧
      t.cf = some (decide (k < 8 * xb.length)) ∧ t.mem = s.mem ∧ t.gpr .rax = BitVec.ofNat 64 k) (by
    xrun [h9, hax, shl3 (show 8 * xb.length < 2 ^ 64 by omega)]
    simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]) rfl) fun s₁ ⟨⟨h1, hc, hm, ha⟩, k₁⟩ => ?_)
  refine WP.ite (decide (k < 8 * xb.length)) (by simp [eval, hc]) (fun hb => ?_) (fun hb => ?_)
  · have hb' : k < 8 * xb.length := by simpa using hb
    have hi : xb.length - k / 8 - 1 < xb.length := by omega
    have e1 : xb.length - k / 8 - 1 = xb.length - 1 - k / 8 := by omega
    have hr : InRegions (s₁.rd ++ s₁.wr) (xp + BitVec.ofNat 64 (xb.length - k / 8 - 1)) 1 := by
      rw [k₁.2.1, k₁.2.2]; exact hrd _ hi
    have hv : s₁.mem (xp + BitVec.ofNat 64 (xb.length - k / 8 - 1)) = xb[xb.length - 1 - k / 8] := by
      rw [hm]; simp only [e1]; exact hval _ (by omega)
    have hsi₁ : s₁.gpr .rsi = xp := (k₁.gpr (by decide)).trans hsi
    have h9₁ : s₁.gpr .r9 = BitVec.ofNat 64 xb.length := (k₁.gpr (by decide)).trans h9
    refine WP.mono (WP.keep [.r8, .r10, .rdx, .rcx] (Q := fun t =>
        t.gpr .rdx = BitVec.ofNat 64 (xb[xb.length - 1 - k / 8].toNat / 2 ^ (k % 8) % 2) ∧ t.mem = s₁.mem) (by
      unfold bitBody
      xrun [State.ea, ha, h9₁, hsi₁, shr3 (show k < 2 ^ 64 by omega), sub_ofNat (show k / 8 ≤ xb.length by omega)
        (show xb.length < 2 ^ 64 by omega), byteAddr xp (show 1 ≤ xb.length - k / 8 by omega) (by omega), hr, hv, and7,
        execShiftCl, VarShiftOp.eval, mod8_64 k, byteBit _ (Nat.mod_lt k (show 0 < 8 by decide))]) rfl) fun t ⟨⟨h1, h2⟩, k₂⟩ => ⟨?_, h2.trans hm, (k₁.trans k₂).mono (by decide)⟩
    rw [h1, CombBitBytes.os2ip_bit xb k hb']
  · have hb' : ¬k < 8 * xb.length := by simpa using hb
    refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = 0 ∧ t.mem = s₁.mem) (by xrun) rfl)
      fun t ⟨⟨h1, h2⟩, k₂⟩ => ⟨?_, h2.trans hm, (k₁.trans k₂).mono (by decide)⟩
    rw [h1, os2ip_bit_high xb (by omega)]; rfl

/-! ## A row's digit -/

theorem imul3_low' (a : BitVec 64) (b : BitVec 32) :
    BitVec.ofInt 64 (a.toInt * (b.signExtend 64).toInt) = a * b.signExtend 64 := by
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt]

theorem mul_imm {a j : Nat} (hj : j < 2 ^ 31) :
    BitVec.ofNat 64 a * BitVec.signExtend 64 (BitVec.ofNat 32 j) = BitVec.ofNat 64 (a * j) := by
  rw [sx_ofNat hj]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  exact (Nat.mul_mod _ _ _).symm

theorem or_bit {S b j : Nat} (hS : S < 2 ^ j) (hb : b < 2) (hj : j < 63) :
    BitVec.ofNat 64 S ||| BitVec.ofNat 64 (b * 2 ^ j) = BitVec.ofNat 64 (S + b * 2 ^ j) := by
  have h2 : 2 ^ j < 2 ^ 63 := Nat.pow_lt_pow_right (by decide) hj
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
  · simp
  · rw [Nat.one_mul, Nat.mod_eq_of_lt (show S < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 2 ^ j < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show S + 2 ^ j < 2 ^ 64 by omega), Nat.or_two_pow_eq_add_of_lt hS]

theorem shl_bit {b j : Nat} (hb : b < 2) (hj : j < 63) :
    BitVec.ofNat 64 b <<< j = BitVec.ofNat 64 (b * 2 ^ j) := by
  have h2 : 2 ^ j < 2 ^ 63 := Nat.pow_lt_pow_right (by decide) hj
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b * 2 ^ j < 2 ^ 64 by
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> omega), Nat.mul_comm]

/-- Tooth `j`'s bit index: `rax := i + j rows`, from `iI = i + 1` and `iRows`. -/
theorem toothA_ok {s : State} {O : Addr} {Zs w : Nat} {mi : BitVec 64} (hg : Good s O Zs w mi)
    (hZ : 8 * 32 ≤ Zs) {i rows j : Nat} (hj : j < 5)
    (hI : word s.mem O (8 * iI) = BitVec.ofNat 64 (i + 1)) (hR : word s.mem O (8 * iRows) = BitVec.ofNat 64 rows) :
    WP isa (.block [.mov .rax (.mem (hdr iI)), .alu .sub .rax (.imm 1), .mov .rdx (.mem (hdr iRows)),
      .imul3 .rdx .rdx (BitVec.ofNat 32 j), .alu .add .rax (.reg .rdx)]) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (i + j * rows) ∧ t.mem = s.mem ∧ Keep [.rax, .rdx] s t := by
  have hl : ∀ k < 32, InRegions (s.rd ++ s.wr) (off O (8 * k)) 8 := fun k hk => hg.scr.ld (by omega)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (i + j * rows) ∧
      t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl iI (by decide), hl iRows (by decide), hI, hR, ofNat_succ_sub_one,
      execImul3, imul3_low', mul_imm (show j < 2 ^ 31 by omega), BitVec.ofNat_add_ofNat]
    rw [Nat.mul_comm]) rfl) fun t ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩

/-- Tooth `j` of row `i`: `r13 := r13 + 2^j` bit `i + j rows` of `x`. -/
theorem tooth_ok {s : State} {O : Addr} {Zs w : Nat} {mi : BitVec 64} (hg : Good s O Zs w mi)
    (hZ : 8 * 32 ≤ Zs) {xp : Addr} {xb : List Byte} {i rows j S : Nat} (hj : j < 5)
    (hI : word s.mem O (8 * iI) = BitVec.ofNat 64 (i + 1)) (hR : word s.mem O (8 * iRows) = BitVec.ofNat 64 rows)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 xb.length) (hsi : s.gpr .rsi = xp)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 S) (hS : S < 2 ^ j)
    (hrd : ∀ i < xb.length, InRegions (s.rd ++ s.wr) (xp + BitVec.ofNat 64 i) 1)
    (hval : ∀ i (h : i < xb.length), s.mem (xp + BitVec.ofNat 64 i) = xb[i])
    (hi : i < rows) (hr : 5 * rows < 2 ^ 31) (hL : 8 * xb.length < 2 ^ 32) :
    WP isa (tooth j) s fun t =>
      t.gpr .r13 = BitVec.ofNat 64 (S + Spec.Rsa.os2ip xb / 2 ^ (i + j * rows) % 2 * 2 ^ j) ∧ t.mem = s.mem ∧
      Keep [.rax, .rdx, .r8, .r10, .rcx, .r13] s t := by
  unfold tooth
  refine WP.seq (WP.mono (toothA_ok hg hZ hj hI hR) fun s₁ ⟨ha₁, hm₁, k₁⟩ => ?_)
  have hk : i + j * rows < 2 ^ 32 := by have := Nat.mul_le_mul_right rows (show j ≤ 5 by omega); omega
  refine WP.seq (WP.mono (bit_ok ha₁ ((k₁.gpr (by decide)).trans h9) ((k₁.gpr (by decide)).trans hsi)
    (fun i hi => by rw [k₁.2.1, k₁.2.2]; exact hrd i hi) (fun i hi => by rw [hm₁]; exact hval i hi) hk hL)
    fun s₂ ⟨hd₂, hm₂, k₂⟩ => ?_)
  have h13₂ : s₂.gpr .r13 = BitVec.ofNat 64 S := ((k₁.trans k₂).gpr (by decide)).trans h13
  have hb : Spec.Rsa.os2ip xb / 2 ^ (i + j * rows) % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases hj0 : j = 0
  · subst hj0
    refine WP.mono (WP.keep [.r13] (Q := fun t => t.gpr .r13 =
        BitVec.ofNat 64 (S + Spec.Rsa.os2ip xb / 2 ^ (i + 0 * rows) % 2 * 2 ^ 0) ∧ t.mem = s₂.mem) (by
      simp only [ite_true, List.nil_append]
      xrun [hd₂, h13₂]
      have := or_bit (j := 0) hS hb (by decide)
      simpa only [Nat.pow_zero, Nat.mul_one] using this) rfl)
      fun t ⟨⟨h1, h2⟩, k₃⟩ => ⟨h1, h2.trans (hm₂.trans hm₁), ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · have hj1 : 1 ≤ j := by omega
    have hj63 : j ≤ 63 := by omega
    refine WP.mono (WP.keep [.rdx, .r13] (Q := fun t => t.gpr .r13 =
        BitVec.ofNat 64 (S + Spec.Rsa.os2ip xb / 2 ^ (i + j * rows) % 2 * 2 ^ j) ∧ t.mem = s₂.mem) (by
      rw [ite_eq_right hj0]
      xrun [List.cons_append, List.nil_append, hd₂, h13₂, hj1, hj63, execShift, shl_bit hb (show j < 63 by omega), or_bit hS hb (show j < 63 by omega)])
      (by rw [ite_eq_right hj0]; rfl))
      fun t ⟨⟨h1, h2⟩, k₃⟩ => ⟨h1, h2.trans (hm₂.trans hm₁), ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- The first `j` teeth of row `i`'s digit. -/
def digitPart (x i rows : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => digitPart x i rows j + x / 2 ^ (i + j * rows) % 2 * 2 ^ j

theorem digitPart_lt (x i rows : Nat) : ∀ j, digitPart x i rows j < 2 ^ j
  | 0 => by simp [digitPart]
  | j + 1 => by
    have := digitPart_lt x i rows j
    have : x / 2 ^ (i + j * rows) % 2 < 2 := Nat.mod_lt _ (by decide)
    rw [digitPart, Nat.pow_succ]
    rcases (show x / 2 ^ (i + j * rows) % 2 = 0 ∨ x / 2 ^ (i + j * rows) % 2 = 1 by omega) with h | h <;>
      rw [h] <;> omega

theorem digitPart_five (bits x i : Nat) :
    digitPart x i (Spec.Rsa.FixedBaseComb.rows bits) 5 = Rsa.FixedBaseComb.digit bits x i := by
  simp only [digitPart, Rsa.FixedBaseComb.digit, Rsa.FixedBaseComb.bit, Nat.zero_mul, Nat.add_zero, Nat.one_mul,
    Nat.pow_zero, Nat.mul_one, Nat.zero_add, show (2 : Nat) ^ 1 = 2 from rfl, show (2 : Nat) ^ 2 = 4 from rfl,
    show (2 : Nat) ^ 3 = 8 from rfl, show (2 : Nat) ^ 4 = 16 from rfl]
  omega

/-- `r13 :=` row `i`'s digit, from `iXp`, `iXl`, `iI = i + 1` and `iRows`. -/
theorem digit_ok {s : State} {O : Addr} {Zs w : Nat} {mi : BitVec 64} (hg : Good s O Zs w mi)
    (hZ : 8 * 32 ≤ Zs) {xp : Addr} {xb : List Byte} {i bits : Nat}
    (hI : word s.mem O (8 * iI) = BitVec.ofNat 64 (i + 1))
    (hR : word s.mem O (8 * iRows) = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits))
    (hXp : word s.mem O (8 * iXp) = xp) (hXl : word s.mem O (8 * iXl) = BitVec.ofNat 64 xb.length)
    (hrd : ∀ i < xb.length, InRegions (s.rd ++ s.wr) (xp + BitVec.ofNat 64 i) 1)
    (hval : ∀ i (h : i < xb.length), s.mem (xp + BitVec.ofNat 64 i) = xb[i])
    (hi : i < Spec.Rsa.FixedBaseComb.rows bits) (hr : 5 * Spec.Rsa.FixedBaseComb.rows bits < 2 ^ 31)
    (hL : 8 * xb.length < 2 ^ 32) :
    WP isa digit s fun t => t.gpr .r13 = BitVec.ofNat 64 (Rsa.FixedBaseComb.digit bits (Spec.Rsa.os2ip xb) i) ∧
      t.mem = s.mem ∧ Keep [.rsi, .r9, .rax, .rdx, .r8, .r10, .rcx, .r13] s t := by
  have hl : ∀ k < 32, InRegions (s.rd ++ s.wr) (off O (8 * k)) 8 := fun k hk => hg.scr.ld (by omega)
  unfold digit
  refine WP.seq (WP.mono (WP.keep [.rsi, .r9, .r13] (Q := fun t => t.gpr .rsi = xp ∧
      t.gpr .r9 = BitVec.ofNat 64 xb.length ∧ t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl iXp (by decide), hl iXl (by decide), hXp, hXl]) rfl)
    fun s₁ ⟨⟨hsi, h9, h13, hm₁⟩, k₁⟩ => ?_)
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .r13 = BitVec.ofNat 64 (digitPart (Spec.Rsa.os2ip xb) i (Spec.Rsa.FixedBaseComb.rows bits) j) ∧
      t.mem = s.mem ∧ Keep [.r13, .rax, .rdx, .r8, .r10, .rcx] s₁ t
  have step : ∀ j < 5, ∀ t, Inv j t → WP isa (tooth j) t (Inv (j + 1)) := by
    intro j hj t ⟨h13t, hmt, kt⟩
    have hgt : Good t O Zs w mi :=
      ⟨hg.scr.congr ((k₁.trans kt).2.2), ((k₁.trans kt).gpr (by decide)).trans hg.rdi, by rw [hmt]; exact hg.hdr⟩
    refine WP.mono (tooth_ok hgt hZ hj (by rw [hmt]; exact hI) (by rw [hmt]; exact hR)
      ((kt.gpr (by decide)).trans h9) ((kt.gpr (by decide)).trans hsi) h13t (digitPart_lt _ _ _ j)
      (fun i hi => by rw [(k₁.trans kt).2.1, (k₁.trans kt).2.2]; exact hrd i hi) (fun i hi => by rw [hmt]; exact hval i hi) hi hr hL)
      fun u ⟨h13u, hmu, ku⟩ => ⟨h13u, hmu.trans hmt, (kt.trans ku).mono (by decide)⟩
  have h0 : Inv 0 s₁ := ⟨h13, hm₁, Keep.refl _ _⟩
  change WP isa (.seq (tooth 0) (.seq (tooth 1) (.seq (tooth 2) (.seq (tooth 3) (tooth 4))))) s₁ _
  refine WP.seq (WP.mono (step 0 (by decide) _ h0) fun t₁ h₁ => WP.seq (WP.mono (step 1 (by decide) _ h₁)
    fun t₂ h₂ => WP.seq (WP.mono (step 2 (by decide) _ h₂) fun t₃ h₃ => WP.seq (WP.mono (step 3 (by decide) _ h₃)
      fun t₄ h₄ => WP.mono (step 4 (by decide) _ h₄) fun t ⟨h13t, hmt, kt⟩ => ?_))))
  exact ⟨by rw [h13t, digitPart_five], hmt, (k₁.trans kt).mono (by decide)⟩

/-! ## Selecting an entry -/

/-- The mask of `e = d`. -/
def eqMask (e d : Nat) : BitVec 64 := if e = d then BitVec.allOnes 64 else 0#64

theorem sbb_mask {e d : Nat} (he : e < 2 ^ 64) (hd : d < 2 ^ 64) :
    0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide ((BitVec.ofNat 64 e ^^^ BitVec.ofNat 64 d).toNat <
      BitVec.toNat (1 : BitVec 64)))) = eqMask e d := by
  unfold eqMask
  by_cases h : e = d
  · subst h
    rw [BitVec.xor_self, ite_eq_left rfl]
    decide
  · have hne : BitVec.ofNat 64 e ^^^ BitVec.ofNat 64 d ≠ 0#64 := fun hx => h (by
      have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp hx)
      simpa [Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hd] using this)
    have h1 : ¬(BitVec.ofNat 64 e ^^^ BitVec.ofNat 64 d).toNat < BitVec.toNat (1 : BitVec 64) := by
      intro hl
      apply hne
      apply BitVec.eq_of_toNat_eq
      rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl] at hl
      rw [show (0#64).toNat = 0 from rfl]; omega
    rw [decide_eq_false h1, ite_eq_right h]
    decide

theorem ofNat_add_two (e : Nat) : BitVec.ofNat 64 e + 2 = BitVec.ofNat 64 (e + 2) := by
  rw [BitVec.ofNat_add]; rfl

theorem ofNat_add_one' (e : Nat) : BitVec.ofNat 64 e + 1 = BitVec.ofNat 64 (e + 1) := by
  rw [BitVec.ofNat_add]; rfl

/-- `rdx :=` the mask of `iE = r13`, `rax := iE + 2`. -/
theorem mask_ok {s : State} {O : Addr} {Zs w : Nat} {mi : BitVec 64} (hg : Good s O Zs w mi)
    (hZ : 8 * 32 ≤ Zs) {e d : Nat} (hE : word s.mem O (8 * iE) = BitVec.ofNat 64 e)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 d) (he : e < 32) (hd : d < 32) :
    WP isa (.block [.mov .rax (.mem (hdr iE)), .alu .xor .rax (.reg .r13), .alu .cmp .rax (.imm 1),
      .alu .sbb .rdx (.reg .rdx), .mov .rax (.mem (hdr iE)), .alu .add .rax (.imm 2)]) s fun t =>
      t.gpr .rdx = eqMask e d ∧ t.gpr .rax = BitVec.ofNat 64 (e + 2) ∧ t.mem = s.mem ∧ Keep [.rax, .rdx] s t := by
  have hl : ∀ k < 32, InRegions (s.rd ++ s.wr) (off O (8 * k)) 8 := fun k hk => hg.scr.ld (by omega)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.gpr .rdx = eqMask e d ∧ t.gpr .rax = BitVec.ofNat 64 (e + 2) ∧
      t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl iE (by decide), hE, h13, sbb_mask (show e < 2 ^ 64 by omega) (show d < 2 ^ 64 by omega),
      ofNat_add_two]) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩

/-- Word `i` of the selected entry after the entries below `e`. -/
def sel (E : Nat → Nat → BitVec 64) (d e i : Nat) : BitVec 64 := if d < e then E d i else 0#64

theorem mask_sel (E : Nat → Nat → BitVec 64) (d e i : Nat) :
    E e i &&& eqMask e d ||| sel E d e i = sel E d (e + 1) i := by
  unfold eqMask sel
  by_cases h : e = d
  · subst h
    rw [ite_eq_left rfl, ite_eq_right (Nat.lt_irrefl e), ite_eq_left (Nat.lt_succ_self e), BitVec.and_allOnes,
      BitVec.or_zero]
  · rw [ite_eq_right h, BitVec.and_zero, BitVec.zero_or]
    by_cases h' : d < e
    · rw [ite_eq_left h', ite_eq_left (by omega)]
    · rw [ite_eq_right h', ite_eq_right (by omega)]

/-- After `j` words of entry `e`'s scan, from `t₀`. -/
structure SelW (t₀ : State) (D : Addr) (eD : Nat) (E : Nat → Nat → BitVec 64) (d e j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r14] t₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  done : ∀ i < j, word t.mem D (eD + 8 * i) = sel E d (e + 1) i
  frame : Outside D eD (8 * j) t₀.mem t.mem

theorem selStep_ok {t₀ : State} {S D : Addr} {eS eD w : Nat} {E : Nat → Nat → BitVec 64} {d e : Nat}
    (hsi : t₀.gpr .rsi = off S eS) (hbx : t₀.gpr .rbx = off D eD) (h12 : t₀.gpr .r12 = BitVec.ofNat 64 w)
    (hdx : t₀.gpr .rdx = eqMask e d) (hw : w < 2 ^ 32) (hD : eD + 8 * w ≤ 2 ^ 64)
    (hrd : ∀ j < w, InRegions (t₀.rd ++ t₀.wr) (off S (eS + 8 * j)) 8)
    (hld : ∀ j < w, InRegions (t₀.rd ++ t₀.wr) (off D (eD + 8 * j)) 8)
    (hwr : ∀ j < w, InRegions t₀.wr (off D (eD + 8 * j)) 8)
    (hsep : ∀ j < w, ∀ b < 8, ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * w ≤ ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b))
    (hS : ∀ j < w, word t₀.mem S (eS + 8 * j) = E e j)
    (hold : ∀ j < w, word t₀.mem D (eD + 8 * j) = sel E d e j)
    {j : Nat} (hj : j < w) {t : State} (hI : SelW t₀ D eD E d e j t) :
    WP isa (.block (selectWord ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ SelW t₀ D eD E d e (j + 1) t' := by
  have tsi : t.gpr .rsi = off S eS := (hI.keep.gpr (by decide)).trans hsi
  have tbx : t.gpr .rbx = off D eD := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have tdx : t.gpr .rdx = eqMask e d := (hI.keep.gpr (by decide)).trans hdx
  have hl1 : InRegions (t.rd ++ t.wr) (off S (eS + 8 * j)) 8 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd j hj
  have hl2 : InRegions (t.rd ++ t.wr) (off D (eD + 8 * j)) 8 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hld j hj
  have hst : InRegions t.wr (off D (eD + 8 * j)) 8 := by rw [hI.keep.2.2]; exact hwr j hj
  have hv : word t.mem S (eS + 8 * j) = E e j :=
    (Mem.readW_congr fun b hb => hI.frame _ (by have := hsep j hj b hb; omega)).trans (hS j hj)
  have hv' : word t.mem D (eD + 8 * j) = sel E d e j :=
    (hI.frame.word (Or.inr (by omega)) (by omega)).trans (hold j hj)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off D (eD + 8 * j)) (sel E d (e + 1) j)) ?_ rfl)
    fun t₁ ⟨hm, k₁⟩ => ?_
  · unfold selectWord
    xrun [State.ea, ix, addr0 tsi hI.r14, addr0 tbx hI.r14, hl1, hl2, hst, hv, hv', tdx, mask_sel]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨((hI.keep.trans k₁).trans k').mono (by decide), h14, fun i hi => ?_, ?_⟩
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [(writeW_outside t.mem D _ (by omega)).word (by omega) (by omega)]; exact hI.done i hi
    · exact word_writeW_self _ _ _ _
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem D _ (by omega) x (by omega)]
    exact hI.frame x (by omega)

/-- The context's `n` words at `cp`: readable, outside the working space. -/
structure CtxRd (s : State) (B : Addr) (Z : Nat) (cp : Addr) (n : Nat) : Prop where
  rd : ∀ i < n, InRegions (s.rd ++ s.wr) (off cp (8 * i)) 8
  sep : ∀ i < 8 * n, Z ≤ ofs B (cp + BitVec.ofNat 64 i)
  nowrap : cp.toNat + 8 * n ≤ 2 ^ 64

theorem CtxRd.congr {s t : State} {B : Addr} {Z : Nat} {cp : Addr} {n : Nat} (h : CtxRd s B Z cp n)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : CtxRd t B Z cp n :=
  ⟨fun i hi => by rw [hrd, hwr]; exact h.rd i hi, h.sep, h.nowrap⟩

theorem CtxRd.out {s : State} {B : Addr} {Z : Nat} {cp : Addr} {n : Nat} (h : CtxRd s B Z cp n)
    {d : Nat} (hd : d < 8 * n) : Z ≤ ofs B (off cp d) := by
  have := h.sep d hd
  simpa [off] using this

/-- A word of the context is unchanged by a change inside the working space. -/
theorem CtxRd.word {s : State} {B : Addr} {Z : Nat} {cp : Addr} {n : Nat} (h : CtxRd s B Z cp n)
    {m m' : Mem} (hm : InScr B Z m m') {d : Nat} (hd : d + 8 ≤ 8 * n) : word m' cp d = word m cp d :=
  Mem.readW_congr fun b hb => hm _ (by
    have e : off cp d + BitVec.ofNat 64 b = off cp (d + b) := by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [e]
    exact h.out (by omega))

/-- What `select` changes: `iE` and `aXm`'s words. -/
def selR (w : Nat) : List (Nat × Nat) := [(8 * iE, 8), (slot w aXm, 8 * w)]

theorem selR_ok (w : Nat) : ∀ r ∈ selR w, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 := by
  have := slot_le (w := w) (show aXm < 8 by decide)
  have := hdr_lt_slot w aXm (show iE < 32 by decide)
  simp only [selR, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl) <;> simp only [slot, hdrBytes, aXm, iE, sFn] at * <;> omega

/-- After the entries below `e`, from `s`. -/
def SelO (B : Addr) (o w : Nat) (E : Nat → Nat → BitVec 64) (d : Nat) (s : State) (e : Nat) (t : State) : Prop :=
  Frm (off B o) (selR w) s.mem t.mem ∧ word t.mem (off B o) (8 * iE) = BitVec.ofNat 64 e ∧
    (∀ i < w, word t.mem (off B o) (slot w aXm + 8 * i) = sel E d e i) ∧
    Keep [.rax, .rdx, .rsi, .rbx, .r12, .r14] s t

theorem ofNat_cmp32 {e : Nat} (he : e < 32) :
    (BitVec.ofNat 64 (e + 1) - (32 : BitVec 64) == 0) = decide (e + 1 = 32) :=
  ofNat_sub_beq (N := 32) (by omega) (by omega)

/-- What every entry of the scan has, from the scan's start `s`. -/
structure SelB (B : Addr) (Z o w : Nat) (mi : BitVec 64) (cp : Addr) (E : Nat → Nat → BitVec 64) (d : Nat)
    (s : State) : Prop where
  hc : SubCtx s B Z o w w mi
  wide : o + slot w 8 + tabBytes w 32 ≤ Z
  ctx : word s.mem (off B o) (8 * iCtx) = cp
  reg : CtxRd s B Z cp (3 + 34 * w)
  w1 : 1 ≤ w
  w28 : w < 2 ^ 28
  ent : ∀ a < 32, ∀ i < w, word s.mem cp (24 + 8 * w * (a + 2) + 8 * i) = E a i
  r13 : s.gpr .r13 = BitVec.ofNat 64 d
  d32 : d < 32

/-- What the scan keeps at entry `e`. -/
theorem SelO.facts {B : Addr} {Z o w : Nat} {mi : BitVec 64} {cp : Addr} {E : Nat → Nat → BitVec 64} {d e : Nat}
    {s t : State} (hb : SelB B Z o w mi cp E d s) (hI : SelO B o w E d s e t) :
    SubCtx t B Z o w w mi ∧ word t.mem (off B o) (8 * iCtx) = cp ∧ InScr B Z s.mem t.mem ∧
      (∀ a < 32, ∀ i < w, word t.mem cp (24 + 8 * w * (a + 2) + 8 * i) = E a i) ∧
      t.gpr .r13 = BitVec.ofNat 64 d ∧ CtxRd t B Z cp (3 + 34 * w) := by
  obtain ⟨hf, _, _, k⟩ := hI
  have hn := hb.hc.scr.nowrap
  have hi := hb.hc.hi
  have hin : InScr B Z s.mem t.mem :=
    (VG.Proof.Ffdh.X86_64.child_frm hb.hc hb.wide hf fun r hr => by have := (selR_ok w r hr).2; omega).2
  refine ⟨hb.hc.of_frm hf (selR_ok w) k.2.2 (k.gpr (by decide)), (hf.word_eq (fun r hr => by
    have := hdr_lt_slot w aXm (show iCtx < 32 by decide)
    simp only [selR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [iCtx, iE, sFn] at * <;> omega) (by unfold iCtx sFn; omega)).trans hb.ctx,
    hin, fun a ha i hi' => ?_, (k.gpr (by decide)).trans hb.r13, hb.reg.congr k.2.1 k.2.2⟩
  have : w * (a + 2) + w ≤ 34 * w := by
    have := Nat.mul_le_mul_left w (show a + 3 ≤ 34 by omega); rw [Nat.mul_add] at this ⊢; omega
  rw [hb.reg.word hin (by rw [Nat.mul_assoc]; omega)]; exact hb.ent a ha i hi'

/-- The scan's mask block. -/
abbrev maskBlk : List Instr := [.mov .rax (.mem (hdr iE)), .alu .xor .rax (.reg .r13), .alu .cmp .rax (.imm 1),
  .alu .sbb .rdx (.reg .rdx), .mov .rax (.mem (hdr iE)), .alu .add .rax (.imm 2)]

/-- The scan's row block. -/
abbrev rowBlk : List Instr := rowPtr ++ [.mov .rsi (.reg .rbx), .mov .rbx (.mem (hdr (sArr aXm)))]

/-- The scan's count block. -/
abbrev endBlk : List Instr :=
  [.mov .rax (.mem (hdr iE)), .alu .add .rax (.imm 1), .store (hdr iE) .rax, .alu .cmp .rax (.imm 32)]

theorem selectStep_eq : selectStep = .seq (.block maskBlk) (.seq (.block rowBlk) (.seq (wordLoop 0 selectWord)
    (.block endBlk))) := rfl

theorem selMask_ok {B : Addr} {Z o w : Nat} {mi : BitVec 64} {cp : Addr} {E : Nat → Nat → BitVec 64} {d e : Nat}
    {s t : State} (hb : SelB B Z o w mi cp E d s) (he : e < 32) (hI : SelO B o w E d s e t) :
    WP isa (.block maskBlk) t fun u => SelO B o w E d s e u ∧ u.gpr .rax = BitVec.ofNat 64 (e + 2) ∧
      u.gpr .rdx = eqMask e d := by
  obtain ⟨hct, _, _, _, h13t, _⟩ := hI.facts hb
  have hZ8 : 8 * 32 ≤ slot w 8 := by unfold slot hdrBytes; omega
  obtain ⟨hf, hiE, hsel, k⟩ := hI
  refine WP.mono (mask_ok hct.good hZ8 hiE h13t he hb.d32) fun u ⟨hdx, hax, hm, ku⟩ => ⟨⟨by rw [hm]; exact hf,
    by rw [hm]; exact hiE, fun i hi => by rw [hm]; exact hsel i hi, (k.trans ku).mono (by decide)⟩, hax, hdx⟩

theorem selRow_ok {B : Addr} {Z o w : Nat} {mi : BitVec 64} {cp : Addr} {E : Nat → Nat → BitVec 64} {d e : Nat}
    {s t : State} (hb : SelB B Z o w mi cp E d s) (hI : SelO B o w E d s e t)
    (hax : t.gpr .rax = BitVec.ofNat 64 (e + 2)) (hdx : t.gpr .rdx = eqMask e d) :
    WP isa (.block rowBlk) t fun u => SelO B o w E d s e u ∧ u.gpr .rdx = eqMask e d ∧
      u.gpr .rsi = off cp (24 + 8 * w * (e + 2)) ∧ u.gpr .rbx = off (off B o) (slot w aXm) ∧
      u.gpr .r12 = BitVec.ofNat 64 w := by
  obtain ⟨hct, hctxt, _, _, _, _⟩ := hI.facts hb
  have hn := hb.hc.scr.nowrap
  have hi := hb.hc.hi
  have hlo := hb.hc.lo
  rw [WP.block_append_iff]
  refine WP.mono (rowPtr_ok (cp := cp) hct hctxt hax) fun t₂ ⟨hbx, h12, hm₂, k₂⟩ => ?_
  have hg₂ : Good t₂ (off B o) (slot w 8) w mi :=
    ⟨hct.good.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hct.good.rdi, by rw [hm₂]; exact hct.good.hdr⟩
  have hA := hdr_lt_slot w 8 (show sArr aXm < 32 by unfold sArr aXm; omega)
  refine WP.mono (WP.keep [.rsi, .rbx] (Q := fun u => u.gpr .rsi = off cp (24 + 8 * w * (e + 2)) ∧
      u.gpr .rbx = off (off B o) (slot w aXm) ∧ u.mem = t₂.mem)
    (by xrun [State.ea, hdr, hg₂.rdi, hdrOff, hbx, hg₂.scr.ld (d := 8 * sArr aXm) (by omega),
      hg₂.hdr.harr aXm (by decide)]) rfl)
    fun t₃ ⟨⟨hsi, hbx₃, hm₃⟩, k₃⟩ => ?_
  obtain ⟨hf, hiE, hsel, k⟩ := hI
  have hm : t₃.mem = t.mem := hm₃.trans hm₂
  refine ⟨⟨by rw [hm]; exact hf, by rw [hm]; exact hiE, fun i hi => by rw [hm]; exact hsel i hi,
    (k.trans (k₂.trans k₃)).mono (by decide)⟩, ((k₂.trans k₃).gpr (by decide)).trans hdx, hsi, hbx₃,
    (k₃.gpr (by decide)).trans h12⟩

/-- After entry `e`'s words. -/
def SelF (B : Addr) (o w : Nat) (E : Nat → Nat → BitVec 64) (d : Nat) (s : State) (e : Nat) (t : State) : Prop :=
  Frm (off B o) (selR w) s.mem t.mem ∧ word t.mem (off B o) (8 * iE) = BitVec.ofNat 64 e ∧
    (∀ i < w, word t.mem (off B o) (slot w aXm + 8 * i) = sel E d (e + 1) i) ∧
    Keep [.rax, .rdx, .rsi, .rbx, .r12, .r14] s t

theorem selWords_ok {B : Addr} {Z o w : Nat} {mi : BitVec 64} {cp : Addr} {E : Nat → Nat → BitVec 64} {d e : Nat}
    {s t : State} (hb : SelB B Z o w mi cp E d s) (he : e < 32) (hI : SelO B o w E d s e t)
    (hdx : t.gpr .rdx = eqMask e d) (hsi : t.gpr .rsi = off cp (24 + 8 * w * (e + 2)))
    (hbx : t.gpr .rbx = off (off B o) (slot w aXm)) (h12 : t.gpr .r12 = BitVec.ofNat 64 w) :
    WP isa (wordLoop 0 selectWord) t (SelF B o w E d s e) := by
  obtain ⟨hct, _, _, hEt, _, hrt⟩ := hI.facts hb
  have hw := hb.w1
  have hw' := hb.w28
  have hn := hb.hc.scr.nowrap
  have hi := hb.hc.hi
  have hlo := hb.hc.lo
  have hsx := slot_le (w := w) (show aXm < 8 by decide)
  have hcn := hb.reg.nowrap
  obtain ⟨hf, hiE, hsel, k⟩ := hI
  have hsc : Scr t (off B o) (slot w 8) := hct.good.scr
  have hfit : 3 + w * (e + 2) + w ≤ 3 + 34 * w := by
    have := Nat.mul_le_mul_left w (show e + 3 ≤ 34 by omega); rw [Nat.mul_add] at this ⊢; omega
  have e8 : 8 * w * (e + 2) = 8 * (w * (e + 2)) := Nat.mul_assoc _ _ _
  have h0 : ∀ u, u.gpr .r14 = BitVec.ofNat 64 0 → u.mem = t.mem → Keep [.r14] t u → u.cf = t.cf →
      SelW t (off B o) (slot w aXm) E d e 0 u := fun u h14 hm ku _ =>
    ⟨ku.mono (by decide), h14, fun i hi => absurd hi (Nat.not_lt_zero _), by rw [hm]; exact Outside.refl _ _ _ _⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) (by omega) (SelW t (off B o) (slot w aXm) E d e) h0
    (fun j _ hj u hI => selStep_ok hsi hbx h12 hdx (by omega) (by omega)
      (fun i hi' => by rw [rowOff]; exact hrt.rd (3 + w * (e + 2) + i) (by omega))
      (fun i hi' => hsc.ld (by omega)) (fun i hi' => hsc.st (by omega))
      (fun i hi' b hb' => Or.inr (by
        have hb'' : 24 + 8 * w * (e + 2) + 8 * i + b < 8 * (3 + 34 * w) := by omega
        have := hb.reg.out (d := 24 + 8 * w * (e + 2) + 8 * i + b) hb''
        rw [show off cp (24 + 8 * w * (e + 2) + 8 * i + b) =
            off cp (24 + 8 * w * (e + 2) + 8 * i) + BitVec.ofNat 64 b by
          simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]] at this
        rcases ofs_rebase B (off cp (24 + 8 * w * (e + 2) + 8 * i) + BitVec.ofNat 64 b) (o := o) (by omega)
          with ⟨_, h⟩ | ⟨h, _⟩
        · rw [h]; omega
        · omega))
      (fun i hi' => hEt e he i hi') (fun i hi' => hsel i hi') hj hI))
    fun u hW => ?_
  have hf₄ : Frm (off B o) [(slot w aXm, 8 * w)] t.mem u.mem := Frm.of_outside hW.frame (List.mem_singleton.mpr rfl)
  refine ⟨Frm.widen (hf.append hf₄) fun r hr => ?_, ?_, hW.done, (k.trans hW.keep).mono (by decide)⟩
  · simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [selR], Nat.le_refl _, Nat.le_refl _⟩
  · rw [hW.frame.word (Or.inl (by have := hdr_lt_slot w aXm (show iE < 32 by decide); omega))
      (by unfold iE sFn; omega), hiE]

theorem selEnd_ok {B : Addr} {Z o w : Nat} {mi : BitVec 64} {cp : Addr} {E : Nat → Nat → BitVec 64} {d e : Nat}
    {s t : State} (hb : SelB B Z o w mi cp E d s) (he : e < 32) (hF : SelF B o w E d s e t) :
    WP isa (.block endBlk) t fun u => u.zf = some (decide (e + 1 = 32)) ∧ SelO B o w E d s (e + 1) u := by
  obtain ⟨hf, hE₄, hsel, k⟩ := hF
  have hn := hb.hc.scr.nowrap
  have hi := hb.hc.hi
  have hlo := hb.hc.lo
  have hsx := slot_le (w := w) (show aXm < 8 by decide)
  have hct : SubCtx t B Z o w w mi := hb.hc.of_frm hf (selR_ok w) k.2.2 (k.gpr (by decide))
  have hsc₄ := hct.good.scr
  have hdi₄ : t.gpr .rdi = off B o := hct.rdi
  have hlE := hdr_lt_slot w 8 (show iE < 32 by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.zf = some (decide (e + 1 = 32)) ∧
      u.mem = t.mem.writeW (off (off B o) (8 * iE)) (BitVec.ofNat 64 (e + 1))) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hsc₄.ld (d := 8 * iE) (by omega), hsc₄.st (d := 8 * iE) (by omega), hE₄,
      ofNat_add_one', ofNat_cmp32 he]) rfl)
    fun t₅ ⟨⟨hz, hm₅⟩, k₅⟩ => ⟨hz, ?_⟩
  have ho₅ := writeW_outside t.mem (off B o) (d := 8 * iE) (BitVec.ofNat 64 (e + 1)) (by omega)
  rw [← hm₅] at ho₅
  refine ⟨Frm.widen (hf.append (Frm.of_outside ho₅ (List.mem_singleton.mpr rfl))) fun r hr => ?_,
    by rw [hm₅]; exact word_writeW_self _ _ _ _, fun i hi' => ?_, (k.trans k₅).mono (by decide)⟩
  · simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [selR], Nat.le_refl _, Nat.le_refl _⟩
  · rw [ho₅.word (Or.inr (by have := hdr_lt_slot w aXm (show iE < 32 by decide); omega)) (by omega)]
    exact hsel i hi'

/-- Entry `e` of the scan. -/
theorem selectStep_ok {B : Addr} {Z o w : Nat} {mi : BitVec 64} {cp : Addr} {E : Nat → Nat → BitVec 64} {d e : Nat}
    {s t : State} (hb : SelB B Z o w mi cp E d s) (he : e < 32) (hI : SelO B o w E d s e t) :
    WP isa selectStep t fun u => u.zf = some (decide (e + 1 = 32)) ∧ SelO B o w E d s (e + 1) u := by
  rw [selectStep_eq]
  refine WP.seq (WP.mono (selMask_ok hb he hI) fun t₁ ⟨h₁, hax, hdx⟩ => ?_)
  refine WP.seq (WP.mono (selRow_ok hb h₁ hax hdx) fun t₂ ⟨h₂, hdx₂, hsi, hbx, h12⟩ => ?_)
  exact WP.seq (WP.mono (selWords_ok hb he h₂ hdx₂ hsi hbx h12) fun t₃ h₃ => selEnd_ok hb he h₃)

/-- `aXm :=` entry `d`'s words, reading every entry, from `aXm`'s first `w` words zero. -/
theorem select_ok {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {cp : Addr}
    (hc : SubCtx s B Z o w w mi) (hwide : o + slot w 8 + tabBytes w 32 ≤ Z)
    (hctx : word s.mem (off B o) (8 * iCtx) = cp) (hreg : CtxRd s B Z cp (3 + 34 * w))
    (hw : 1 ≤ w) (hw' : w < 2 ^ 28) {E : Nat → Nat → BitVec 64}
    (hE : ∀ a < 32, ∀ i < w, word s.mem cp (24 + 8 * w * (a + 2) + 8 * i) = E a i)
    {d : Nat} (h13 : s.gpr .r13 = BitVec.ofNat 64 d) (hd : d < 32)
    (hz : ∀ i < w, word s.mem (off B o) (slot w aXm + 8 * i) = 0#64) :
    WP isa select s fun t => (∀ i < w, word t.mem (off B o) (slot w aXm + 8 * i) = E d i) ∧
      Frm (off B o) (selR w) s.mem t.mem ∧ Keep [.rax, .rdx, .rsi, .rbx, .r12, .r14] s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have hsx := slot_le (w := w) (show aXm < 8 by decide)
  have hlE := hdr_lt_slot w 8 (show iE < 32 by decide)
  have hsc := hc.good.scr
  unfold select
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun u =>
      u.mem = s.mem.writeW (off (off B o) (8 * iE)) (BitVec.ofNat 64 0)) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hsc.st (d := 8 * iE) (by omega)]; rfl) rfl)
    fun t₀ ⟨hm₀, k₀⟩ => ?_)
  have ho₀ := writeW_outside s.mem (off B o) (d := 8 * iE) (BitVec.ofNat 64 0) (by omega)
  rw [← hm₀] at ho₀
  have hI0 : SelO B o w E d s 0 t₀ := ⟨Frm.of_outside ho₀ (by simp [selR]), by rw [hm₀]; exact word_writeW_self _ _ _ _,
    fun i hi' => by
      rw [ho₀.word (Or.inr (by have := hdr_lt_slot w aXm (show iE < 32 by decide); omega)) (by omega), hz i hi']
      rfl, k₀.mono (by decide)⟩
  refine wp_upto (a := 0) (N := 32) (by decide) (SelO B o w E d s)
    (fun e _ he t hI => selectStep_ok ⟨hc, hwide, hctx, hreg, hw, hw', hE, h13, hd⟩ he hI)
    (fun t ⟨hf, _, hsel, k⟩ => ?_) hI0
  exact ⟨fun i hi' => (hsel i hi').trans (by unfold sel; rw [ite_eq_left hd]), hf, k⟩

/-! ## The comb's environment -/

/-- What the comb keeps: the inner workspace for `p`, the context and the
scalar's bytes, and their pointers and lengths in the inner header. -/
structure CEnv (T : TabP) (xp : Addr) (xb : List Byte) (s : State) : Prop where
  mc : ModCtx s T.B T.Z T.o T.w T.mi T.P
  ctx : word s.mem (off T.B T.o) (8 * iCtx) = T.cp
  rows : word s.mem (off T.B T.o) (8 * iRows) = BitVec.ofNat 64 T.rows
  xpw : word s.mem (off T.B T.o) (8 * iXp) = xp
  xlw : word s.mem (off T.B T.o) (8 * iXl) = BitVec.ofNat 64 xb.length
  reg : CtxRd s T.B T.Z T.cp T.n
  ent : ∀ a < 32, row s.mem T.cp T.w (2 + a) = Spec.Rsa.toWords (T.entry a) T.w
  x : Src s T.B T.Z xp xb

/-- What the comb changes in the inner workspace: `iI`, `iE` and the arrays
but `aN`, `aR2` and `aOne`. -/
def combR (w : Nat) : List (Nat × Nat) :=
  [(8 * iI, 16), (slot w aX, 3 * (8 * (w + 2))), (slot w aXm, 2 * (8 * (w + 2)))]

theorem combR_inner (w : Nat) : ∀ r ∈ combR w, ∃ r' ∈ innerR w, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := by
  have := hdr_lt_slot w aX (show 31 < 32 by decide)
  simp only [combR, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨(8 * 17, 8 * 15), by simp [innerR], by simp only [iI, sFn]; omega, by simp only [iI, sFn]; omega⟩
  · exact ⟨_, by simp [innerR], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, by simp [innerR], Nat.le_refl _, Nat.le_refl _⟩

theorem combR_le (w : Nat) : ∀ r ∈ combR w, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 := fun r hr => by
  obtain ⟨r', hr', h1, h2⟩ := combR_inner w r hr
  have := innerR_ok w r' hr'
  omega

/-- The inner header's pointers and counts the comb only reads. -/
theorem combR_hdr (w : Nat) {i : Nat} (hi : i = iCtx ∨ i = iRows ∨ i = iXp ∨ i = iXl) :
    ∀ r ∈ combR w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
  have h0 := hdr_lt_slot w aX (show i < 32 by rcases hi with rfl | rfl | rfl | rfl <;> decide)
  simp only [combR, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl) <;> rcases hi with rfl | rfl | rfl | rfl <;> simp only [iI, iCtx, iRows, iXp, iXl, sFn] at * <;>
    simp only [slot, hdrBytes, aX, aXm] at * <;> omega

theorem CEnv.of_frm {T : TabP} {xp : Addr} {xb : List Byte} {s t : State} (h : CEnv T xp xb s)
    (hf : Frm (off T.B T.o) (combR T.w) s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) :
    CEnv T xp xb t ∧ InScr T.B T.Z s.mem t.mem ∧ (∀ i < 32, word t.mem T.B (8 * i) = word s.mem T.B (8 * i)) := by
  obtain ⟨hh, hin⟩ := VG.Proof.Ffdh.X86_64.child_frm h.mc.sub h.mc.wide hf fun r hr => by
    have := (combR_le T.w r hr).2; omega
  have hw : ∀ i, (i = iCtx ∨ i = iRows ∨ i = iXp ∨ i = iXl) →
      word t.mem (off T.B T.o) (8 * i) = word s.mem (off T.B T.o) (8 * i) := fun i hi =>
    hf.word_eq (combR_hdr T.w hi) (by
      have := h.mc.sub.scr.nowrap; have := h.mc.sub.hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp only [iCtx, iRows, iXp, iXl, sFn] <;> omega)
  refine ⟨⟨h.mc.of_inner (Frm.widen hf (combR_inner T.w)) hwr hdi, (hw _ (.inl rfl)).trans h.ctx,
    (hw _ (.inr (.inl rfl))).trans h.rows, (hw _ (.inr (.inr (.inl rfl)))).trans h.xpw,
    (hw _ (.inr (.inr (.inr rfl)))).trans h.xlw, h.reg.congr hrd hwr, fun a ha => ?_, h.x.congr hin hrd hwr⟩,
    hin, hh⟩
  rw [← h.ent a ha]
  refine row_congr fun i hi => h.reg.word hin ?_
  have : T.w * (2 + a) + T.w ≤ 34 * T.w := by
    have h := Nat.mul_le_mul_left T.w (show 2 + a + 1 ≤ 34 by omega); rw [Nat.mul_succ] at h; omega
  unfold TabP.n
  rw [Nat.mul_assoc]; omega

/-- A frame of fewer bytes than `combR`. -/
theorem Frm.toCombR {B : Addr} {w : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hc : ∀ r ∈ rs, ∃ r' ∈ combR w, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Frm B (combR w) m m' :=
  Frm.widen h hc

/-- The ranges of `mm`'s writes are in `combR`. -/
theorem mm_combR (w : Nat) {out : Nat} (ho : out = aX ∨ out = aXm ∨ out = aY) :
    ∀ r ∈ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w out, 8 * (w + 2))],
      ∃ r' ∈ combR w, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := fun r hr => by
  obtain ⟨r', hr', h1, h2⟩ := mm_cover w ho r hr
  simp only [innerR, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exfalso
    rcases hr with rfl | rfl | rfl
    · simp only [slot, hdrBytes, aAcc] at h1 h2; omega
    · simp only [slot, hdrBytes, aTmp] at h1 h2; omega
    · rcases ho with rfl | rfl | rfl <;> simp only [slot, hdrBytes, aX, aXm, aY] at h1 h2 <;> omega
  · exact ⟨_, by simp [combR], h1, h2⟩
  · exact ⟨_, by simp [combR], h1, h2⟩

/-- Montgomery multiplication in the comb's environment. -/
theorem mm_cenv (Mo : Mont) {T : TabP} {xp : Addr} {xb : List Byte} {s : State} (he : CEnv T xp xb s)
    {out a b : Nat} (ho : out = aX ∨ out = aXm ∨ out = aY) (ha : a < 8) (hb : b < 8) (ha₁ : a ≠ aAcc)
    (ha₂ : a ≠ aTmp) (hb₁ : b ≠ aAcc) (hb₂ : b ≠ aTmp)
    (hbl : wv s.mem (off T.B T.o) (slot T.w b) T.w < T.P) :
    WP isa (Mo.mm out a b) s fun t => CEnv T xp xb t ∧
      wv t.mem (off T.B T.o) (slot T.w out) T.w < T.P ∧
      wv t.mem (off T.B T.o) (slot T.w out) T.w * T.R % T.P =
        wv s.mem (off T.B T.o) (slot T.w a) T.w * wv s.mem (off T.B T.o) (slot T.w b) T.w % T.P ∧
      Arrays (off T.B T.o) T.w [aAcc, aTmp, out] s.mem t.mem ∧
      Frm (off T.B T.o) (combR T.w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hc := he.mc
  have hout : out < 8 := by rcases ho with rfl | rfl | rfl <;> decide
  have ho₁ : out ≠ aAcc := by rcases ho with rfl | rfl | rfl <;> decide
  have ho₂ : out ≠ aTmp := by rcases ho with rfl | rfl | rfl <;> decide
  refine WP.mono (Mo.mm_ok hc.sub.good (Nat.le_refl _) (by have := hc.w2; omega) (by have := hc.w28; omega) hout
    ha hb ho₁ ho₂ ha₁ hb₁ hc.xv.inv (by rw [hc.xv.n]; exact hbl) ha₂ hb₂) fun t ⟨_, hl, hv, ha', k⟩ => ?_
  rw [hc.xv.n] at hl hv
  have hf : Frm (off T.B T.o) (combR T.w) s.mem t.mem := Frm.toCombR (Frm.of_arrays ha' (by simp)) (mm_combR T.w ho)
  exact ⟨(he.of_frm hf k.2.1 k.2.2 (k.gpr (by decide))).1, hl, hv, ha', hf, k⟩

theorem Frm.combR_trans {B : Addr} {w : Nat} {m₁ m₂ m₃ : Mem} (h₁ : Frm B (combR w) m₁ m₂)
    (h₂ : Frm B (combR w) m₂ m₃) : Frm B (combR w) m₁ m₃ :=
  Frm.widen (h₁.append h₂) fun r hr => ⟨r, by simpa using hr, Nat.le_refl _, Nat.le_refl _⟩

/-- `[iI] := [iI] - 1`, and whether it is now zero. -/
theorem decI_ok {s : State} {O : Addr} {Zs w : Nat} {mi : BitVec 64} (hg : Good s O Zs w mi) (hZ : 8 * 32 ≤ Zs)
    {k : Nat} (hv : word s.mem O (8 * iI) = BitVec.ofNat 64 (k + 1)) (hk : k + 1 < 2 ^ 64) :
    WP isa (.block [.mov .rax (.mem (hdr iI)), .alu .sub .rax (.imm 1), .store (hdr iI) .rax]) s fun t =>
      t.zf = some (decide (k = 0)) ∧ t.mem = s.mem.writeW (off O (8 * iI)) (BitVec.ofNat 64 k) ∧
      Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (k = 0)) ∧
      t.mem = s.mem.writeW (off O (8 * iI)) (BitVec.ofNat 64 k)) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * iI) (by unfold iI sFn; omega),
      hg.scr.st (d := 8 * iI) (by unfold iI sFn; omega), hv, ofNat_succ_sub_one k,
      ofNat_beq_zero (show k < 2 ^ 64 by omega)]) rfl) fun t ⟨h, k'⟩ => ⟨h.1, h.2, k'⟩

/-- `mm`'s writes keep the inner header. -/
theorem arrays3_hdr {O : Addr} {w out : Nat} {m m' : Mem} (h : Arrays O w [aAcc, aTmp, out] m m') (_hout : out < 8)
    {i : Nat} (hi : i < 32) : word m' O (8 * i) = word m O (8 * i) :=
  (Frm.of_arrays (rs := [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w out, 8 * (w + 2))]) h
    (by simp)).word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Or.inl (hdr_lt_slot w aAcc hi)
      · exact Or.inl (hdr_lt_slot w aTmp hi)
      · exact Or.inl (hdr_lt_slot w out hi)) (by omega)

/-! ## A row of the comb -/

/-- After `j` rows from the top, from `s₀`. -/
def CInv (T : TabP) (xp : Addr) (xb : List Byte) (s₀ : State) (j : Nat) (t : State) : Prop :=
  CEnv T xp xb t ∧ word t.mem (off T.B T.o) (8 * iI) = BitVec.ofNat 64 (T.rows - j) ∧
    wv t.mem (off T.B T.o) (slot T.w aY) T.w = T.M (Rsa.FixedBaseComb.high T.bits (Spec.Rsa.os2ip xb) (T.rows - j)) ∧
    Frm (off T.B T.o) (combR T.w) s₀.mem t.mem ∧ Keep mmRegs s₀ t

theorem CEnv.good {T : TabP} {xp : Addr} {xb : List Byte} {s : State} (h : CEnv T xp xb s) :
    Good s (off T.B T.o) (slot T.w 8) T.w T.mi := h.mc.sub.good

theorem slot8_ge (w : Nat) : 8 * 32 ≤ slot w 8 := by unfold slot hdrBytes; omega

theorem CEnv.P_lt {T : TabP} {xp : Addr} {xb : List Byte} {s : State} (he : CEnv T xp xb s) :
    T.P < 2 ^ (64 * T.w) := by
  rw [← he.mc.xv.n]; exact wv_lt _ _ _ _

/-- Row `i = rows - j - 1`: the square, the digit's entry and the product. -/
theorem combStep_ok (Mo : Mont) {T : TabP} {xp : Addr} {xb : List Byte} {s₀ : State}
    (hr : 5 * T.rows < 2 ^ 31) (hL : 8 * xb.length < 2 ^ 32) {j : Nat} (hj : j < T.rows) {t : State}
    (hI : CInv T xp xb s₀ j t) :
    WP isa (step Mo.mm) t fun u => u.zf = some (decide (j + 1 = T.rows)) ∧ CInv T xp xb s₀ (j + 1) u := by
  obtain ⟨he, hiI, hy, hf, k⟩ := hI
  have hP : 0 < T.P := by have := he.mc.x1; omega
  have hw2 := he.mc.w2
  have hw28 := he.mc.w28
  have hn := he.mc.sub.scr.nowrap
  obtain ⟨i, hi_def⟩ : ∃ i, i = T.rows - j - 1 := ⟨_, rfl⟩
  have hri : T.rows - j = i + 1 := by omega
  have hilt : i < T.rows := by omega
  have hrj : T.rows - (j + 1) = i := by omega
  rw [hri] at hiI hy
  unfold step
  simp only [seqs]
  -- The square.
  refine WP.seq (WP.mono (mm_cenv Mo he (Or.inr (Or.inr rfl)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hy]; exact T.M_lt hP _)) fun t₁ ⟨he₁, hl₁, hv₁, ha₁, hf₁, k₁⟩ => ?_)
  rw [hy] at hv₁
  have hy₁ := T.M_mul he.mc.odd hl₁ hv₁
  have hiI₁ : word t₁.mem (off T.B T.o) (8 * iI) = BitVec.ofNat 64 (i + 1) := by
    rw [arrays3_hdr ha₁ (by decide) (by decide), hiI]
  -- `aXm := 0`.
  have hg₁ := he₁.good
  refine WP.seq (WP.mono (zeroArr_ok hg₁ (Nat.le_refl _) (by omega) (by omega) (show aXm < 8 by decide))
    fun t₂ ⟨hz₂, ho₂, k₂⟩ => ?_)
  have hf₂ : Frm (off T.B T.o) (combR T.w) t₁.mem t₂.mem :=
    Frm.of_outside (ho₂.mono (o' := slot T.w aXm) (n' := 2 * (8 * (T.w + 2))) (Nat.le_refl _) (by omega))
      (by simp [combR])
  obtain ⟨he₂, hin₂, _⟩ := he₁.of_frm hf₂ k₂.2.1 k₂.2.2 (k₂.gpr (by decide))
  have hsx := slot_le (w := T.w) (show aXm < 8 by decide)
  have hiI₂ : word t₂.mem (off T.B T.o) (8 * iI) = BitVec.ofNat 64 (i + 1) := by
    rw [ho₂.word (Or.inl (hdr_lt_slot T.w aXm (show iI < 32 by decide))) (by unfold iI sFn; omega), hiI₁]
  have hy₂ : wv t₂.mem (off T.B T.o) (slot T.w aY) T.w = T.M (Rsa.FixedBaseComb.high T.bits (Spec.Rsa.os2ip xb) (i + 1) +
      Rsa.FixedBaseComb.high T.bits (Spec.Rsa.os2ip xb) (i + 1)) := by
    rw [ho₂.wv (Or.inr (by simp only [slot, aXm, aY]; omega)) (by simp only [slot, hdrBytes, aY]; omega), hy₁]
  -- The digit.
  have hg₂ := he₂.good
  refine WP.seq (WP.mono (digit_ok hg₂ (slot8_ge _) hiI₂ he₂.rows he₂.xpw he₂.xlw he₂.x.rd he₂.x.val
    hilt hr hL) fun t₃ ⟨h13, hm₃, k₃⟩ => ?_)
  have he₃ : CEnv T xp xb t₃ := (he₂.of_frm (fun x _ => by rw [hm₃]) k₃.2.1 k₃.2.2 (k₃.gpr (by decide))).1
  -- The selection.
  have hd := Rsa.FixedBaseComb.digit_lt T.bits (Spec.Rsa.os2ip xb) i
  refine WP.seq (WP.mono (select_ok he₃.mc.sub he₃.mc.wide he₃.ctx he₃.reg (by omega) hw28
    (E := fun a i => word t₃.mem T.cp (24 + 8 * T.w * (a + 2) + 8 * i)) (fun _ _ _ _ => rfl) h13 hd
    (fun i' hi' => by
      rw [hm₃]; exact (wv_eq_zero_iff _ _ _ _).mp hz₂ i' (by omega)))
    fun t₄ ⟨hx₄, hf₄, k₄⟩ => ?_)
  have hf₄' : Frm (off T.B T.o) (combR T.w) t₃.mem t₄.mem := Frm.widen hf₄ fun r hr => by
    simp only [selR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨(8 * iI, 16), by simp [combR], by simp only [iI, iE, sFn]; omega, by simp only [iI, iE, sFn]; omega⟩
    · exact ⟨(slot T.w aXm, 2 * (8 * (T.w + 2))), by simp [combR], Nat.le_refl _, by omega⟩
  obtain ⟨he₄, hin₄, _⟩ := he₃.of_frm hf₄' k₄.2.1 k₄.2.2 (k₄.gpr (by decide))
  have hent := he₃.ent _ hd
  have hxm : wv t₄.mem (off T.B T.o) (slot T.w aXm) T.w = T.entry (Rsa.FixedBaseComb.digit T.bits (Spec.Rsa.os2ip xb) i) := by
    rw [wv_congr2 (p := T.cp) (d := 24 + 8 * T.w * (2 + Rsa.FixedBaseComb.digit T.bits (Spec.Rsa.os2ip xb) i))
      (m := t₃.mem) fun i' hi' => (hx₄ i' hi').trans (by rw [Nat.add_comm 2]),
      wv_of_row hent (T.M_lt_R hP (Nat.le_of_lt he.P_lt) _)]
  have hy₄ : wv t₄.mem (off T.B T.o) (slot T.w aY) T.w = wv t₂.mem (off T.B T.o) (slot T.w aY) T.w := by
    rw [hf₄.wv_eq (fun r hr => by
      simp only [selR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inr (by have := hdr_lt_slot T.w aY (show iE < 32 by decide); simp only; omega)
      · exact Or.inr (by simp only [slot, aXm, aY]; omega))
      (by simp only [slot, hdrBytes, aY]; omega), hm₃]
  have hiI₄ : word t₄.mem (off T.B T.o) (8 * iI) = BitVec.ofNat 64 (i + 1) := by
    rw [hf₄.word_eq (fun r hr => by
      simp only [selR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inl (by simp only [iI, iE, sFn]; omega)
      · exact Or.inl (by have := hdr_lt_slot T.w aXm (show iI < 32 by decide); omega))
      (by unfold iI sFn; omega), hm₃, hiI₂]
  -- The product.
  refine WP.seq (WP.mono (mm_cenv Mo he₄ (Or.inr (Or.inr rfl)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hxm]; exact T.M_lt hP _)) fun t₅ ⟨he₅, hl₅, hv₅, ha₅, hf₅, k₅⟩ => ?_)
  rw [hy₄, hy₂, hxm] at hv₅
  have hy₅ := T.M_mul he.mc.odd hl₅ hv₅
  have hiI₅ : word t₅.mem (off T.B T.o) (8 * iI) = BitVec.ofNat 64 (i + 1) := by
    rw [arrays3_hdr ha₅ (by decide) (by decide), hiI₄]
  -- `iI := i`.
  refine WP.mono (decI_ok he₅.good (slot8_ge _) hiI₅ (by omega)) fun u ⟨hz, hmu, ku⟩ => ?_
  have hou := writeW_outside t₅.mem (off T.B T.o) (d := 8 * iI) (BitVec.ofNat 64 i) (by unfold iI sFn; omega)
  rw [← hmu] at hou
  have hfu : Frm (off T.B T.o) (combR T.w) t₅.mem u.mem :=
    Frm.of_outside (hou.mono (o' := 8 * iI) (n' := 16) (Nat.le_refl _) (by omega)) (by simp [combR])
  obtain ⟨heu, _, _⟩ := he₅.of_frm hfu ku.2.1 ku.2.2 (ku.gpr (by decide))
  refine ⟨by rw [hz]; congr 1; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_iff]; omega, heu,
    by rw [hmu, word_writeW_self, hrj], ?_, ?_, ?_⟩
  · rw [hou.wv (Or.inr (by have := hdr_lt_slot T.w aY (show iI < 32 by decide); omega))
      (by simp only [slot, hdrBytes, aY]; omega), hy₅, hrj, Rsa.FixedBaseComb.high_step _ _ _ hilt]
    congr 1; omega
  · have hf₃ : Frm (off T.B T.o) (combR T.w) t₂.mem t₃.mem := fun x _ => by rw [hm₃]
    exact Frm.combR_trans (Frm.combR_trans (Frm.combR_trans (Frm.combR_trans (Frm.combR_trans
      (Frm.combR_trans hf hf₁) hf₂) hf₃) hf₄') hf₅) hfu
  · exact (((((k.trans k₁).trans k₂).trans k₃).trans k₄).trans (k₅.trans ku)).mono (by decide)

/-! ## The comb's setup -/

/-- A store to an inner counter slot. -/
theorem _root_.VG.Proof.Ffdh.X86_64.ModCtx.store {s t : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {P : Nat}
    (hc : ModCtx s B Z o w mi P) {i : Nat} (hi : 17 ≤ i) (hi' : i < 32) {v : BitVec 64}
    (hm : t.mem = s.mem.writeW (off (off B o) (8 * i)) v) (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = s.gpr .rdi) :
    ModCtx t B Z o w mi P ∧ Frm (off B o) [(8 * i, 8)] s.mem t.mem ∧ word t.mem (off B o) (8 * i) = v ∧
      (∀ k < 32, k ≠ i → word t.mem (off B o) (8 * k) = word s.mem (off B o) (8 * k)) ∧
      InScr B Z s.mem t.mem ∧ (∀ k < 32, word t.mem B (8 * k) = word s.mem B (8 * k)) := by
  have ho := writeW_outside s.mem (off B o) (d := 8 * i) v (by omega)
  rw [← hm] at ho
  have hf : Frm (off B o) [(8 * i, 8)] s.mem t.mem := Frm.of_outside ho (by simp)
  have hl := hdr_lt_slot w 8 hi'
  refine ⟨hc.of_inner (Frm.cover hf fun r hr => ⟨(8 * 17, 8 * 15), by simp [innerR], by
      rw [List.mem_singleton.mp hr]; simp only; omega, by rw [List.mem_singleton.mp hr]; simp only; omega⟩) hwr hdi,
    hf, by rw [hm]; exact word_writeW_self _ _ _ _, fun k hk hne => ho.word (by omega) (by
      have := hdr_lt_slot w 8 hk; omega),
    (VG.Proof.Ffdh.X86_64.child_frm hc.sub hc.wide hf fun r hr => by
      rw [List.mem_singleton.mp hr]; simp only; unfold tabBytes; omega).2,
    (VG.Proof.Ffdh.X86_64.child_frm hc.sub hc.wide hf fun r hr => by
      rw [List.mem_singleton.mp hr]; simp only; unfold tabBytes; omega).1⟩

/-- The outer slot `oo` to the inner slot `i`, through the link. -/
theorem fromOuter_ok {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {P : Nat}
    (hc : ModCtx s B Z o w mi P) {oo i : Nat} (hoo : oo < 32) (hi' : i < 32) {v : BitVec 64}
    (hv : word s.mem B (8 * oo) = v) :
    WP isa (.block (fromOuter oo i)) s fun t => t.mem = s.mem.writeW (off (off B o) (8 * i)) v ∧
      t.gpr .rdx = v ∧ Keep [.rax, .rdx] s t := by
  have hg := hc.sub.good
  have hlo := hc.sub.lo
  have hhi := hc.sub.hi
  have hO : InRegions (s.rd ++ s.wr) (off B (8 * oo)) 8 := hc.sub.scr.ld (by
    have := hdr_lt_slot w 8 hoo; omega)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = s.mem.writeW (off (off B o) (8 * i)) v ∧
      t.gpr .rdx = v) (by
    unfold fromOuter
    xrun [State.ea, hdr, Crt.ws, hg.rdi, hdrOff, hg.scr.ld (d := 8 * Crt.sLink) (hdr_lt_slot _ 8 (by decide)),
      hc.sub.link, hO, hv, hg.scr.st (d := 8 * i) (hdr_lt_slot _ 8 hi')]) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩

theorem atOff' (b : Addr) (d : Nat) : b + BitVec.ofInt 64 (d : Int) = off b d := by
  rw [BitVec.ofInt_natCast]

/-- The comb's header block, in the pieces between loads that address. -/
abbrev headA1 : List Instr := [.mov .rdx (.mem (Crt.stk 6))]
abbrev headA2 : List Instr := [.store (hdr iCtx) .rdx, .mov .rdx (.mem (at_ .rdx 16)), .store (hdr iRows) .rdx,
  .store (hdr iI) .rdx, .mov .rax (.mem (hdr Crt.sLink))]
abbrev headA3 : List Instr := [.mov .rdx (.mem (Crt.ws .rax VG.Impl.Ffdh.X86_64.Domain.sX)), .store (hdr iXp) .rdx,
  .mov .rax (.mem (hdr Crt.sLink))]
abbrev headA4 : List Instr := [.mov .rdx (.mem (Crt.ws .rax VG.Impl.Ffdh.X86_64.Domain.sXl)), .store (hdr iXl) .rdx]

theorem head_eq : ([.mov .rdx (.mem (Crt.stk 6)), .store (hdr iCtx) .rdx, .mov .rdx (.mem (at_ .rdx 16)),
    .store (hdr iRows) .rdx, .store (hdr iI) .rdx] : List Instr) ++ fromOuter VG.Impl.Ffdh.X86_64.Domain.sX iXp ++
    fromOuter VG.Impl.Ffdh.X86_64.Domain.sXl iXl = headA1 ++ (headA2 ++ (headA3 ++ headA4)) := rfl

/-- What the header block keeps, from its start `s`. -/
def HI (B : Addr) (Z o w : Nat) (mi : BitVec 64) (P : Nat) (s t : State) : Prop :=
  ModCtx t B Z o w mi P ∧ InScr B Z s.mem t.mem ∧ Frm (off B o) [(8 * 17, 8 * 15)] s.mem t.mem ∧
    (∀ k < 32, word t.mem B (8 * k) = word s.mem B (8 * k)) ∧ Keep [.rax, .rdx] s t

theorem HI.store {B : Addr} {Z o w : Nat} {mi : BitVec 64} {P : Nat} {s t u : State} (h : HI B Z o w mi P s t)
    {i : Nat} (hi : 17 ≤ i) (hi' : i < 32) {v : BitVec 64} (hm : u.mem = t.mem.writeW (off (off B o) (8 * i)) v)
    (k : Keep [.rax, .rdx] t u) :
    HI B Z o w mi P s u ∧ word u.mem (off B o) (8 * i) = v ∧
      (∀ k < 32, k ≠ i → word u.mem (off B o) (8 * k) = word t.mem (off B o) (8 * k)) := by
  obtain ⟨hc, hin, hf, hb, kt⟩ := h
  obtain ⟨hc', hf', hw, ho, hin', hb'⟩ := hc.store hi hi' hm k.2.2 (k.gpr (by decide))
  refine ⟨⟨hc', hin.trans hin', Frm.widen (hf.append hf') fun r hr => ?_, fun j hj => (hb' j hj).trans (hb j hj),
    (kt.trans k).mono (by decide)⟩, hw, ho⟩
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(8 * 17, 8 * 15), by simp, by simp only; omega, by simp only; omega⟩

theorem head1_ok {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {P : Nat} {cp : Addr}
    (hc : ModCtx s B Z o w mi P) (hsp : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) (8 * 6)) 8)
    (hCtx : word s.mem (s.gpr .rsp) (8 * 6) = cp) :
    WP isa (.block headA1) s fun t => HI B Z o w mi P s t ∧ t.gpr .rdx = cp := by
  refine WP.mono (WP.keep [.rdx] (Q := fun t => t.mem = s.mem ∧ t.gpr .rdx = cp) (by
    xrun [State.ea, Crt.stk, hdrOff, hsp, hCtx]) rfl) fun t ⟨⟨hm, hd⟩, k⟩ => ⟨⟨?_, fun x _ => by rw [hm],
      fun x _ => by rw [hm], fun _ _ => by rw [hm], k.mono (by decide)⟩, hd⟩
  exact hc.of_inner (fun x _ => by rw [hm]) k.2.2 (k.gpr (by decide))

theorem head2_ok {s t : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {P : Nat} {cp : Addr} {rows : Nat}
    (hs : ModCtx s B Z o w mi P) (hreg : CtxRd s B Z cp (3 + 34 * w)) (hrows : word s.mem cp 16 = BitVec.ofNat 64 rows)
    (h : HI B Z o w mi P s t) (hd : t.gpr .rdx = cp) :
    WP isa (.block headA2) t fun u => HI B Z o w mi P s u ∧ u.gpr .rax = B ∧
      word u.mem (off B o) (8 * iCtx) = cp ∧ word u.mem (off B o) (8 * iRows) = BitVec.ofNat 64 rows ∧
      word u.mem (off B o) (8 * iI) = BitVec.ofNat 64 rows := by
  have hlo := hs.sub.lo
  have hhi := hs.sub.hi
  have hn := hs.sub.scr.nowrap
  have hg := h.1.sub.good
  change WP isa (.block ([.store (hdr iCtx) .rdx] ++ ([.mov .rdx (.mem (at_ .rdx 16)), .store (hdr iRows) .rdx] ++
    ([.store (hdr iI) .rdx] ++ [.mov .rax (.mem (hdr Crt.sLink))])))) t _
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = t.mem.writeW (off (off B o) (8 * iCtx)) cp) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hd, hg.scr.st (d := 8 * iCtx) (hdr_lt_slot _ 8 (by decide))]) rfl)
    fun t₁ ⟨hm₁, k₁⟩ => ?_
  obtain ⟨h₁, hw₁, ho₁⟩ := h.store (by decide) (by decide) hm₁ (k₁.mono (by decide))
  rw [WP.block_append_iff]
  have hg₁ := h₁.1.sub.good
  have hr₁ : word t₁.mem cp 16 = BitVec.ofNat 64 rows := by rw [hreg.word h₁.2.1 (by omega)]; exact hrows
  have hrd₁ : InRegions (t₁.rd ++ t₁.wr) (off cp 16) 8 := by
    rw [(h₁.2.2.2.2).2.1, (h₁.2.2.2.2).2.2]; exact hreg.rd 2 (by omega)
  have hd₁ : t₁.gpr .rdx = cp := (k₁.gpr (by decide)).trans hd
  refine WP.mono (WP.keep [.rdx] (Q := fun u => u.mem = t₁.mem.writeW (off (off B o) (8 * iRows)) (BitVec.ofNat 64 rows) ∧
      u.gpr .rdx = BitVec.ofNat 64 rows) (by
    xrun [State.ea, hdr, at_, hg₁.rdi, hdrOff, hd₁, atOff', hrd₁, hr₁, hg₁.scr.st (d := 8 * iRows) (hdr_lt_slot _ 8 (by decide))]) rfl)
    fun t₂ ⟨⟨hm₂, hd₂⟩, k₂⟩ => ?_
  obtain ⟨h₂, hw₂, ho₂⟩ := h₁.store (by decide) (by decide) hm₂ (k₂.mono (by decide))
  rw [WP.block_append_iff]
  have hg₂ := h₂.1.sub.good
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = t₂.mem.writeW (off (off B o) (8 * iI)) (BitVec.ofNat 64 rows)) (by
    xrun [State.ea, hdr, hg₂.rdi, hdrOff, hd₂, hg₂.scr.st (d := 8 * iI) (hdr_lt_slot _ 8 (by decide))]) rfl)
    fun t₃ ⟨hm₃, k₃⟩ => ?_
  obtain ⟨h₃, hw₃, ho₃⟩ := h₂.store (by decide) (by decide) hm₃ (k₃.mono (by decide))
  have hg₃ := h₃.1.sub.good
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t₃.mem ∧ u.gpr .rax = B) (by
    xrun [State.ea, hdr, hg₃.rdi, hdrOff, hg₃.scr.ld (d := 8 * Crt.sLink) (hdr_lt_slot _ 8 (by decide)),
      h₃.1.sub.link]) rfl)
    fun u ⟨⟨hm, hax⟩, ku⟩ => ?_
  obtain ⟨hc₃, hin₃, hf₃, hb₃, k₃'⟩ := h₃
  refine ⟨⟨hc₃.of_inner (fun x _ => by rw [hm]) ku.2.2 (ku.gpr (by decide)), by intro x hx; rw [hm]; exact hin₃ x hx, fun x hx => by rw [hm]; exact hf₃ x hx,
      fun j hj => by rw [hm]; exact hb₃ j hj, (k₃'.trans ku).mono (by decide)⟩, hax, ?_, ?_, ?_⟩
  · rw [hm, ho₃ _ (by decide) (by decide), ho₂ _ (by decide) (by decide), hw₁]
  · rw [hm, ho₃ _ (by decide) (by decide), hw₂]
  · rw [hm, hw₃]

/-- `fromOuter`'s load and store, then the link again. -/
theorem head3_ok {s t : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {P : Nat} {v : BitVec 64}
    (hv : word s.mem B (8 * VG.Impl.Ffdh.X86_64.Domain.sX) = v)
    (h : HI B Z o w mi P s t) (hax : t.gpr .rax = B) :
    WP isa (.block headA3) t fun u => HI B Z o w mi P s u ∧ u.gpr .rax = B ∧ word u.mem (off B o) (8 * iXp) = v ∧
      (∀ k < 32, k ≠ iXp → word u.mem (off B o) (8 * k) = word t.mem (off B o) (8 * k)) := by
  have hc := h.1
  have hg := hc.sub.good
  have hlo := hc.sub.lo
  have hhi := hc.sub.hi
  have hO : InRegions (t.rd ++ t.wr) (off B (8 * VG.Impl.Ffdh.X86_64.Domain.sX)) 8 := hc.sub.scr.ld (by
    have := hdr_lt_slot w 8 (show VG.Impl.Ffdh.X86_64.Domain.sX < 32 by decide); omega)
  have hv' : word t.mem B (8 * VG.Impl.Ffdh.X86_64.Domain.sX) = v := (h.2.2.2.1 _ (by decide)).trans hv
  change WP isa (.block ([.mov .rdx (.mem (Crt.ws .rax VG.Impl.Ffdh.X86_64.Domain.sX)), .store (hdr iXp) .rdx] ++
    [.mov .rax (.mem (hdr Crt.sLink))])) t _
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun u => u.mem = t.mem.writeW (off (off B o) (8 * iXp)) v) (by
    xrun [State.ea, hdr, Crt.ws, hg.rdi, hdrOff, hax, hO, hv', hg.scr.st (d := 8 * iXp) (hdr_lt_slot _ 8 (by decide))]) rfl)
    fun t₁ ⟨hm₁, k₁⟩ => ?_
  obtain ⟨h₁, hw₁, ho₁⟩ := h.store (by decide) (by decide) hm₁ (k₁.mono (by decide))
  have hg₁ := h₁.1.sub.good
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t₁.mem ∧ u.gpr .rax = B) (by
    xrun [State.ea, hdr, hg₁.rdi, hdrOff, hg₁.scr.ld (d := 8 * Crt.sLink) (hdr_lt_slot _ 8 (by decide)),
      h₁.1.sub.link]) rfl)
    fun u ⟨⟨hm, hax'⟩, ku⟩ => ?_
  obtain ⟨hc₁, hin₁, hf₁, hb₁, k₁'⟩ := h₁
  refine ⟨⟨hc₁.of_inner (fun x _ => by rw [hm]) ku.2.2 (ku.gpr (by decide)),
      by intro x hx; rw [hm]; exact hin₁ x hx, fun x hx => by rw [hm]; exact hf₁ x hx,
      fun j hj => by rw [hm]; exact hb₁ j hj, (k₁'.trans ku).mono (by decide)⟩, hax', by rw [hm, hw₁],
    fun j hj hne => by rw [hm]; exact ho₁ j hj hne⟩

theorem head4_ok {s t : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {P : Nat} {v : BitVec 64}
    (hv : word s.mem B (8 * VG.Impl.Ffdh.X86_64.Domain.sXl) = v)
    (h : HI B Z o w mi P s t) (hax : t.gpr .rax = B) :
    WP isa (.block headA4) t fun u => HI B Z o w mi P s u ∧ word u.mem (off B o) (8 * iXl) = v ∧
      (∀ k < 32, k ≠ iXl → word u.mem (off B o) (8 * k) = word t.mem (off B o) (8 * k)) := by
  have hc := h.1
  have hg := hc.sub.good
  have hlo := hc.sub.lo
  have hhi := hc.sub.hi
  have hO : InRegions (t.rd ++ t.wr) (off B (8 * VG.Impl.Ffdh.X86_64.Domain.sXl)) 8 := hc.sub.scr.ld (by
    have := hdr_lt_slot w 8 (show VG.Impl.Ffdh.X86_64.Domain.sXl < 32 by decide); omega)
  have hv' : word t.mem B (8 * VG.Impl.Ffdh.X86_64.Domain.sXl) = v := (h.2.2.2.1 _ (by decide)).trans hv
  refine WP.mono (WP.keep [.rdx] (Q := fun u => u.mem = t.mem.writeW (off (off B o) (8 * iXl)) v) (by
    xrun [State.ea, hdr, Crt.ws, hg.rdi, hdrOff, hax, hO, hv', hg.scr.st (d := 8 * iXl) (hdr_lt_slot _ 8 (by decide))]) rfl)
    fun u ⟨hm, k⟩ => ?_
  obtain ⟨h₁, hw₁, ho₁⟩ := h.store (by decide) (by decide) hm (k.mono (by decide))
  exact ⟨h₁, hw₁, ho₁⟩

/-- The comb's pointers and counts into the inner header: `iCtx`, `iRows`,
`iI := rows`, `iXp` and `iXl`. -/
theorem combHead_ok {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {P : Nat}
    (hc : ModCtx s B Z o w mi P) {cp xp : Addr} {L rows : Nat}
    (hsp : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) (8 * 6)) 8)
    (hCtx : word s.mem (s.gpr .rsp) (8 * 6) = cp) (hX : word s.mem B (8 * VG.Impl.Ffdh.X86_64.Domain.sX) = xp)
    (hXl : word s.mem B (8 * VG.Impl.Ffdh.X86_64.Domain.sXl) = BitVec.ofNat 64 L)
    (hreg : CtxRd s B Z cp (3 + 34 * w)) (hrows : word s.mem cp 16 = BitVec.ofNat 64 rows) :
    WP isa (.block (([.mov .rdx (.mem (Crt.stk 6)), .store (hdr iCtx) .rdx, .mov .rdx (.mem (at_ .rdx 16)),
      .store (hdr iRows) .rdx, .store (hdr iI) .rdx] : List Instr) ++ fromOuter VG.Impl.Ffdh.X86_64.Domain.sX iXp ++
      fromOuter VG.Impl.Ffdh.X86_64.Domain.sXl iXl)) s fun t => ModCtx t B Z o w mi P ∧
      word t.mem (off B o) (8 * iCtx) = cp ∧ word t.mem (off B o) (8 * iRows) = BitVec.ofNat 64 rows ∧
      word t.mem (off B o) (8 * iI) = BitVec.ofNat 64 rows ∧ word t.mem (off B o) (8 * iXp) = xp ∧
      word t.mem (off B o) (8 * iXl) = BitVec.ofNat 64 L ∧ Frm (off B o) [(8 * 17, 8 * 15)] s.mem t.mem ∧
      InScr B Z s.mem t.mem ∧ Keep [.rax, .rdx] s t := by
  rw [head_eq, WP.block_append_iff]
  refine WP.mono (head1_ok hc hsp hCtx) fun t₁ ⟨h₁, hd₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (head2_ok hc hreg hrows h₁ hd₁) fun t₂ ⟨h₂, hax₂, hC, hR, hI⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (head3_ok hX h₂ hax₂) fun t₃ ⟨h₃, hax₃, hXp, ho₃⟩ => ?_
  refine WP.mono (head4_ok hXl h₃ hax₃) fun t ⟨h₄, hXl', ho₄⟩ => ?_
  obtain ⟨hc₄, hin₄, hf₄, _, k₄⟩ := h₄
  refine ⟨hc₄, ?_, ?_, ?_, ?_, hXl', hf₄, hin₄, k₄⟩
  · rw [ho₄ _ (by decide) (by decide), ho₃ _ (by decide) (by decide), hC]
  · rw [ho₄ _ (by decide) (by decide), ho₃ _ (by decide) (by decide), hR]
  · rw [ho₄ _ (by decide) (by decide), ho₃ _ (by decide) (by decide), hI]
  · rw [ho₄ _ (by decide) (by decide), hXp]

/-- Montgomery multiplication in the inner workspace for `P`. -/
theorem mm_mc (Mo : Mont) {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {P : Nat}
    (hc : ModCtx s B Z o w mi P) {out a b : Nat} (ho : out = aX ∨ out = aXm ∨ out = aY) (ha : a < 8) (hb : b < 8)
    (ha₁ : a ≠ aAcc) (ha₂ : a ≠ aTmp) (hb₁ : b ≠ aAcc) (hb₂ : b ≠ aTmp)
    (hbl : wv s.mem (off B o) (slot w b) w < P) :
    WP isa (Mo.mm out a b) s fun t => ModCtx t B Z o w mi P ∧
      wv t.mem (off B o) (slot w out) w < P ∧
      wv t.mem (off B o) (slot w out) w * 2 ^ (64 * w) % P =
        wv s.mem (off B o) (slot w a) w * wv s.mem (off B o) (slot w b) w % P ∧
      Frm (off B o) (combR w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hout : out < 8 := by rcases ho with rfl | rfl | rfl <;> decide
  have ho₁ : out ≠ aAcc := by rcases ho with rfl | rfl | rfl <;> decide
  have ho₂ : out ≠ aTmp := by rcases ho with rfl | rfl | rfl <;> decide
  refine WP.mono (Mo.mm_ok hc.sub.good (Nat.le_refl _) (by have := hc.w2; omega) (by have := hc.w28; omega) hout
    ha hb ho₁ ho₂ ha₁ hb₁ hc.xv.inv (by rw [hc.xv.n]; exact hbl) ha₂ hb₂) fun t ⟨_, hl, hv, ha', k⟩ => ?_
  rw [hc.xv.n] at hl hv
  have hf : Frm (off B o) (combR w) s.mem t.mem := Frm.toCombR (Frm.of_arrays ha' (by simp)) (mm_combR w ho)
  exact ⟨hc.of_inner (Frm.widen hf (combR_inner w)) k.2.2 (k.gpr (by decide)), hl, hv, hf, k⟩

theorem TabP.M_zero (T : TabP) (h1 : 1 < T.P) : T.M 0 = T.R % T.P := by
  unfold TabP.M
  rw [powMod_eq, Nat.pow_zero, Nat.mod_eq_of_lt h1, Nat.one_mul]

/-- What the comb needs: the inner workspace for `p`, the context and its
pointer, the scalar's bytes, and their pointer and count in the outer header. -/
structure CombIn (T : TabP) (xp : Addr) (xb : List Byte) (s : State) : Prop where
  hc : ModCtx s T.B T.Z T.o T.w T.mi T.P
  hsp : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) (8 * 6)) 8
  hspo : ∀ {m : Mem}, InScr T.B T.Z s.mem m → word m (s.gpr .rsp) (8 * 6) = word s.mem (s.gpr .rsp) (8 * 6)
  hCtx : word s.mem (s.gpr .rsp) (8 * 6) = T.cp
  hX : word s.mem T.B (8 * VG.Impl.Ffdh.X86_64.Domain.sX) = xp
  hXl : word s.mem T.B (8 * VG.Impl.Ffdh.X86_64.Domain.sXl) = BitVec.ofNat 64 xb.length
  hreg : CtxRd s T.B T.Z T.cp T.n
  hrows : word s.mem T.cp 16 = BitVec.ofNat 64 T.rows
  hent : ∀ a < 32, row s.mem T.cp T.w (2 + a) = Spec.Rsa.toWords (T.entry a) T.w
  hx : Src s T.B T.Z xp xb
  hr1 : 1 ≤ T.rows
  hr : 5 * T.rows < 2 ^ 31
  hL : 8 * xb.length < 2 ^ 32
  hxb : Spec.Rsa.os2ip xb < 2 ^ T.bits

/-- After `aY := R mod p`. -/
def C1 (T : TabP) (s s₁ : State) : Prop :=
  ModCtx s₁ T.B T.Z T.o T.w T.mi T.P ∧ wv s₁.mem (off T.B T.o) (slot T.w aY) T.w = T.M 0 ∧
    Frm (off T.B T.o) (combR T.w) s.mem s₁.mem ∧ Keep mmRegs s s₁

theorem comb1_ok (Mo : Mont) {T : TabP} {xp : Addr} {xb : List Byte} {s : State} (h : CombIn T xp xb s) :
    WP isa (Mo.mm aY aR2 aOne) s (C1 T s) := by
  have hc := h.hc
  have hR : Nat.Coprime T.R T.P := VG.Proof.Bignum.coprime_pow2 hc.odd _
  refine WP.mono (mm_mc Mo hc (Or.inr (Or.inr rfl)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [hc.xv.one]; exact hc.x1)) fun s₁ ⟨hc₁, hl₁, hv₁, hf₁, k₁⟩ =>
    ⟨hc₁, ?_, hf₁, k₁⟩
  rw [T.M_zero hc.x1]
  have := mont_cancel hR (o := wv s₁.mem (off T.B T.o) (slot T.w aY) T.w) (c := T.R) (by
    rw [hv₁, hc.xv.one, Nat.mul_one, ← hc.r2])
  rw [Nat.mod_eq_of_lt hl₁] at this
  exact this

/-- What the header block needs after `aY := R mod p`. -/
theorem C1.head {T : TabP} {xp : Addr} {xb : List Byte} {s s₁ : State} (h : CombIn T xp xb s) (h₁ : C1 T s s₁) :
    InRegions (s₁.rd ++ s₁.wr) (off (s₁.gpr .rsp) (8 * 6)) 8 ∧ word s₁.mem (s₁.gpr .rsp) (8 * 6) = T.cp ∧
      word s₁.mem T.B (8 * VG.Impl.Ffdh.X86_64.Domain.sX) = xp ∧
      word s₁.mem T.B (8 * VG.Impl.Ffdh.X86_64.Domain.sXl) = BitVec.ofNat 64 xb.length ∧
      CtxRd s₁ T.B T.Z T.cp (3 + 34 * T.w) ∧ word s₁.mem T.cp 16 = BitVec.ofNat 64 T.rows ∧
      InScr T.B T.Z s.mem s₁.mem := by
  obtain ⟨_, _, hf₁, k₁⟩ := h₁
  have hc := h.hc
  have hn := hc.sub.scr.nowrap
  obtain ⟨hh₁, hin₁⟩ := VG.Proof.Ffdh.X86_64.child_frm hc.sub hc.wide hf₁ fun r hr => by
    have := (combR_le T.w r hr).2; omega
  exact ⟨by rw [k₁.2.1, k₁.2.2, k₁.gpr (by decide)]; exact h.hsp,
    by rw [k₁.gpr (by decide), h.hspo hin₁]; exact h.hCtx, by rw [hh₁ _ (by decide)]; exact h.hX,
    by rw [hh₁ _ (by decide)]; exact h.hXl, h.hreg.congr k₁.2.1 k₁.2.2,
    by rw [h.hreg.word hin₁ (by unfold TabP.n; omega)]; exact h.hrows, hin₁⟩

/-- After the header block: the rows' invariant, from no row. -/
theorem head_cinv {T : TabP} {xp : Addr} {xb : List Byte} {s s₁ s₂ : State} (h : CombIn T xp xb s)
    (h₁ : C1 T s s₁) (hc₂ : ModCtx s₂ T.B T.Z T.o T.w T.mi T.P)
    (hC₂ : word s₂.mem (off T.B T.o) (8 * iCtx) = T.cp)
    (hR₂ : word s₂.mem (off T.B T.o) (8 * iRows) = BitVec.ofNat 64 T.rows)
    (hI₂ : word s₂.mem (off T.B T.o) (8 * iI) = BitVec.ofNat 64 T.rows)
    (hXp₂ : word s₂.mem (off T.B T.o) (8 * iXp) = xp)
    (hXl₂ : word s₂.mem (off T.B T.o) (8 * iXl) = BitVec.ofNat 64 xb.length)
    (hf₂ : Frm (off T.B T.o) [(8 * 17, 8 * 15)] s₁.mem s₂.mem) (hin₂ : InScr T.B T.Z s₁.mem s₂.mem)
    (k₂ : Keep [.rax, .rdx] s₁ s₂) : CInv T xp xb s₂ 0 s₂ := by
  have hin₁ := (h₁.head h).2.2.2.2.2.2
  obtain ⟨_, hY₁, _, k₁⟩ := h₁
  have hin₁₂ := hin₁.trans hin₂
  have he₂ : CEnv T xp xb s₂ := ⟨hc₂, hC₂, hR₂, hXp₂, hXl₂, h.hreg.congr (k₁.trans k₂).2.1 (k₁.trans k₂).2.2,
    fun a ha => by
      rw [← h.hent a ha]
      refine row_congr fun i hi => h.hreg.word hin₁₂ ?_
      have : T.w * (2 + a) + T.w ≤ 34 * T.w := by
        have h := Nat.mul_le_mul_left T.w (show 2 + a + 1 ≤ 34 by omega); rw [Nat.mul_succ] at h; omega
      unfold TabP.n
      rw [Nat.mul_assoc]; omega,
    h.hx.congr hin₁₂ (k₁.trans k₂).2.1 (k₁.trans k₂).2.2⟩
  have hY₂ : wv s₂.mem (off T.B T.o) (slot T.w aY) T.w = T.M 0 := by
    rw [hf₂.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inr (by have := hdr_lt_slot T.w aY (show 31 < 32 by decide); simp only; omega))
      (by simp only [slot, hdrBytes, aY]; have := h.hc.w28; omega), hY₁]
  exact ⟨he₂, by rw [hI₂, Nat.sub_zero], by rw [hY₂, Nat.sub_zero, Rsa.FixedBaseComb.high_top],
    fun _ _ => rfl, Keep.refl _ _⟩

/-- Out of Montgomery form, after the rows. -/
theorem combEnd_ok (Mo : Mont) {T : TabP} {xp : Addr} {xb : List Byte} {s₀ t : State}
    (hx1 : 1 < T.P) (hxb : Spec.Rsa.os2ip xb < 2 ^ T.bits) (h : CInv T xp xb s₀ T.rows t) :
    WP isa (Mo.mm aY aY aOne) t fun u => ModCtx u T.B T.Z T.o T.w T.mi T.P ∧
      wv u.mem (off T.B T.o) (slot T.w aY) T.w = Spec.Rsa.powMod T.G (Spec.Rsa.os2ip xb) T.P ∧
      Frm (off T.B T.o) (combR T.w) t.mem u.mem ∧ Keep mmRegs t u := by
  have hP : 0 < T.P := by omega
  obtain ⟨he₃, _, hy₃, _, _⟩ := h
  have hR : Nat.Coprime T.R T.P := VG.Proof.Bignum.coprime_pow2 he₃.mc.odd _
  rw [Nat.sub_self, Rsa.FixedBaseComb.high_zero _ _ hxb] at hy₃
  refine WP.mono (mm_cenv Mo he₃ (Or.inr (Or.inr rfl)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [he₃.mc.xv.one]; exact hx1)) fun u ⟨heu, hlu, hvu, _, hfu, ku⟩ => ?_
  rw [hy₃, he₃.mc.xv.one, Nat.mul_one] at hvu
  refine ⟨heu.mc, ?_, hfu, ku⟩
  have := mont_cancel hR (o := wv u.mem (off T.B T.o) (slot T.w aY) T.w)
    (c := Spec.Rsa.powMod T.G (Spec.Rsa.os2ip xb) T.P) (by rw [hvu]; unfold TabP.M; rw [Nat.mod_mod])
  rw [Nat.mod_eq_of_lt hlu, Nat.mod_eq_of_lt (by rw [powMod_eq]; exact Nat.mod_lt _ hP)] at this
  exact this

/-- `aY := g^x mod p`, by the context's comb over its rows. -/
theorem comb_ok' (Mo : Mont) {T : TabP} {xp : Addr} {xb : List Byte} {s : State} (h : CombIn T xp xb s) :
    WP isa (seqs (comb Mo.mm)) s fun t => ModCtx t T.B T.Z T.o T.w T.mi T.P ∧
      wv t.mem (off T.B T.o) (slot T.w aY) T.w = Spec.Rsa.powMod T.G (Spec.Rsa.os2ip xb) T.P ∧
      Frm (off T.B T.o) (innerR T.w) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold comb
  refine wp_seqs_cons (by simp) (WP.mono (comb1_ok Mo h) fun s₁ h₁ => ?_)
  obtain ⟨hsp₁, hCtx₁, hX₁, hXl₁, hreg₁, hrows₁, _⟩ := h₁.head h
  refine wp_seqs_cons (by simp) (WP.mono (combHead_ok h₁.1 (cp := T.cp) (xp := xp) (L := xb.length) (rows := T.rows)
    hsp₁ hCtx₁ hX₁ hXl₁ hreg₁ hrows₁) fun s₂ ⟨hc₂, hC₂, hR₂, hI₂, hXp₂, hXl₂, hf₂, hin₂, k₂⟩ => ?_)
  have hI0 := head_cinv h h₁ hc₂ hC₂ hR₂ hI₂ hXp₂ hXl₂ hf₂ hin₂ k₂
  refine wp_seqs_cons (by simp) (wp_upto (a := 0) (N := T.rows) h.hr1 (CInv T xp xb s₂)
    (fun j _ hj t hI => combStep_ok Mo h.hr h.hL hj hI) (fun t hI => ?_) hI0)
  refine WP.mono (combEnd_ok Mo h.hc.x1 h.hxb hI) fun u ⟨hcu, hv, hfu, ku⟩ => ⟨hcu, hv, ?_, ?_⟩
  · have w₁ := Frm.widen h₁.2.2.1 (combR_inner T.w)
    have w₂ : Frm (off T.B T.o) (innerR T.w) s₁.mem s₂.mem := Frm.widen hf₂ fun r hr =>
      ⟨(8 * 17, 8 * 15), by simp [innerR], by rw [List.mem_singleton.mp hr], by rw [List.mem_singleton.mp hr]⟩
    have w₃ := Frm.widen hI.2.2.2.1 (combR_inner T.w)
    have w₄ := Frm.widen hfu (combR_inner T.w)
    exact ((w₁.trans w₂).trans w₃).trans w₄
  · exact (((h₁.2.2.2.trans k₂).trans hI.2.2.2.2).trans ku).mono (by decide)

theorem comb_ok (Mo : Mont) {T : TabP} {xp : Addr} {xb : List Byte} {s : State}
    (hc : ModCtx s T.B T.Z T.o T.w T.mi T.P)
    (hsp : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) (8 * 6)) 8)
    (hspo : ∀ {m : Mem}, InScr T.B T.Z s.mem m → word m (s.gpr .rsp) (8 * 6) = word s.mem (s.gpr .rsp) (8 * 6))
    (hCtx : word s.mem (s.gpr .rsp) (8 * 6) = T.cp) (hX : word s.mem T.B (8 * VG.Impl.Ffdh.X86_64.Domain.sX) = xp)
    (hXl : word s.mem T.B (8 * VG.Impl.Ffdh.X86_64.Domain.sXl) = BitVec.ofNat 64 xb.length)
    (hreg : CtxRd s T.B T.Z T.cp T.n) (hrows : word s.mem T.cp 16 = BitVec.ofNat 64 T.rows)
    (hent : ∀ a < 32, row s.mem T.cp T.w (2 + a) = Spec.Rsa.toWords (T.entry a) T.w)
    (hx : Src s T.B T.Z xp xb)
    (hr1 : 1 ≤ T.rows) (hr : 5 * T.rows < 2 ^ 31) (hL : 8 * xb.length < 2 ^ 32)
    (hxb : Spec.Rsa.os2ip xb < 2 ^ T.bits) :
    WP isa (seqs (comb Mo.mm)) s fun t => ModCtx t T.B T.Z T.o T.w T.mi T.P ∧
      wv t.mem (off T.B T.o) (slot T.w aY) T.w = Spec.Rsa.powMod T.G (Spec.Rsa.os2ip xb) T.P ∧
      Frm (off T.B T.o) (innerR T.w) s.mem t.mem ∧ Keep mmRegs s t :=
  comb_ok' Mo ⟨hc, hsp, hspo, hCtx, hX, hXl, hreg, hrows, hent, hx, hr1, hr, hL, hxb⟩

end VG.Proof.Ffdh.X86_64.Cached
