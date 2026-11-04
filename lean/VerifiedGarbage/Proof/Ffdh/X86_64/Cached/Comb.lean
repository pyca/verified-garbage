module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Table
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.CrtFrame
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
  have hl : ∀ k < 32, InRegions (s.rd ++ s.wr) (off O (8 * k)) 8 := fun k hk => hg.scr.ld (by omega)
  unfold tooth
  refine WP.seq (WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (i + j * rows) ∧
      t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl iI (by decide), hl iRows (by decide), hI, hR, ofNat_succ_sub_one,
      execImul3, imul3_low', mul_imm (show j < 2 ^ 31 by omega), BitVec.ofNat_add_ofNat]
    rw [Nat.mul_comm]) rfl) fun s₁ ⟨⟨ha₁, hm₁⟩, k₁⟩ => ?_)
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

/-- Entry `e` of the scan. -/
theorem selectStep_ok {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {cp : Addr}
    (hc : SubCtx s B Z o w w mi) (hwide : o + slot w 8 + tabBytes w 32 ≤ Z)
    (hctx : word s.mem (off B o) (8 * iCtx) = cp) (hreg : CtxRd s B Z cp (3 + 34 * w))
    (hw : 1 ≤ w) (hw' : w < 2 ^ 28) {E : Nat → Nat → BitVec 64}
    (hE : ∀ a < 32, ∀ i < w, word s.mem cp (24 + 8 * w * (a + 2) + 8 * i) = E a i)
    {d : Nat} (h13 : s.gpr .r13 = BitVec.ofNat 64 d) (hd : d < 32) {e : Nat} (he : e < 32) {t : State}
    (hI : SelO B o w E d s e t) :
    WP isa selectStep t fun u => u.zf = some (decide (e + 1 = 32)) ∧ SelO B o w E d s (e + 1) u := by
  obtain ⟨hf, hiE, hsel, k⟩ := hI
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have hsx := slot_le (w := w) (show aXm < 8 by decide)
  have hcn := hreg.nowrap
  have hct : SubCtx t B Z o w w mi := hc.of_frm hf (selR_ok w) k.2.2 (k.gpr (by decide))
  have hctxt : word t.mem (off B o) (8 * iCtx) = cp := (hf.word_eq (fun r hr => by
    have := hdr_lt_slot w aXm (show iCtx < 32 by decide)
    simp only [selR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [iCtx, iE, sFn] at * <;> omega) (by unfold iCtx sFn; omega)).trans hctx
  have hin : InScr B Z s.mem t.mem :=
    (VG.Proof.Ffdh.X86_64.child_frm hc hwide hf fun r hr => by have := (selR_ok w r hr).2; omega).2
  have hEt : ∀ a < 32, ∀ i < w, word t.mem cp (24 + 8 * w * (a + 2) + 8 * i) = E a i := fun a ha i hi' => by
    have : w * (a + 2) + w ≤ 34 * w := by have := Nat.mul_le_mul_left w (show a + 3 ≤ 34 by omega); rw [Nat.mul_add] at this ⊢; omega
    rw [hreg.word hin (by rw [Nat.mul_assoc]; omega)]; exact hE a ha i hi'
  have h13t : t.gpr .r13 = BitVec.ofNat 64 d := (k.gpr (by decide)).trans h13
  have hrt : CtxRd t B Z cp (3 + 34 * w) := hreg.congr k.2.1 k.2.2
  unfold selectStep
  simp only [seqs]
  have hZ8 : 8 * 32 ≤ slot w 8 := by unfold slot hdrBytes; omega
  refine WP.seq (WP.mono (mask_ok hct.good hZ8 hiE h13t he hd) fun t₁ ⟨hdx, hax, hm₁, k₁⟩ => ?_)
  have hct₁ : SubCtx t₁ B Z o w w mi := hct.of_frm (rs := []) (fun x _ => by rw [hm₁]) (by simp) k₁.2.2
    (k₁.gpr (by decide))
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (rowPtr_ok (cp := cp) hct₁ (by rw [hm₁]; exact hctxt) hax) fun t₂ ⟨hbx, h12, hm₂, k₂⟩ => ?_
  have hg₂ : Good t₂ (off B o) (slot w 8) w mi :=
    ⟨hct₁.good.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hct₁.good.rdi, by rw [hm₂]; exact hct₁.good.hdr⟩
  have hA := hdr_lt_slot w 8 (show sArr aXm < 32 by unfold sArr aXm; omega)
  refine WP.mono (WP.keep [.rsi, .rbx] (Q := fun u => u.gpr .rsi = off cp (24 + 8 * w * (e + 2)) ∧
      u.gpr .rbx = off (off B o) (slot w aXm) ∧ u.mem = t₂.mem)
    (by xrun [State.ea, hdr, hg₂.rdi, hdrOff, hbx, hg₂.scr.ld (d := 8 * sArr aXm) (by omega),
      hg₂.hdr.harr aXm (by decide)]) rfl)
    fun t₃ ⟨⟨hsi, hbx₃, hm₃⟩, k₃⟩ => ?_
  have k13 : Keep ([.rax, .rdx] ++ [.rbx, .r12] ++ [.rsi, .rbx]) t t₃ := (k₁.trans k₂).trans k₃
  have hm13 : t₃.mem = t.mem := hm₃.trans (hm₂.trans hm₁)
  have hsc₃ : Scr t₃ (off B o) (slot w 8) := hct.good.scr.congr k13.2.2
  have hfit : 3 + w * (e + 2) + w ≤ 3 + 34 * w := by
    have := Nat.mul_le_mul_left w (show e + 3 ≤ 34 by omega); rw [Nat.mul_add] at this ⊢; omega
  have e8 : 8 * w * (e + 2) = 8 * (w * (e + 2)) := Nat.mul_assoc _ _ _
  have h0 : ∀ u, u.gpr .r14 = BitVec.ofNat 64 0 → u.mem = t₃.mem → Keep [.r14] t₃ u → u.cf = t₃.cf →
      SelW t₃ (off B o) (slot w aXm) E d e 0 u := fun u h14 hm ku _ =>
    ⟨ku.mono (by decide), h14, fun i hi => absurd hi (Nat.not_lt_zero _), by rw [hm]; exact Outside.refl _ _ _ _⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) (by omega) (SelW t₃ (off B o) (slot w aXm) E d e) h0
    (fun j _ hj u hI => selStep_ok hsi hbx₃ ((k₃.gpr (by decide)).trans h12)
      (((k₂.trans k₃).gpr (by decide)).trans hdx) (by omega) (by omega)
      (fun i hi' => by rw [k13.2.1, k13.2.2, rowOff]; exact hrt.rd (3 + w * (e + 2) + i) (by omega))
      (fun i hi' => hsc₃.ld (by omega)) (fun i hi' => hsc₃.st (by omega))
      (fun i hi' b hb => Or.inr (by
        have hb' : 24 + 8 * w * (e + 2) + 8 * i + b < 8 * (3 + 34 * w) := by omega
        have := hreg.out (d := 24 + 8 * w * (e + 2) + 8 * i + b) hb'
        rw [show off cp (24 + 8 * w * (e + 2) + 8 * i + b) =
            off cp (24 + 8 * w * (e + 2) + 8 * i) + BitVec.ofNat 64 b by
          simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]] at this
        rcases ofs_rebase B (off cp (24 + 8 * w * (e + 2) + 8 * i) + BitVec.ofNat 64 b) (o := o) (by omega)
          with ⟨_, h⟩ | ⟨h, _⟩
        · rw [h]; omega
        · omega))
      (fun i hi' => by rw [hm13]; exact hEt e he i hi') (fun i hi' => by rw [hm13]; exact hsel i hi') hj hI))
    fun t₄ hW => ?_)
  have hsc₄ : Scr t₄ (off B o) (slot w 8) := hsc₃.congr hW.keep.2.2
  have hE₄ : word t₄.mem (off B o) (8 * iE) = BitVec.ofNat 64 e := by
    rw [hW.frame.word (Or.inl (by have := hdr_lt_slot w aXm (show iE < 32 by decide); omega))
      (by unfold iE sFn; omega), hm13, hiE]
  have hdi₄ : t₄.gpr .rdi = off B o := ((k13.trans hW.keep).gpr (by decide)).trans hct.rdi
  have hlE := hdr_lt_slot w 8 (show iE < 32 by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.zf = some (decide (e + 1 = 32)) ∧
      u.mem = t₄.mem.writeW (off (off B o) (8 * iE)) (BitVec.ofNat 64 (e + 1))) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hsc₄.ld (d := 8 * iE) (by omega), hsc₄.st (d := 8 * iE) (by omega), hE₄,
      ofNat_add_one', ofNat_cmp32 he]) rfl)
    fun t₅ ⟨⟨hz, hm₅⟩, k₅⟩ => ⟨hz, ?_⟩
  have ho₅ := writeW_outside t₄.mem (off B o) (d := 8 * iE) (BitVec.ofNat 64 (e + 1)) (by omega)
  rw [← hm₅] at ho₅
  have hf₄ : Frm (off B o) [(slot w aXm, 8 * w)] t.mem t₄.mem := by
    rw [← hm13]; exact Frm.of_outside hW.frame (List.mem_singleton.mpr rfl)
  refine ⟨Frm.widen ((hf.append hf₄).append (Frm.of_outside ho₅ (List.mem_singleton.mpr rfl))) fun r hr => ?_,
    by rw [hm₅]; exact word_writeW_self _ _ _ _, fun i hi' => ?_, ((k.trans (k13.trans hW.keep)).trans k₅).mono (by decide)⟩
  · simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (hr | rfl) | rfl
    · exact ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [selR], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [selR], Nat.le_refl _, Nat.le_refl _⟩
  · rw [ho₅.word (Or.inr (by have := hdr_lt_slot w aXm (show iE < 32 by decide); omega)) (by omega)]
    exact hW.done i hi'

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
    (fun e _ he t hI => selectStep_ok hc hwide hctx hreg hw hw' hE h13 hd he hI) (fun t ⟨hf, _, hsel, k⟩ => ?_) hI0
  exact ⟨fun i hi' => (hsel i hi').trans (by unfold sel; rw [ite_eq_left hd]), hf, k⟩

end VG.Proof.Ffdh.X86_64.Cached
