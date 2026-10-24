module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.ModArithReduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Prep

/-!
# An FFDH parameter candidate on PPC64LE: the bit-serial remainder

`smallMod_ok`: `r3 := ` the number in the `w` words at array 0 modulo `d`
(in `r4`, from 2 to `2^62`), from the top bit: `r := 2 r + b`, less `d` when
that is not negative (`modStep_ok`, by the sign of the difference as a mask:
`sub_sel`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE

/-- `t` or `t − d` by the sign of `t − d` as a mask: `t mod d` for `t < 2 d`. -/
theorem sub_sel {t d : Nat} (ht : t < 2 ^ 63) (hd : d < 2 ^ 63) :
    BitVec.ofNat 64 t ^^^ ((BitVec.ofNat 64 t - BitVec.ofNat 64 d ^^^ BitVec.ofNat 64 t) &&&
        ((BitVec.ofNat 64 t - BitVec.ofNat 64 d) >>> 63 - BitVec.ofNat 64 1)) =
      BitVec.ofNat 64 (if d ≤ t then t - d else t) := by
  by_cases h : d ≤ t
  · have e : BitVec.ofNat 64 t - BitVec.ofNat 64 d = BitVec.ofNat 64 (t - d) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    have e2 : BitVec.ofNat 64 (t - d) >>> 63 - BitVec.ofNat 64 1 = BitVec.allOnes 64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_allOnes,
        Nat.shiftRight_eq_div_pow]
      have : (t - d) % 2 ^ 64 / 2 ^ 63 = 0 := by rw [Nat.div_eq_of_lt]; omega
      omega
    rw [e, e2, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_comm (BitVec.ofNat 64 t), BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero, ite_eq_left h]
  · have e2 : (BitVec.ofNat 64 t - BitVec.ofNat 64 d) >>> 63 - BitVec.ofNat 64 1 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
      have h1 : (2 ^ 64 - d % 2 ^ 64 + t % 2 ^ 64) % 2 ^ 64 / 2 ^ 63 = 1 := by
        rw [Nat.mod_eq_of_lt (show t < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (by omega)]
        omega
      rw [h1]
    rw [e2, BitVec.and_zero, BitVec.xor_zero, ite_eq_right h]

/-- One step of the remainder: `r3 := (2 r + b) mod d` for `b` the top bit
of `r7`, which is shifted left. -/
theorem modStep_ok (u : State) {d r : Nat} (hd : 2 ≤ d) (hd' : d < 2 ^ 62) (h4 : u.gpr .r4 = BitVec.ofNat 64 d)
    (h3 : u.gpr .r3 = BitVec.ofNat 64 r) (hr : r < d) :
    WP isa (.block ([.lsr .d .r9 .r7 63, .lsl .r7 .r7 1, .add .r3 .r3 .r3, .add .r3 .r3 .r9,
        .sub .r9 .r3 .r4, .lsr .d .r14 .r9 63, .subi .r14 .r14 1, .logic .xor .r9 .r9 .r3,
        .logic .and .r9 .r9 .r14, .logic .xor .r3 .r3 .r9] : List Instr)) u fun u' =>
      (u'.gpr .r3 = BitVec.ofNat 64 ((2 * r + (u.gpr .r7 >>> 63).toNat) % d) ∧ u'.gpr .r7 = u.gpr .r7 <<< 1 ∧
        u'.mem = u.mem) ∧ Keep [.r3, .r7, .r9, .r14] u u' := by
  refine WP.keep _ ?_ (by decide)
  have hb : (u.gpr .r7 >>> 63).toNat ≤ 1 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := (u.gpr .r7).isLt; omega
  have et : BitVec.ofNat 64 r + BitVec.ofNat 64 r + u.gpr .r7 >>> 63 =
      BitVec.ofNat 64 (2 * r + (u.gpr .r7 >>> 63).toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  prun [h3, h4]
  rw [et, sub_sel (by omega) (by omega)]
  congr 1
  generalize (u.gpr .r7 >>> 63).toNat = b at hb
  split
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem top_bit (x : BitVec 64) {i : Nat} (hi : i < 64) :
    (BitVec.ofNat 64 (x.toNat * 2 ^ i % 2 ^ 64) >>> 63).toNat = x.toNat / 2 ^ (63 - i) % 2 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_mod, Nat.shiftRight_eq_div_pow]
  have e1 : (2 : Nat) ^ 64 = 2 ^ i * (2 ^ (63 - i) * 2) := by
    rw [← Nat.pow_succ, ← Nat.pow_add]; congr 1; omega
  have e2 : (2 : Nat) ^ 63 = 2 ^ i * 2 ^ (63 - i) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e1, e2, Nat.mul_comm x.toNat, Nat.mul_mod_mul_left, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _),
    Nat.mod_mul_right_div_self]

theorem shl_step (x : BitVec 64) (i : Nat) :
    BitVec.ofNat 64 (x.toNat * 2 ^ i % 2 ^ 64) <<< 1 = BitVec.ofNat 64 (x.toNat * 2 ^ (i + 1) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod, Nat.shiftLeft_eq,
    Nat.pow_succ 2 i, ← Nat.mul_assoc, Nat.pow_one, Nat.mod_mul_mod, Nat.mod_mod]

theorem div_step (x : Nat) {i : Nat} (hi : i < 64) : x / 2 ^ (63 - i) = 2 * (x / 2 ^ (64 - i)) + x / 2 ^ (63 - i) % 2 := by
  rw [show 64 - i = 63 - i + 1 by omega, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  omega

/-- The 64 steps over the word `x` in `r7`: `r3 := (2^64 v + x) mod d`. -/
theorem bits_ok {s : State} {d V : Nat} {x : BitVec 64} (hd : 2 ≤ d) (hd' : d < 2 ^ 62)
    (h4 : s.gpr .r4 = BitVec.ofNat 64 d) (h3 : s.gpr .r3 = BitVec.ofNat 64 (V % d)) (h7 : s.gpr .r7 = x)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 64) :
    WP isa (countLoop .r8 [.lsr .d .r9 .r7 63, .lsl .r7 .r7 1, .add .r3 .r3 .r3, .add .r3 .r3 .r9,
        .sub .r9 .r3 .r4, .lsr .d .r14 .r9 63, .subi .r14 .r14 1, .logic .xor .r9 .r9 .r3,
        .logic .and .r9 .r9 .r14, .logic .xor .r3 .r3 .r9]) s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 ((V * 2 ^ 64 + x.toNat) % d) ∧ t.mem = s.mem) ∧
        Keep [.r3, .r7, .r8, .r9, .r14] s t := by
  let Inv : Nat → State → Prop := fun i u =>
    (u.gpr .r3 = BitVec.ofNat 64 ((V * 2 ^ i + x.toNat / 2 ^ (64 - i)) % d) ∧
      u.gpr .r7 = BitVec.ofNat 64 (x.toNat * 2 ^ i % 2 ^ 64) ∧ u.mem = s.mem) ∧ Keep [.r3, .r7, .r8, .r9, .r14] s u
  refine WP.mono (wp_countdown (cnt := .r8) (N := 64) (by decide) (by decide) Inv
    (fun i hi u ⟨⟨u3, u7, um⟩, ku⟩ _ => ?_) ⟨⟨?_, ?_, rfl⟩, Keep.refl _ _⟩ h8) fun t ⟨⟨t3, _, tm⟩, kt⟩ => ?_
  · rw [WP.block_append_iff]
    have u4 : u.gpr .r4 = BitVec.ofNat 64 d := (ku.gpr .r4 (by decide)).trans h4
    refine WP.mono (modStep_ok u hd hd' u4 u3 (Nat.mod_lt _ (by omega))) fun u₁ ⟨⟨a3, a7, am⟩, k1⟩ => ?_
    refine WP.mono (subi_ok u₁ .r8 (by decide)) fun u₂ e => ?_
    subst e
    refine ⟨⟨⟨?_, ?_, by rw [mem_write, am, um]⟩, (ku.trans (k1.trans (Keep.write _ _ _))).mono (by decide)⟩, ?_⟩
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]
      rw [a3, u7, top_bit x hi, Proof.Bignum.PPC64LE.ModArith.mod_double_bit]
      congr 2
      rw [Nat.pow_succ]
      have := div_step x.toNat hi
      have hf : V * (2 ^ i * 2) = 2 * (V * 2 ^ i) := by rw [Nat.mul_comm (2 ^ i) 2, Nat.mul_left_comm]
      rw [show 64 - (i + 1) = 63 - i by omega, hf]
      omega
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]
      rw [a7, u7, shl_step]
    · simp only [gpr_write, ↓reduceIte]; rw [k1.gpr .r8 (by decide)]
  · rw [h3, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, Nat.div_eq_of_lt (by have := x.isLt; omega), Nat.add_zero]
  · rw [h7, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt x.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · refine ⟨⟨?_, tm⟩, kt⟩
    rw [t3, Nat.sub_self, Nat.pow_zero, Nat.div_one]

/-- The registers `smallMod` writes. -/
def smRegs : List Reg := [.r3, .r5, .r6, .r7, .r8, .r9, .r14]

/-- `smallMod`: `r3 := ` the `w` words at `o` modulo `d` (in `r4`). -/
theorem smallMod_ok {s : State} {B : Addr} {Z o w d : Nat} (hs : Scr s B Z) (h10 : s.gpr .r10 = off B o)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h4 : s.gpr .r4 = BitVec.ofNat 64 d) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : o + 8 * w ≤ Z) (hd : 2 ≤ d) (hd' : d < 2 ^ 62) :
    WP isa smallMod s fun t => (t.gpr .r3 = BitVec.ofNat 64 (wv s.mem B o w % d) ∧ t.mem = s.mem) ∧
      Keep smRegs s t := by
  have hnw := hs.nowrap
  unfold smallMod
  refine WP.seq (WP.mono (WP.keep [.r3, .r5, .r6] (Q := fun u => u.gpr .r5 = off B (o + 8 * w) ∧
      u.gpr .r6 = BitVec.ofNat 64 w ∧ u.gpr .r3 = BitVec.ofNat 64 0 ∧ u.mem = s.mem) ?_ (by decide))
    fun u ⟨⟨a5, a6, a3, am⟩, k1⟩ => ?_)
  · prun [h10, h11]
    refine ⟨by rw [Proof.MillerRabin.PPC64LE.shl2_ofNat, off, off, Offset.add_add], ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  let Inv : Nat → State → Prop := fun j t =>
    (t.gpr .r3 = BitVec.ofNat 64 (wv s.mem B (o + 8 * (w - j)) j % d) ∧ t.gpr .r5 = off B (o + 8 * (w - j)) ∧
      t.mem = s.mem) ∧ Keep smRegs s t
  refine WP.mono (wp_countdown (cnt := .r6) (N := w) (by omega) (by omega) Inv
    (fun j hj t ⟨⟨t3, t5, tm⟩, kt⟩ _ => ?_) ⟨⟨by rw [a3]; simp [wv], by rw [a5, Nat.sub_zero], am⟩,
      k1.mono (by decide)⟩ a6)
    fun t ⟨⟨t3, _, tm⟩, kt⟩ => ⟨⟨by rw [t3, Nat.sub_self, Nat.mul_zero, Nat.add_zero], tm⟩, kt⟩
  have ht : Scr t B Z := hs.congr kt.wr
  have hrd : InRegions (t.rd ++ t.wr) (off B (o + 8 * (w - (j + 1)))) 8 := ht.ld (by omega)
  have e5 : off B (o + 8 * (w - j)) - BitVec.ofNat 64 8 = off B (o + 8 * (w - (j + 1))) := by
    simp only [off]; rw [Offset.add_ofNat_sub _ (by omega)]; congr 2; omega
  refine WP.seq (WP.mono (WP.keep [.r5, .r7, .r8] (Q := fun u => u.gpr .r5 = off B (o + 8 * (w - (j + 1))) ∧
      u.gpr .r7 = word s.mem B (o + 8 * (w - (j + 1))) ∧ u.gpr .r8 = BitVec.ofNat 64 64 ∧ u.mem = s.mem) ?_
    (by decide)) fun u ⟨⟨u5, u7, u8, um⟩, ku⟩ => ?_)
  · prun [t5, e5, hrd, BitVec.add_zero, tm]
  refine WP.seq (WP.mono (bits_ok (V := wv s.mem B (o + 8 * (w - j)) j) hd hd'
    ((ku.gpr .r4 (by decide)).trans ((kt.gpr .r4 (by decide)).trans h4)) ((ku.gpr .r3 (by decide)).trans t3) u7 u8)
    fun v ⟨⟨v3, vm⟩, kv⟩ => ?_)
  refine WP.mono (subi_ok v .r6 (by decide)) fun v₂ e => ?_
  subst e
  refine ⟨⟨⟨?_, ?_, by rw [mem_write, vm, um]⟩, ((kt.trans ku).trans (kv.trans (Keep.write _ _ _))).mono (by decide)⟩,
    ?_⟩
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]
    rw [v3]
    congr 2
    have e := wv_add s.mem B (o + 8 * (w - (j + 1))) 1 j
    rw [Nat.add_comm 1 j] at e
    rw [e, show o + 8 * (w - (j + 1)) + 8 * 1 = o + 8 * (w - j) by omega]
    simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.mul_one]
    rw [Nat.mul_comm _ (2 ^ 64), Nat.add_comm]
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]
    rw [kv.gpr .r5 (by decide), u5]
  · simp only [gpr_write, ↓reduceIte]
    rw [kv.gpr .r6 (by decide), ku.gpr .r6 (by decide)]

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
