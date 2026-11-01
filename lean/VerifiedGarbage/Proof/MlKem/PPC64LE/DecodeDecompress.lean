module

import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Compress
public import VerifiedGarbage.Proof.MlKem.PolyContract
import VerifiedGarbage.Proof.MlKem.PPC64LE.CompressEncode
import VerifiedGarbage.Proof.MlKem.PPC64LE.Bytes
public import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.MlKem.PPC64LE.Compress
meta import VerifiedGarbage.Proof.MlKem.PolyContract
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.CompressEncode
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Reduce
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Bytes
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Arith
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Spec.MlKem
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RunR

/-!
# ML-KEM on PPC64LE: `vg_mlkem_decode_decompress`

A loop for each width `d`, over the input, each iteration a group of bytes
loaded (into `r8` for `d = 10`) and taken apart into fields with pairs of
shifts, each decompressed (`dec`) and stored. The body is symbolically
executed once for any pointers (`body1_ok`, `body4_ok`, `body10_ok`). The
values are `decompress_val`, and the coefficients `decodeDecompress1`,
`decodeDecompress4_even`/`_odd` and `decodeDecompress10_0`–`_3`.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.DecodeDecompress

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## The loop bodies -/

/-- `(q · y + 2ᵈ⁻¹) >> d`, as `decompressTo` computes it. -/
def dec (d : Nat) (y : BitVec 64) : BitVec 64 := (y * 3329 + BitVec.ofNat 64 (2 ^ (d - 1))) >>> d

/-- What every iteration keeps. -/
def Keep (s s' : State) : Prop :=
  s'.gpr .r9 = s.gpr .r9 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧
    ∀ r ∈ preserved, s'.gpr r = s.gpr r

/-- The five bytes of a group of `ByteDecode₁₀`, in one doubleword. -/
abbrev G10 (s : State) (x : BitVec 64) : BitVec 64 :=
  (s.mem x).setWidth 64 + (s.mem (x + BitVec.ofNat 64 1)).setWidth 64 <<< 8 +
    (s.mem (x + BitVec.ofNat 64 2)).setWidth 64 <<< 16 + (s.mem (x + BitVec.ofNat 64 3)).setWidth 64 <<< 24 +
    (s.mem (x + BitVec.ofNat 64 4)).setWidth 64 <<< 32

section
variable {s : State} {x y c : BitVec 64}

theorem body1_ok (h3 : s.gpr .r3 = x) (h6 : s.gpr .r6 = y) (h11 : s.gpr .r11 = c) (h9 : s.gpr .r9 = 3329)
    (ib : InRegions (s.rd ++ s.wr) x 1) (oc : ∀ j < 8, InRegions s.wr (y + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block dd1Body) s fun s' =>
      s'.gpr .r3 = x + 1 ∧ s'.gpr .r6 = y + 32 ∧ s'.gpr .r11 = c - 1 ∧ Keep s s' ∧
      s'.mem = ((((((((s.mem.writeW y ((dec 1 ((s.mem x).setWidth 64 <<< 63 >>> 63)).setWidth 32)).writeW (y + BitVec.ofNat 64 4) ((dec 1 ((s.mem x).setWidth 64 <<< 62 >>> 63)).setWidth 32)).writeW (y + BitVec.ofNat 64 8) ((dec 1 ((s.mem x).setWidth 64 <<< 61 >>> 63)).setWidth 32)).writeW (y + BitVec.ofNat 64 12) ((dec 1 ((s.mem x).setWidth 64 <<< 60 >>> 63)).setWidth 32)).writeW (y + BitVec.ofNat 64 16) ((dec 1 ((s.mem x).setWidth 64 <<< 59 >>> 63)).setWidth 32)).writeW (y + BitVec.ofNat 64 20) ((dec 1 ((s.mem x).setWidth 64 <<< 58 >>> 63)).setWidth 32)).writeW (y + BitVec.ofNat 64 24) ((dec 1 ((s.mem x).setWidth 64 <<< 57 >>> 63)).setWidth 32)).writeW (y + BitVec.ofNat 64 28) ((dec 1 ((s.mem x).setWidth 64 <<< 56 >>> 63)).setWidth 32)) := by
  have o0 := oc 0 (by decide)
  have o1 := oc 1 (by decide)
  have o2 := oc 2 (by decide)
  have o3 := oc 3 (by decide)
  have o4 := oc 4 (by decide)
  have o5 := oc 5 (by decide)
  have o6 := oc 6 (by decide)
  have o7 := oc 7 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at o0 o1 o2 o3 o4 o5 o6 o7
  crunr [dd1Body, dd1Bit, decompressTo, Keep, dec, h3, h6, h11, h9, ib, o0, o1, o2, o3, o4, o5, o6, o7,
    preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append,
    List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [Mem.writeW, setWidth_zero_append]

theorem body4_ok (h3 : s.gpr .r3 = x) (h6 : s.gpr .r6 = y) (h11 : s.gpr .r11 = c) (h9 : s.gpr .r9 = 3329)
    (ib : InRegions (s.rd ++ s.wr) x 1) (o0 : InRegions s.wr y 4) (o1 : InRegions s.wr (y + BitVec.ofNat 64 4) 4) :
    WP isa (.block dd4Body) s fun s' =>
      s'.gpr .r3 = x + 1 ∧ s'.gpr .r6 = y + 8 ∧ s'.gpr .r11 = c - 1 ∧ Keep s s' ∧
      s'.mem = ((s.mem.writeW y ((dec 4 ((s.mem x).setWidth 64 <<< 60 >>> 60)).setWidth 32)).writeW (y + BitVec.ofNat 64 4) ((dec 4 ((s.mem x).setWidth 64 >>> 4)).setWidth 32)) := by
  crunr [dd4Body, decompressTo, Keep, dec, h3, h6, h11, h9, ib, o0, o1,
    preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, setWidth_zero_append]

theorem body10_ok (h3 : s.gpr .r3 = x) (h6 : s.gpr .r6 = y) (h11 : s.gpr .r11 = c) (h9 : s.gpr .r9 = 3329)
    (ib : ∀ k < 5, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 k) 1)
    (oc : ∀ j < 4, InRegions s.wr (y + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block dd10Body) s fun s' =>
      s'.gpr .r3 = x + 5 ∧ s'.gpr .r6 = y + 16 ∧ s'.gpr .r11 = c - 1 ∧ Keep s s' ∧
      s'.mem = ((((s.mem.writeW y ((dec 10 (G10 s x <<< 54 >>> 54)).setWidth 32)).writeW (y + BitVec.ofNat 64 4) ((dec 10 (G10 s x <<< 44 >>> 54)).setWidth 32)).writeW (y + BitVec.ofNat 64 8) ((dec 10 (G10 s x <<< 34 >>> 54)).setWidth 32)).writeW (y + BitVec.ofNat 64 12) ((dec 10 (G10 s x <<< 24 >>> 54)).setWidth 32)) := by
  have b0 := ib 0 (by decide)
  have b1 := ib 1 (by decide)
  have b2 := ib 2 (by decide)
  have b3 := ib 3 (by decide)
  have b4 := ib 4 (by decide)
  have o0 := oc 0 (by decide)
  have o1 := oc 1 (by decide)
  have o2 := oc 2 (by decide)
  have o3 := oc 3 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at b0 o0 o1 o2 o3
  crunr [dd10Body, dd10Byte, dd10Field, decompressTo, Keep, dec, G10, h3, h6, h11, h9, b0, b1, b2, b3, b4,
    o0, o1, o2, o3, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append,
    List.nil_append]
  simp [Mem.writeW, setWidth_zero_append]

end

/-! ## The values -/

theorem byte64 (b : Byte) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := b.isLt; omega_arith)

/-- A byte added above the low `k` bits of a doubleword whose value fits in them. -/
theorem toNat_add_shl {a : BitVec 64} {b : Byte} {k n : Nat} (ha : a.toNat = n) (hn : n < 2 ^ k)
    (hk : 2 ^ k * 2 ^ 8 ≤ 2 ^ 64) : (a + b.setWidth 64 <<< k).toNat = n + 2 ^ k * b.toNat := by
  have hb := b.isLt
  have hl : 2 ^ k * (b.toNat + 1) ≤ 2 ^ k * 2 ^ 8 := Nat.mul_le_mul_left _ hb
  rw [Nat.mul_succ] at hl
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, byte64, Nat.shiftLeft_eq, ha, Nat.mul_comm b.toNat,
    Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

/-- The `w`-bit field of `c` at bit `p`, as a pair of shifts extracts it. -/
theorem ext_toNat (c : BitVec 64) {w p : Nat} (hp : p + w ≤ 64) :
    ((c <<< (64 - w - p)) >>> (64 - w)).toNat = c.toNat / 2 ^ p % 2 ^ w := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have e1 : (2 : Nat) ^ 64 = 2 ^ (p + w) * 2 ^ (64 - w - p) := by rw [← Nat.pow_add]; congr 1; omega_arith
  have e2 : (2 : Nat) ^ (64 - w) = 2 ^ p * 2 ^ (64 - w - p) := by rw [← Nat.pow_add]; congr 1; omega_arith
  rw [e1, Nat.mul_mod_mul_right, e2, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _), Nat.pow_add,
    Nat.mod_mul_right_div_self]

theorem dec_val {d : Nat} (hd : d ∈ compressWidths) {Y : BitVec 64} {y : Nat} (hY : Y.toNat = y) (hy : y < 2 ^ d) :
    (dec d Y).setWidth 32 = BitVec.ofNat 32 (decompress d y).val := by
  obtain ⟨e, lt⟩ := decompress_val hd hy
  have hd' : d ≤ 10 := by rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide
  have hp : 2 ^ (d - 1) ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have hP : 2 ^ d ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) hd'
  have hq : q = 3329 := q_eq
  refine setWidth32_ofNat ?_ (by omega_arith)
  have h3 : (3329 : BitVec 64).toNat = 3329 := rfl
  rw [e, dec, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_mul, hY,
    h3, BitVec.toNat_ofNat, q_eq]
  congr 1
  rw [Nat.mod_eq_of_lt (a := 2 ^ (d - 1)) (by omega_arith), Nat.mod_eq_of_lt (a := y * 3329) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith), Nat.mul_comm]

/-- The doubleword of a group of five bytes. -/
theorem g10_toNat (s : State) (x : BitVec 64) :
    (G10 s x).toNat = (s.mem x).toNat + 2 ^ 8 * (s.mem (x + BitVec.ofNat 64 1)).toNat +
      2 ^ 16 * (s.mem (x + BitVec.ofNat 64 2)).toNat + 2 ^ 24 * (s.mem (x + BitVec.ofNat 64 3)).toNat +
      2 ^ 32 * (s.mem (x + BitVec.ofNat 64 4)).toNat := by
  have b0 := (s.mem x).isLt
  have b1 := (s.mem (x + BitVec.ofNat 64 1)).isLt
  have b2 := (s.mem (x + BitVec.ofNat 64 2)).isLt
  have b3 := (s.mem (x + BitVec.ofNat 64 3)).isLt
  have b4 := (s.mem (x + BitVec.ofNat 64 4)).isLt
  simp only [Nat.reducePow] at b0 b1 b2 b3 b4
  refine toNat_add_shl (toNat_add_shl (toNat_add_shl (toNat_add_shl (byte64 _) ?_ (by decide)) ?_ (by decide)) ?_ (by decide)) ?_ (by decide)
  all_goals (simp only [Nat.reducePow]; omega_arith)

theorem bit_val (b : Byte) {j : Nat} (hj : j < 8) :
    (dec 1 (b.setWidth 64 <<< (64 - 1 - j) >>> (64 - 1))).setWidth 32 =
      BitVec.ofNat 32 (decompress 1 (b.toNat / 2 ^ j % 2)).val :=
  dec_val (by decide) (by rw [ext_toNat _ (by omega_arith), byte64]) (Nat.mod_lt _ (by decide))

/-! ## The loops -/

section
variable (s₀ : State)

abbrev B : Addr := s₀.gpr .r3
abbrev L : Nat := (s₀.gpr .r4).toNat
/-- `d`, the low word of `r5`. -/
abbrev dN : Nat := ((s₀.gpr .r5).setWidth 32).toNat
abbrev F : Addr := s₀.gpr .r6
abbrev inR : Region := ⟨B s₀, L s₀⟩
abbrev Bl : List Byte := bytesAt s₀.mem (B s₀) (L s₀)
abbrev D : Poly := decodeDecompress (dN s₀) (Bl s₀)

/-- The value stored in coefficient `j`. -/
def out (j : Nat) : BitVec 32 := BitVec.ofNat 32 ((D s₀)[j]!).val

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [inR s₀]
  wr : s₀.wr = [polyRegion (F s₀)]
  disj : (inR s₀).Disjoint (polyRegion (F s₀))
  fitB : (B s₀).toNat + L s₀ ≤ 2 ^ 64
  fitF : (F s₀).toNat + 1024 ≤ 2 ^ 64
  dw : dN s₀ ∈ compressWidths
  len : L s₀ = 32 * dN s₀

/-- After `i` iterations of the loop that reads `inS` bytes and writes `cnt`
coefficients each, `N` in all. -/
structure Inv (s₀ : State) (inS cnt N : Nat) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = B s₀ + BitVec.ofNat 64 (inS * i)
  r6 : s.gpr .r6 = F s₀ + BitVec.ofNat 64 (4 * cnt * i)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (N - i)
  r9 : s.gpr .r9 = 3329
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (F s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (F s₀) j = if j < cnt * i then out s₀ j else coeffAt s₀.mem (F s₀) j

section
variable {s₀ : State} (hp : Pre s₀) {inS cnt N i : Nat} {s : State} (h : Inv s₀ inS cnt N i s)
include hp h

/-- A byte of the input, as read in the loop: the input is never written. -/
theorem byte_rd {k : Nat} (hk : k < L s₀) : s.mem (B s₀ + BitVec.ofNat 64 k) = (Bl s₀).getD k 0 := by
  rw [bytesAt_getD _ _ hk]
  exact h.frame.bytes (R := inR s₀) (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj)
    (by have := hp.fitB; show L s₀ ≤ 2 ^ 64; omega_arith) hk

theorem in_rd {k : Nat} (hk : k < L s₀) : InRegions (s.rd ++ s.wr) (B s₀ + BitVec.ofNat 64 k) 1 := by
  have := hp.fitB
  rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨inR s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

theorem out_wr {j : Nat} (hj : j < 256) : InRegions s.wr (coeffAddr (F s₀) j) 4 := by
  rw [h.wr, hp.wr]; exact ⟨_, List.mem_singleton_self _, coeff_contains _ (by rw [n_eq]; exact hj)⟩

end

theorem out_frame {s₀ : State} {m : Mem} (hf : Frame [polyRegion (F s₀)] s₀.mem m) {j : Nat} (hj : j < 256)
    (v : BitVec 32) : Frame [polyRegion (F s₀)] s₀.mem (m.writeW (coeffAddr (F s₀) j) v) :=
  hf.writeW (List.mem_singleton_self _) _ (coeff_contains _ (by rw [n_eq]; exact hj))

theorem out1 {s₀ : State} (hd : dN s₀ = 1) {i : Nat} (hi : i < 32) {j : Nat} (hj : j < 8) :
    out s₀ (8 * i + j) = BitVec.ofNat 32 (decompress 1 (((Bl s₀).getD i 0).toNat / 2 ^ j % 2)).val := by
  have e := decodeDecompress1 (Bl s₀) (i := 8 * i + j) (by rw [n_eq]; omega_arith)
  rw [show (8 * i + j) / 8 = i by omega_arith, show (8 * i + j) % 8 = j by omega_arith] at e
  rw [out, D, hd, e]

/-- The counter of an iteration. -/
theorem count_step {N i : Nat} (hi : i < N) (hN : N < 2 ^ 64) :
    BitVec.ofNat 64 (N - i) - 1 = BitVec.ofNat 64 (N - (i + 1)) ∧
      (BitVec.ofNat 64 (N - i) - 1 != 0) = decide (i + 1 ≠ N) := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
  exact ⟨rfl, count_nz hi hN⟩

theorem step1 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 1) {i : Nat} (hi : i < 32) {s : State}
    (h : Inv s₀ 1 8 32 i s) :
    WP isa (.block dd1Body) s fun s' => Inv s₀ 1 8 32 (i + 1) s' ∧ (s'.gpr .r11 != 0) = decide (i + 1 ≠ 32) := by
  have hL : L s₀ = 32 := by rw [hp.len, hd]
  have rb : s.mem (B s₀ + BitVec.ofNat 64 i) = (Bl s₀).getD i 0 := byte_rd hp h (by omega_arith)
  have a0 : F s₀ + BitVec.ofNat 64 (4 * 8 * i) = coeffAddr (F s₀) (8 * i) := by
    rw [show 4 * 8 * i = 4 * (8 * i) by omega_arith]
  have a1 : F s₀ + BitVec.ofNat 64 (4 * 8 * i) + BitVec.ofNat 64 4 = coeffAddr (F s₀) (8 * i + 1) := by
    rw [ptr_add, show 4 * 8 * i + 4 = 4 * (8 * i + 1) by omega_arith]
  have a2 : F s₀ + BitVec.ofNat 64 (4 * 8 * i) + BitVec.ofNat 64 8 = coeffAddr (F s₀) (8 * i + 2) := by
    rw [ptr_add, show 4 * 8 * i + 8 = 4 * (8 * i + 2) by omega_arith]
  have a3 : F s₀ + BitVec.ofNat 64 (4 * 8 * i) + BitVec.ofNat 64 12 = coeffAddr (F s₀) (8 * i + 3) := by
    rw [ptr_add, show 4 * 8 * i + 12 = 4 * (8 * i + 3) by omega_arith]
  have a4 : F s₀ + BitVec.ofNat 64 (4 * 8 * i) + BitVec.ofNat 64 16 = coeffAddr (F s₀) (8 * i + 4) := by
    rw [ptr_add, show 4 * 8 * i + 16 = 4 * (8 * i + 4) by omega_arith]
  have a5 : F s₀ + BitVec.ofNat 64 (4 * 8 * i) + BitVec.ofNat 64 20 = coeffAddr (F s₀) (8 * i + 5) := by
    rw [ptr_add, show 4 * 8 * i + 20 = 4 * (8 * i + 5) by omega_arith]
  have a6 : F s₀ + BitVec.ofNat 64 (4 * 8 * i) + BitVec.ofNat 64 24 = coeffAddr (F s₀) (8 * i + 6) := by
    rw [ptr_add, show 4 * 8 * i + 24 = 4 * (8 * i + 6) by omega_arith]
  have a7 : F s₀ + BitVec.ofNat 64 (4 * 8 * i) + BitVec.ofNat 64 28 = coeffAddr (F s₀) (8 * i + 7) := by
    rw [ptr_add, show 4 * 8 * i + 28 = 4 * (8 * i + 7) by omega_arith]
  have x1 : B s₀ + BitVec.ofNat 64 (1 * i) = B s₀ + BitVec.ofNat 64 i := by rw [Nat.one_mul]
  refine WP.mono (body1_ok h.r3 h.r6 h.r11 h.r9 (by rw [x1]; exact in_rd hp h (by omega_arith))
    (fun j hj => ?_)) fun s' ⟨r3, r6, r11, ⟨r9, rd, wr, sp, lr, pres⟩, m⟩ => ?_
  · rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.mul_zero, BitVec.add_zero, Nat.reduceMul] <;>
      (first | rw [a7] | rw [a6] | rw [a5] | rw [a4] | rw [a3] | rw [a2] | rw [a1] | rw [a0]) <;>
      exact out_wr hp h (by omega_arith)
  obtain ⟨c1, c2⟩ := count_step (N := 32) hi (by decide)
  refine ⟨⟨?_, ?_, r11.trans c1, r9.trans h.r9, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
    lr.trans h.lr, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, by rw [r11]; exact c2⟩
  · rw [r3]; exact ptr_succ _ 1 i
  · rw [r6]; exact ptr_succ _ (4 * 8) i
  · rw [m, a7, a6, a5, a4, a3, a2, a1, a0]
    refine out_frame (out_frame (out_frame (out_frame (out_frame (out_frame (out_frame (out_frame h.frame
      ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _ <;> omega_arith
  · rw [x1] at m
    have w0 := bit_val (s.mem (B s₀ + BitVec.ofNat 64 i)) (j := 0) (by decide)
    simp only [Nat.reduceSub] at w0
    rw [rb, ← out1 hd hi (j := 0) (by decide)] at w0
    have w1 := bit_val (s.mem (B s₀ + BitVec.ofNat 64 i)) (j := 1) (by decide)
    simp only [Nat.reduceSub] at w1
    rw [rb, ← out1 hd hi (j := 1) (by decide)] at w1
    have w2 := bit_val (s.mem (B s₀ + BitVec.ofNat 64 i)) (j := 2) (by decide)
    simp only [Nat.reduceSub] at w2
    rw [rb, ← out1 hd hi (j := 2) (by decide)] at w2
    have w3 := bit_val (s.mem (B s₀ + BitVec.ofNat 64 i)) (j := 3) (by decide)
    simp only [Nat.reduceSub] at w3
    rw [rb, ← out1 hd hi (j := 3) (by decide)] at w3
    have w4 := bit_val (s.mem (B s₀ + BitVec.ofNat 64 i)) (j := 4) (by decide)
    simp only [Nat.reduceSub] at w4
    rw [rb, ← out1 hd hi (j := 4) (by decide)] at w4
    have w5 := bit_val (s.mem (B s₀ + BitVec.ofNat 64 i)) (j := 5) (by decide)
    simp only [Nat.reduceSub] at w5
    rw [rb, ← out1 hd hi (j := 5) (by decide)] at w5
    have w6 := bit_val (s.mem (B s₀ + BitVec.ofNat 64 i)) (j := 6) (by decide)
    simp only [Nat.reduceSub] at w6
    rw [rb, ← out1 hd hi (j := 6) (by decide)] at w6
    have w7 := bit_val (s.mem (B s₀ + BitVec.ofNat 64 i)) (j := 7) (by decide)
    simp only [Nat.reduceSub] at w7
    rw [rb, ← out1 hd hi (j := 7) (by decide)] at w7
    rw [m, a7, a6, a5, a4, a3, a2, a1, a0, rb, w0, w1, w2, w3, w4, w5, w6, w7, show 8 * (i + 1) = 8 * i + 7 + 1 by omega_arith]
    exact (coeff_one (by omega_arith) (coeff_one (by omega_arith) (coeff_one (by omega_arith) (coeff_one (by omega_arith) (coeff_one (by omega_arith) (coeff_one (by omega_arith) (coeff_one (by omega_arith) (coeff_one (by omega_arith) h.coeff rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl)

theorem step4 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 4) {i : Nat} (hi : i < 128) {s : State}
    (h : Inv s₀ 1 2 128 i s) :
    WP isa (.block dd4Body) s fun s' => Inv s₀ 1 2 128 (i + 1) s' ∧ (s'.gpr .r11 != 0) = decide (i + 1 ≠ 128) := by
  have hL : L s₀ = 128 := by rw [hp.len, hd]
  have hB : (Bl s₀).length = 128 := by rw [bytesAt_length, hL]
  have rb : s.mem (B s₀ + BitVec.ofNat 64 i) = (Bl s₀).getD i 0 := byte_rd hp h (by omega_arith)
  have a0 : F s₀ + BitVec.ofNat 64 (4 * 2 * i) = coeffAddr (F s₀) (2 * i) := by
    rw [show 4 * 2 * i = 4 * (2 * i) by omega_arith]
  have a1 : F s₀ + BitVec.ofNat 64 (4 * 2 * i) + BitVec.ofNat 64 4 = coeffAddr (F s₀) (2 * i + 1) := by
    rw [ptr_add, show 4 * 2 * i + 4 = 4 * (2 * i + 1) by omega_arith]
  have x1 : B s₀ + BitVec.ofNat 64 (1 * i) = B s₀ + BitVec.ofNat 64 i := by rw [Nat.one_mul]
  refine WP.mono (body4_ok h.r3 h.r6 h.r11 h.r9 (by rw [x1]; exact in_rd hp h (by omega_arith))
    (by rw [a0]; exact out_wr hp h (by omega_arith)) (by rw [a1]; exact out_wr hp h (by omega_arith)))
    fun s' ⟨r3, r6, r11, ⟨r9, rd, wr, sp, lr, pres⟩, m⟩ => ?_
  obtain ⟨c1, c2⟩ := count_step (N := 128) hi (by decide)
  refine ⟨⟨?_, ?_, r11.trans c1, r9.trans h.r9, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
    lr.trans h.lr, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, by rw [r11]; exact c2⟩
  · rw [r3]; exact ptr_succ _ 1 i
  · rw [r6]; exact ptr_succ _ (4 * 2) i
  · rw [m, a1, a0]
    exact out_frame (out_frame h.frame (by omega_arith) _) (by omega_arith) _
  · rw [x1] at m
    have w0 : (dec 4 (((Bl s₀).getD i 0).setWidth 64 <<< 60 >>> 60)).setWidth 32 = out s₀ (2 * i) := by
      rw [out, D, hd, decodeDecompress4_even _ hB hi]
      refine dec_val (by decide) ?_ (Nat.mod_lt _ (by decide))
      have := ext_toNat (((Bl s₀).getD i 0).setWidth 64) (w := 4) (p := 0) (by decide)
      simp only [Nat.reduceSub, Nat.pow_zero, Nat.div_one, byte64] at this
      exact this
    have w1 : (dec 4 (((Bl s₀).getD i 0).setWidth 64 >>> 4)).setWidth 32 = out s₀ (2 * i + 1) := by
      rw [out, D, hd, decodeDecompress4_odd _ hB hi]
      refine dec_val (by decide) ?_ (by have := ((Bl s₀).getD i 0).isLt; omega_arith)
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, byte64]
    rw [m, a1, a0, rb, w0, w1, show 2 * (i + 1) = 2 * i + 1 + 1 by omega_arith]
    exact coeff_one (by omega_arith) (coeff_one (by omega_arith) h.coeff rfl) rfl

theorem f10_val (G : BitVec 64) {k : Nat} (hk : k < 4) :
    (dec 10 (G <<< (64 - 10 - 10 * k) >>> (64 - 10))).setWidth 32 =
      BitVec.ofNat 32 (decompress 10 (G.toNat / 2 ^ (10 * k) % 2 ^ 10)).val :=
  dec_val (by decide) (ext_toNat _ (by omega_arith)) (Nat.mod_lt _ (by decide))

theorem step10 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 10) {i : Nat} (hi : i < 64) {s : State}
    (h : Inv s₀ 5 4 64 i s) :
    WP isa (.block dd10Body) s fun s' => Inv s₀ 5 4 64 (i + 1) s' ∧ (s'.gpr .r11 != 0) = decide (i + 1 ≠ 64) := by
  have hL : L s₀ = 320 := by rw [hp.len, hd]
  have hB : (Bl s₀).length = 320 := by rw [bytesAt_length, hL]
  have eb : ∀ k < 5, B s₀ + BitVec.ofNat 64 (5 * i) + BitVec.ofNat 64 k = B s₀ + BitVec.ofNat 64 (5 * i + k) :=
    fun k _ => ptr_add _ _ _
  have rb : ∀ k < 5, s.mem (B s₀ + BitVec.ofNat 64 (5 * i + k)) = (Bl s₀).getD (5 * i + k) 0 :=
    fun k hk => byte_rd hp h (by omega_arith)
  have a0 : F s₀ + BitVec.ofNat 64 (4 * 4 * i) = coeffAddr (F s₀) (4 * i) := by
    rw [show 4 * 4 * i = 4 * (4 * i) by omega_arith]
  have a1 : F s₀ + BitVec.ofNat 64 (4 * 4 * i) + BitVec.ofNat 64 4 = coeffAddr (F s₀) (4 * i + 1) := by
    rw [ptr_add, show 4 * 4 * i + 4 = 4 * (4 * i + 1) by omega_arith]
  have a2 : F s₀ + BitVec.ofNat 64 (4 * 4 * i) + BitVec.ofNat 64 8 = coeffAddr (F s₀) (4 * i + 2) := by
    rw [ptr_add, show 4 * 4 * i + 8 = 4 * (4 * i + 2) by omega_arith]
  have a3 : F s₀ + BitVec.ofNat 64 (4 * 4 * i) + BitVec.ofNat 64 12 = coeffAddr (F s₀) (4 * i + 3) := by
    rw [ptr_add, show 4 * 4 * i + 12 = 4 * (4 * i + 3) by omega_arith]
  refine WP.mono (body10_ok h.r3 h.r6 h.r11 h.r9 (fun k hk => by rw [eb k hk]; exact in_rd hp h (by omega_arith))
    (fun j hj => ?_)) fun s' ⟨r3, r6, r11, ⟨r9, rd, wr, sp, lr, pres⟩, m⟩ => ?_
  · rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
      simp only [Nat.mul_zero, BitVec.add_zero, Nat.reduceMul] <;>
      (first | rw [a3] | rw [a2] | rw [a1] | rw [a0]) <;> exact out_wr hp h (by omega_arith)
  obtain ⟨c1, c2⟩ := count_step (N := 64) hi (by decide)
  refine ⟨⟨?_, ?_, r11.trans c1, r9.trans h.r9, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
    lr.trans h.lr, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, by rw [r11]; exact c2⟩
  · rw [r3]; exact ptr_succ _ 5 i
  · rw [r6]; exact ptr_succ _ (4 * 4) i
  · rw [m, a3, a2, a1, a0]
    exact out_frame (out_frame (out_frame (out_frame h.frame (by omega_arith) _) (by omega_arith) _) (by omega_arith) _) (by omega_arith) _
  · have e := g10_toNat s (B s₀ + BitVec.ofNat 64 (5 * i))
    rw [eb 1 (by omega_arith), eb 2 (by omega_arith), eb 3 (by omega_arith), eb 4 (by omega_arith),
      show B s₀ + BitVec.ofNat 64 (5 * i) = B s₀ + BitVec.ofNat 64 (5 * i + 0) from rfl,
      rb 0 (by omega_arith), rb 1 (by omega_arith), rb 2 (by omega_arith), rb 3 (by omega_arith), rb 4 (by omega_arith), Nat.add_zero] at e
    have l0 := ((Bl s₀).getD (5 * i) 0).isLt
    have l1 := ((Bl s₀).getD (5 * i + 1) 0).isLt
    have l2 := ((Bl s₀).getD (5 * i + 2) 0).isLt
    have l3 := ((Bl s₀).getD (5 * i + 3) 0).isLt
    have l4 := ((Bl s₀).getD (5 * i + 4) 0).isLt
    have v : ∀ k < 4, (dec 10 (G10 s (B s₀ + BitVec.ofNat 64 (5 * i)) <<< (64 - 10 - 10 * k) >>> (64 - 10))).setWidth 32 =
        out s₀ (4 * i + k) := fun k hk => by
      rw [f10_val _ hk, out, D, hd, e]
      rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
      · simp only [Nat.add_zero]
        rw [decodeDecompress10_0 _ hB hi]
        refine congrArg (fun y => BitVec.ofNat 32 (decompress 10 y).val) ?_
        simp only [Nat.reducePow, Nat.mul_zero, Nat.pow_zero, Nat.div_one]; omega_arith
      · rw [decodeDecompress10_1 _ hB hi]
        refine congrArg (fun y => BitVec.ofNat 32 (decompress 10 y).val) ?_
        simp only [Nat.reducePow, Nat.reduceMul]; omega_arith
      · rw [decodeDecompress10_2 _ hB hi]
        refine congrArg (fun y => BitVec.ofNat 32 (decompress 10 y).val) ?_
        simp only [Nat.reducePow, Nat.reduceMul]; omega_arith
      · rw [decodeDecompress10_3 _ hB hi]
        refine congrArg (fun y => BitVec.ofNat 32 (decompress 10 y).val) ?_
        simp only [Nat.reducePow, Nat.reduceMul]; omega_arith
    have v0 := v 0 (by decide)
    have v1 := v 1 (by decide)
    have v2 := v 2 (by decide)
    have v3 := v 3 (by decide)
    simp only [Nat.reduceSub, Nat.reduceMul, Nat.add_zero] at v0 v1 v2 v3
    rw [m, a3, a2, a1, a0, v0, v1, v2, v3, show 4 * (i + 1) = 4 * i + 3 + 1 by omega_arith]
    exact coeff_one (by omega_arith) (coeff_one (by omega_arith) (coeff_one (by omega_arith) (coeff_one (by omega_arith) h.coeff rfl)
      rfl) rfl) rfl

/-! ## The branches -/

/-- What the loops end with. -/
def Fin (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
    ∀ j < 256, coeffAt s.mem (F s₀) j = out s₀ j

/-- What a branch starts from. -/
def Start (s₀ s : State) : Prop :=
  s.gpr .r3 = B s₀ ∧ s.gpr .r6 = F s₀ ∧ s.gpr .r9 = 3329 ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
    s.lr = s₀.lr ∧ (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem

theorem st {s₀ s : State} (h : Start s₀ s) {r : Reg} (hr : r = .r7 ∨ r = .r11) (v : BitVec 64) :
    Start s₀ (s.write r v) := by
  obtain ⟨r3, r6, r9, rd, wr, sp, lr, pres, m⟩ := h
  have h3 : Reg.r3 ≠ r := by rcases hr with rfl | rfl <;> decide
  have h6 : Reg.r6 ≠ r := by rcases hr with rfl | rfl <;> decide
  have h9 : Reg.r9 ≠ r := by rcases hr with rfl | rfl <;> decide
  refine ⟨by simp [State.write, h3, r3], by simp [State.write, h6, r6], by simp [State.write, h9, r9], rd, wr,
    sp, lr, fun r' hr' => ?_, m⟩
  have : r' ≠ r := by rcases hr with rfl | rfl <;> revert r' hr' <;> decide
  simp [State.write, this, pres r' hr']

theorem loop_fin {s₀ : State} {inS cnt N : Nat} (hN : cnt * N = 256) {s : State}
    (h : Inv s₀ inS cnt N N s) : Fin s₀ s :=
  ⟨h.pres, h.sp, h.lr, fun j hj => by rw [h.coeff j hj, ite_eq_left (by omega_arith)]⟩

theorem inv_zero {s₀ : State} {inS cnt N : Nat} {s : State} (h : Start s₀ s)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 N) : Inv s₀ inS cnt N 0 s := by
  obtain ⟨r3, r6, r9, rd, wr, sp, lr, pres, m⟩ := h
  exact ⟨by simp [r3], by simp [r6], by simp [h11], r9, rd, wr, sp, lr, pres, by rw [m]; exact Frame.refl _ _,
    fun j _ => by rw [m, ite_eq_right (by omega_arith)]⟩

theorem branch1 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 1) {s : State} (h : Start s₀ s) :
    WP isa (.seq (.block [.li .r11 32]) (.loop (.block dd1Body) (.nonzero .d .r11))) s (Fin s₀) := by
  refine WP.seq (WP.cons (exec_li (by decide)) (wp_nil ?_))
  refine wp_loop_nz (Inv s₀ 1 8 32) (N := 32) (by decide) (fun i hi s h => step1 hp hd hi h)
    (fun s h => loop_fin (by decide) h) (inv_zero (st h (.inr rfl) _) (by simp [State.write]))

theorem branch4 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 4) {s : State} (h : Start s₀ s) :
    WP isa (.seq (.block [.li .r11 128]) (.loop (.block dd4Body) (.nonzero .d .r11))) s (Fin s₀) := by
  refine WP.seq (WP.cons (exec_li (by decide)) (wp_nil ?_))
  refine wp_loop_nz (Inv s₀ 1 2 128) (N := 128) (by decide) (fun i hi s h => step4 hp hd hi h)
    (fun s h => loop_fin (by decide) h) (inv_zero (st h (.inr rfl) _) (by simp [State.write]))

theorem branch10 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 10) {s : State} (h : Start s₀ s) :
    WP isa (.seq (.block [.li .r11 64]) (.loop (.block dd10Body) (.nonzero .d .r11))) s (Fin s₀) := by
  refine WP.seq (WP.cons (exec_li (by decide)) (wp_nil ?_))
  refine wp_loop_nz (Inv s₀ 5 4 64) (N := 64) (by decide) (fun i hi s h => step10 hp hd hi h)
    (fun s h => loop_fin (by decide) h) (inv_zero (st h (.inr rfl) _) (by simp [State.write]))

/-- `r5` zero-extended. -/
abbrev Z (s₀ : State) : BitVec 64 := (((s₀.gpr .r5).setWidth 32).rotateRight 0).setWidth 64

theorem sel_eval {s₀ s : State} {k : Nat} (hk : k < 2 ^ 15) (h : s.gpr .r7 = Z s₀ - BitVec.ofNat 64 k) :
    isa.eval (.zero .w .r7) s = some (decide (dN s₀ = k)) := by
  have r0 : ∀ v : BitVec 32, v.rotateRight 0 = v := fun v => by
    simp [BitVec.rotateRight, BitVec.rotateRightAux]
  show VG.PPC64LE.eval (.zero .w .r7) s = _
  simp only [VG.PPC64LE.eval, State.read, Size.bits, h]
  rw [CompressEncode.dsel _ hk, r0]

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa decodeDecompress s₀ (Fin s₀) := by
  refine WP.seq (WP.cons (exec_rotr_w (by decide)) (wp_nil ?_))
  refine WP.seq (WP.cons (exec_li (by decide)) (WP.cons (exec_subi (by decide) (by decide)) (wp_nil ?_)))
  have s0 : Start s₀ ((s₀.write .r5 (Z s₀)).write .r9 (BitVec.ofNat 64 3329)) :=
    ⟨by simp [State.write], by simp [State.write], by simp [State.write], rfl, rfl, rfl, rfl, fun r hr => by
      have : r ≠ .r5 ∧ r ≠ .r9 := by revert r hr; decide
      simp [State.write, this.1, this.2], rfl⟩
  rcases mem_compressWidths hp.dw with hd | hd | hd
  · refine WP.ite true (by rw [sel_eval (s₀ := s₀) (k := 1) (by decide) (by simp [State.write]), hd]; rfl)
      (fun _ => branch1 hp hd (st s0 (.inl rfl) _)) (fun h => absurd h (by decide))
  · refine WP.ite false (by rw [sel_eval (s₀ := s₀) (k := 1) (by decide) (by simp [State.write]), hd]; rfl)
      (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (WP.cons (exec_subi (by decide) (by decide)) (wp_nil ?_))
    refine WP.ite true (by rw [sel_eval (s₀ := s₀) (k := 4) (by decide) (by simp [State.write]), hd]; rfl)
      (fun _ => branch4 hp hd (st (st s0 (.inl rfl) _) (.inl rfl) _)) (fun h => absurd h (by decide))
  · refine WP.ite false (by rw [sel_eval (s₀ := s₀) (k := 1) (by decide) (by simp [State.write]), hd]; rfl)
      (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (WP.cons (exec_subi (by decide) (by decide)) (wp_nil ?_))
    refine WP.ite false (by rw [sel_eval (s₀ := s₀) (k := 4) (by decide) (by simp [State.write]), hd]; rfl)
      (fun h => absurd h (by decide)) (fun _ => branch10 hp hd (st (st s0 (.inl rfl) _) (.inl rfl) _))

/-! ## Verified -/

/-- The public registers but `r5`, and `r5`'s low word, agree. -/
def LoAgree (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ (∀ r ∈ [Reg.r3, .r4, .r6], s₁.gpr r = s₂.gpr r) ∧
    (s₁.gpr .r5).setWidth 32 = (s₂.gpr .r5).setWidth 32

/-- What the zero-extension of `r5` leaves from `σ`. -/
def ZextF (σ s : State) : Prop :=
  s.sp = σ.sp ∧ (∀ r ∈ [Reg.r3, .r4, .r6], s.gpr r = σ.gpr r) ∧ s.gpr .r5 = Z σ

theorem zext_ok (σ : State) : WP isa (.block [.rotr .w .r5 .r5 0]) σ (ZextF σ) :=
  WP.cons (exec_rotr_w (by decide)) (wp_nil ⟨rfl, fun r hr => by
    have : r ≠ .r5 := by revert r hr; decide
    simp [State.write, this], by simp [State.write]⟩)

theorem zext_rel : RelCT isa LoAgree (.block [.rotr .w .r5 .r5 0])
    fun s₁ s₂ => s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r3, .r4, .r5, .r6], s₁.gpr r = s₂.gpr r := by
  have ht : RelCT isa LoAgree (.block [.rotr .w .r5 .r5 0]) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4, .r6])
      (fun _ _ ⟨hsp, hr, _⟩ => ⟨hsp, fun r h => hr r (Taint.mem_ofRegs.mp h)⟩) (by taint_decide)
  refine (ht.wpDep (F := ZextF) fun σ₁ σ₂ _ => ⟨zext_ok σ₁, zext_ok σ₂⟩).mono (fun _ _ h => h) ?_
  rintro s₁ s₂ ⟨-, σ₁, σ₂, ⟨hsp, hr, hlo⟩, ⟨f1, g1, k1⟩, ⟨f2, g2, k2⟩⟩
  refine ⟨by rw [f1, f2, hsp], fun r hr' => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl
  · rw [g1 _ (by decide), g2 _ (by decide), hr _ (by decide)]
  · rw [g1 _ (by decide), g2 _ (by decide), hr _ (by decide)]
  · rw [k1, k2, Z, Z, hlo]
  · rw [g1 _ (by decide), g2 _ (by decide), hr _ (by decide)]

theorem pre_of {s : State} (h : (Proof.MlKem.decodeDecompressContract PPC64LE.abi).pre s) : Pre s := by
  sig_pre [Proof.MlKem.decodeDecompressContract, Proof.MlKem.decodeDecompressSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 32 | .r5 => 1 | .r6 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 1024⟩]

theorem verified : Verified PPC64LE.target Impl.MlKem.PPC64LE.decodeDecompress
    (Proof.MlKem.decodeDecompressContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, RelCT.constantTime (Q := fun _ _ => True) ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hlr⟩, ?_⟩
    sig_post [Proof.MlKem.decodeDecompressContract, Proof.MlKem.decodeDecompressSig, PPC64LE.abi, PPC64LE.argRegs]
    exact polyIs_of_coeffAt (p := F s) fun j hj => by rw [h j (by rw [n_eq] at hj; exact hj)]; rfl
  · refine RelCT.seq (zext_rel.mono (fun s₁ s₂ ⟨_, _, hp⟩ => ?_) fun _ _ h => h)
      (RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
        (fun _ _ ⟨hsp, hr⟩ => ⟨hsp, fun r h => hr r (Taint.mem_ofRegs.mp h)⟩) (by taint_decide))
    sig_pub [Proof.MlKem.decodeDecompressContract, Proof.MlKem.decodeDecompressSig, PPC64LE.abi,
      PPC64LE.argRegs] at hp
    obtain ⟨hsp, h3, h4, h5, h6⟩ := hp
    refine ⟨hsp, fun r hr => ?_, h5⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h3
    · exact h4
    · exact h6
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.decodeDecompressContract, Proof.MlKem.decodeDecompressSig, PPC64LE.abi,
        PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem.PPC64LE.DecodeDecompress
