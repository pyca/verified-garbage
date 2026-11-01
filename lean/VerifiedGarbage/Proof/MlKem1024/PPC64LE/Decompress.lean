module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.DecodeDecompress
public import VerifiedGarbage.Impl.MlKem1024.PPC64LE.Poly
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.MlKem1024.Contract
import VerifiedGarbage.Proof.MlKem.Encode1024
import VerifiedGarbage.Proof.MlKem.Compress1024
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.CompressEncode
import VerifiedGarbage.Proof.MlKem.PPC64LE.Bytes
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.DecodeDecompress
meta import VerifiedGarbage.Impl.MlKem1024.PPC64LE.Poly
meta import VerifiedGarbage.Spec.MlKem.Contract1024
meta import VerifiedGarbage.Proof.MlKem1024.Contract
meta import VerifiedGarbage.Proof.MlKem.Encode1024
meta import VerifiedGarbage.Proof.MlKem.Compress1024
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.CompressEncode
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Reduce
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Bytes
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Arith
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.MlKem
public import VerifiedGarbage.Proof.MlKem.PolyContract
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RunR

/-!
# ML-KEM-1024 on PPC64LE: `vg_mlkem1024_decode_decompress`

A loop for each width, over the input, each iteration a group of bytes
loaded into `r8` and taken apart into fields with pairs of shifts, each
decompressed (`dec`) and stored: the five bytes of a group of eight 5-bit
fields, and for `d = 11` the first six and the last six of the eleven bytes
of a group of eight 11-bit fields, which overlap in the byte holding the
fourth and fifth. The body is symbolically executed once for any pointers
(`body5_ok`, `body11_ok`). The values are `decompress1024_val`, and the
coefficients `decodeDecompress5_group` and `decodeDecompress11_group`.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.PPC64LE.Decompress

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE VG.Impl.MlKem1024.PPC64LE
open VG.Spec.MlKem
open VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.PPC64LE
open VG.Proof.MlKem.PPC64LE.DecodeDecompress (dec Keep byte64 ext_toNat toNat_add_shl)
open VG.Proof.MlKem.PPC64LE.CompressEncode (dsel)

/-! ## The loop bodies -/

/-- The five bytes of a group of `ByteDecode₅`, in one doubleword. -/
abbrev G5 (s : State) (x : BitVec 64) : BitVec 64 :=
  (s.mem x).setWidth 64 + (s.mem (x + BitVec.ofNat 64 1)).setWidth 64 <<< 8 +
    (s.mem (x + BitVec.ofNat 64 2)).setWidth 64 <<< 16 +
    (s.mem (x + BitVec.ofNat 64 3)).setWidth 64 <<< 24 +
    (s.mem (x + BitVec.ofNat 64 4)).setWidth 64 <<< 32

/-- The first six bytes of a group of `ByteDecode₁₁`, in one doubleword. -/
abbrev G11a (s : State) (x : BitVec 64) : BitVec 64 :=
  (s.mem x).setWidth 64 + (s.mem (x + BitVec.ofNat 64 1)).setWidth 64 <<< 8 +
    (s.mem (x + BitVec.ofNat 64 2)).setWidth 64 <<< 16 +
    (s.mem (x + BitVec.ofNat 64 3)).setWidth 64 <<< 24 +
    (s.mem (x + BitVec.ofNat 64 4)).setWidth 64 <<< 32 +
    (s.mem (x + BitVec.ofNat 64 5)).setWidth 64 <<< 40

/-- Its last six bytes. -/
abbrev G11b (s : State) (x : BitVec 64) : BitVec 64 :=
  (s.mem (x + BitVec.ofNat 64 5)).setWidth 64 +
    (s.mem (x + BitVec.ofNat 64 6)).setWidth 64 <<< 8 +
    (s.mem (x + BitVec.ofNat 64 7)).setWidth 64 <<< 16 +
    (s.mem (x + BitVec.ofNat 64 8)).setWidth 64 <<< 24 +
    (s.mem (x + BitVec.ofNat 64 9)).setWidth 64 <<< 32 +
    (s.mem (x + BitVec.ofNat 64 10)).setWidth 64 <<< 40

section
variable {s : State} {x y c : BitVec 64}

theorem body5_ok (h3 : s.gpr .r3 = x) (h6 : s.gpr .r6 = y) (h11 : s.gpr .r11 = c)
    (h9 : s.gpr .r9 = 3329) (ib : ∀ k < 5, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 k) 1)
    (oc : ∀ j < 8, InRegions s.wr (y + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block dd5Body) s fun s' =>
      s'.gpr .r3 = x + 5 ∧ s'.gpr .r6 = y + 32 ∧ s'.gpr .r11 = c - 1 ∧ Keep s s' ∧
      s'.mem = (((((((s.mem.writeW y
        ((dec 5 (G5 s x <<< 59 >>> 59)).setWidth 32)).writeW (y + BitVec.ofNat 64 4)
        ((dec 5 (G5 s x <<< 54 >>> 59)).setWidth 32)).writeW (y + BitVec.ofNat 64 8)
        ((dec 5 (G5 s x <<< 49 >>> 59)).setWidth 32)).writeW (y + BitVec.ofNat 64 12)
        ((dec 5 (G5 s x <<< 44 >>> 59)).setWidth 32)).writeW (y + BitVec.ofNat 64 16)
        ((dec 5 (G5 s x <<< 39 >>> 59)).setWidth 32)).writeW (y + BitVec.ofNat 64 20)
        ((dec 5 (G5 s x <<< 34 >>> 59)).setWidth 32)).writeW (y + BitVec.ofNat 64 24)
        ((dec 5 (G5 s x <<< 29 >>> 59)).setWidth 32)).writeW (y + BitVec.ofNat 64 28)
        ((dec 5 (G5 s x <<< 24 >>> 59)).setWidth 32) := by
  have b0 := ib 0 (by decide)
  have b1 := ib 1 (by decide)
  have b2 := ib 2 (by decide)
  have b3 := ib 3 (by decide)
  have b4 := ib 4 (by decide)
  have o0 := oc 0 (by decide)
  have o1 := oc 1 (by decide)
  have o2 := oc 2 (by decide)
  have o3 := oc 3 (by decide)
  have o4 := oc 4 (by decide)
  have o5 := oc 5 (by decide)
  have o6 := oc 6 (by decide)
  have o7 := oc 7 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at b0 o0 o1 o2 o3 o4 o5 o6 o7
  crunr [dd5Body, ddByteAt, dd5Field, decompressTo, Keep, dec, G5, h3, h6, h11, h9, b0, b1, b2, b3,
    b4, o0, o1, o2, o3, o4, o5, o6, o7, preserved, List.forall_mem_cons, List.not_mem_nil,
    false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, setWidth_zero_append]

theorem body11_ok (h3 : s.gpr .r3 = x) (h6 : s.gpr .r6 = y) (h11 : s.gpr .r11 = c)
    (h9 : s.gpr .r9 = 3329) (ib : ∀ k < 11, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 k) 1)
    (oc : ∀ j < 8, InRegions s.wr (y + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block dd11Body) s fun s' =>
      s'.gpr .r3 = x + 11 ∧ s'.gpr .r6 = y + 32 ∧ s'.gpr .r11 = c - 1 ∧ Keep s s' ∧
      s'.mem = (((((((s.mem.writeW y
        ((dec 11 (G11a s x <<< 53 >>> 53)).setWidth 32)).writeW (y + BitVec.ofNat 64 4)
        ((dec 11 (G11a s x <<< 42 >>> 53)).setWidth 32)).writeW (y + BitVec.ofNat 64 8)
        ((dec 11 (G11a s x <<< 31 >>> 53)).setWidth 32)).writeW (y + BitVec.ofNat 64 12)
        ((dec 11 (G11a s x <<< 20 >>> 53)).setWidth 32)).writeW (y + BitVec.ofNat 64 16)
        ((dec 11 (G11b s x <<< 49 >>> 53)).setWidth 32)).writeW (y + BitVec.ofNat 64 20)
        ((dec 11 (G11b s x <<< 38 >>> 53)).setWidth 32)).writeW (y + BitVec.ofNat 64 24)
        ((dec 11 (G11b s x <<< 27 >>> 53)).setWidth 32)).writeW (y + BitVec.ofNat 64 28)
        ((dec 11 (G11b s x <<< 16 >>> 53)).setWidth 32) := by
  have b0 := ib 0 (by decide)
  have b1 := ib 1 (by decide)
  have b2 := ib 2 (by decide)
  have b3 := ib 3 (by decide)
  have b4 := ib 4 (by decide)
  have b5 := ib 5 (by decide)
  have b6 := ib 6 (by decide)
  have b7 := ib 7 (by decide)
  have b8 := ib 8 (by decide)
  have b9 := ib 9 (by decide)
  have b10 := ib 10 (by decide)
  have o0 := oc 0 (by decide)
  have o1 := oc 1 (by decide)
  have o2 := oc 2 (by decide)
  have o3 := oc 3 (by decide)
  have o4 := oc 4 (by decide)
  have o5 := oc 5 (by decide)
  have o6 := oc 6 (by decide)
  have o7 := oc 7 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at b0 o0 o1 o2 o3 o4 o5 o6 o7
  crunr [dd11Body, ddByteAt, ddByteAtHi, dd11Field, dd11FieldHi, decompressTo, Keep, dec, G11a, G11b, h3, h6, h11, h9, b0, b1,
    b2, b3, b4, b5, b6, b7, b8, b9, b10, o0, o1, o2, o3, o4, o5, o6, o7, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, setWidth_zero_append]

end

/-! ## The values -/

theorem dec_val4 {d : Nat} (hd : d ∈ Proof.MlKem1024.compressWidths) {Y : BitVec 64} {y : Nat}
    (hY : Y.toNat = y) (hy : y < 2 ^ d) :
    (dec d Y).setWidth 32 = BitVec.ofNat 32 (decompress d y).val := by
  obtain ⟨e, lt⟩ := decompress1024_val hd hy
  have hd' : d ≤ 11 := by rcases mem_compressWidths1024 hd with rfl | rfl <;> decide
  have hp : 2 ^ (d - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have hP : 2 ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hd'
  have hq : q = 3329 := q_eq
  refine setWidth32_ofNat ?_ (by omega_arith)
  have h3 : (3329 : BitVec 64).toNat = 3329 := rfl
  rw [e, dec, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_mul,
    hY, h3, BitVec.toNat_ofNat, q_eq]
  congr 1
  rw [Nat.mod_eq_of_lt (a := 2 ^ (d - 1)) (by omega_arith), Nat.mod_eq_of_lt (a := y * 3329) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith), Nat.mul_comm]

/-- The doubleword of a group of five bytes. -/
theorem g5_toNat (s : State) (x : BitVec 64) :
    (G5 s x).toNat = (s.mem x).toNat + 2 ^ 8 * (s.mem (x + BitVec.ofNat 64 1)).toNat +
      2 ^ 16 * (s.mem (x + BitVec.ofNat 64 2)).toNat +
      2 ^ 24 * (s.mem (x + BitVec.ofNat 64 3)).toNat +
      2 ^ 32 * (s.mem (x + BitVec.ofNat 64 4)).toNat := by
  have b0 := (s.mem x).isLt
  have b1 := (s.mem (x + BitVec.ofNat 64 1)).isLt
  have b2 := (s.mem (x + BitVec.ofNat 64 2)).isLt
  have b3 := (s.mem (x + BitVec.ofNat 64 3)).isLt
  have b4 := (s.mem (x + BitVec.ofNat 64 4)).isLt
  simp only [Nat.reducePow] at b0 b1 b2 b3 b4
  refine toNat_add_shl (toNat_add_shl (toNat_add_shl (toNat_add_shl (byte64 _) ?_ (by decide)) ?_ (by decide)) ?_ (by decide)) ?_ (by decide)
  all_goals (simp only [Nat.reducePow]; omega_arith)

/-- The doubleword of the first six bytes of a group. -/
theorem g11a_toNat (s : State) (x : BitVec 64) :
    (G11a s x).toNat = (s.mem x).toNat + 2 ^ 8 * (s.mem (x + BitVec.ofNat 64 1)).toNat +
      2 ^ 16 * (s.mem (x + BitVec.ofNat 64 2)).toNat +
      2 ^ 24 * (s.mem (x + BitVec.ofNat 64 3)).toNat +
      2 ^ 32 * (s.mem (x + BitVec.ofNat 64 4)).toNat +
      2 ^ 40 * (s.mem (x + BitVec.ofNat 64 5)).toNat := by
  have b0 := (s.mem x).isLt
  have b1 := (s.mem (x + BitVec.ofNat 64 1)).isLt
  have b2 := (s.mem (x + BitVec.ofNat 64 2)).isLt
  have b3 := (s.mem (x + BitVec.ofNat 64 3)).isLt
  have b4 := (s.mem (x + BitVec.ofNat 64 4)).isLt
  have b5 := (s.mem (x + BitVec.ofNat 64 5)).isLt
  simp only [Nat.reducePow] at b0 b1 b2 b3 b4 b5
  refine toNat_add_shl (toNat_add_shl (toNat_add_shl (toNat_add_shl (toNat_add_shl (byte64 _) ?_ (by decide)) ?_ (by decide)) ?_ (by decide)) ?_ (by decide)) ?_ (by decide)
  all_goals (simp only [Nat.reducePow]; omega_arith)

/-- The doubleword of the last six bytes of a group. -/
theorem g11b_toNat (s : State) (x : BitVec 64) :
    (G11b s x).toNat = (s.mem (x + BitVec.ofNat 64 5)).toNat +
      2 ^ 8 * (s.mem (x + BitVec.ofNat 64 6)).toNat +
      2 ^ 16 * (s.mem (x + BitVec.ofNat 64 7)).toNat +
      2 ^ 24 * (s.mem (x + BitVec.ofNat 64 8)).toNat +
      2 ^ 32 * (s.mem (x + BitVec.ofNat 64 9)).toNat +
      2 ^ 40 * (s.mem (x + BitVec.ofNat 64 10)).toNat := by
  have b5 := (s.mem (x + BitVec.ofNat 64 5)).isLt
  have b6 := (s.mem (x + BitVec.ofNat 64 6)).isLt
  have b7 := (s.mem (x + BitVec.ofNat 64 7)).isLt
  have b8 := (s.mem (x + BitVec.ofNat 64 8)).isLt
  have b9 := (s.mem (x + BitVec.ofNat 64 9)).isLt
  have b10 := (s.mem (x + BitVec.ofNat 64 10)).isLt
  simp only [Nat.reducePow] at b5 b6 b7 b8 b9 b10
  refine toNat_add_shl (toNat_add_shl (toNat_add_shl (toNat_add_shl (toNat_add_shl (byte64 _) ?_ (by decide)) ?_ (by decide)) ?_ (by decide)) ?_ (by decide)) ?_ (by decide)
  all_goals (simp only [Nat.reducePow]; omega_arith)

theorem f5_val (G : BitVec 64) {k : Nat} (hk : k < 8) :
    (dec 5 (G <<< (64 - 5 - 5 * k) >>> (64 - 5))).setWidth 32 =
      BitVec.ofNat 32 (decompress 5 (G.toNat / 2 ^ (5 * k) % 2 ^ 5)).val :=
  dec_val4 (by decide) (ext_toNat _ (by omega_arith)) (Nat.mod_lt _ (by decide))

theorem f11_val (G : BitVec 64) {p : Nat} (hp : p + 11 ≤ 64) :
    (dec 11 (G <<< (64 - 11 - p) >>> (64 - 11))).setWidth 32 =
      BitVec.ofNat 32 (decompress 11 (G.toNat / 2 ^ p % 2 ^ 11)).val :=
  dec_val4 (by decide) (ext_toNat _ hp) (Nat.mod_lt _ (by decide))

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
  dw : dN s₀ ∈ Proof.MlKem1024.compressWidths
  len : L s₀ = 32 * dN s₀

/-- After `i` iterations of the loop that reads `inS` bytes and writes 8
coefficients each, `N` in all. -/
structure Inv (s₀ : State) (inS N : Nat) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = B s₀ + BitVec.ofNat 64 (inS * i)
  r6 : s.gpr .r6 = F s₀ + BitVec.ofNat 64 (32 * i)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (N - i)
  r9 : s.gpr .r9 = 3329
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (F s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (F s₀) j =
    if j < 8 * i then out s₀ j else coeffAt s₀.mem (F s₀) j

section
variable {s₀ : State} (hp : Pre s₀) {inS N i : Nat} {s : State} (h : Inv s₀ inS N i s)
include hp h

/-- A byte of the input, as read in the loop: the input is never written. -/
theorem byte_rd {k : Nat} (hk : k < L s₀) : s.mem (B s₀ + BitVec.ofNat 64 k) = (Bl s₀).getD k 0 := by
  rw [bytesAt_getD _ _ hk]
  exact h.frame.bytes (R := inR s₀) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.disj)
    (by have := hp.fitB; show L s₀ ≤ 2 ^ 64; omega_arith) hk

theorem in_rd {k : Nat} (hk : k < L s₀) :
    InRegions (s.rd ++ s.wr) (B s₀ + BitVec.ofNat 64 k) 1 := by
  have := hp.fitB
  rw [h.rd, h.wr, hp.rd, hp.wr]
  exact ⟨inR s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

theorem out_wr {j : Nat} (hj : j < 256) : InRegions s.wr (coeffAddr (F s₀) j) 4 := by
  rw [h.wr, hp.wr]; exact ⟨_, List.mem_singleton_self _, coeff_contains _ (by rw [n_eq]; exact hj)⟩

end

theorem out_frame {s₀ : State} {m : Mem} (hf : Frame [polyRegion (F s₀)] s₀.mem m) {j : Nat}
    (hj : j < 256) (v : BitVec 32) :
    Frame [polyRegion (F s₀)] s₀.mem (m.writeW (coeffAddr (F s₀) j) v) :=
  hf.writeW (List.mem_singleton_self _) _ (coeff_contains _ (by rw [n_eq]; exact hj))

/-- The counter of an iteration. -/
theorem count_step {N i : Nat} (hi : i < N) (hN : N < 2 ^ 64) :
    BitVec.ofNat 64 (N - i) - 1 = BitVec.ofNat 64 (N - (i + 1)) ∧
      (BitVec.ofNat 64 (N - i) - 1 != 0) = decide (i + 1 ≠ N) := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
  exact ⟨rfl, count_nz hi hN⟩

theorem step5 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 5) {i : Nat} (hi : i < 32) {s : State}
    (h : Inv s₀ 5 32 i s) :
    WP isa (.block dd5Body) s fun s' =>
      Inv s₀ 5 32 (i + 1) s' ∧ (s'.gpr .r11 != 0) = decide (i + 1 ≠ 32) := by
  have hL : L s₀ = 160 := by rw [hp.len, hd]
  have hB : (Bl s₀).length = 160 := by rw [bytesAt_length, hL]
  have eb : ∀ k < 5, B s₀ + BitVec.ofNat 64 (5 * i) + BitVec.ofNat 64 k =
      B s₀ + BitVec.ofNat 64 (5 * i + k) := fun k _ => ptr_add _ _ _
  have rb : ∀ k < 5, s.mem (B s₀ + BitVec.ofNat 64 (5 * i + k)) = (Bl s₀).getD (5 * i + k) 0 :=
    fun k hk => byte_rd hp h (by omega_arith)
  have a : ∀ j < 8, F s₀ + BitVec.ofNat 64 (32 * i) + BitVec.ofNat 64 (4 * j) =
      coeffAddr (F s₀) (8 * i + j) := fun j _ => by
    rw [ptr_add, show 32 * i + 4 * j = 4 * (8 * i + j) by omega_arith]
  have a0 : F s₀ + BitVec.ofNat 64 (32 * i) = coeffAddr (F s₀) (8 * i) := by
    rw [show 32 * i = 4 * (8 * i) by omega_arith]
  refine WP.mono (body5_ok h.r3 h.r6 h.r11 h.r9 (fun k hk => by
      rw [eb k hk]; exact in_rd hp h (by omega_arith)) (fun j hj => ?_))
    fun s' ⟨r3, r6, r11, ⟨r9, rd, wr, sp, lr, pres⟩, m⟩ => ?_
  · rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.mul_zero, BitVec.add_zero, Nat.reduceMul] <;>
      (first | rw [a 7 (by decide)] | rw [a 6 (by decide)] | rw [a 5 (by decide)] |
        rw [a 4 (by decide)] | rw [a 3 (by decide)] | rw [a 2 (by decide)] | rw [a 1 (by decide)] |
        rw [a0]) <;> exact out_wr hp h (by omega_arith)
  obtain ⟨c1, c2⟩ := count_step (N := 32) hi (by decide)
  have e := g5_toNat s (B s₀ + BitVec.ofNat 64 (5 * i))
  rw [eb 1 (by omega_arith), eb 2 (by omega_arith), eb 3 (by omega_arith), eb 4 (by omega_arith),
    show B s₀ + BitVec.ofNat 64 (5 * i) = B s₀ + BitVec.ofNat 64 (5 * i + 0) from rfl,
    rb 0 (by omega_arith), rb 1 (by omega_arith), rb 2 (by omega_arith), rb 3 (by omega_arith), rb 4 (by omega_arith),
    Nat.add_zero] at e
  have v : ∀ k < 8, (dec 5 (G5 s (B s₀ + BitVec.ofNat 64 (5 * i)) <<< (64 - 5 - 5 * k) >>>
      (64 - 5))).setWidth 32 = out s₀ (8 * i + k) := fun k hk => by
    rw [f5_val _ hk, out, D, hd, decodeDecompress5_group _ hB hi hk, e]
  have v0 := v 0 (by decide)
  have v1 := v 1 (by decide)
  have v2 := v 2 (by decide)
  have v3 := v 3 (by decide)
  have v4 := v 4 (by decide)
  have v5 := v 5 (by decide)
  have v6 := v 6 (by decide)
  have v7 := v 7 (by decide)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.mul_zero, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7
  refine ⟨⟨?_, ?_, r11.trans c1, r9.trans h.r9, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
    lr.trans h.lr, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, by rw [r11]; exact c2⟩
  · rw [r3]; exact ptr_succ _ 5 i
  · rw [r6]; exact ptr_succ _ 32 i
  · rw [m, a 7 (by decide), a 6 (by decide), a 5 (by decide), a 4 (by decide), a 3 (by decide),
      a 2 (by decide), a 1 (by decide), a0]
    refine out_frame (out_frame (out_frame (out_frame (out_frame (out_frame (out_frame (out_frame
      h.frame ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _ <;> omega_arith
  · rw [m, a 7 (by decide), a 6 (by decide), a 5 (by decide), a 4 (by decide), a 3 (by decide),
      a 2 (by decide), a 1 (by decide), a0, v0, v1, v2, v3, v4, v5, v6, v7,
      show 8 * (i + 1) = 8 * i + 7 + 1 by omega_arith]
    exact coeff_one (by omega_arith) (coeff_one (by omega_arith) (coeff_one (by omega_arith) (coeff_one (by omega_arith)
      (coeff_one (by omega_arith) (coeff_one (by omega_arith) (coeff_one (by omega_arith) (coeff_one (by omega_arith)
      h.coeff rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl

theorem step11 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 11) {i : Nat} (hi : i < 32) {s : State}
    (h : Inv s₀ 11 32 i s) :
    WP isa (.block dd11Body) s fun s' =>
      Inv s₀ 11 32 (i + 1) s' ∧ (s'.gpr .r11 != 0) = decide (i + 1 ≠ 32) := by
  have hL : L s₀ = 352 := by rw [hp.len, hd]
  have hB : (Bl s₀).length = 352 := by rw [bytesAt_length, hL]
  have eb : ∀ k < 11, B s₀ + BitVec.ofNat 64 (11 * i) + BitVec.ofNat 64 k =
      B s₀ + BitVec.ofNat 64 (11 * i + k) := fun k _ => ptr_add _ _ _
  have rb : ∀ k < 11, s.mem (B s₀ + BitVec.ofNat 64 (11 * i + k)) = (Bl s₀).getD (11 * i + k) 0 :=
    fun k hk => byte_rd hp h (by omega_arith)
  have a : ∀ j < 8, F s₀ + BitVec.ofNat 64 (32 * i) + BitVec.ofNat 64 (4 * j) =
      coeffAddr (F s₀) (8 * i + j) := fun j _ => by
    rw [ptr_add, show 32 * i + 4 * j = 4 * (8 * i + j) by omega_arith]
  have a0 : F s₀ + BitVec.ofNat 64 (32 * i) = coeffAddr (F s₀) (8 * i) := by
    rw [show 32 * i = 4 * (8 * i) by omega_arith]
  refine WP.mono (body11_ok h.r3 h.r6 h.r11 h.r9 (fun k hk => by
      rw [eb k hk]; exact in_rd hp h (by omega_arith)) (fun j hj => ?_))
    fun s' ⟨r3, r6, r11, ⟨r9, rd, wr, sp, lr, pres⟩, m⟩ => ?_
  · rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.mul_zero, BitVec.add_zero, Nat.reduceMul] <;>
      (first | rw [a 7 (by decide)] | rw [a 6 (by decide)] | rw [a 5 (by decide)] |
        rw [a 4 (by decide)] | rw [a 3 (by decide)] | rw [a 2 (by decide)] | rw [a 1 (by decide)] |
        rw [a0]) <;> exact out_wr hp h (by omega_arith)
  obtain ⟨c1, c2⟩ := count_step (N := 32) hi (by decide)
  have ea := g11a_toNat s (B s₀ + BitVec.ofNat 64 (11 * i))
  rw [eb 1 (by omega_arith), eb 2 (by omega_arith), eb 3 (by omega_arith), eb 4 (by omega_arith), eb 5 (by omega_arith),
    show B s₀ + BitVec.ofNat 64 (11 * i) = B s₀ + BitVec.ofNat 64 (11 * i + 0) from rfl,
    rb 0 (by omega_arith), rb 1 (by omega_arith), rb 2 (by omega_arith), rb 3 (by omega_arith), rb 4 (by omega_arith),
    rb 5 (by omega_arith), Nat.add_zero] at ea
  have ebb := g11b_toNat s (B s₀ + BitVec.ofNat 64 (11 * i))
  rw [eb 5 (by omega_arith), eb 6 (by omega_arith), eb 7 (by omega_arith), eb 8 (by omega_arith), eb 9 (by omega_arith),
    eb 10 (by omega_arith), rb 5 (by omega_arith), rb 6 (by omega_arith), rb 7 (by omega_arith), rb 8 (by omega_arith),
    rb 9 (by omega_arith), rb 10 (by omega_arith)] at ebb
  have l0 := ((Bl s₀).getD (11 * i) 0).isLt
  have l1 := ((Bl s₀).getD (11 * i + 1) 0).isLt
  have l2 := ((Bl s₀).getD (11 * i + 2) 0).isLt
  have l3 := ((Bl s₀).getD (11 * i + 3) 0).isLt
  have l4 := ((Bl s₀).getD (11 * i + 4) 0).isLt
  have l5 := ((Bl s₀).getD (11 * i + 5) 0).isLt
  have l6 := ((Bl s₀).getD (11 * i + 6) 0).isLt
  have l7 := ((Bl s₀).getD (11 * i + 7) 0).isLt
  have l8 := ((Bl s₀).getD (11 * i + 8) 0).isLt
  have l9 := ((Bl s₀).getD (11 * i + 9) 0).isLt
  have l10 := ((Bl s₀).getD (11 * i + 10) 0).isLt
  simp only [Nat.reducePow] at l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10
  have va : ∀ k < 4, (dec 11 (G11a s (B s₀ + BitVec.ofNat 64 (11 * i)) <<< (64 - 11 - 11 * k) >>>
      (64 - 11))).setWidth 32 = out s₀ (8 * i + k) := fun k hk => by
    rw [f11_val _ (by omega_arith), out, D, hd, decodeDecompress11_group _ hB hi (by omega_arith), ea]
    refine congrArg (fun y => BitVec.ofNat 32 (decompress 11 y).val) ?_
    rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
      simp only [Nat.reducePow, Nat.reduceMul, Nat.mul_zero, Nat.pow_zero, Nat.div_one] <;> omega_arith
  have vb : ∀ k < 4, (dec 11 (G11b s (B s₀ + BitVec.ofNat 64 (11 * i)) <<<
      (64 - 11 - (11 * k + 4)) >>> (64 - 11))).setWidth 32 = out s₀ (8 * i + 4 + k) :=
    fun k hk => by
    rw [f11_val _ (by omega_arith), out, D, hd,
      show 8 * i + 4 + k = 8 * i + (4 + k) by omega_arith,
      decodeDecompress11_group _ hB hi (by omega_arith), ebb]
    refine congrArg (fun y => BitVec.ofNat 32 (decompress 11 y).val) ?_
    rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] <;> omega_arith
  have v0 := va 0 (by decide)
  have v1 := va 1 (by decide)
  have v2 := va 2 (by decide)
  have v3 := va 3 (by decide)
  have v4 := vb 0 (by decide)
  have v5 := vb 1 (by decide)
  have v6 := vb 2 (by decide)
  have v7 := vb 3 (by decide)
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    at v0 v1 v2 v3 v4 v5 v6 v7
  refine ⟨⟨?_, ?_, r11.trans c1, r9.trans h.r9, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
    lr.trans h.lr, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, by rw [r11]; exact c2⟩
  · rw [r3]; exact ptr_succ _ 11 i
  · rw [r6]; exact ptr_succ _ 32 i
  · rw [m, a 7 (by decide), a 6 (by decide), a 5 (by decide), a 4 (by decide), a 3 (by decide),
      a 2 (by decide), a 1 (by decide), a0]
    refine out_frame (out_frame (out_frame (out_frame (out_frame (out_frame (out_frame (out_frame
      h.frame ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _ <;> omega_arith
  · rw [m, a 7 (by decide), a 6 (by decide), a 5 (by decide), a 4 (by decide), a 3 (by decide),
      a 2 (by decide), a 1 (by decide), a0, v0, v1, v2, v3, v4, v5, v6, v7,
      show 8 * (i + 1) = 8 * i + 7 + 1 by omega_arith]
    exact coeff_one (by omega_arith) (coeff_one (by omega_arith) (coeff_one (by omega_arith) (coeff_one (by omega_arith)
      (coeff_one (by omega_arith) (coeff_one (by omega_arith) (coeff_one (by omega_arith) (coeff_one (by omega_arith)
      h.coeff rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl

/-! ## The branches -/

/-- What the loops end with. -/
def Fin (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
    ∀ j < 256, coeffAt s.mem (F s₀) j = out s₀ j

/-- What a branch starts from. -/
def Start (s₀ s : State) : Prop :=
  s.gpr .r3 = B s₀ ∧ s.gpr .r6 = F s₀ ∧ s.gpr .r9 = 3329 ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    s.sp = s₀.sp ∧ s.lr = s₀.lr ∧ (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem

theorem st {s₀ s : State} (h : Start s₀ s) {r : Reg} (hr : r = .r7 ∨ r = .r11) (v : BitVec 64) :
    Start s₀ (s.write r v) := by
  obtain ⟨r3, r6, r9, rd, wr, sp, lr, pres, m⟩ := h
  have h3 : Reg.r3 ≠ r := by rcases hr with rfl | rfl <;> decide
  have h6 : Reg.r6 ≠ r := by rcases hr with rfl | rfl <;> decide
  have h9 : Reg.r9 ≠ r := by rcases hr with rfl | rfl <;> decide
  refine ⟨by simp [State.write, h3, r3], by simp [State.write, h6, r6],
    by simp [State.write, h9, r9], rd, wr, sp, lr, fun r' hr' => ?_, m⟩
  have : r' ≠ r := by rcases hr with rfl | rfl <;> revert r' hr' <;> decide
  simp [State.write, this, pres r' hr']

theorem loop_fin {s₀ : State} {inS N : Nat} (hN : 8 * N = 256) {s : State}
    (h : Inv s₀ inS N N s) : Fin s₀ s :=
  ⟨h.pres, h.sp, h.lr, fun j hj => by rw [h.coeff j hj, ite_eq_left (by omega_arith)]⟩

theorem inv_zero {s₀ : State} {inS N : Nat} {s : State} (h : Start s₀ s)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 N) : Inv s₀ inS N 0 s := by
  obtain ⟨r3, r6, r9, rd, wr, sp, lr, pres, m⟩ := h
  exact ⟨by simp [r3], by simp [r6], by simp [h11], r9, rd, wr, sp, lr, pres,
    by rw [m]; exact Frame.refl _ _, fun j _ => by rw [m, ite_eq_right (by omega_arith)]⟩

theorem branch5 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 5) {s : State} (h : Start s₀ s) :
    WP isa (.seq (.block [.li .r11 32]) (.loop (.block dd5Body) (.nonzero .d .r11))) s (Fin s₀) := by
  refine WP.seq (WP.cons (exec_li (by decide)) (wp_nil ?_))
  refine wp_loop_nz (Inv s₀ 5 32) (N := 32) (by decide) (fun i hi s h => step5 hp hd hi h)
    (fun s h => loop_fin (by decide) h) (inv_zero (st h (.inr rfl) _) (by simp [State.write]))

theorem branch11 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 11) {s : State} (h : Start s₀ s) :
    WP isa (.seq (.block [.li .r11 32]) (.loop (.block dd11Body) (.nonzero .d .r11))) s (Fin s₀) := by
  refine WP.seq (WP.cons (exec_li (by decide)) (wp_nil ?_))
  refine wp_loop_nz (Inv s₀ 11 32) (N := 32) (by decide) (fun i hi s h => step11 hp hd hi h)
    (fun s h => loop_fin (by decide) h) (inv_zero (st h (.inr rfl) _) (by simp [State.write]))

/-- `r5` zero-extended. -/
abbrev Z (s₀ : State) : BitVec 64 := (((s₀.gpr .r5).setWidth 32).rotateRight 0).setWidth 64

theorem sel_eval {s₀ s : State} {k : Nat} (hk : k < 2 ^ 15)
    (h : s.gpr .r7 = Z s₀ - BitVec.ofNat 64 k) :
    isa.eval (.zero .w .r7) s = some (decide (dN s₀ = k)) := by
  have r0 : ∀ v : BitVec 32, v.rotateRight 0 = v := fun v => by
    simp [BitVec.rotateRight, BitVec.rotateRightAux]
  show VG.PPC64LE.eval (.zero .w .r7) s = _
  simp only [VG.PPC64LE.eval, State.read, Size.bits, h]
  rw [dsel _ hk, r0]

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa decodeDecompress1024 s₀ (Fin s₀) := by
  refine WP.seq (WP.cons (exec_rotr_w (by decide)) (wp_nil ?_))
  refine WP.seq (WP.cons (exec_li (by decide)) (WP.cons (exec_subi (by decide) (by decide))
    (wp_nil ?_)))
  have s0 : Start s₀ ((s₀.write .r5 (Z s₀)).write .r9 (BitVec.ofNat 64 3329)) :=
    ⟨by simp [State.write], by simp [State.write], by simp [State.write], rfl, rfl, rfl, rfl,
      fun r hr => by
        have : r ≠ .r5 ∧ r ≠ .r9 := by revert r hr; decide
        simp [State.write, this.1, this.2], rfl⟩
  rcases mem_compressWidths1024 hp.dw with hd | hd
  · refine WP.ite true
      (by rw [sel_eval (s₀ := s₀) (k := 5) (by decide) (by simp [State.write]), hd]; rfl)
      (fun _ => branch5 hp hd (st s0 (.inl rfl) _)) (fun h => absurd h (by decide))
  · refine WP.ite false
      (by rw [sel_eval (s₀ := s₀) (k := 5) (by decide) (by simp [State.write]), hd]; rfl)
      (fun h => absurd h (by decide)) (fun _ => branch11 hp hd (st s0 (.inl rfl) _))

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlKem1024.decodeDecompressContract PPC64LE.abi).pre s) :
    Pre s := by
  sig_pre [Proof.MlKem1024.decodeDecompressContract, Proof.MlKem1024.decodeDecompressSig,
    PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 160 | .r5 => 5 | .r6 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 160⟩]
  wr := [⟨0x2000, 1024⟩]

theorem verified : Verified PPC64LE.target decodeDecompress1024
    (Proof.MlKem1024.decodeDecompressContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, RelCT.constantTime (Q := fun _ _ => True) ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hlr⟩, ?_⟩
    sig_post [Proof.MlKem1024.decodeDecompressContract, Proof.MlKem1024.decodeDecompressSig,
      PPC64LE.abi, PPC64LE.argRegs]
    exact polyIs_of_coeffAt (p := F s) fun j hj => by
      rw [h j (by rw [n_eq] at hj; exact hj)]; rfl
  · refine RelCT.seq (VG.Proof.MlKem.PPC64LE.DecodeDecompress.zext_rel.mono
      (fun s₁ s₂ ⟨_, _, hp⟩ => ?_) fun _ _ h => h)
      (RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
        (fun _ _ ⟨hsp, hr⟩ => ⟨hsp, fun r h => hr r (Taint.mem_ofRegs.mp h)⟩) (by taint_decide))
    sig_pub [Proof.MlKem1024.decodeDecompressContract, Proof.MlKem1024.decodeDecompressSig,
      PPC64LE.abi, PPC64LE.argRegs] at hp
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
    · sig_reduce [Proof.MlKem1024.decodeDecompressContract, Proof.MlKem1024.decodeDecompressSig,
        PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem1024.PPC64LE.Decompress
