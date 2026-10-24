module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.DecodeDecompress
public import VerifiedGarbage.Impl.MlKem1024.PPC64LE.Poly
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.MlKem.Encode1024
public import VerifiedGarbage.Proof.MlKem.Compress1024
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
import VerifiedGarbage.Proof.MlKem.PPC64LE.Reduce
import VerifiedGarbage.Proof.MlKem.PPC64LE.Bytes
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Compress
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
meta import VerifiedGarbage.Proof.MlKem.Encode1024
meta import VerifiedGarbage.Proof.MlKem.Compress1024
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
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
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.PPC64LE
open VG.Proof.MlKem.PPC64LE.DecodeDecompress (dec Keep byte64 ext_toNat)

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
  crun [dd5Body, ddByteAt, dd5Field, decompressTo, Keep, dec, G5, h3, h6, h11, h9, b0, b1, b2, b3,
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
  crun [dd11Body, ddByteAt, dd11Field, decompressTo, Keep, dec, G11a, G11b, h3, h6, h11, h9, b0, b1,
    b2, b3, b4, b5, b6, b7, b8, b9, b10, o0, o1, o2, o3, o4, o5, o6, o7, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, setWidth_zero_append]

end

/-! ## The values -/

theorem dec_val4 {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) {Y : BitVec 64} {y : Nat}
    (hY : Y.toNat = y) (hy : y < 2 ^ d) :
    (dec d Y).setWidth 32 = BitVec.ofNat 32 (decompress d y).val := by
  obtain ⟨e, lt⟩ := decompress1024_val hd hy
  have hd' : d ≤ 11 := by rcases mem_compressWidths1024 hd with rfl | rfl <;> decide
  have hp : 2 ^ (d - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega)
  have hP : 2 ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hd'
  have hq : q = 3329 := q_eq
  refine setWidth32_ofNat ?_ (by omega)
  have h3 : (3329 : BitVec 64).toNat = 3329 := rfl
  rw [e, dec, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_mul,
    hY, h3, BitVec.toNat_ofNat, q_eq]
  congr 1
  rw [Nat.mod_eq_of_lt (a := 2 ^ (d - 1)) (by omega), Nat.mod_eq_of_lt (a := y * 3329) (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

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
  simp only [G5, BitVec.toNat_add, BitVec.toNat_shiftLeft, byte64, Nat.shiftLeft_eq]
  generalize (s.mem x).toNat = a0 at *
  generalize (s.mem (x + BitVec.ofNat 64 1)).toNat = a1 at *
  generalize (s.mem (x + BitVec.ofNat 64 2)).toNat = a2 at *
  generalize (s.mem (x + BitVec.ofNat 64 3)).toNat = a3 at *
  generalize (s.mem (x + BitVec.ofNat 64 4)).toNat = a4 at *
  simp only [Nat.reducePow] at *
  omega

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
  simp only [G11a, BitVec.toNat_add, BitVec.toNat_shiftLeft, byte64, Nat.shiftLeft_eq]
  generalize (s.mem x).toNat = a0 at *
  generalize (s.mem (x + BitVec.ofNat 64 1)).toNat = a1 at *
  generalize (s.mem (x + BitVec.ofNat 64 2)).toNat = a2 at *
  generalize (s.mem (x + BitVec.ofNat 64 3)).toNat = a3 at *
  generalize (s.mem (x + BitVec.ofNat 64 4)).toNat = a4 at *
  generalize (s.mem (x + BitVec.ofNat 64 5)).toNat = a5 at *
  simp only [Nat.reducePow] at *
  omega

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
  simp only [G11b, BitVec.toNat_add, BitVec.toNat_shiftLeft, byte64, Nat.shiftLeft_eq]
  generalize (s.mem (x + BitVec.ofNat 64 5)).toNat = a5 at *
  generalize (s.mem (x + BitVec.ofNat 64 6)).toNat = a6 at *
  generalize (s.mem (x + BitVec.ofNat 64 7)).toNat = a7 at *
  generalize (s.mem (x + BitVec.ofNat 64 8)).toNat = a8 at *
  generalize (s.mem (x + BitVec.ofNat 64 9)).toNat = a9 at *
  generalize (s.mem (x + BitVec.ofNat 64 10)).toNat = a10 at *
  simp only [Nat.reducePow] at *
  omega

theorem f5_val (G : BitVec 64) {k : Nat} (hk : k < 8) :
    (dec 5 (G <<< (64 - 5 - 5 * k) >>> (64 - 5))).setWidth 32 =
      BitVec.ofNat 32 (decompress 5 (G.toNat / 2 ^ (5 * k) % 2 ^ 5)).val :=
  dec_val4 (by decide) (ext_toNat _ (by omega)) (Nat.mod_lt _ (by decide))

theorem f11_val (G : BitVec 64) {p : Nat} (hp : p + 11 ≤ 64) :
    (dec 11 (G <<< (64 - 11 - p) >>> (64 - 11))).setWidth 32 =
      BitVec.ofNat 32 (decompress 11 (G.toNat / 2 ^ p % 2 ^ 11)).val :=
  dec_val4 (by decide) (ext_toNat _ hp) (Nat.mod_lt _ (by decide))

end VG.Proof.MlKem1024.PPC64LE.Decompress
