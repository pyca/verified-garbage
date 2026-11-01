module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.CompressEncode
public import VerifiedGarbage.Impl.MlKem1024.PPC64LE.Poly
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.MlKem1024.Contract
import VerifiedGarbage.Proof.MlKem.Encode1024
public import VerifiedGarbage.Proof.MlKem.Compress1024
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Reduce
import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
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
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.CompressEncode
meta import VerifiedGarbage.Impl.MlKem1024.PPC64LE.Poly
meta import VerifiedGarbage.Spec.MlKem.Contract1024
meta import VerifiedGarbage.Proof.MlKem1024.Contract
meta import VerifiedGarbage.Proof.MlKem.Encode1024
meta import VerifiedGarbage.Proof.MlKem.Compress1024
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Reduce
import VerifiedGarbage.Proof.MlKem.PPC64LE.Reduce
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
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
public import VerifiedGarbage.Spec.MlKem
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RunR

/-!
# ML-KEM-1024 on PPC64LE: `vg_mlkem1024_compress_encode`

A loop for each width, over the output, each iteration a group of 8
coefficients whose fields are added into `r8` and stored a byte at a time:
five bytes for `d = 5`, and for `d = 11` five from the first four
coefficients and six from what is left of them and the last four. The body
is symbolically executed once for any pointers (`body5_ok`, `body11_ok`).
The values are `compress1024_eq`, with the product in 64 bits
(`cmpV4_toNat`), and the bytes `compressEncode5_group` and
`compressEncode11_group`.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.PPC64LE.CompressEncode

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE VG.Impl.MlKem1024.PPC64LE
open VG.Spec.MlKem
open VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.PPC64LE
open VG.Proof.MlKem.PPC64LE.CompressEncode (fld field_toNat toNat_add_eq dsel Keep A)

/-! ## The values -/

/-- `(x · M + 2¹⁸ - 256) >> 19`, as `compressAt` computes it with the bias
of ML-KEM-1024. -/
def cmpV4 (M x : BitVec 64) : BitVec 64 := (x * M + 261888) >>> 19

theorem cmpV4_toNat {d : Nat} (hd : d ∈ Proof.MlKem1024.compressWidths) {M : BitVec 64}
    (hM : M.toNat = compressMul1024 d) (x : Zq) :
    (cmpV4 M (BitVec.ofNat 64 x.val)).toNat = (x.val * compressMul1024 d + compressAdd1024) / 2 ^ 19 := by
  have hx := val_lt x
  have ha := compress1024_arg_lt hd x
  have hp : (BitVec.ofNat 64 x.val * M).toNat = x.val * compressMul1024 d := by
    rw [BitVec.toNat_mul, toNat_val64, hM]
    exact Nat.mod_eq_of_lt (by unfold compressAdd1024 at ha; omega_arith)
  unfold compressAdd1024 at ha ⊢
  unfold cmpV4
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, hp]
  refine congrArg (· / 2 ^ 19) ?_
  rw [show (261888 : BitVec 64).toNat = 261888 from rfl]
  omega_arith

theorem fld_cmp4 {d : Nat} (hd : d ∈ Proof.MlKem1024.compressWidths) {M : BitVec 64}
    (hM : M.toNat = compressMul1024 d) (v : Zq) {p : Nat} (hp : p + d ≤ 64) :
    (fld d p (cmpV4 M (BitVec.ofNat 64 v.val))).toNat = compress d v * 2 ^ p := by
  unfold fld
  rw [field_toNat _ hp, cmpV4_toNat hd hM, compress1024_eq hd]

/-! ## The loop bodies -/

section
variable {s : State} {x y c M : BitVec 64}

/-- The eight fields of a group of `ByteEncode₅(Compress₅)`, in one doubleword. -/
abbrev V5 (s : State) (x M : BitVec 64) : BitVec 64 :=
  0 + fld 5 0 (cmpV4 M (A s x 0)) + fld 5 5 (cmpV4 M (A s x 1)) + fld 5 10 (cmpV4 M (A s x 2)) +
    fld 5 15 (cmpV4 M (A s x 3)) + fld 5 20 (cmpV4 M (A s x 4)) + fld 5 25 (cmpV4 M (A s x 5)) +
    fld 5 30 (cmpV4 M (A s x 6)) + fld 5 35 (cmpV4 M (A s x 7))

theorem body5_ok (h3 : s.gpr .r3 = x) (h5 : s.gpr .r5 = y) (h11 : s.gpr .r11 = c) (h9 : s.gpr .r9 = M)
    (h10 : s.gpr .r10 = 261888)
    (ia : ∀ j < 8, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (4 * j)) 4)
    (ob : ∀ k < 5, InRegions s.wr (y + BitVec.ofNat 64 k) 1) :
    WP isa (.block ce5Body) s fun s' =>
      s'.gpr .r3 = x + 32 ∧ s'.gpr .r5 = y + 5 ∧ s'.gpr .r11 = c - 1 ∧ Keep s s' ∧
      s'.mem = ((((s.mem.writeW y ((V5 s x M).setWidth 8)).writeW (y + BitVec.ofNat 64 1)
        ((V5 s x M >>> 8).setWidth 8)).writeW (y + BitVec.ofNat 64 2) ((V5 s x M >>> 16).setWidth 8)).writeW
        (y + BitVec.ofNat 64 3) ((V5 s x M >>> 24).setWidth 8)).writeW (y + BitVec.ofNat 64 4)
        ((V5 s x M >>> 32).setWidth 8) := by
  have i0 := ia 0 (by decide)
  have i1 := ia 1 (by decide)
  have i2 := ia 2 (by decide)
  have i3 := ia 3 (by decide)
  have i4 := ia 4 (by decide)
  have i5 := ia 5 (by decide)
  have i6 := ia 6 (by decide)
  have i7 := ia 7 (by decide)
  have o0 := ob 0 (by decide)
  have o1 := ob 1 (by decide)
  have o2 := ob 2 (by decide)
  have o3 := ob 3 (by decide)
  have o4 := ob 4 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at i0 i1 i2 i3 i4 i5 i6 i7 o0
  crunr [ce5Body, ce5Coeff, ce5Store, compressAt, Keep, V5, A, fld, cmpV4, h3, h5, h11, h9, h10,
    i0, i1, i2, i3, i4, i5, i6, i7, o0, o1, o2, o3, o4, preserved, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

/-- The first four fields of a group of `ByteEncode₁₁(Compress₁₁)`, in one doubleword. -/
abbrev V11a (s : State) (x M : BitVec 64) : BitVec 64 :=
  0 + fld 11 0 (cmpV4 M (A s x 0)) + fld 11 11 (cmpV4 M (A s x 1)) + fld 11 22 (cmpV4 M (A s x 2)) +
    fld 11 33 (cmpV4 M (A s x 3))

/-- What is left of them, and the last four fields. -/
abbrev V11b (s : State) (x M : BitVec 64) : BitVec 64 :=
  V11a s x M >>> 40 + (0 + fld 11 4 (cmpV4 M (A s x 4)) + fld 11 15 (cmpV4 M (A s x 5)) +
    fld 11 26 (cmpV4 M (A s x 6)) + fld 11 37 (cmpV4 M (A s x 7)))

theorem body11_ok (h3 : s.gpr .r3 = x) (h5 : s.gpr .r5 = y) (h11 : s.gpr .r11 = c) (h9 : s.gpr .r9 = M)
    (h10 : s.gpr .r10 = 261888)
    (ia : ∀ j < 8, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (4 * j)) 4)
    (ob : ∀ k < 11, InRegions s.wr (y + BitVec.ofNat 64 k) 1) :
    WP isa (.block ce11Body) s fun s' =>
      s'.gpr .r3 = x + 32 ∧ s'.gpr .r5 = y + 11 ∧ s'.gpr .r11 = c - 1 ∧ Keep s s' ∧
      s'.mem = ((((((((((s.mem.writeW y ((V11a s x M).setWidth 8)).writeW (y + BitVec.ofNat 64 1)
        ((V11a s x M >>> 8).setWidth 8)).writeW (y + BitVec.ofNat 64 2)
        ((V11a s x M >>> 16).setWidth 8)).writeW (y + BitVec.ofNat 64 3)
        ((V11a s x M >>> 24).setWidth 8)).writeW (y + BitVec.ofNat 64 4)
        ((V11a s x M >>> 32).setWidth 8)).writeW (y + BitVec.ofNat 64 5)
        ((V11b s x M).setWidth 8)).writeW (y + BitVec.ofNat 64 6)
        ((V11b s x M >>> 8).setWidth 8)).writeW (y + BitVec.ofNat 64 7)
        ((V11b s x M >>> 16).setWidth 8)).writeW (y + BitVec.ofNat 64 8)
        ((V11b s x M >>> 24).setWidth 8)).writeW (y + BitVec.ofNat 64 9)
        ((V11b s x M >>> 32).setWidth 8)).writeW (y + BitVec.ofNat 64 10)
        ((V11b s x M >>> 40).setWidth 8) := by
  have i0 := ia 0 (by decide)
  have i1 := ia 1 (by decide)
  have i2 := ia 2 (by decide)
  have i3 := ia 3 (by decide)
  have i4 := ia 4 (by decide)
  have i5 := ia 5 (by decide)
  have i6 := ia 6 (by decide)
  have i7 := ia 7 (by decide)
  have o0 := ob 0 (by decide)
  have o1 := ob 1 (by decide)
  have o2 := ob 2 (by decide)
  have o3 := ob 3 (by decide)
  have o4 := ob 4 (by decide)
  have o5 := ob 5 (by decide)
  have o6 := ob 6 (by decide)
  have o7 := ob 7 (by decide)
  have o8 := ob 8 (by decide)
  have o9 := ob 9 (by decide)
  have o10 := ob 10 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at i0 i1 i2 i3 i4 i5 i6 i7 o0
  crunr [ce11Body, ce11Coeff, ce11CoeffHi, ce5Store, ce11Store, compressAt, Keep, V11a, V11b, A, fld, cmpV4,
    h3, h5, h11, h9, h10, i0, i1, i2, i3, i4, i5, i6, i7, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10,
    preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The bytes -/

section
variable (f : Poly) {M : BitVec 64}

/-- The eight compressed coefficients of group `g`, as a doubleword. -/
abbrev W5 (g : Nat) : BitVec 64 :=
  0 + fld 5 0 (cmpV4 M (BitVec.ofNat 64 f[8 * g]!.val)) +
    fld 5 5 (cmpV4 M (BitVec.ofNat 64 f[8 * g + 1]!.val)) +
    fld 5 10 (cmpV4 M (BitVec.ofNat 64 f[8 * g + 2]!.val)) +
    fld 5 15 (cmpV4 M (BitVec.ofNat 64 f[8 * g + 3]!.val)) +
    fld 5 20 (cmpV4 M (BitVec.ofNat 64 f[8 * g + 4]!.val)) +
    fld 5 25 (cmpV4 M (BitVec.ofNat 64 f[8 * g + 5]!.val)) +
    fld 5 30 (cmpV4 M (BitVec.ofNat 64 f[8 * g + 6]!.val)) +
    fld 5 35 (cmpV4 M (BitVec.ofNat 64 f[8 * g + 7]!.val))

theorem w5_toNat (hM : M.toNat = compressMul1024 5) (g : Nat) :
    (W5 f (M := M) g).toNat = compress 5 f[8 * g]! + 32 * compress 5 f[8 * g + 1]! +
      1024 * compress 5 f[8 * g + 2]! + 32768 * compress 5 f[8 * g + 3]! +
      1048576 * compress 5 f[8 * g + 4]! + 33554432 * compress 5 f[8 * g + 5]! +
      1073741824 * compress 5 f[8 * g + 6]! + 34359738368 * compress 5 f[8 * g + 7]! := by
  have b : ∀ k, compress 5 f[8 * g + k]! < 2 ^ 5 := fun k => compress_lt 5 _
  have b0 := compress_lt 5 f[8 * g]!
  have e : ∀ {p : Nat}, p + 5 ≤ 64 → ∀ v : Zq, (fld 5 p (cmpV4 M (BitVec.ofNat 64 v.val))).toNat =
      compress 5 v * 2 ^ p := fun hp v => fld_cmp4 (by decide) hM v hp
  have h0 := e (p := 0) (by decide) f[8 * g]!
  have h1 := e (p := 5) (by decide) f[8 * g + 1]!
  have h2 := e (p := 10) (by decide) f[8 * g + 2]!
  have h3 := e (p := 15) (by decide) f[8 * g + 3]!
  have h4 := e (p := 20) (by decide) f[8 * g + 4]!
  have h5 := e (p := 25) (by decide) f[8 * g + 5]!
  have h6 := e (p := 30) (by decide) f[8 * g + 6]!
  have h7 := e (p := 35) (by decide) f[8 * g + 7]!
  have c1 := b 1
  have c2 := b 2
  have c3 := b 3
  have c4 := b 4
  have c5 := b 5
  have c6 := b 6
  have c7 := b 7
  rw [toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq
    (toNat_add_eq (toNat_add_eq (a := 0) (A := 0) rfl h0 (by simp only [Nat.pow_zero]; omega_arith))
      h1 (by simp only [Nat.reducePow]; omega_arith)) h2 (by simp only [Nat.reducePow]; omega_arith))
      h3 (by simp only [Nat.reducePow]; omega_arith)) h4 (by simp only [Nat.reducePow]; omega_arith))
      h5 (by simp only [Nat.reducePow]; omega_arith)) h6 (by simp only [Nat.reducePow]; omega_arith))
      h7 (by simp only [Nat.reducePow]; omega_arith)]
  simp only [Nat.reducePow, Nat.mul_one, Nat.zero_add]
  omega_arith

theorem byte5 (hM : M.toNat = compressMul1024 5) {g : Nat} (hg : g < 32) :
    (W5 f (M := M) g).setWidth 8 = (compressEncode 5 f)[5 * g]! ∧
    (W5 f (M := M) g >>> 8).setWidth 8 = (compressEncode 5 f)[5 * g + 1]! ∧
    (W5 f (M := M) g >>> 16).setWidth 8 = (compressEncode 5 f)[5 * g + 2]! ∧
    (W5 f (M := M) g >>> 24).setWidth 8 = (compressEncode 5 f)[5 * g + 3]! ∧
    (W5 f (M := M) g >>> 32).setWidth 8 = (compressEncode 5 f)[5 * g + 4]! := by
  have e := w5_toNat f hM g
  have g0 := compressEncode5_group f hg (j := 0) (by decide)
  have g1 := compressEncode5_group f hg (j := 1) (by decide)
  have g2 := compressEncode5_group f hg (j := 2) (by decide)
  have g3 := compressEncode5_group f hg (j := 3) (by decide)
  have g4 := compressEncode5_group f hg (j := 4) (by decide)
  simp only [Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul] at g0 g1 g2 g3 g4
  rw [g0, g1, g2, g3, g4]
  generalize W5 f (M := M) g = V at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat] <;>
    (try rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]) <;> rw [e] <;>
    simp only [Nat.reducePow] <;> omega_arith

end

section
variable (f : Poly) {M : BitVec 64}

/-- The first four compressed coefficients of group `g`, as a doubleword. -/
abbrev W11a (g : Nat) : BitVec 64 :=
  0 + fld 11 0 (cmpV4 M (BitVec.ofNat 64 f[8 * g]!.val)) +
    fld 11 11 (cmpV4 M (BitVec.ofNat 64 f[8 * g + 1]!.val)) +
    fld 11 22 (cmpV4 M (BitVec.ofNat 64 f[8 * g + 2]!.val)) +
    fld 11 33 (cmpV4 M (BitVec.ofNat 64 f[8 * g + 3]!.val))

/-- What is left of them, and the last four, as a doubleword. -/
abbrev W11b (g : Nat) : BitVec 64 :=
  W11a f (M := M) g >>> 40 + (0 + fld 11 4 (cmpV4 M (BitVec.ofNat 64 f[8 * g + 4]!.val)) +
    fld 11 15 (cmpV4 M (BitVec.ofNat 64 f[8 * g + 5]!.val)) +
    fld 11 26 (cmpV4 M (BitVec.ofNat 64 f[8 * g + 6]!.val)) +
    fld 11 37 (cmpV4 M (BitVec.ofNat 64 f[8 * g + 7]!.val)))

theorem w11a_toNat (hM : M.toNat = compressMul1024 11) (g : Nat) :
    (W11a f (M := M) g).toNat = compress 11 f[8 * g]! + 2048 * compress 11 f[8 * g + 1]! +
      4194304 * compress 11 f[8 * g + 2]! + 8589934592 * compress 11 f[8 * g + 3]! := by
  have e : ∀ {p : Nat}, p + 11 ≤ 64 → ∀ v : Zq, (fld 11 p (cmpV4 M (BitVec.ofNat 64 v.val))).toNat =
      compress 11 v * 2 ^ p := fun hp v => fld_cmp4 (by decide) hM v hp
  have h0 := e (p := 0) (by decide) f[8 * g]!
  have h1 := e (p := 11) (by decide) f[8 * g + 1]!
  have h2 := e (p := 22) (by decide) f[8 * g + 2]!
  have h3 := e (p := 33) (by decide) f[8 * g + 3]!
  have b0 := compress_lt 11 f[8 * g]!
  have b1 := compress_lt 11 f[8 * g + 1]!
  have b2 := compress_lt 11 f[8 * g + 2]!
  have b3 := compress_lt 11 f[8 * g + 3]!
  simp only [Nat.reducePow] at b0 b1 b2 b3
  rw [toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq (a := 0) (A := 0) rfl h0
    (by simp only [Nat.pow_zero]; omega_arith)) h1 (by simp only [Nat.reducePow]; omega_arith))
    h2 (by simp only [Nat.reducePow]; omega_arith)) h3 (by simp only [Nat.reducePow]; omega_arith)]
  simp only [Nat.reducePow, Nat.mul_one, Nat.zero_add]
  omega_arith

theorem w11b_toNat (hM : M.toNat = compressMul1024 11) (g : Nat) :
    (W11b f (M := M) g).toNat =
      (compress 11 f[8 * g]! + 2048 * compress 11 f[8 * g + 1]! +
        4194304 * compress 11 f[8 * g + 2]! + 8589934592 * compress 11 f[8 * g + 3]!) / 1099511627776 +
      16 * compress 11 f[8 * g + 4]! + 32768 * compress 11 f[8 * g + 5]! +
      67108864 * compress 11 f[8 * g + 6]! + 137438953472 * compress 11 f[8 * g + 7]! := by
  have e : ∀ {p : Nat}, p + 11 ≤ 64 → ∀ v : Zq, (fld 11 p (cmpV4 M (BitVec.ofNat 64 v.val))).toNat =
      compress 11 v * 2 ^ p := fun hp v => fld_cmp4 (by decide) hM v hp
  have h4 := e (p := 4) (by decide) f[8 * g + 4]!
  have h5 := e (p := 15) (by decide) f[8 * g + 5]!
  have h6 := e (p := 26) (by decide) f[8 * g + 6]!
  have h7 := e (p := 37) (by decide) f[8 * g + 7]!
  have b4 := compress_lt 11 f[8 * g + 4]!
  have b5 := compress_lt 11 f[8 * g + 5]!
  have b6 := compress_lt 11 f[8 * g + 6]!
  have b7 := compress_lt 11 f[8 * g + 7]!
  simp only [Nat.reducePow] at b4 b5 b6 b7
  have ha := w11a_toNat f hM g
  have hs : (W11a f (M := M) g >>> 40).toNat =
      (compress 11 f[8 * g]! + 2048 * compress 11 f[8 * g + 1]! +
        4194304 * compress 11 f[8 * g + 2]! + 8589934592 * compress 11 f[8 * g + 3]!) /
          1099511627776 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ha]
  have hb0 := compress_lt 11 f[8 * g]!
  have hb1 := compress_lt 11 f[8 * g + 1]!
  have hb2 := compress_lt 11 f[8 * g + 2]!
  have hb3 := compress_lt 11 f[8 * g + 3]!
  simp only [Nat.reducePow] at hb0 hb1 hb2 hb3
  have hlt : (compress 11 f[8 * g]! + 2048 * compress 11 f[8 * g + 1]! +
      4194304 * compress 11 f[8 * g + 2]! + 8589934592 * compress 11 f[8 * g + 3]!) /
        1099511627776 < 16 := by omega_arith
  rw [toNat_add_eq hs (toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq (a := 0) (A := 0) rfl
    h4 (by simp only [Nat.reducePow]; omega_arith)) h5 (by simp only [Nat.reducePow]; omega_arith))
    h6 (by simp only [Nat.reducePow]; omega_arith)) h7 (by simp only [Nat.reducePow]; omega_arith))
    (by simp only [Nat.reducePow]; omega_arith)]
  simp only [Nat.reducePow, Nat.zero_add]
  omega_arith

theorem byte11a (hM : M.toNat = compressMul1024 11) {g : Nat} (hg : g < 32) :
    (W11a f (M := M) g).setWidth 8 = (compressEncode 11 f)[11 * g]! ∧
    (W11a f (M := M) g >>> 8).setWidth 8 = (compressEncode 11 f)[11 * g + 1]! ∧
    (W11a f (M := M) g >>> 16).setWidth 8 = (compressEncode 11 f)[11 * g + 2]! ∧
    (W11a f (M := M) g >>> 24).setWidth 8 = (compressEncode 11 f)[11 * g + 3]! ∧
    (W11a f (M := M) g >>> 32).setWidth 8 = (compressEncode 11 f)[11 * g + 4]! := by
  have e := w11a_toNat f hM g
  have b4 := compress_lt 11 f[8 * g + 4]!
  have b5 := compress_lt 11 f[8 * g + 5]!
  have b6 := compress_lt 11 f[8 * g + 6]!
  have b7 := compress_lt 11 f[8 * g + 7]!
  simp only [Nat.reducePow] at b4 b5 b6 b7
  have g0 := compressEncode11_group f hg (j := 0) (by decide)
  have g1 := compressEncode11_group f hg (j := 1) (by decide)
  have g2 := compressEncode11_group f hg (j := 2) (by decide)
  have g3 := compressEncode11_group f hg (j := 3) (by decide)
  have g4 := compressEncode11_group f hg (j := 4) (by decide)
  simp only [Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul] at g0 g1 g2 g3 g4
  rw [g0, g1, g2, g3, g4]
  generalize W11a f (M := M) g = V at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat] <;>
    (try rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]) <;> rw [e] <;>
    simp only [Nat.reducePow] <;> omega_arith

end

section
variable (f : Poly) {M : BitVec 64}

theorem byte11b (hM : M.toNat = compressMul1024 11) {g : Nat} (hg : g < 32) :
    (W11b f (M := M) g).setWidth 8 = (compressEncode 11 f)[11 * g + 5]! ∧
    (W11b f (M := M) g >>> 8).setWidth 8 = (compressEncode 11 f)[11 * g + 6]! ∧
    (W11b f (M := M) g >>> 16).setWidth 8 = (compressEncode 11 f)[11 * g + 7]! ∧
    (W11b f (M := M) g >>> 24).setWidth 8 = (compressEncode 11 f)[11 * g + 8]! ∧
    (W11b f (M := M) g >>> 32).setWidth 8 = (compressEncode 11 f)[11 * g + 9]! ∧
    (W11b f (M := M) g >>> 40).setWidth 8 = (compressEncode 11 f)[11 * g + 10]! := by
  have e := w11b_toNat f hM g
  have b0 := compress_lt 11 f[8 * g]!
  have b1 := compress_lt 11 f[8 * g + 1]!
  have b2 := compress_lt 11 f[8 * g + 2]!
  have b3 := compress_lt 11 f[8 * g + 3]!
  have b4 := compress_lt 11 f[8 * g + 4]!
  have b5 := compress_lt 11 f[8 * g + 5]!
  have b6 := compress_lt 11 f[8 * g + 6]!
  have b7 := compress_lt 11 f[8 * g + 7]!
  simp only [Nat.reducePow] at b0 b1 b2 b3 b4 b5 b6 b7
  have g5 := compressEncode11_group f hg (j := 5) (by decide)
  have g6 := compressEncode11_group f hg (j := 6) (by decide)
  have g7 := compressEncode11_group f hg (j := 7) (by decide)
  have g8 := compressEncode11_group f hg (j := 8) (by decide)
  have g9 := compressEncode11_group f hg (j := 9) (by decide)
  have g10 := compressEncode11_group f hg (j := 10) (by decide)
  simp only [Nat.reduceMul] at g5 g6 g7 g8 g9 g10
  rw [g5, g6, g7, g8, g9, g10]
  generalize W11b f (M := M) g = V at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat] <;>
    (try rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]) <;> rw [e] <;>
    simp only [Nat.reducePow] <;> omega_arith

end

/-! ## The loops -/

section
variable (s₀ : State)

abbrev F : Addr := s₀.gpr .r3
abbrev O : Addr := s₀.gpr .r5
/-- `d`, the low word of `r4`. -/
abbrev dN : Nat := ((s₀.gpr .r4).setWidth 32).toNat
abbrev L : Nat := (s₀.gpr .r6).toNat
abbrev outR : Region := ⟨O s₀, L s₀⟩
abbrev P : Poly := polyAt s₀.mem (F s₀)
abbrev E : List Byte := compressEncode (dN s₀) (P s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (F s₀)]
  wr : s₀.wr = [outR s₀]
  disj : (polyRegion (F s₀)).Disjoint (outR s₀)
  fitF : (F s₀).toNat + 1024 ≤ 2 ^ 64
  fitO : (O s₀).toNat + L s₀ ≤ 2 ^ 64
  dw : dN s₀ ∈ Proof.MlKem1024.compressWidths
  len : L s₀ = 32 * dN s₀
  red : Reduced s₀.mem (F s₀)

/-- After `i` iterations of the loop that reads 32 bytes of coefficients and
writes `b` bytes each, `N` in all, with the multiplier `M`. -/
structure Inv (s₀ : State) (M : BitVec 64) (b N : Nat) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = F s₀ + BitVec.ofNat 64 (32 * i)
  r5 : s.gpr .r5 = O s₀ + BitVec.ofNat 64 (b * i)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (N - i)
  r9 : s.gpr .r9 = M
  r10 : s.gpr .r10 = 261888
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [outR s₀] s₀.mem s.mem
  bytes : ∀ k < L s₀, s.mem (O s₀ + BitVec.ofNat 64 k) =
    if k < b * i then (E s₀)[k]! else s₀.mem (O s₀ + BitVec.ofNat 64 k)

section
variable {s₀ : State} (hp : Pre s₀) {M : BitVec 64} {b N i : Nat} {s : State} (h : Inv s₀ M b N i s)
include hp h

/-- Coefficient `j`, as read in the loop: the input is never written. -/
theorem coef_rd {j : Nat} (hj : j < 256) :
    (s.mem.readW (coeffAddr (F s₀) j) 32).setWidth 64 = BitVec.ofNat 64 ((P s₀)[j]!).val := by
  have e := coeffAt_congr (bytes_frame h.frame (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.disj) (by decide)) (by rw [n_eq]; exact hj)
  have v := polyAt_val hp.red (i := j) (by rw [n_eq]; exact hj)
  rw [← coeffAt_eq, e]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_setWidth64, BitVec.toNat_ofNat, v,
    Nat.mod_eq_of_lt (by have := (coeffAt s₀.mem (F s₀) j).isLt; omega_arith)]

theorem in_rd {j : Nat} (hj : j < 256) : InRegions (s.rd ++ s.wr) (coeffAddr (F s₀) j) 4 := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, coeff_contains _ (by rw [n_eq]; exact hj)⟩

theorem out_wr {k : Nat} (hk : k < L s₀) : InRegions s.wr (O s₀ + BitVec.ofNat 64 k) 1 := by
  have := hp.fitO
  rw [h.wr, hp.wr]; exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

end

theorem out_frame {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [outR s₀] s₀.mem m) {k : Nat}
    (hk : k < L s₀) (v : Byte) :
    Frame [outR s₀] s₀.mem (m.writeW (O s₀ + BitVec.ofNat 64 k) v) := by
  have := hp.fitO
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))

/-- The counter of an iteration. -/
theorem count_step {N i : Nat} (hi : i < N) (hN : N < 2 ^ 64) {c : BitVec 64}
    (hc : c = BitVec.ofNat 64 (N - i)) :
    c - 1 = BitVec.ofNat 64 (N - (i + 1)) ∧ (c - 1 != 0) = decide (i + 1 ≠ N) := by
  subst hc
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
  exact ⟨rfl, count_nz hi hN⟩

theorem step5 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 5) {M : BitVec 64}
    (hM : M.toNat = compressMul1024 5) {i : Nat} (hi : i < 32) {s : State} (h : Inv s₀ M 5 32 i s) :
    WP isa (.block ce5Body) s fun s' =>
      Inv s₀ M 5 32 (i + 1) s' ∧ (s'.gpr .r11 != 0) = decide (i + 1 ≠ 32) := by
  have hL : L s₀ = 160 := by rw [hp.len, hd]
  have fO := hp.fitO
  have ek : ∀ j < 8, F s₀ + BitVec.ofNat 64 (32 * i) + BitVec.ofNat 64 (4 * j) =
      coeffAddr (F s₀) (8 * i + j) := fun j _ => by
    rw [ptr_add, show 32 * i + 4 * j = 4 * (8 * i + j) by omega_arith]
  have eo : ∀ k < 5, O s₀ + BitVec.ofNat 64 (5 * i) + BitVec.ofNat 64 k =
      O s₀ + BitVec.ofNat 64 (5 * i + k) := fun k _ => ptr_add _ _ _
  have a : ∀ j < 8, A s (F s₀ + BitVec.ofNat 64 (32 * i)) j =
      BitVec.ofNat 64 ((P s₀)[8 * i + j]!).val := fun j hj => by
    rw [A, ek j hj]; exact coef_rd hp h (by omega_arith)
  have a0 := a 0 (by decide)
  have a1 := a 1 (by decide)
  have a2 := a 2 (by decide)
  have a3 := a 3 (by decide)
  have a4 := a 4 (by decide)
  have a5 := a 5 (by decide)
  have a6 := a 6 (by decide)
  have a7 := a 7 (by decide)
  simp only [Nat.add_zero] at a0
  have x0 : O s₀ + BitVec.ofNat 64 (5 * i) = O s₀ + BitVec.ofNat 64 (5 * i + 0) := rfl
  refine WP.mono (body5_ok h.r3 h.r5 h.r11 h.r9 h.r10
    (fun j hj => by rw [ek j hj]; exact in_rd hp h (by omega_arith))
    (fun k hk => by rw [eo k hk]; exact out_wr hp h (by omega_arith)))
    fun s' ⟨r3, r5, r11, ⟨r9, r10, rd, wr, sp, lr, pres⟩, m⟩ => ?_
  obtain ⟨c1, c2⟩ := count_step (N := 32) hi (by decide) rfl
  obtain ⟨v0, v1, v2, v3, v4⟩ := byte5 (P s₀) hM hi
  refine ⟨⟨?_, ?_, r11.trans c1, r9.trans h.r9, r10.trans h.r10, rd.trans h.rd, wr.trans h.wr,
    sp.trans h.sp, lr.trans h.lr, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩,
    by rw [r11]; exact c2⟩
  · rw [r3]; exact ptr_succ _ 32 i
  · rw [r5]; exact ptr_succ _ 5 i
  · rw [m, eo 1 (by omega_arith), eo 2 (by omega_arith), eo 3 (by omega_arith), eo 4 (by omega_arith), x0]
    exact out_frame hp (out_frame hp (out_frame hp (out_frame hp (out_frame hp h.frame (by omega_arith) _)
      (by omega_arith) _) (by omega_arith) _) (by omega_arith) _) (by omega_arith) _
  · have e : V5 s (F s₀ + BitVec.ofNat 64 (32 * i)) M = W5 (P s₀) (M := M) i := by
      rw [V5, W5, a0, a1, a2, a3, a4, a5, a6, a7]
    rw [m, eo 1 (by omega_arith), eo 2 (by omega_arith), eo 3 (by omega_arith), eo 4 (by omega_arith), x0, e, v0, v1, v2, v3,
      v4, show 5 * (i + 1) = 5 * i + 4 + 1 by omega_arith]
    refine byte_one (by omega_arith) (by omega_arith) (byte_one (by omega_arith) (by omega_arith) (byte_one (by omega_arith)
      (by omega_arith) (byte_one (by omega_arith) (by omega_arith) (byte_one (by omega_arith) (by omega_arith) h.bytes ?_) ?_) ?_)
      ?_) ?_ <;> rw [E, hd]

theorem step11 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 11) {M : BitVec 64}
    (hM : M.toNat = compressMul1024 11) {i : Nat} (hi : i < 32) {s : State} (h : Inv s₀ M 11 32 i s) :
    WP isa (.block ce11Body) s fun s' =>
      Inv s₀ M 11 32 (i + 1) s' ∧ (s'.gpr .r11 != 0) = decide (i + 1 ≠ 32) := by
  have hL : L s₀ = 352 := by rw [hp.len, hd]
  have fO := hp.fitO
  have ek : ∀ j < 8, F s₀ + BitVec.ofNat 64 (32 * i) + BitVec.ofNat 64 (4 * j) =
      coeffAddr (F s₀) (8 * i + j) := fun j _ => by
    rw [ptr_add, show 32 * i + 4 * j = 4 * (8 * i + j) by omega_arith]
  have eo : ∀ k < 11, O s₀ + BitVec.ofNat 64 (11 * i) + BitVec.ofNat 64 k =
      O s₀ + BitVec.ofNat 64 (11 * i + k) := fun k _ => ptr_add _ _ _
  have a : ∀ j < 8, A s (F s₀ + BitVec.ofNat 64 (32 * i)) j =
      BitVec.ofNat 64 ((P s₀)[8 * i + j]!).val := fun j hj => by
    rw [A, ek j hj]; exact coef_rd hp h (by omega_arith)
  have a0 := a 0 (by decide)
  have a1 := a 1 (by decide)
  have a2 := a 2 (by decide)
  have a3 := a 3 (by decide)
  have a4 := a 4 (by decide)
  have a5 := a 5 (by decide)
  have a6 := a 6 (by decide)
  have a7 := a 7 (by decide)
  simp only [Nat.add_zero] at a0
  have x0 : O s₀ + BitVec.ofNat 64 (11 * i) = O s₀ + BitVec.ofNat 64 (11 * i + 0) := rfl
  refine WP.mono (body11_ok h.r3 h.r5 h.r11 h.r9 h.r10
    (fun j hj => by rw [ek j hj]; exact in_rd hp h (by omega_arith))
    (fun k hk => by rw [eo k hk]; exact out_wr hp h (by omega_arith)))
    fun s' ⟨r3, r5, r11, ⟨r9, r10, rd, wr, sp, lr, pres⟩, m⟩ => ?_
  obtain ⟨c1, c2⟩ := count_step (N := 32) hi (by decide) rfl
  obtain ⟨u0, u1, u2, u3, u4⟩ := byte11a (P s₀) hM hi
  obtain ⟨v5, v6, v7, v8, v9, v10⟩ := byte11b (P s₀) hM hi
  refine ⟨⟨?_, ?_, r11.trans c1, r9.trans h.r9, r10.trans h.r10, rd.trans h.rd, wr.trans h.wr,
    sp.trans h.sp, lr.trans h.lr, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩,
    by rw [r11]; exact c2⟩
  · rw [r3]; exact ptr_succ _ 32 i
  · rw [r5]; exact ptr_succ _ 11 i
  · rw [m, eo 1 (by omega_arith), eo 2 (by omega_arith), eo 3 (by omega_arith), eo 4 (by omega_arith), eo 5 (by omega_arith),
      eo 6 (by omega_arith), eo 7 (by omega_arith), eo 8 (by omega_arith), eo 9 (by omega_arith), eo 10 (by omega_arith), x0]
    exact out_frame hp (out_frame hp (out_frame hp (out_frame hp (out_frame hp (out_frame hp
      (out_frame hp (out_frame hp (out_frame hp (out_frame hp (out_frame hp h.frame (by omega_arith) _)
      (by omega_arith) _) (by omega_arith) _) (by omega_arith) _) (by omega_arith) _) (by omega_arith) _) (by omega_arith) _)
      (by omega_arith) _) (by omega_arith) _) (by omega_arith) _) (by omega_arith) _
  · have ea : V11a s (F s₀ + BitVec.ofNat 64 (32 * i)) M = W11a (P s₀) (M := M) i := by
      rw [V11a, W11a, a0, a1, a2, a3]
    have eb : V11b s (F s₀ + BitVec.ofNat 64 (32 * i)) M = W11b (P s₀) (M := M) i := by
      rw [V11b, W11b, ea, a4, a5, a6, a7]
    rw [m, eo 1 (by omega_arith), eo 2 (by omega_arith), eo 3 (by omega_arith), eo 4 (by omega_arith), eo 5 (by omega_arith),
      eo 6 (by omega_arith), eo 7 (by omega_arith), eo 8 (by omega_arith), eo 9 (by omega_arith), eo 10 (by omega_arith), x0,
      ea, eb, u0, u1, u2, u3, u4, v5, v6, v7, v8, v9, v10,
      show 11 * (i + 1) = 11 * i + 10 + 1 by omega_arith]
    refine byte_one (by omega_arith) (by omega_arith) (byte_one (by omega_arith) (by omega_arith) (byte_one (by omega_arith)
      (by omega_arith) (byte_one (by omega_arith) (by omega_arith) (byte_one (by omega_arith) (by omega_arith) (byte_one
      (by omega_arith) (by omega_arith) (byte_one (by omega_arith) (by omega_arith) (byte_one (by omega_arith) (by omega_arith)
      (byte_one (by omega_arith) (by omega_arith) (byte_one (by omega_arith) (by omega_arith) (byte_one (by omega_arith)
      (by omega_arith) h.bytes ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_ <;> rw [E, hd]

/-! ## The branches -/

/-- What the loops end with. -/
def Fin (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
    ∀ k < L s₀, s.mem (O s₀ + BitVec.ofNat 64 k) = (E s₀)[k]!

/-- What a branch starts from. -/
def Start (s₀ s : State) : Prop :=
  s.gpr .r3 = F s₀ ∧ s.gpr .r5 = O s₀ ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
    (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem

theorem loop_fin {s₀ : State} {M : BitVec 64} {b N : Nat} (hbN : b * N = L s₀) {s : State}
    (h : Inv s₀ M b N N s) : Fin s₀ s :=
  ⟨h.pres, h.sp, h.lr, fun k hk => by rw [h.bytes k hk, ite_eq_left (by omega_arith)]⟩

theorem inv_zero {s₀ : State} {M : BitVec 64} {b N : Nat} {s : State} (h : Start s₀ s)
    (h9 : s.gpr .r9 = M) (h10 : s.gpr .r10 = 261888) (h11 : s.gpr .r11 = BitVec.ofNat 64 N) :
    Inv s₀ M b N 0 s := by
  obtain ⟨r3, r5, rd, wr, sp, lr, pres, m⟩ := h
  refine ⟨by simp [r3], by simp [r5], by simp [h11], h9, h10, rd, wr, sp, lr, pres,
    by rw [m]; exact Frame.refl _ _, fun k _ => by rw [m, ite_eq_right (by omega_arith)]⟩

theorem setup_li4 {s : State} {m n : Nat} (hm : m < 2 ^ 15) (hn : n < 2 ^ 15) :
    WP isa (.block (biasConst1024 ++ ([.li .r9 m, .li .r11 n] : List Instr))) s fun s' =>
      s'.gpr .r9 = BitVec.ofNat 64 m ∧ s'.gpr .r10 = 261888 ∧ s'.gpr .r11 = BitVec.ofNat 64 n ∧
        s'.gpr .r3 = s.gpr .r3 ∧ s'.gpr .r5 = s.gpr .r5 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp ∧ s'.lr = s.lr ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  crunr [biasConst1024, hm, hn, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    List.cons_append, List.nil_append]
  decide

theorem setup_11 {s : State} :
    WP isa (.block (biasConst1024 ++
      ([.lis .r9 0x4, .ori .r9 .r9 0xEBEE, .li .r11 32] : List Instr))) s fun s' =>
      s'.gpr .r9 = 322542 ∧ s'.gpr .r10 = 261888 ∧ s'.gpr .r11 = BitVec.ofNat 64 32 ∧
        s'.gpr .r3 = s.gpr .r3 ∧ s'.gpr .r5 = s.gpr .r5 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp ∧ s'.lr = s.lr ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  crunr [biasConst1024, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    List.cons_append, List.nil_append]
  decide

theorem branch5 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 5) {s : State} (h : Start s₀ s) :
    WP isa (.seq (.block (biasConst1024 ++ ([.li .r9 5040, .li .r11 32] : List Instr)))
      (.loop (.block ce5Body) (.nonzero .d .r11))) s (Fin s₀) := by
  refine WP.seq (WP.mono (setup_li4 (by decide) (by decide))
    fun s₁ ⟨r9, r10, r11, r3, r5, rd, wr, sp, lr, pres, m⟩ => ?_)
  obtain ⟨h3, h5, hrd, hwr, hsp, hlr, hpres, hm⟩ := h
  refine wp_loop_nz (Inv s₀ (BitVec.ofNat 64 5040) 5 32) (N := 32) (by decide)
    (fun i hi s h => step5 hp hd (by decide) hi h) (fun s h => loop_fin (by rw [hp.len, hd]) h)
    (inv_zero ⟨r3.trans h3, r5.trans h5, rd.trans hrd, wr.trans hwr, sp.trans hsp, lr.trans hlr,
      fun r hr => (pres r hr).trans (hpres r hr), m.trans hm⟩ r9 r10 r11)

theorem branch11 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 11) {s : State} (h : Start s₀ s) :
    WP isa (.seq (.block (biasConst1024 ++
      ([.lis .r9 0x4, .ori .r9 .r9 0xEBEE, .li .r11 32] : List Instr)))
      (.loop (.block ce11Body) (.nonzero .d .r11))) s (Fin s₀) := by
  refine WP.seq (WP.mono setup_11 fun s₁ ⟨r9, r10, r11, r3, r5, rd, wr, sp, lr, pres, m⟩ => ?_)
  obtain ⟨h3, h5, hrd, hwr, hsp, hlr, hpres, hm⟩ := h
  refine wp_loop_nz (Inv s₀ 322542 11 32) (N := 32) (by decide)
    (fun i hi s h => step11 hp hd (by decide) hi h) (fun s h => loop_fin (by rw [hp.len, hd]) h)
    (inv_zero ⟨r3.trans h3, r5.trans h5, rd.trans hrd, wr.trans hwr, sp.trans hsp, lr.trans hlr,
      fun r hr => (pres r hr).trans (hpres r hr), m.trans hm⟩ r9 r10 r11)

/-- `r4` zero-extended. -/
abbrev Z (s₀ : State) : BitVec 64 := (((s₀.gpr .r4).setWidth 32).rotateRight 0).setWidth 64

theorem sel_eval {s₀ s : State} {k : Nat} (hk : k < 2 ^ 15)
    (h : s.gpr .r7 = Z s₀ - BitVec.ofNat 64 k) :
    isa.eval (.zero .w .r7) s = some (decide (dN s₀ = k)) := by
  have r0 : ∀ v : BitVec 32, v.rotateRight 0 = v := fun v => by
    simp [BitVec.rotateRight, BitVec.rotateRightAux]
  show VG.PPC64LE.eval (.zero .w .r7) s = _
  simp only [VG.PPC64LE.eval, State.read, Size.bits, h]
  rw [dsel _ hk, r0]

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa compressEncode1024 s₀ (Fin s₀) := by
  refine WP.seq (WP.cons (exec_rotr_w (by decide)) (wp_nil ?_))
  refine WP.seq (WP.cons (exec_subi (by decide) (by decide)) (wp_nil ?_))
  have st : ∀ {s : State}, Start s₀ s → ∀ v, Start s₀ (s.write .r7 v) :=
    fun ⟨r3, r5, rd, wr, sp, lr, pres, m⟩ v =>
    ⟨by simp [State.write, r3], by simp [State.write, r5], rd, wr, sp, lr, fun r hr => by
      have : r ≠ .r7 := by revert r hr; decide
      simp [State.write, this, pres r hr], m⟩
  have s0 : Start s₀ (s₀.write .r4 (Z s₀)) :=
    ⟨by simp [State.write], by simp [State.write], rfl, rfl, rfl, rfl, fun r hr => by
      have : r ≠ .r4 := by revert r hr; decide
      simp [State.write, this], rfl⟩
  rcases mem_compressWidths1024 hp.dw with hd | hd
  · refine WP.ite true (by rw [sel_eval (s₀ := s₀) (k := 5) (by decide) (by simp [State.write]), hd]; rfl)
      (fun _ => branch5 hp hd (st s0 _)) (fun h => absurd h (by decide))
  · refine WP.ite false (by rw [sel_eval (s₀ := s₀) (k := 5) (by decide) (by simp [State.write]), hd]; rfl)
      (fun h => absurd h (by decide)) (fun _ => branch11 hp hd (st s0 _))

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlKem1024.compressEncodeContract PPC64LE.abi).pre s) :
    Pre s := by
  sig_pre [Proof.MlKem1024.compressEncodeContract, Proof.MlKem1024.compressEncodeSig, PPC64LE.abi,
    PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 5 | .r5 => 0x2000 | .r6 => 160 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 160⟩]

theorem verified : Verified PPC64LE.target compressEncode1024
    (Proof.MlKem1024.compressEncodeContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, RelCT.constantTime (Q := fun _ _ => True) ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hlr⟩, ?_⟩
    sig_post [Proof.MlKem1024.compressEncodeContract, Proof.MlKem1024.compressEncodeSig, PPC64LE.abi,
      PPC64LE.argRegs]
    exact bytesAt_eq! (compressEncode_length _ _ ▸ (pre_of hs).len.symm) h
  · refine RelCT.seq (VG.Proof.MlKem.PPC64LE.CompressEncode.zext_rel.mono
      (fun s₁ s₂ ⟨_, _, hp⟩ => ?_) fun _ _ h => h)
      (RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
        (fun _ _ ⟨hsp, hr⟩ => ⟨hsp, fun r h => hr r (Taint.mem_ofRegs.mp h)⟩) (by taint_decide))
    sig_pub [Proof.MlKem1024.compressEncodeContract, Proof.MlKem1024.compressEncodeSig, PPC64LE.abi,
      PPC64LE.argRegs] at hp
    obtain ⟨hsp, h3, h4, h5, h6⟩ := hp
    refine ⟨hsp, fun r hr => ?_, h4⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h3
    · exact h5
    · exact h6
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem1024.compressEncodeContract, Proof.MlKem1024.compressEncodeSig,
        PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact Add.reduced_zero _
        | decide +kernel

end VG.Proof.MlKem1024.PPC64LE.CompressEncode
