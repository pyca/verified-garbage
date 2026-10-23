module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Compress
public import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
import VerifiedGarbage.Proof.MlKem.PPC64LE.Reduce
import VerifiedGarbage.Proof.MlKem.PPC64LE.Bytes
public import VerifiedGarbage.Proof.MlKem.Encode
public import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.MlKem.PPC64LE.Compress
meta import VerifiedGarbage.Spec.MlKem.Poly
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
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

/-!
# ML-KEM on PPC64LE: `vg_mlkem_compress_encode`

A loop for each width `d`, over the output, each iteration a group of
coefficients whose fields are added into `r8` and stored a byte at a time.
The body is symbolically executed once for any pointers (`body1_ok`,
`body4_ok`, `body10_ok`). The values are `compress_eq`, with the product in
64 bits (`cmpV_toNat`), and the bytes `compressEncode1`, `compressEncode4`
and `compressEncode10_0`–`_4`.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.CompressEncode

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## The values -/

/-- `(x · M + 2¹⁸ - 64) >> 19`, as `compressAt` computes it. -/
def cmpV (M x : BitVec 64) : BitVec 64 := (x * M + 262080) >>> 19

theorem bias_val : ((0x3 : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 ||| (0xFFC0 : BitVec 16).setWidth 64 =
    262080 := by decide

theorem m10_val : ((0x2 : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 ||| (0x75F7 : BitVec 16).setWidth 64 =
    161271 := by decide

theorem cmpV_toNat {d : Nat} (hd : d ∈ compressWidths) {M : BitVec 64} (hM : M.toNat = compressMul d)
    (x : Zq) : (cmpV M (BitVec.ofNat 64 x.val)).toNat = (x.val * compressMul d + compressAdd) / 2 ^ 19 := by
  have hx := val_lt x
  have ha := compress_arg_lt hd x
  have hp : (BitVec.ofNat 64 x.val * M).toNat = x.val * compressMul d := by
    rw [BitVec.toNat_mul, toNat_val64, hM]
    exact Nat.mod_eq_of_lt (by unfold compressAdd at ha; omega)
  unfold compressAdd at ha ⊢
  unfold cmpV
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, hp]
  refine congrArg (· / 2 ^ 19) ?_
  rw [show (262080 : BitVec 64).toNat = 262080 from rfl]
  omega

/-- A field of `c`: its low `w` bits, at bit `p` (`p + w ≤ 64`). -/
theorem field_toNat (c : BitVec 64) {w p : Nat} (hp : p + w ≤ 64) :
    ((c <<< (64 - w)) >>> (64 - w - p)).toNat = c.toNat % 2 ^ w * 2 ^ p := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have e1 : (2 : Nat) ^ 64 = 2 ^ w * 2 ^ (64 - w) := by rw [← Nat.pow_add]; congr 1; omega
  have e2 : (2 : Nat) ^ (64 - w) = 2 ^ (64 - w - p) * 2 ^ p := by rw [← Nat.pow_add]; congr 1; omega
  rw [e1, Nat.mul_mod_mul_right, e2, ← Nat.mul_assoc, Nat.mul_right_comm, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- The `w`-bit field of `c` at bit `p`, as a pair of shifts computes it. -/
def fld (w p : Nat) (c : BitVec 64) : BitVec 64 := (c <<< (64 - w)) >>> (64 - w - p)

/-! ## The loop bodies -/

section
variable {s : State} {x y c M : BitVec 64}

/-- Word `j` from `x`, zero-extended. -/
abbrev A (s : State) (x : BitVec 64) (j : Nat) : BitVec 64 := (s.mem.readW (x + BitVec.ofNat 64 (4 * j)) 32).setWidth 64

/-- What every iteration keeps. -/
def Keep (s s' : State) : Prop :=
  s'.gpr .r9 = s.gpr .r9 ∧ s'.gpr .r10 = s.gpr .r10 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
    s'.lr = s.lr ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r

theorem body1_ok (h3 : s.gpr .r3 = x) (h5 : s.gpr .r5 = y) (h11 : s.gpr .r11 = c) (h9 : s.gpr .r9 = M)
    (h10 : s.gpr .r10 = 262080)
    (ia : ∀ j < 8, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (4 * j)) 4)
    (ob : InRegions s.wr y 1) :
    WP isa (.block ce1Body) s fun s' =>
      s'.gpr .r3 = x + 32 ∧ s'.gpr .r5 = y + 1 ∧ s'.gpr .r11 = c - 1 ∧ Keep s s' ∧
      s'.mem = s.mem.writeW y ((0 + fld 1 0 (cmpV M (A s x 0)) + fld 1 1 (cmpV M (A s x 1)) +
        fld 1 2 (cmpV M (A s x 2)) + fld 1 3 (cmpV M (A s x 3)) + fld 1 4 (cmpV M (A s x 4)) +
        fld 1 5 (cmpV M (A s x 5)) + fld 1 6 (cmpV M (A s x 6)) + fld 1 7 (cmpV M (A s x 7))).setWidth 8) := by
  have i0 := ia 0 (by decide)
  have i1 := ia 1 (by decide)
  have i2 := ia 2 (by decide)
  have i3 := ia 3 (by decide)
  have i4 := ia 4 (by decide)
  have i5 := ia 5 (by decide)
  have i6 := ia 6 (by decide)
  have i7 := ia 7 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at i0 i1 i2 i3 i4 i5 i6 i7
  crun [ce1Body, ce1Bit, compressAt, Keep, A, fld, cmpV, h3, h5, h11, h9, h10, i0, i1, i2, i3, i4, i5, i6, i7,
    ob, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append,
    List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [Mem.writeW, Mem.readW, Mem.read]

theorem body4_ok (h3 : s.gpr .r3 = x) (h5 : s.gpr .r5 = y) (h11 : s.gpr .r11 = c) (h9 : s.gpr .r9 = M)
    (h10 : s.gpr .r10 = 262080)
    (ia : ∀ j < 2, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (4 * j)) 4)
    (ob : InRegions s.wr y 1) :
    WP isa (.block ce4Body) s fun s' =>
      s'.gpr .r3 = x + 8 ∧ s'.gpr .r5 = y + 1 ∧ s'.gpr .r11 = c - 1 ∧ Keep s s' ∧
      s'.mem = s.mem.writeW y ((fld 4 0 (cmpV M (A s x 0)) + fld 4 4 (cmpV M (A s x 1))).setWidth 8) := by
  have i0 := ia 0 (by decide)
  have i1 := ia 1 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at i0 i1
  crun [ce4Body, compressAt, Keep, A, fld, cmpV, h3, h5, h11, h9, h10, i0, i1, ob, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

/-- The four fields of a group of `ByteEncode₁₀(Compress₁₀)`, in one doubleword. -/
abbrev V10 (s : State) (x M : BitVec 64) : BitVec 64 :=
  0 + fld 10 0 (cmpV M (A s x 0)) + fld 10 10 (cmpV M (A s x 1)) + fld 10 20 (cmpV M (A s x 2)) +
    fld 10 30 (cmpV M (A s x 3))

theorem body10_ok (h3 : s.gpr .r3 = x) (h5 : s.gpr .r5 = y) (h11 : s.gpr .r11 = c) (h9 : s.gpr .r9 = M)
    (h10 : s.gpr .r10 = 262080)
    (ia : ∀ j < 4, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (4 * j)) 4)
    (ob : ∀ k < 5, InRegions s.wr (y + BitVec.ofNat 64 k) 1) :
    WP isa (.block ce10Body) s fun s' =>
      s'.gpr .r3 = x + 16 ∧ s'.gpr .r5 = y + 5 ∧ s'.gpr .r11 = c - 1 ∧ Keep s s' ∧
      s'.mem = ((((s.mem.writeW y ((V10 s x M).setWidth 8)).writeW (y + BitVec.ofNat 64 1)
        ((V10 s x M >>> 8).setWidth 8)).writeW (y + BitVec.ofNat 64 2) ((V10 s x M >>> 16).setWidth 8)).writeW
        (y + BitVec.ofNat 64 3) ((V10 s x M >>> 24).setWidth 8)).writeW (y + BitVec.ofNat 64 4)
        ((V10 s x M >>> 32).setWidth 8) := by
  have i0 := ia 0 (by decide)
  have i1 := ia 1 (by decide)
  have i2 := ia 2 (by decide)
  have i3 := ia 3 (by decide)
  have o0 := ob 0 (by decide)
  have o1 := ob 1 (by decide)
  have o2 := ob 2 (by decide)
  have o3 := ob 3 (by decide)
  have o4 := ob 4 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at i0 i1 i2 i3 o0
  crun [ce10Body, ce10Coeff, compressAt, Keep, V10, A, fld, cmpV, h3, h5, h11, h9, h10, i0, i1, i2, i3,
    o0, o1, o2, o3, o4, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append,
    List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The bytes -/

theorem fld_cmp {d : Nat} (hd : d ∈ compressWidths) {M : BitVec 64} (hM : M.toNat = compressMul d) (v : Zq)
    {p : Nat} (hp : p + d ≤ 64) : (fld d p (cmpV M (BitVec.ofNat 64 v.val))).toNat = compress d v * 2 ^ p := by
  unfold fld
  rw [field_toNat _ hp, cmpV_toNat hd hM, compress_eq hd]

/-- A sum of doublewords that does not wrap around. -/
theorem toNat_add_eq {a b : BitVec 64} {A B : Nat} (ha : a.toNat = A) (hb : b.toNat = B) (h : A + B < 2 ^ 64) :
    (a + b).toNat = A + B := by
  rw [BitVec.toNat_add, ha, hb, Nat.mod_eq_of_lt h]

section
variable (f : Poly) {M : BitVec 64}

theorem byte1 (hM : M.toNat = compressMul 1) {k : Nat} (hk : k < 32) :
    (0 + fld 1 0 (cmpV M (BitVec.ofNat 64 f[8 * k]!.val)) + fld 1 1 (cmpV M (BitVec.ofNat 64 f[8 * k + 1]!.val)) +
      fld 1 2 (cmpV M (BitVec.ofNat 64 f[8 * k + 2]!.val)) + fld 1 3 (cmpV M (BitVec.ofNat 64 f[8 * k + 3]!.val)) +
      fld 1 4 (cmpV M (BitVec.ofNat 64 f[8 * k + 4]!.val)) + fld 1 5 (cmpV M (BitVec.ofNat 64 f[8 * k + 5]!.val)) +
      fld 1 6 (cmpV M (BitVec.ofNat 64 f[8 * k + 6]!.val)) +
      fld 1 7 (cmpV M (BitVec.ofNat 64 f[8 * k + 7]!.val))).setWidth 8 = (compressEncode 1 f)[k]! := by
  rw [compressEncode1 f hk]
  have b0 := compress_lt 1 f[8 * k]!
  have b1 := compress_lt 1 f[8 * k + 1]!
  have b2 := compress_lt 1 f[8 * k + 2]!
  have b3 := compress_lt 1 f[8 * k + 3]!
  have b4 := compress_lt 1 f[8 * k + 4]!
  have b5 := compress_lt 1 f[8 * k + 5]!
  have b6 := compress_lt 1 f[8 * k + 6]!
  have b7 := compress_lt 1 f[8 * k + 7]!
  simp only [Nat.pow_one] at b0 b1 b2 b3 b4 b5 b6 b7
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, (toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq (a := 0) (A := 0) rfl (fld_cmp (d := 1) (by decide) hM _ (p := 0) (by decide)) (by omega)) (fld_cmp (d := 1) (by decide) hM _ (p := 1) (by decide)) (by omega)) (fld_cmp (d := 1) (by decide) hM _ (p := 2) (by decide)) (by omega)) (fld_cmp (d := 1) (by decide) hM _ (p := 3) (by decide)) (by omega)) (fld_cmp (d := 1) (by decide) hM _ (p := 4) (by decide)) (by omega)) (fld_cmp (d := 1) (by decide) hM _ (p := 5) (by decide)) (by omega)) (fld_cmp (d := 1) (by decide) hM _ (p := 6) (by decide)) (by omega)) (fld_cmp (d := 1) (by decide) hM _ (p := 7) (by decide)) (by omega)), BitVec.toNat_ofNat]
  omega

theorem byte4 (hM : M.toNat = compressMul 4) {k : Nat} (hk : k < 128) :
    (fld 4 0 (cmpV M (BitVec.ofNat 64 f[2 * k]!.val)) +
      fld 4 4 (cmpV M (BitVec.ofNat 64 f[2 * k + 1]!.val))).setWidth 8 = (compressEncode 4 f)[k]! := by
  rw [compressEncode4 f hk]
  have b0 := compress_lt 4 f[2 * k]!
  have b1 := compress_lt 4 f[2 * k + 1]!
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, toNat_add_eq (fld_cmp (d := 4) (by decide) hM _ (p := 0) (by decide))
    (fld_cmp (d := 4) (by decide) hM _ (p := 4) (by decide)) (by omega), BitVec.toNat_ofNat]
  omega

/-- The four compressed coefficients of group `g`, as a doubleword. -/
abbrev W10 (g : Nat) : BitVec 64 :=
  0 + fld 10 0 (cmpV M (BitVec.ofNat 64 f[4 * g]!.val)) + fld 10 10 (cmpV M (BitVec.ofNat 64 f[4 * g + 1]!.val)) +
    fld 10 20 (cmpV M (BitVec.ofNat 64 f[4 * g + 2]!.val)) + fld 10 30 (cmpV M (BitVec.ofNat 64 f[4 * g + 3]!.val))

theorem byte10 (hM : M.toNat = compressMul 10) {g : Nat} (hg : g < 64) :
    (W10 f (M := M) g).setWidth 8 = (compressEncode 10 f)[5 * g]! ∧
    (W10 f (M := M) g >>> 8).setWidth 8 = (compressEncode 10 f)[5 * g + 1]! ∧
    (W10 f (M := M) g >>> 16).setWidth 8 = (compressEncode 10 f)[5 * g + 2]! ∧
    (W10 f (M := M) g >>> 24).setWidth 8 = (compressEncode 10 f)[5 * g + 3]! ∧
    (W10 f (M := M) g >>> 32).setWidth 8 = (compressEncode 10 f)[5 * g + 4]! := by
  have b0 := compress_lt 10 f[4 * g]!
  have b1 := compress_lt 10 f[4 * g + 1]!
  have b2 := compress_lt 10 f[4 * g + 2]!
  have b3 := compress_lt 10 f[4 * g + 3]!
  have e : (W10 f (M := M) g).toNat = 0 + compress 10 f[4 * g]! * 2 ^ 0 + compress 10 f[4 * g + 1]! * 2 ^ 10 +
      compress 10 f[4 * g + 2]! * 2 ^ 20 + compress 10 f[4 * g + 3]! * 2 ^ 30 := (toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq (a := 0) (A := 0) rfl (fld_cmp (d := 10) (by decide) hM _ (p := 0) (by decide)) (by omega)) (fld_cmp (d := 10) (by decide) hM _ (p := 10) (by decide)) (by omega)) (fld_cmp (d := 10) (by decide) hM _ (p := 20) (by decide)) (by omega)) (fld_cmp (d := 10) (by decide) hM _ (p := 30) (by decide)) (by omega))
  rw [compressEncode10_0 f hg, compressEncode10_1 f hg, compressEncode10_2 f hg, compressEncode10_3 f hg,
    compressEncode10_4 f hg]
  simp only [Nat.reducePow, Nat.mul_one, Nat.zero_add] at e
  generalize compress 10 f[4 * g]! = c0 at *
  generalize compress 10 f[4 * g + 1]! = c1 at *
  generalize compress 10 f[4 * g + 2]! = c2 at *
  generalize compress 10 f[4 * g + 3]! = c3 at *
  generalize W10 f (M := M) g = V at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat] <;>
    (try rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]) <;> rw [e] <;> omega

end

end VG.Proof.MlKem.PPC64LE.CompressEncode
