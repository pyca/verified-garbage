module

public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.MlKem.RISCV64.Compress
public import VerifiedGarbage.Proof.MlKem.PolyContract
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
import VerifiedGarbage.Proof.MlKem.RISCV64.Reduce
import VerifiedGarbage.Proof.MlKem.RISCV64.Bytes
public import VerifiedGarbage.Proof.MlKem.Encode
public import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.MlKem.RISCV64.Compress
meta import VerifiedGarbage.Proof.MlKem.PolyContract
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Reduce
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Bytes
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Arith
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# ML-KEM on RISC-V: `vg_mlkem_compress_encode`

A loop for each width `d`, over the output, each iteration a group of
coefficients whose fields are added into `a5` and stored a byte at a time,
as on PPC64LE (`Proof/MlKem/PPC64LE/CompressEncode.lean`).
The body is symbolically executed once for any pointers (`body1_ok`,
`body4_ok`, `body10_ok`). The values are `compress_eq`, with the product in
64 bits (`cmpV_toNat`), and the bytes `compressEncode1`, `compressEncode4`
and `compressEncode10_0`–`_4`.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.CompressEncode

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## The values -/

/-- `(x · M + 2¹⁸ - 64) >> 19`, as `compressAt` computes it. -/
def cmpV (M x : BitVec 64) : BitVec 64 := (x * M + 262080) >>> 19

theorem cmpV_toNat {d : Nat} (hd : d ∈ compressWidths) {M : BitVec 64} (hM : M.toNat = compressMul d)
    (x : Zq) : (cmpV M (BitVec.ofNat 64 x.val)).toNat = (x.val * compressMul d + compressAdd) / 2 ^ 19 := by
  have hx := val_lt x
  have ha := compress_arg_lt hd x
  have hp : (BitVec.ofNat 64 x.val * M).toNat = x.val * compressMul d := by
    rw [BitVec.toNat_mul, toNat_val64, hM]
    exact Nat.mod_eq_of_lt (by unfold compressAdd at ha; omega_arith)
  unfold compressAdd at ha ⊢
  unfold cmpV
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, hp]
  refine congrArg (· / 2 ^ 19) ?_
  rw [show (262080 : BitVec 64).toNat = 262080 from rfl]
  omega_arith

/-- A field of `c`: its low `w` bits, at bit `p` (`p + w ≤ 64`). -/
theorem field_toNat (c : BitVec 64) {w p : Nat} (hp : p + w ≤ 64) :
    ((c <<< (64 - w)) >>> (64 - w - p)).toNat = c.toNat % 2 ^ w * 2 ^ p := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have e1 : (2 : Nat) ^ 64 = 2 ^ w * 2 ^ (64 - w) := by rw [← Nat.pow_add]; congr 1; omega_arith
  have e2 : (2 : Nat) ^ (64 - w) = 2 ^ (64 - w - p) * 2 ^ p := by rw [← Nat.pow_add]; congr 1; omega_arith
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
  s'.gpr .a6 = s.gpr .a6 ∧ s'.gpr .a7 = s.gpr .a7 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
    s'.gpr .ra = s.gpr .ra ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r

theorem body1_ok (h3 : s.gpr .a0 = x) (h5 : s.gpr .a2 = y) (h11 : s.gpr .t1 = c) (h9 : s.gpr .a6 = M)
    (h10 : s.gpr .a7 = 262080)
    (ia : ∀ j < 8, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (4 * j)) 4)
    (aa : ∀ j < 8, (x + BitVec.ofNat 64 (4 * j)).toNat % 4 = 0)
    (ob : InRegions s.wr y 1) :
    WP isa (.block ce1Body) s fun s' =>
      s'.gpr .a0 = x + 32 ∧ s'.gpr .a2 = y + 1 ∧ s'.gpr .t1 = c - 1 ∧ Keep s s' ∧
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
  have j0 := aa 0 (by decide)
  have j1 := aa 1 (by decide)
  have j2 := aa 2 (by decide)
  have j3 := aa 3 (by decide)
  have j4 := aa 4 (by decide)
  have j5 := aa 5 (by decide)
  have j6 := aa 6 (by decide)
  have j7 := aa 7 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at i0 i1 i2 i3 i4 i5 i6 i7 j0 j1 j2 j3 j4 j5 j6 j7
  crun [ce1Body, ce1Bit, compressAt, Keep, A, fld, cmpV, h3, h5, h11, h9, h10, i0, i1, i2, i3, i4, i5, i6, i7,
    j0, j1, j2, j3, j4, j5, j6, j7,
    ob, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append,
    List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [Mem.writeW, Mem.readW, Mem.read]

theorem body4_ok (h3 : s.gpr .a0 = x) (h5 : s.gpr .a2 = y) (h11 : s.gpr .t1 = c) (h9 : s.gpr .a6 = M)
    (h10 : s.gpr .a7 = 262080)
    (ia : ∀ j < 2, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (4 * j)) 4)
    (aa : ∀ j < 2, (x + BitVec.ofNat 64 (4 * j)).toNat % 4 = 0)
    (ob : InRegions s.wr y 1) :
    WP isa (.block ce4Body) s fun s' =>
      s'.gpr .a0 = x + 8 ∧ s'.gpr .a2 = y + 1 ∧ s'.gpr .t1 = c - 1 ∧ Keep s s' ∧
      s'.mem = s.mem.writeW y ((fld 4 0 (cmpV M (A s x 0)) + fld 4 4 (cmpV M (A s x 1))).setWidth 8) := by
  have i0 := ia 0 (by decide)
  have i1 := ia 1 (by decide)
  have j0 := aa 0 (by decide)
  have j1 := aa 1 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at i0 i1 j0 j1
  crun [ce4Body, compressAt, Keep, A, fld, cmpV, h3, h5, h11, h9, h10, i0, i1, j0, j1, ob, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

/-- The four fields of a group of `ByteEncode₁₀(Compress₁₀)`, in one doubleword. -/
abbrev V10 (s : State) (x M : BitVec 64) : BitVec 64 :=
  0 + fld 10 0 (cmpV M (A s x 0)) + fld 10 10 (cmpV M (A s x 1)) + fld 10 20 (cmpV M (A s x 2)) +
    fld 10 30 (cmpV M (A s x 3))

theorem body10_ok (h3 : s.gpr .a0 = x) (h5 : s.gpr .a2 = y) (h11 : s.gpr .t1 = c) (h9 : s.gpr .a6 = M)
    (h10 : s.gpr .a7 = 262080)
    (ia : ∀ j < 4, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (4 * j)) 4)
    (aa : ∀ j < 4, (x + BitVec.ofNat 64 (4 * j)).toNat % 4 = 0)
    (ob : ∀ k < 5, InRegions s.wr (y + BitVec.ofNat 64 k) 1) :
    WP isa (.block ce10Body) s fun s' =>
      s'.gpr .a0 = x + 16 ∧ s'.gpr .a2 = y + 5 ∧ s'.gpr .t1 = c - 1 ∧ Keep s s' ∧
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
  have j0 := aa 0 (by decide)
  have j1 := aa 1 (by decide)
  have j2 := aa 2 (by decide)
  have j3 := aa 3 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at i0 i1 i2 i3 o0 j0 j1 j2 j3
  crun [ce10Body, ce10Coeff, compressAt, Keep, V10, A, fld, cmpV, h3, h5, h11, h9, h10, i0, i1, i2, i3,
    j0, j1, j2, j3,
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
  rw [BitVec.toNat_setWidth, (toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq (a := 0) (A := 0) rfl (fld_cmp (d := 1) (by decide) hM _ (p := 0) (by decide)) (by omega_arith)) (fld_cmp (d := 1) (by decide) hM _ (p := 1) (by decide)) (by omega_arith)) (fld_cmp (d := 1) (by decide) hM _ (p := 2) (by decide)) (by omega_arith)) (fld_cmp (d := 1) (by decide) hM _ (p := 3) (by decide)) (by omega_arith)) (fld_cmp (d := 1) (by decide) hM _ (p := 4) (by decide)) (by omega_arith)) (fld_cmp (d := 1) (by decide) hM _ (p := 5) (by decide)) (by omega_arith)) (fld_cmp (d := 1) (by decide) hM _ (p := 6) (by decide)) (by omega_arith)) (fld_cmp (d := 1) (by decide) hM _ (p := 7) (by decide)) (by omega_arith)), BitVec.toNat_ofNat]
  omega_arith

theorem byte4 (hM : M.toNat = compressMul 4) {k : Nat} (hk : k < 128) :
    (fld 4 0 (cmpV M (BitVec.ofNat 64 f[2 * k]!.val)) +
      fld 4 4 (cmpV M (BitVec.ofNat 64 f[2 * k + 1]!.val))).setWidth 8 = (compressEncode 4 f)[k]! := by
  rw [compressEncode4 f hk]
  have b0 := compress_lt 4 f[2 * k]!
  have b1 := compress_lt 4 f[2 * k + 1]!
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, toNat_add_eq (fld_cmp (d := 4) (by decide) hM _ (p := 0) (by decide))
    (fld_cmp (d := 4) (by decide) hM _ (p := 4) (by decide)) (by omega_arith), BitVec.toNat_ofNat]
  omega_arith

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
      compress 10 f[4 * g + 2]! * 2 ^ 20 + compress 10 f[4 * g + 3]! * 2 ^ 30 := (toNat_add_eq (toNat_add_eq (toNat_add_eq (toNat_add_eq (a := 0) (A := 0) rfl (fld_cmp (d := 10) (by decide) hM _ (p := 0) (by decide)) (by omega_arith)) (fld_cmp (d := 10) (by decide) hM _ (p := 10) (by decide)) (by omega_arith)) (fld_cmp (d := 10) (by decide) hM _ (p := 20) (by decide)) (by omega_arith)) (fld_cmp (d := 10) (by decide) hM _ (p := 30) (by decide)) (by omega_arith))
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
    (try rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]) <;> rw [e] <;> omega_arith

end

/-! ## The loops -/

section
variable (s₀ : State)

abbrev F : Addr := s₀.gpr .a0
abbrev O : Addr := s₀.gpr .a2
/-- `d`, the low word of `r4`. -/
abbrev dN : Nat := ((s₀.gpr .a1).setWidth 32).toNat
abbrev L : Nat := (s₀.gpr .a3).toNat
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
  dw : dN s₀ ∈ compressWidths
  len : L s₀ = 32 * dN s₀
  red : Reduced s₀.mem (F s₀)
  alF : (F s₀).toNat % 4 = 0

/-- After `i` iterations of the loop that reads `inS` bytes and writes `b`
bytes each, `N` in all, with the multiplier `M`. -/
structure Inv (s₀ : State) (M : BitVec 64) (inS b N : Nat) (i : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = F s₀ + BitVec.ofNat 64 (inS * i)
  a2 : s.gpr .a2 = O s₀ + BitVec.ofNat 64 (b * i)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (N - i)
  a6 : s.gpr .a6 = M
  a7 : s.gpr .a7 = 262080
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  ra : s.gpr .ra = s₀.gpr .ra
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [outR s₀] s₀.mem s.mem
  bytes : ∀ k < L s₀, s.mem (O s₀ + BitVec.ofNat 64 k) =
    if k < b * i then (E s₀)[k]! else s₀.mem (O s₀ + BitVec.ofNat 64 k)

section
variable {s₀ : State} (hp : Pre s₀) {M : BitVec 64} {inS b N i : Nat} {s : State} (h : Inv s₀ M inS b N i s)
include hp h

/-- Coefficient `j`, as read in the loop: the input is never written. -/
theorem coef_rd {j : Nat} (hj : j < 256) :
    (s.mem.readW (coeffAddr (F s₀) j) 32).setWidth 64 = BitVec.ofNat 64 ((P s₀)[j]!).val := by
  have e := coeffAt_congr (bytes_frame h.frame (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.disj) (by decide)) (by rw [n_eq]; exact hj)
  have v := polyAt_val hp.red (i := j) (by rw [n_eq]; exact hj)
  rw [← coeffAt_eq, e]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_setWidth64, BitVec.toNat_ofNat, v, Nat.mod_eq_of_lt (by have := (coeffAt s₀.mem (F s₀) j).isLt; omega_arith)]

theorem in_rd {j : Nat} (hj : j < 256) : InRegions (s.rd ++ s.wr) (coeffAddr (F s₀) j) 4 := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, coeff_contains _ (by rw [n_eq]; exact hj)⟩

theorem out_wr {k : Nat} (hk : k < L s₀) : InRegions s.wr (O s₀ + BitVec.ofNat 64 k) 1 := by
  have := hp.fitO
  rw [h.wr, hp.wr]; exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

end

theorem out_frame {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [outR s₀] s₀.mem m) {k : Nat} (hk : k < L s₀) (v : Byte) :
    Frame [outR s₀] s₀.mem (m.writeW (O s₀ + BitVec.ofNat 64 k) v) := by
  have := hp.fitO
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))

/-- The counter of an iteration. -/
theorem count_step {N i : Nat} (hi : i < N) (hN : N < 2 ^ 64) {c : BitVec 64} (hc : c = BitVec.ofNat 64 (N - i)) :
    c - 1 = BitVec.ofNat 64 (N - (i + 1)) ∧ (c - 1 != 0) = decide (i + 1 ≠ N) := by
  subst hc
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
  exact ⟨rfl, count_nz hi hN⟩

theorem step4 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 4) {M : BitVec 64} (hM : M.toNat = compressMul 4)
    {i : Nat} (hi : i < 128) {s : State} (h : Inv s₀ M 8 1 128 i s) :
    WP isa (.block ce4Body) s fun s' => Inv s₀ M 8 1 128 (i + 1) s' ∧ (s'.gpr .t1 != 0) = decide (i + 1 ≠ 128) := by
  have hL : L s₀ = 128 := by rw [hp.len, hd]
  have e0 : F s₀ + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 (4 * 0) = coeffAddr (F s₀) (2 * i) := by
    rw [ptr_add, show 8 * i + 4 * 0 = 4 * (2 * i) by omega_arith]
  have e1 : F s₀ + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 (4 * 1) = coeffAddr (F s₀) (2 * i + 1) := by
    rw [ptr_add, show 8 * i + 4 * 1 = 4 * (2 * i + 1) by omega_arith]
  have a0 : A s (F s₀ + BitVec.ofNat 64 (8 * i)) 0 = BitVec.ofNat 64 ((P s₀)[2 * i]!).val := by
    rw [A, e0]; exact coef_rd hp h (by omega_arith)
  have a1 : A s (F s₀ + BitVec.ofNat 64 (8 * i)) 1 = BitVec.ofNat 64 ((P s₀)[2 * i + 1]!).val := by
    rw [A, e1]; exact coef_rd hp h (by omega_arith)
  refine WP.mono (body4_ok h.a0 h.a2 h.t1 h.a6 h.a7 (fun j hj => ?_) (fun j hj => ?_) (by
    rw [Nat.one_mul]; exact out_wr hp h (by omega_arith)))
    fun s' ⟨r3, r5, r11, ⟨r9, r10, rd, wr, sp, ra, pres⟩, m⟩ => ?_
  · rcases (by omega_arith : j = 0 ∨ j = 1) with rfl | rfl
    · rw [e0]; exact in_rd hp h (by omega_arith)
    · rw [e1]; exact in_rd hp h (by omega_arith)
  · rcases (by omega_arith : j = 0 ∨ j = 1) with rfl | rfl
    · rw [e0]; exact align4_add hp.alF _
    · rw [e1]; exact align4_add hp.alF _
  obtain ⟨c1, c2⟩ := count_step (N := 128) hi (by decide) rfl
  refine ⟨⟨?_, ?_, r11.trans c1, r9.trans h.a6, r10.trans h.a7, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
    ra.trans h.ra, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, by rw [r11]; exact c2⟩
  · rw [r3]; exact ptr_succ _ 8 i
  · rw [r5]; exact ptr_succ _ 1 i
  · rw [m, Nat.one_mul]; exact out_frame hp h.frame (by omega_arith) _
  · have hb := h.bytes
    simp only [Nat.one_mul] at hb ⊢
    rw [m, a0, a1, byte4 _ hM hi, Nat.one_mul]
    exact byte_one (by omega_arith) (by omega_arith) hb (by rw [E, hd])

theorem step1 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 1) {M : BitVec 64} (hM : M.toNat = compressMul 1)
    {i : Nat} (hi : i < 32) {s : State} (h : Inv s₀ M 32 1 32 i s) :
    WP isa (.block ce1Body) s fun s' => Inv s₀ M 32 1 32 (i + 1) s' ∧ (s'.gpr .t1 != 0) = decide (i + 1 ≠ 32) := by
  have hL : L s₀ = 32 := by rw [hp.len, hd]
  have ek : ∀ j < 8, F s₀ + BitVec.ofNat 64 (32 * i) + BitVec.ofNat 64 (4 * j) = coeffAddr (F s₀) (8 * i + j) :=
    fun j _ => by rw [ptr_add, show 32 * i + 4 * j = 4 * (8 * i + j) by omega_arith]
  have a0 : A s (F s₀ + BitVec.ofNat 64 (32 * i)) 0 = BitVec.ofNat 64 ((P s₀)[8 * i]!).val := by
    rw [A, ek 0 (by omega_arith), Nat.add_zero]; exact coef_rd hp h (by omega_arith)
  have a1 : A s (F s₀ + BitVec.ofNat 64 (32 * i)) 1 = BitVec.ofNat 64 ((P s₀)[8 * i + 1]!).val := by
    rw [A, ek 1 (by omega_arith)]; exact coef_rd hp h (by omega_arith)
  have a2 : A s (F s₀ + BitVec.ofNat 64 (32 * i)) 2 = BitVec.ofNat 64 ((P s₀)[8 * i + 2]!).val := by
    rw [A, ek 2 (by omega_arith)]; exact coef_rd hp h (by omega_arith)
  have a3 : A s (F s₀ + BitVec.ofNat 64 (32 * i)) 3 = BitVec.ofNat 64 ((P s₀)[8 * i + 3]!).val := by
    rw [A, ek 3 (by omega_arith)]; exact coef_rd hp h (by omega_arith)
  have a4 : A s (F s₀ + BitVec.ofNat 64 (32 * i)) 4 = BitVec.ofNat 64 ((P s₀)[8 * i + 4]!).val := by
    rw [A, ek 4 (by omega_arith)]; exact coef_rd hp h (by omega_arith)
  have a5 : A s (F s₀ + BitVec.ofNat 64 (32 * i)) 5 = BitVec.ofNat 64 ((P s₀)[8 * i + 5]!).val := by
    rw [A, ek 5 (by omega_arith)]; exact coef_rd hp h (by omega_arith)
  have a6 : A s (F s₀ + BitVec.ofNat 64 (32 * i)) 6 = BitVec.ofNat 64 ((P s₀)[8 * i + 6]!).val := by
    rw [A, ek 6 (by omega_arith)]; exact coef_rd hp h (by omega_arith)
  have a7 : A s (F s₀ + BitVec.ofNat 64 (32 * i)) 7 = BitVec.ofNat 64 ((P s₀)[8 * i + 7]!).val := by
    rw [A, ek 7 (by omega_arith)]; exact coef_rd hp h (by omega_arith)
  refine WP.mono (body1_ok h.a0 h.a2 h.t1 h.a6 h.a7 (fun j hj => by rw [ek j hj]; exact in_rd hp h (by omega_arith))
    (fun j hj => by rw [ek j hj]; exact align4_add hp.alF _)
    (by rw [Nat.one_mul]; exact out_wr hp h (by omega_arith)))
    fun s' ⟨r3, r5, r11, ⟨r9, r10, rd, wr, sp, ra, pres⟩, m⟩ => ?_
  obtain ⟨c1, c2⟩ := count_step (N := 32) hi (by decide) rfl
  refine ⟨⟨?_, ?_, r11.trans c1, r9.trans h.a6, r10.trans h.a7, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
    ra.trans h.ra, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, by rw [r11]; exact c2⟩
  · rw [r3]; exact ptr_succ _ 32 i
  · rw [r5]; exact ptr_succ _ 1 i
  · rw [m, Nat.one_mul]; exact out_frame hp h.frame (by omega_arith) _
  · have hb := h.bytes
    simp only [Nat.one_mul] at hb ⊢
    rw [m, a0, a1, a2, a3, a4, a5, a6, a7, byte1 _ hM hi, Nat.one_mul]
    exact byte_one (by omega_arith) (by omega_arith) hb (by rw [E, hd])

theorem step10 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 10) {M : BitVec 64} (hM : M.toNat = compressMul 10)
    {i : Nat} (hi : i < 64) {s : State} (h : Inv s₀ M 16 5 64 i s) :
    WP isa (.block ce10Body) s fun s' => Inv s₀ M 16 5 64 (i + 1) s' ∧ (s'.gpr .t1 != 0) = decide (i + 1 ≠ 64) := by
  have hL : L s₀ = 320 := by rw [hp.len, hd]
  have fO := hp.fitO
  have ek : ∀ j < 4, F s₀ + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (4 * j) = coeffAddr (F s₀) (4 * i + j) :=
    fun j _ => by rw [ptr_add, show 16 * i + 4 * j = 4 * (4 * i + j) by omega_arith]
  have eo : ∀ k < 5, O s₀ + BitVec.ofNat 64 (5 * i) + BitVec.ofNat 64 k = O s₀ + BitVec.ofNat 64 (5 * i + k) :=
    fun k _ => ptr_add _ _ _
  have a0 : A s (F s₀ + BitVec.ofNat 64 (16 * i)) 0 = BitVec.ofNat 64 ((P s₀)[4 * i]!).val := by
    rw [A, ek 0 (by omega_arith), Nat.add_zero]; exact coef_rd hp h (by omega_arith)
  have a1 : A s (F s₀ + BitVec.ofNat 64 (16 * i)) 1 = BitVec.ofNat 64 ((P s₀)[4 * i + 1]!).val := by
    rw [A, ek 1 (by omega_arith)]; exact coef_rd hp h (by omega_arith)
  have a2 : A s (F s₀ + BitVec.ofNat 64 (16 * i)) 2 = BitVec.ofNat 64 ((P s₀)[4 * i + 2]!).val := by
    rw [A, ek 2 (by omega_arith)]; exact coef_rd hp h (by omega_arith)
  have a3 : A s (F s₀ + BitVec.ofNat 64 (16 * i)) 3 = BitVec.ofNat 64 ((P s₀)[4 * i + 3]!).val := by
    rw [A, ek 3 (by omega_arith)]; exact coef_rd hp h (by omega_arith)
  have x0 : O s₀ + BitVec.ofNat 64 (5 * i) = O s₀ + BitVec.ofNat 64 (5 * i + 0) := rfl
  refine WP.mono (body10_ok h.a0 h.a2 h.t1 h.a6 h.a7 (fun j hj => by rw [ek j hj]; exact in_rd hp h (by omega_arith))
    (fun j hj => by rw [ek j hj]; exact align4_add hp.alF _)
    (fun k hk => by rw [eo k hk]; exact out_wr hp h (by omega_arith)))
    fun s' ⟨r3, r5, r11, ⟨r9, r10, rd, wr, sp, ra, pres⟩, m⟩ => ?_
  obtain ⟨c1, c2⟩ := count_step (N := 64) hi (by decide) rfl
  obtain ⟨v0, v1, v2, v3, v4⟩ := byte10 (P s₀) hM hi
  refine ⟨⟨?_, ?_, r11.trans c1, r9.trans h.a6, r10.trans h.a7, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
    ra.trans h.ra, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, by rw [r11]; exact c2⟩
  · rw [r3]; exact ptr_succ _ 16 i
  · rw [r5]; exact ptr_succ _ 5 i
  · rw [m, eo 1 (by omega_arith), eo 2 (by omega_arith), eo 3 (by omega_arith), eo 4 (by omega_arith), x0]
    exact out_frame hp (out_frame hp (out_frame hp (out_frame hp (out_frame hp h.frame (by omega_arith) _)
      (by omega_arith) _) (by omega_arith) _) (by omega_arith) _) (by omega_arith) _
  · have e : V10 s (F s₀ + BitVec.ofNat 64 (16 * i)) M = W10 (P s₀) (M := M) i := by
      rw [V10, a0, a1, a2, a3]
    rw [m, eo 1 (by omega_arith), eo 2 (by omega_arith), eo 3 (by omega_arith), eo 4 (by omega_arith), x0, e, v0, v1, v2, v3, v4,
      show 5 * (i + 1) = 5 * i + 4 + 1 by omega_arith]
    refine byte_one (by omega_arith) (by omega_arith) (byte_one (by omega_arith) (by omega_arith) (byte_one (by omega_arith) (by omega_arith)
      (byte_one (by omega_arith) (by omega_arith) (byte_one (by omega_arith) (by omega_arith) h.bytes ?_) ?_) ?_) ?_) ?_ <;>
      rw [E, hd]

/-! ## The branches -/

/-- What the loops end with. -/
def Fin (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.gpr .ra = s₀.gpr .ra ∧
    ∀ k < L s₀, s.mem (O s₀ + BitVec.ofNat 64 k) = (E s₀)[k]!

/-- What a branch starts from. -/
def Start (s₀ s : State) : Prop :=
  s.gpr .a0 = F s₀ ∧ s.gpr .a2 = O s₀ ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧ s.gpr .ra = s₀.gpr .ra ∧
    (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem

theorem loop_fin {s₀ : State} {M : BitVec 64} {inS b N : Nat} (hbN : b * N = L s₀) {s : State}
    (h : Inv s₀ M inS b N N s) : Fin s₀ s :=
  ⟨h.pres, h.sp, h.ra, fun k hk => by rw [h.bytes k hk, ite_eq_left (by omega_arith)]⟩

theorem inv_zero {s₀ : State} {M : BitVec 64} {inS b N : Nat} {s : State} (h : Start s₀ s)
    (h9 : s.gpr .a6 = M) (h10 : s.gpr .a7 = 262080) (h11 : s.gpr .t1 = BitVec.ofNat 64 N) :
    Inv s₀ M inS b N 0 s := by
  obtain ⟨r3, r5, rd, wr, sp, ra, pres, m⟩ := h
  refine ⟨by simp [r3], by simp [r5], by simp [h11], h9, h10, rd, wr, sp, ra, pres, by rw [m]; exact Frame.refl _ _,
    fun k _ => by rw [m, ite_eq_right (by omega_arith)]⟩

theorem setup_1 {s : State} :
    WP isa (.block (biasConst ++ ([.li .a6 315, .li .t1 32] : List Instr))) s fun s' =>
      s'.gpr .a6 = BitVec.ofNat 64 315 ∧ s'.gpr .a7 = 262080 ∧ s'.gpr .t1 = BitVec.ofNat 64 32 ∧
        s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a2 = s.gpr .a2 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        s'.gpr .ra = s.gpr .ra ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  crun [biasConst, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    List.cons_append, List.nil_append]
  all_goals decide

theorem setup_4 {s : State} :
    WP isa (.block (biasConst ++ liq .a6 2520 ++ ([.li .t1 128] : List Instr))) s fun s' =>
      s'.gpr .a6 = BitVec.ofNat 64 2520 ∧ s'.gpr .a7 = 262080 ∧ s'.gpr .t1 = BitVec.ofNat 64 128 ∧
        s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a2 = s.gpr .a2 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        s'.gpr .ra = s.gpr .ra ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  simp only [biasConst, liq, Nat.reduceLT, ite_false, List.cons_append, List.nil_append,
    Int.reduceSub, Int.reduceNeg, Int.cast_ofNat_Int]
  crun [preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  all_goals decide

theorem setup_10 {s : State} :
    WP isa (.block (biasConst ++ ([.lui .a6 0x27, .addi .a6 .a6 1527, .li .t1 64] : List Instr))) s fun s' =>
      s'.gpr .a6 = 161271 ∧ s'.gpr .a7 = 262080 ∧ s'.gpr .t1 = BitVec.ofNat 64 64 ∧
        s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a2 = s.gpr .a2 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        s'.gpr .ra = s.gpr .ra ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  crun [biasConst, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    List.cons_append, List.nil_append]
  all_goals decide

theorem branch1 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 1) {s : State} (h : Start s₀ s) :
    WP isa (.seq (.block (biasConst ++ ([.li .a6 315, .li .t1 32] : List Instr))) (.loop (.block ce1Body) (.nonzero .t1)))
      s (Fin s₀) := by
  refine WP.seq (WP.mono setup_1 fun s₁ ⟨r9, r10, r11, r3, r5, rd, wr, sp, ra, pres, m⟩ => ?_)
  obtain ⟨h3, h5, hrd, hwr, hsp, hlr, hpres, hm⟩ := h
  refine wp_loop_nz (Inv s₀ (BitVec.ofNat 64 315) 32 1 32) (N := 32) (by decide)
    (fun i hi s h => step1 hp hd (by decide) hi h) (fun s h => loop_fin (by rw [hp.len, hd]) h)
    (inv_zero ⟨r3.trans h3, r5.trans h5, rd.trans hrd, wr.trans hwr, sp.trans hsp, ra.trans hlr,
      fun r hr => (pres r hr).trans (hpres r hr), m.trans hm⟩ r9 r10 r11)

theorem branch4 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 4) {s : State} (h : Start s₀ s) :
    WP isa (.seq (.block (biasConst ++ liq .a6 2520 ++ ([.li .t1 128] : List Instr)))
      (.loop (.block ce4Body) (.nonzero .t1))) s (Fin s₀) := by
  refine WP.seq (WP.mono setup_4 fun s₁ ⟨r9, r10, r11, r3, r5, rd, wr, sp, ra, pres, m⟩ => ?_)
  obtain ⟨h3, h5, hrd, hwr, hsp, hlr, hpres, hm⟩ := h
  refine wp_loop_nz (Inv s₀ (BitVec.ofNat 64 2520) 8 1 128) (N := 128) (by decide)
    (fun i hi s h => step4 hp hd (by decide) hi h) (fun s h => loop_fin (by rw [hp.len, hd]) h)
    (inv_zero ⟨r3.trans h3, r5.trans h5, rd.trans hrd, wr.trans hwr, sp.trans hsp, ra.trans hlr,
      fun r hr => (pres r hr).trans (hpres r hr), m.trans hm⟩ r9 r10 r11)

theorem branch10 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 10) {s : State} (h : Start s₀ s) :
    WP isa (.seq (.block (biasConst ++ ([.lui .a6 0x27, .addi .a6 .a6 1527, .li .t1 64] : List Instr)))
      (.loop (.block ce10Body) (.nonzero .t1))) s (Fin s₀) := by
  refine WP.seq (WP.mono setup_10 fun s₁ ⟨r9, r10, r11, r3, r5, rd, wr, sp, ra, pres, m⟩ => ?_)
  obtain ⟨h3, h5, hrd, hwr, hsp, hlr, hpres, hm⟩ := h
  refine wp_loop_nz (Inv s₀ 161271 16 5 64) (N := 64) (by decide)
    (fun i hi s h => step10 hp hd (by decide) hi h) (fun s h => loop_fin (by rw [hp.len, hd]) h)
    (inv_zero ⟨r3.trans h3, r5.trans h5, rd.trans hrd, wr.trans hwr, sp.trans hsp, ra.trans hlr,
      fun r hr => (pres r hr).trans (hpres r hr), m.trans hm⟩ r9 r10 r11)

/-- `a1` zero-extended. -/
abbrev Z (s₀ : State) : BitVec 64 := ((s₀.gpr .a1).setWidth 32).setWidth 64

/-- The zero-extension by a pair of shifts. -/
theorem zext_eq (x : BitVec 64) : x <<< 32 >>> 32 = (x.setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have := x.isLt
  omega

/-- The branch on `d`, zero-extended: `d - k` is zero exactly when `d = k`. -/
theorem dsel (y : BitVec 32) {k : Nat} (hk : k < 2048) :
    (y.setWidth 64 - BitVec.ofNat 64 k == 0) = decide (y.toNat = k) := by
  have hy := y.isLt
  have h0 : (0 : BitVec 64).toNat = 0 := rfl
  have e : y.setWidth 64 - BitVec.ofNat 64 k = 0 ↔ y.toNat = k := by
    constructor
    · intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat, h0] at this
      omega
    · intro e
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat, h0]
      omega
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  exact e

theorem sel_eval {s₀ s : State} {k : Nat} (hk : k < 2048) (h : s.gpr .a4 = Z s₀ - BitVec.ofNat 64 k) :
    isa.eval (.zero .a4) s = some (decide (dN s₀ = k)) := by
  show (some (s.gpr .a4 == 0) : Option Bool) = _
  rw [h, dsel _ hk]

theorem zext_start {s₀ : State} :
    WP isa (.block (zext32 .a1)) s₀ fun s => Start s₀ s ∧ s.gpr .a1 = Z s₀ := by
  crun [zext32, Start, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  exact zext_eq _

theorem sub1_ok {s₀ s : State} (h : Start s₀ s) (h1 : s.gpr .a1 = Z s₀) :
    WP isa (.block [.addi .a4 .a1 (-1)]) s fun s' =>
      Start s₀ s' ∧ s'.gpr .a1 = Z s₀ ∧ s'.gpr .a4 = Z s₀ - BitVec.ofNat 64 1 := by
  obtain ⟨r3, r5, rd, wr, sp, ra, pres, m⟩ := h
  simp only [preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at pres
  crun [Start, r3, r5, rd, wr, sp, ra, m, h1, pres, preserved, List.forall_mem_cons, List.not_mem_nil,
    false_imp_iff]

theorem sub4_ok {s₀ s : State} (h : Start s₀ s) (h1 : s.gpr .a1 = Z s₀) :
    WP isa (.block [.addi .a4 .a1 (-4)]) s fun s' =>
      Start s₀ s' ∧ s'.gpr .a1 = Z s₀ ∧ s'.gpr .a4 = Z s₀ - BitVec.ofNat 64 4 := by
  obtain ⟨r3, r5, rd, wr, sp, ra, pres, m⟩ := h
  simp only [preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at pres
  crun [Start, r3, r5, rd, wr, sp, ra, m, h1, pres, preserved, List.forall_mem_cons, List.not_mem_nil,
    false_imp_iff]

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa compressEncode s₀ (Fin s₀) := by
  refine WP.seq (WP.mono zext_start fun s₁ ⟨st₁, z₁⟩ => WP.seq (WP.mono (sub1_ok st₁ z₁)
    fun s₂ ⟨st₂, z₂, e₂⟩ => ?_))
  rcases mem_compressWidths hp.dw with hd | hd | hd
  · refine WP.ite true (by rw [sel_eval (s₀ := s₀) (k := 1) (by decide) e₂, hd]; rfl)
      (fun _ => branch1 hp hd st₂) (fun h => absurd h (by decide))
  · refine WP.ite false (by rw [sel_eval (s₀ := s₀) (k := 1) (by decide) e₂, hd]; rfl)
      (fun h => absurd h (by decide)) (fun _ => WP.seq (WP.mono (sub4_ok st₂ z₂) fun s₃ ⟨st₃, _, e₃⟩ => ?_))
    exact WP.ite true (by rw [sel_eval (s₀ := s₀) (k := 4) (by decide) e₃, hd]; rfl)
      (fun _ => branch4 hp hd st₃) (fun h => absurd h (by decide))
  · refine WP.ite false (by rw [sel_eval (s₀ := s₀) (k := 1) (by decide) e₂, hd]; rfl)
      (fun h => absurd h (by decide)) (fun _ => WP.seq (WP.mono (sub4_ok st₂ z₂) fun s₃ ⟨st₃, _, e₃⟩ => ?_))
    exact WP.ite false (by rw [sel_eval (s₀ := s₀) (k := 4) (by decide) e₃, hd]; rfl)
      (fun h => absurd h (by decide)) (fun _ => branch10 hp hd st₃)

/-! ## Verified -/

/-- The public registers but `a1`, and `a1`'s low word, agree. -/
def LoAgree (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ (∀ r ∈ [Reg.a0, .a2, .a3], s₁.gpr r = s₂.gpr r) ∧
    (s₁.gpr .a1).setWidth 32 = (s₂.gpr .a1).setWidth 32

/-- What the zero-extension of `a1` leaves from `σ`. -/
def ZextF (σ s : State) : Prop :=
  s.sp = σ.sp ∧ (∀ r ∈ [Reg.a0, .a2, .a3], s.gpr r = σ.gpr r) ∧ s.gpr .a1 = Z σ

theorem zext_ok (σ : State) : WP isa (.block (zext32 .a1)) σ (ZextF σ) := by
  crun [zext32, ZextF, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  exact zext_eq _

theorem zext_rel : RelCT isa LoAgree (.block (zext32 .a1))
    fun s₁ s₂ => s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.a0, .a1, .a2, .a3], s₁.gpr r = s₂.gpr r := by
  have ht : RelCT isa LoAgree (.block (zext32 .a1)) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a2, .a3])
      (fun _ _ ⟨hsp, hr, _⟩ => ⟨hsp, fun r h => hr r (Taint.mem_ofRegs.mp h)⟩) (by taint_decide)
  refine (ht.wpDep (F := ZextF) fun σ₁ σ₂ _ => ⟨zext_ok σ₁, zext_ok σ₂⟩).mono (fun _ _ h => h) ?_
  rintro s₁ s₂ ⟨-, σ₁, σ₂, ⟨hsp, hr, hlo⟩, ⟨f1, g1, k1⟩, ⟨f2, g2, k2⟩⟩
  refine ⟨by rw [f1, f2, hsp], fun r hr' => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl
  · rw [g1 _ (by decide), g2 _ (by decide), hr _ (by decide)]
  · rw [k1, k2, Z, Z, hlo]
  · rw [g1 _ (by decide), g2 _ (by decide), hr _ (by decide)]
  · rw [g1 _ (by decide), g2 _ (by decide), hr _ (by decide)]

theorem pre_of {s : State} (h : (Proof.MlKem.compressEncodeContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Proof.MlKem.compressEncodeContract, Proof.MlKem.compressEncodeSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 1 | .a2 => 0x2000 | .a3 => 32 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 32⟩]

theorem verified : Verified RISCV64.target Impl.MlKem.RISCV64.compressEncode
    (Proof.MlKem.compressEncodeContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, RelCT.constantTime (Q := fun _ _ => True) ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hra, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hra⟩, ?_⟩
    sig_post [Proof.MlKem.compressEncodeContract, Proof.MlKem.compressEncodeSig, RISCV64.abi, RISCV64.argRegs]
    exact bytesAt_eq! (compressEncode_length _ _ ▸ (pre_of hs).len.symm) h
  · refine RelCT.seq (zext_rel.mono (fun s₁ s₂ ⟨_, _, hp⟩ => ?_) fun _ _ h => h)
      (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
        (fun _ _ ⟨hsp, hr⟩ => ⟨hsp, fun r h => hr r (Taint.mem_ofRegs.mp h)⟩) (by taint_decide))
    sig_pub [Proof.MlKem.compressEncodeContract, Proof.MlKem.compressEncodeSig, RISCV64.abi, RISCV64.argRegs] at hp
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
    · sig_reduce [Proof.MlKem.compressEncodeContract, Proof.MlKem.compressEncodeSig, RISCV64.abi,
        RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact Add.reduced_zero _
        | decide +kernel

end VG.Proof.MlKem.RISCV64.CompressEncode
