module

public import VerifiedGarbage.Proof.MlDsa.X86.Arith.VLanes
public import VerifiedGarbage.Proof.MlDsa.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.MlDsa.Arith.Zq
import VerifiedGarbage.Proof.Mont.X86.Sse2.Lanes
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-DSA on x86 (32-bit): coefficients that are not reduced between the layers

The vector transforms of `Impl/MlDsa/X86/Arith/Ntt.lean` keep a coefficient
as a doubleword `v` that stands for `x` modulo `q` and is less than a
multiple `b · q` of `q` (`Lz b v x`), as x86-64's
`Proof/MlDsa/X86_64/Arith/LazyNtt.lean` does:

* a butterfly of `NTT` leaves `a + t` and `a + 2q - t` for
  `t = mont (b · ζ · 2³²) < 2q` (`fS`, `fD`), which stand for `x + ζ · y`
  and `x - ζ · y` and are less than `(b + 2) · q` (`f_ok`);
* a butterfly of `NTT⁻¹` leaves `a + b` and `mont ((a + 128q - b) · ζ · 2³²)`
  (`iS`, `iD`), which stand for `x + y` and `ζ · (x - y)` and are less than
  `2b · q` (`i_ok`);
* the last pass of `NTT` reduces `x < 17q`: `x - (x >> 23) · q` is less than
  `2q` (`fin_ok`, as `finL` computes it: `finL_toNat`); that of `NTT⁻¹`
  multiplies by `256⁻¹` (`scale_ok`).

A layer of the specification pairs coefficient `2 · len · c + r` with the
one `len` further, with the zeta of block `c` (`LayOk`: `fwd_lay`,
`inv_lay`; the zetas of `NTT⁻¹` are numbered in the order of use, `zvI`).

Four butterflies are computed on the doublewords of XMM registers. Their
operands are among the eight doublewords of two vectors (`pos`), gathered
and scattered as a `Shape` says (`sh4` for a layer with `len ≥ 4`, `sh2`
and `sh1` for `len = 2` and `len = 1`): the vectors `fwdX` and `fwdY`
(`invX`, `invY`) the code leaves hold, at each position, what the butterfly
of that position leaves (`fwd_new`, `inv_new`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Arith

open VG VG.X86 VG.X86.Lanes
open VG.Proof.MlDsa.Arith
open VG.Proof.Mont.X86.Sse2 (qword_append_0 qword_append_1)
open VG.Spec.MlDsa (q n Zq Poly zetas ntt nttInv)

/-! ## Unreduced coefficients -/

/-- `v` stands for `x`, and is less than `b · q`. -/
def Lz (b v : Nat) (x : Zq) : Prop := v < b * q ∧ v % q = x.val

theorem Lz.mono {b b' v : Nat} {x : Zq} (h : Lz b v x) (hb : b ≤ b') : Lz b' v x :=
  ⟨Nat.lt_of_lt_of_le h.1 (Nat.mul_le_mul_right q hb), h.2⟩

theorem prod_lt {b z : Nat} (hb : b < 2 ^ 32) (hz : z < q) : b * z < q * 2 ^ 32 := by
  rw [Nat.mul_comm q]; exact Nat.mul_lt_mul_of_lt_of_lt hb hz

/-- The sum of a butterfly of `NTT`. -/
def fS (a b z : Nat) : Nat := a + mont (b * z)

/-- The difference of a butterfly of `NTT`. -/
def fD (a b z : Nat) : Nat := a + 2 * q - mont (b * z)

theorem f_ok {bd a b : Nat} {x y ζ : Zq} (hbd : bd ≤ 15) (ha : Lz bd a x) (hb : Lz bd b y) :
    Lz (bd + 2) (fS a b (ζ.val * 2 ^ 32 % q)) (x + ζ * y) ∧
      Lz (bd + 2) (fD a b (ζ.val * 2 ^ 32 % q)) (x - ζ * y) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hb32 : b < 2 ^ 32 := Nat.lt_of_lt_of_le hb1 (Nat.le_trans (Nat.mul_le_mul_right q hbd) (by decide))
  have ht := mont_lt (prod_lt hb32 (Nat.mod_lt (ζ.val * 2 ^ 32) (by decide : 0 < q)))
  have hm : mont (b * (ζ.val * 2 ^ 32 % q)) % q = (ζ * y).val := by
    rw [mont_mulR, val_mul, ← hb2, Nat.mul_mod_mod, Nat.mul_comm]
  have hzy := val_lt (ζ * y)
  have hxv := val_lt x
  simp only [fS, fD, Lz, val_add', val_sub']
  generalize mont (b * (ζ.val * 2 ^ 32 % q)) = t at ht hm
  rw [← hm, ← ha2]
  rw [q_eq] at ha1 ht ⊢
  refine ⟨⟨by omega_using [ha1, ht], Nat.add_mod _ _ _⟩, by omega_using [ha1, ht], by omega_using [ht]⟩

/-- The sum of a butterfly of `NTT⁻¹`. -/
def iS (a b _z : Nat) : Nat := a + b

/-- The difference of a butterfly of `NTT⁻¹`, times the zeta. -/
def iD (a b z : Nat) : Nat := mont ((a + 128 * q - b) * z)

theorem i_ok {bd a b : Nat} {x y ζ : Zq} (h1 : 1 ≤ bd) (hbd : bd ≤ 128) (ha : Lz bd a x) (hb : Lz bd b y) :
    Lz (2 * bd) (iS a b (ζ.val * 2 ^ 32 % q)) (x + y) ∧
      Lz (2 * bd) (iD a b (ζ.val * 2 ^ 32 % q)) (ζ * (x - y)) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have ha' : a < 128 * q := Nat.lt_of_lt_of_le ha1 (Nat.mul_le_mul_right q hbd)
  have hb' : b < 128 * q := Nat.lt_of_lt_of_le hb1 (Nat.mul_le_mul_right q hbd)
  have hw : a + 128 * q - b < 2 ^ 32 := by rw [q_eq] at ha' hb' ⊢; omega_using [ha', hb']
  have ht := mont_lt (prod_lt hw (Nat.mod_lt (ζ.val * 2 ^ 32) (by decide : 0 < q)))
  have hm : mont ((a + 128 * q - b) * (ζ.val * 2 ^ 32 % q)) % q = (ζ * (x - y)).val := by
    have hl : (a + 128 * q - b) % q = (a % q + (q - b % q)) % q := by
      rw [q_eq] at hb' ⊢; omega_using [hb']
    rw [mont_mulR, val_mul, val_sub', ← ha2, ← hb2, Nat.mul_mod_mod, Nat.mul_comm (a + 128 * q - b), Nat.mul_mod, hl,
      ← Nat.mul_mod]
  have hq2 : 2 * q ≤ 2 * bd * q := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_left q h1)
  simp only [iS, iD, Lz, val_add']
  refine ⟨⟨by rw [Nat.mul_assoc]; omega_using [ha1, hb1], ?_⟩, Nat.lt_of_lt_of_le ht hq2, hm⟩
  rw [← ha2, ← hb2]; exact Nat.add_mod _ _ _

/-- `x - (x >> 23) · q`, from `q = 2²³ - 2¹³ + 1`. -/
def finN (x : Nat) : Nat := x % 8388608 + x / 8388608 * 8191

theorem fin_ok {x : Nat} (hx : x < 17 * q) : finN x < 2 * q ∧ finN x % q = x % q := by
  rw [q_eq] at hx ⊢
  simp only [finN]
  omega_using [hx]

/-- `256⁻¹ mod q`. -/
abbrev c256 : Zq := 8347681

theorem scale_ok {a : Nat} {x : Zq} (h : Lz 256 a x) :
    mont (a * 16382) < 2 * q ∧ mont (a * 16382) % q = (x * c256).val := by
  obtain ⟨h1, h2⟩ := h
  have hl : a * 16382 < q * 2 ^ 32 := by rw [q_eq] at h1 ⊢; omega_using [h1]
  refine ⟨mont_lt hl, ?_⟩
  rw [show (16382 : Nat) = 8347681 * 2 ^ 32 % q by decide, mont_mulR, val_mul, ← h2,
    show (c256 : Zq).val = 8347681 from rfl, Nat.mod_mul_mod]

/-! ## The layers of the specification -/

/-- The layer with `len` from `f` to `G`: coefficient `2 · len · c + r` and
the one `len` further become `sS` and `sD` of them, with the zeta of
number `zp + c`. -/
def LayOk (sS sD : Zq → Zq → Zq → Zq) (zv : Nat → Zq) (f G : Poly) (len zp : Nat) : Prop :=
  ∀ c r, r < len → 2 * len * c + r + len < 256 →
    G[2 * len * c + r]! = sS f[2 * len * c + r]! f[2 * len * c + r + len]! (zv (zp + c)) ∧
      G[2 * len * c + r + len]! = sD f[2 * len * c + r]! f[2 * len * c + r + len]! (zv (zp + c))

theorem div_mod_blk {len c r : Nat} (hr : r < 2 * len) :
    (2 * len * c + r) % (2 * len) = r ∧ (2 * len * c + r) / (2 * len) = c := by
  refine ⟨by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr], ?_⟩
  rw [Nat.mul_add_div (by omega_using [hr]), Nat.div_eq_of_lt hr, Nat.add_zero]

theorem fwd_lay (f : Poly) {len : Nat} (hl : 0 < len) (hd : 2 * len * (128 / len) = 256) :
    LayOk (fun x y ζ => x + ζ * y) (fun x y ζ => x - ζ * y) zetas f (nttLayer f len) len (128 / len) := by
  intro c r hr hx
  have e : nttLayer f len = layF (fun f len k st t => blockN bfly f len (zetas k) st t) f len
      (fun c => 128 / len + c) (128 / len) := rfl
  obtain ⟨m1, d1⟩ := div_mod_blk (len := len) (c := c) (r := r) (by omega_using [hr])
  obtain ⟨m2, d2⟩ := div_mod_blk (len := len) (c := c) (r := r + len) (by omega_using [hr])
  have e3 : 2 * len * c + (r + len) - len = 2 * len * c + r := by omega_using []
  rw [e]
  constructor
  · rw [layF_get nttBlk_ok f hl _ (Nat.le_of_eq hd) (by omega_using [hx]), hd, ite_eq_left (by omega_using [hx]), m1,
      ite_eq_left hr, d1]
  · rw [Nat.add_assoc, layF_get nttBlk_ok f hl _ (Nat.le_of_eq hd) (by omega_using [hx]), hd,
      ite_eq_left (by omega_using [hx]), m2, ite_eq_right (by omega_using []), d2, e3]

/-- The zeta of `NTT⁻¹` of number `k` in the order of use. -/
def zvI (k : Nat) : Zq := -zetas ((256 - k) % 256)

theorem inv_lay (f : Poly) {len : Nat} (hl : 0 < len) (hd : 2 * len * (128 / len) = 256)
    (hB : 128 / len ≤ 128) (hq : 256 / len = 2 * (128 / len)) :
    LayOk (fun x y _ => x + y) (fun x y ζ => ζ * (x - y)) zvI f (nttInvLayer f len) len (257 - 256 / len) := by
  intro c r hr hx
  have e : nttInvLayer f len = layF (fun f len k st t => blockN bflyInv f len (-zetas k) st t) f len
      (fun c => 256 / len - 1 - c) (128 / len) := rfl
  obtain ⟨m1, d1⟩ := div_mod_blk (len := len) (c := c) (r := r) (by omega_using [hr])
  obtain ⟨m2, d2⟩ := div_mod_blk (len := len) (c := c) (r := r + len) (by omega_using [hr])
  have e3 : 2 * len * c + (r + len) - len = 2 * len * c + r := by omega_using []
  have hc : c < 128 / len := by
    refine Nat.lt_of_mul_lt_mul_left (a := 2 * len) ?_
    rw [hd]; omega_using [hx]
  have ez : zvI (257 - 256 / len + c) = -zetas (256 / len - 1 - c) := by
    rw [zvI, hq]
    exact congrArg (fun k => -zetas k) (by omega_using [hc, hB])
  rw [e, ez]
  constructor
  · rw [layF_get nttInvBlk_ok f hl _ (Nat.le_of_eq hd) (by omega_using [hx]), hd, ite_eq_left (by omega_using [hx]),
      m1, ite_eq_left hr]
  · rw [Nat.add_assoc, layF_get nttInvBlk_ok f hl _ (Nat.le_of_eq hd) (by omega_using [hx]), hd,
      ite_eq_left (by omega_using [hx]), m2, ite_eq_right (by omega_using []), d2, e3]
    exact (neg_mul_sub _ _ _).symm

/-! ## Doublewords -/

theorem dword_punpcklqdq (a b : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .punpcklqdq a b) i = if i < 2 then dword a i else dword b (i - 2) := by
  have e : XBinOp.eval .punpcklqdq a b = qword b 0 ++ qword a 0 := rfl
  rcases cases4 hi with rfl | rfl | rfl | rfl
  · exact (dword_lo _ 0).trans (by rw [e, qword_append_0]; exact (dword_lo a 0).symm)
  · exact (dword_hi _ 0).trans (by rw [e, qword_append_0]; exact (dword_hi a 0).symm)
  · exact (dword_lo _ 1).trans (by rw [e, qword_append_1]; exact (dword_lo b 0).symm)
  · exact (dword_hi _ 1).trans (by rw [e, qword_append_1]; exact (dword_hi b 0).symm)

theorem dword_punpckhqdq (a b : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .punpckhqdq a b) i = if i < 2 then dword a (i + 2) else dword b i := by
  have e : XBinOp.eval .punpckhqdq a b = qword b 1 ++ qword a 1 := rfl
  rcases cases4 hi with rfl | rfl | rfl | rfl
  · exact (dword_lo _ 0).trans (by rw [e, qword_append_0]; exact (dword_lo a 1).symm)
  · exact (dword_hi _ 0).trans (by rw [e, qword_append_0]; exact (dword_hi a 1).symm)
  · exact (dword_lo _ 1).trans (by rw [e, qword_append_1]; exact (dword_lo b 1).symm)
  · exact (dword_hi _ 1).trans (by rw [e, qword_append_1]; exact (dword_hi b 1).symm)

/-- `pshufd` with `0xD8`: doublewords 0, 2, 1 and 3. -/
theorem dword_shufD8 (a : BitVec 128) :
    dword (shufDwords a 0xD8) 0 = dword a 0 ∧ dword (shufDwords a 0xD8) 1 = dword a 2 ∧
      dword (shufDwords a 0xD8) 2 = dword a 1 ∧ dword (shufDwords a 0xD8) 3 = dword a 3 :=
  ⟨dword_shufDwords a _ (by decide), dword_shufDwords a _ (by decide), dword_shufDwords a _ (by decide),
    dword_shufDwords a _ (by decide)⟩

/-- `a + t` in each doubleword. -/
def sumV (a t : BitVec 128) : BitVec 128 := XBinOp.eval .paddd a t

/-- `a + c - t` in each doubleword, with `c + 1` in those of `c1`, as `bfTail` computes it. -/
def difV (a t c1 : BitVec 128) : BitVec 128 :=
  XBinOp.eval .paddd (XBinOp.eval .paddd (XBinOp.eval .pxor t onesV) c1) a

theorem dword_difV (a t : BitVec 128) (c1 : BitVec 32) {i : Nat} (hi : i < 4) :
    dword (difV a t (bc c1)) i = subL (dword a i) (dword t i) c1 := by
  rw [difV, dword_paddd _ _ hi, dword_paddd _ _ hi, dword_pxor, onesV, dword_bc _ hi, dword_bc _ hi, subL]
  ac_rfl

/-! ## Gathering and scattering -/

/-- Position `p` of the eight doublewords of `X` and `Y`. -/
def pos (X Y : BitVec 128) (p : Nat) : BitVec 32 := if p < 4 then dword X p else dword Y (p - 4)

/-- How four butterflies are computed from two vectors: the registers of
the `a`s and the `b`s (`gA`, `gB`), whose doubleword `e` is at positions
`pa e` and `pb e`, the vectors stored back from the sums and the
differences (`sX`, `sY`), and the Montgomery multiplication, which
multiplies doubleword `e` by doubleword `zl e` of the zetas. -/
structure Shape where
  gA : BitVec 128 → BitVec 128 → BitVec 128
  gB : BitVec 128 → BitVec 128 → BitVec 128
  sX : BitVec 128 → BitVec 128 → BitVec 128
  sY : BitVec 128 → BitVec 128 → BitVec 128
  mm : BitVec 128 → BitVec 128 → BitVec 128
  pa : Nat → Nat
  pb : Nat → Nat
  zl : Nat → Nat

structure ShapeOk (sh : Shape) : Prop where
  gath : ∀ X Y e, e < 4 → dword (sh.gA X Y) e = pos X Y (sh.pa e) ∧ dword (sh.gB X Y) e = pos X Y (sh.pb e)
  scat : ∀ S D e, e < 4 →
    pos (sh.sX S D) (sh.sY S D) (sh.pa e) = dword S e ∧ pos (sh.sX S D) (sh.sY S D) (sh.pb e) = dword D e
  mont : ∀ d z, (∀ i < 4, (dword d i).toNat * (dword z (sh.zl i)).toNat < q * 2 ^ 32) → ∀ i < 4,
    (dword (sh.mm d z) i).toNat = mont ((dword d i).toNat * (dword z (sh.zl i)).toNat)
  cover : ∀ p < 8, ∃ e < 4, p = sh.pa e ∨ p = sh.pb e
  lt : ∀ e < 4, sh.pa e < 8 ∧ sh.pb e < 8

/-- A layer with `len ≥ 4`: the vector at `[eax]` holds the `a`s and that at `[eax + 4 · len]` the `b`s. -/
def sh4 : Shape where
  gA X _ := X
  gB _ Y := Y
  sX S _ := S
  sY _ D := D
  mm := montV
  pa e := e
  pb e := e + 4
  zl e := 2 * (e / 2)

theorem sh4_ok : ShapeOk sh4 where
  gath X Y e he := by rcases cases4 he with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  scat S D e he := by rcases cases4 he with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  mont _ _ hb _ hi := dword_montV hb hi
  cover := by decide
  lt := by decide

/-- The layer with `len = 2`: two blocks in the vectors at `[eax]` and `[eax + 16]`. -/
def sh2 : Shape where
  gA X Y := XBinOp.eval .punpcklqdq X Y
  gB X Y := XBinOp.eval .punpckhqdq X Y
  sX S D := XBinOp.eval .punpcklqdq S D
  sY S D := XBinOp.eval .punpckhqdq S D
  mm := montV
  pa e := if e < 2 then e else e + 2
  pb e := if e < 2 then e + 2 else e + 4
  zl e := 2 * (e / 2)

theorem sh2_ok : ShapeOk sh2 where
  gath X Y e he := by
    refine ⟨(dword_punpcklqdq X Y he).trans ?_, (dword_punpckhqdq X Y he).trans ?_⟩ <;>
      rcases cases4 he with rfl | rfl | rfl | rfl <;> rfl
  scat S D e he := by
    rcases cases4 he with rfl | rfl | rfl | rfl
    · exact ⟨dword_punpcklqdq S D (i := 0) (by decide), dword_punpcklqdq S D (i := 2) (by decide)⟩
    · exact ⟨dword_punpcklqdq S D (i := 1) (by decide), dword_punpcklqdq S D (i := 3) (by decide)⟩
    · exact ⟨dword_punpckhqdq S D (i := 0) (by decide), dword_punpckhqdq S D (i := 2) (by decide)⟩
    · exact ⟨dword_punpckhqdq S D (i := 1) (by decide), dword_punpckhqdq S D (i := 3) (by decide)⟩
  mont _ _ hb _ hi := dword_montV hb hi
  cover := by decide
  lt := by decide

/-- The layer with `len = 1`: four blocks in the vectors at `[eax]` and `[eax + 16]`. -/
def sh1 : Shape where
  gA X Y := XBinOp.eval .punpcklqdq (shufDwords X 0xD8) (shufDwords Y 0xD8)
  gB X Y := XBinOp.eval .punpckhqdq (shufDwords X 0xD8) (shufDwords Y 0xD8)
  sX S D := XBinOp.eval .punpckldq S D
  sY S D := XBinOp.eval .punpckhdq S D
  mm := mont2V
  pa e := 2 * e
  pb e := 2 * e + 1
  zl e := e

theorem sh1_ok : ShapeOk sh1 where
  gath X Y e he := by
    obtain ⟨x0, x1, x2, x3⟩ := dword_shufD8 X
    obtain ⟨y0, y1, y2, y3⟩ := dword_shufD8 Y
    have l := fun i (hi : i < 4) => dword_punpcklqdq (shufDwords X 0xD8) (shufDwords Y 0xD8) hi
    have h := fun i (hi : i < 4) => dword_punpckhqdq (shufDwords X 0xD8) (shufDwords Y 0xD8) hi
    rcases cases4 he with rfl | rfl | rfl | rfl
    · exact ⟨(l 0 (by decide)).trans x0, (h 0 (by decide)).trans x2⟩
    · exact ⟨(l 1 (by decide)).trans x1, (h 1 (by decide)).trans x3⟩
    · exact ⟨(l 2 (by decide)).trans y0, (h 2 (by decide)).trans y2⟩
    · exact ⟨(l 3 (by decide)).trans y1, (h 3 (by decide)).trans y3⟩
  scat S D e he := by
    rcases cases4 he with rfl | rfl | rfl | rfl
    · exact ⟨dword_ofDwords_0 .., dword_ofDwords_1 ..⟩
    · exact ⟨dword_ofDwords_2 .., dword_ofDwords_3 ..⟩
    · exact ⟨dword_ofDwords_0 .., dword_ofDwords_1 ..⟩
    · exact ⟨dword_ofDwords_2 .., dword_ofDwords_3 ..⟩
  mont _ _ hb _ hi := dword_mont2V hb hi
  cover := by decide
  lt := by decide

/-! ## Four butterflies -/

/-- `2q + 1`, for the differences of `NTT`. -/
abbrev fwdC1 : BitVec 32 := 16760835#32

/-- `128q + 1`, for the differences of `NTT⁻¹`. -/
abbrev invC1 : BitVec 32 := 1072693377#32

/-- The sums of `NTT`. -/
def fwdS (sh : Shape) (X Y Z : BitVec 128) : BitVec 128 := sumV (sh.gA X Y) (sh.mm (sh.gB X Y) Z)

/-- The differences of `NTT`. -/
def fwdD (sh : Shape) (X Y Z : BitVec 128) : BitVec 128 := difV (sh.gA X Y) (sh.mm (sh.gB X Y) Z) (bc fwdC1)

/-- The vector `NTT` stores at `[eax]`. -/
def fwdX (sh : Shape) (X Y Z : BitVec 128) : BitVec 128 := sh.sX (fwdS sh X Y Z) (fwdD sh X Y Z)

/-- The vector `NTT` stores at `[eax + d]`. -/
def fwdY (sh : Shape) (X Y Z : BitVec 128) : BitVec 128 := sh.sY (fwdS sh X Y Z) (fwdD sh X Y Z)

/-- The sums of `NTT⁻¹`. -/
def invS (sh : Shape) (X Y : BitVec 128) : BitVec 128 := sumV (sh.gA X Y) (sh.gB X Y)

/-- The differences of `NTT⁻¹`, times the zetas. -/
def invD (sh : Shape) (X Y Z : BitVec 128) : BitVec 128 := sh.mm (difV (sh.gA X Y) (sh.gB X Y) (bc invC1)) Z

def invX (sh : Shape) (X Y Z : BitVec 128) : BitVec 128 := sh.sX (invS sh X Y) (invD sh X Y Z)

def invY (sh : Shape) (X Y Z : BitVec 128) : BitVec 128 := sh.sY (invS sh X Y) (invD sh X Y Z)

/-- The vectors `FX X Y Z` and `FY X Y Z` hold what the butterflies of the
positions leave: from coefficients that stand for those of `f` (`idx p` at
position `p`), with zetas `ζ e` in Montgomery form, coefficients that stand
for those of `G`, whose pairs are `sS` and `sD` of those of `f`. -/
def NewOk (sh : Shape) (FX FY : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128)
    (sS sD : Zq → Zq → Zq → Zq) (bd bd' : Nat) : Prop :=
  ∀ (f G : Poly) (idx : Nat → Nat) (Z : BitVec 128) (ζ : Nat → Zq),
    (∀ e < 4, (dword Z (sh.zl e)).toNat = (ζ e).val * 2 ^ 32 % q) →
    (∀ e < 4, G[idx (sh.pa e)]! = sS f[idx (sh.pa e)]! f[idx (sh.pb e)]! (ζ e) ∧
      G[idx (sh.pb e)]! = sD f[idx (sh.pa e)]! f[idx (sh.pb e)]! (ζ e)) →
    ∀ X Y, (∀ p < 8, Lz bd (pos X Y p).toNat f[idx p]!) →
      ∀ p < 8, Lz bd' (pos (FX X Y Z) (FY X Y Z) p).toNat G[idx p]!

theorem fwd_new (sh : Shape) (ok : ShapeOk sh) {bd : Nat} (hbd : bd ≤ 15) :
    NewOk sh (fwdX sh) (fwdY sh) (fun x y ζ => x + ζ * y) (fun x y ζ => x - ζ * y) bd (bd + 2) := by
  intro f G idx Z ζ hz hG X Y hV p hp
  obtain ⟨e, he, hpe⟩ := ok.cover p hp
  obtain ⟨ga, gb⟩ := ok.gath X Y e he
  obtain ⟨sa, sb⟩ := ok.scat (fwdS sh X Y Z) (fwdD sh X Y Z) e he
  obtain ⟨la, lb⟩ := ok.lt e he
  have hA := hV _ la
  have hB := hV _ lb
  have hq15 : bd * q ≤ 15 * q := Nat.mul_le_mul_right q hbd
  have hb32 : ∀ i < 4, (dword (sh.gB X Y) i).toNat * (dword Z (sh.zl i)).toNat < q * 2 ^ 32 := fun i hi => by
    rw [(ok.gath X Y i hi).2, hz i hi]
    exact prod_lt (Nat.lt_of_lt_of_le (hV _ (ok.lt i hi).2).1 (Nat.le_trans hq15 (by decide)))
      (Nat.mod_lt _ (by decide))
  have ht := ok.mont _ Z hb32 e he
  rw [gb, hz e he] at ht
  have key := f_ok (ζ := ζ e) hbd hA hB
  have hlt := mont_lt (prod_lt (Nat.lt_of_lt_of_le hB.1 (Nat.le_trans hq15 (by decide)))
    (Nat.mod_lt ((ζ e).val * 2 ^ 32) (by decide : 0 < q)))
  have ha15 : (pos X Y (sh.pa e)).toNat < 15 * 8380417 := Nat.lt_of_lt_of_le hA.1 hq15
  have hlt' : (dword (sh.mm (sh.gB X Y) Z) e).toNat < 2 * 8380417 := by rw [ht]; exact hlt
  have hS : (dword (fwdS sh X Y Z) e).toNat =
      fS (pos X Y (sh.pa e)).toNat (pos X Y (sh.pb e)).toNat ((ζ e).val * 2 ^ 32 % q) := by
    rw [fwdS, sumV, dword_paddd _ _ he, BitVec.toNat_add, ga, Nat.mod_eq_of_lt (by omega_using [hlt', ha15]), ht, fS]
  have hD : (dword (fwdD sh X Y Z) e).toNat =
      fD (pos X Y (sh.pa e)).toNat (pos X Y (sh.pb e)).toNat ((ζ e).val * 2 ^ 32 % q) := by
    rw [fwdD, dword_difV _ _ _ he, subL_toNat (c := 2 * q) rfl
      (by rw [ga]; show _ ≤ _ + 2 * 8380417; omega_using [hlt'])
      (by rw [ga]; show _ + 2 * 8380417 < 2 ^ 32; omega_using [ha15]), ga, ht, fD]
  rcases hpe with rfl | rfl
  · rw [fwdX, fwdY, sa, hS, (hG e he).1]; exact key.1
  · rw [fwdX, fwdY, sb, hD, (hG e he).2]; exact key.2

theorem inv_new (sh : Shape) (ok : ShapeOk sh) {bd : Nat} (h1 : 1 ≤ bd) (hbd : bd ≤ 128) :
    NewOk sh (invX sh) (invY sh) (fun x y _ => x + y) (fun x y ζ => ζ * (x - y)) bd (2 * bd) := by
  intro f G idx Z ζ hz hG X Y hV p hp
  obtain ⟨e, he, hpe⟩ := ok.cover p hp
  obtain ⟨ga, gb⟩ := ok.gath X Y e he
  obtain ⟨sa, sb⟩ := ok.scat (invS sh X Y) (invD sh X Y Z) e he
  obtain ⟨la, lb⟩ := ok.lt e he
  have hA := hV _ la
  have hB := hV _ lb
  have hq128 : bd * q ≤ 128 * q := Nat.mul_le_mul_right q hbd
  have hsub : ∀ i < 4, (dword (difV (sh.gA X Y) (sh.gB X Y) (bc invC1)) i).toNat =
      (pos X Y (sh.pa i)).toNat + 128 * q - (pos X Y (sh.pb i)).toNat := fun i hi => by
    have a1 := Nat.lt_of_lt_of_le (hV _ (ok.lt i hi).1).1 hq128
    have b1 := Nat.lt_of_lt_of_le (hV _ (ok.lt i hi).2).1 hq128
    rw [q_eq] at a1 b1
    rw [dword_difV _ _ _ hi, subL_toNat (c := 128 * q) rfl
      (by rw [(ok.gath X Y i hi).1, (ok.gath X Y i hi).2, q_eq]; omega_using [a1, b1])
      (by rw [(ok.gath X Y i hi).1, q_eq]; omega_using [a1]), (ok.gath X Y i hi).1, (ok.gath X Y i hi).2]
  have hb32 : ∀ i < 4, (dword (difV (sh.gA X Y) (sh.gB X Y) (bc invC1)) i).toNat * (dword Z (sh.zl i)).toNat <
      q * 2 ^ 32 := fun i hi => by
    have a1 := Nat.lt_of_lt_of_le (hV _ (ok.lt i hi).1).1 hq128
    rw [q_eq] at a1
    rw [hsub i hi, hz i hi]
    exact prod_lt (by rw [q_eq]; omega_using [a1]) (Nat.mod_lt _ (by decide))
  have ht := ok.mont _ Z hb32 e he
  rw [hsub e he, hz e he] at ht
  have key := i_ok (ζ := ζ e) h1 hbd hA hB
  have a1 := Nat.lt_of_lt_of_le hA.1 hq128
  have b1 := Nat.lt_of_lt_of_le hB.1 hq128
  rw [q_eq] at a1 b1
  have hS : (dword (invS sh X Y) e).toNat =
      iS (pos X Y (sh.pa e)).toNat (pos X Y (sh.pb e)).toNat ((ζ e).val * 2 ^ 32 % q) := by
    rw [invS, sumV, dword_paddd _ _ he, BitVec.toNat_add, ga, gb, iS]
    exact Nat.mod_eq_of_lt (by omega_using [a1, b1])
  rcases hpe with rfl | rfl
  · rw [invX, invY, sa, hS, (hG e he).1]; exact key.1
  · rw [invX, invY, sb, invD, ht, (hG e he).2]; exact key.2

/-! ## The last passes -/

/-- `finCore` on a doubleword. -/
def finL (x : BitVec 32) : BitVec 32 :=
  csubL ((x &&& 8388607#32) + ((x >>> 23) <<< 13) + ((x >>> 23) ^^^ 4294967295#32) + 1#32)

theorem finL_toNat {x : BitVec 32} (hx : x.toNat < 17 * q) : (finL x).toNat = x.toNat % q := by
  obtain ⟨h1, h2⟩ := fin_ok hx
  have hk : (x >>> 23).toNat = x.toNat / 8388608 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hlo : (x &&& 8388607#32).toNat = x.toNat % 8388608 := by
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 23
  have hsh : ((x >>> 23) <<< 13).toNat = x.toNat / 8388608 * 8192 := by
    rw [BitVec.toNat_shiftLeft, hk, Nat.shiftLeft_eq]
    rw [q_eq] at hx
    exact Nat.mod_eq_of_lt (by omega_using [hx])
  have hxo : ((x >>> 23) ^^^ 4294967295#32).toNat = 2 ^ 32 - 1 - x.toNat / 8388608 := by
    rw [show (4294967295#32 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.xor_allOnes, BitVec.toNat_not, hk]
  have e : ((x &&& 8388607#32) + ((x >>> 23) <<< 13) + ((x >>> 23) ^^^ 4294967295#32) + 1#32).toNat =
      finN x.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, hlo, hsh, hxo, finN]
    rw [q_eq] at hx
    simp only [show (1#32 : BitVec 32).toNat = 1 from rfl]
    omega_using [hx]
  rw [finL, csubL_toNat (by rw [e]; exact h1), e, condSub_eq h1, h2]

/-- The register `finCore` leaves. -/
def finV (x : BitVec 128) : BitVec 128 :=
  let k := XShiftOp.eval .psrld x 23
  let y := XBinOp.eval .paddd (XBinOp.eval .paddd (XBinOp.eval .paddd (XBinOp.eval .pand x (bc 8388607#32))
    (XShiftOp.eval .pslld k 13)) (XBinOp.eval .pxor k onesV)) (bc 4286586880#32)
  XBinOp.eval .paddd y (XBinOp.eval .pandn (XBinOp.eval .paddd (XShiftOp.eval .psrld y 31) onesV) qV)

theorem dword_finV (x : BitVec 128) {i : Nat} (hi : i < 4) : dword (finV x) i = finL (dword x i) := by
  simp only [finV, dword_paddd _ _ hi, dword_pandn _ _ hi, dword_pxor, dword_pand,
    dword_psrld _ _ (show (31 : BitVec 8).toNat < 32 by decide) hi,
    dword_psrld _ _ (show (23 : BitVec 8).toNat < 32 by decide) hi,
    dword_pslld _ _ (show (13 : BitVec 8).toNat < 32 by decide) hi, onesV, qV, dword_bc _ hi, finL, csubL]
  rw [show (4286586880#32 : BitVec 32) = 1#32 + negqB by decide, ← BitVec.add_assoc]
  rfl

/-- What a pass leaves: the doublewords of `F x` are `red` of what those of `x` stand for. -/
def PassLane (bd : Nat) (F : BitVec 128 → BitVec 128) (red : Zq → Zq) : Prop :=
  ∀ (x : BitVec 128) (ys : Nat → Zq), (∀ i < 4, Lz bd (dword x i).toNat (ys i)) → ∀ j < 4,
    (dword (F x) j).toNat = (red (ys j)).val

theorem fin_lanes : PassLane 17 finV id := fun x ys h j hj => by
  rw [dword_finV _ hj, finL_toNat (h j hj).1, (h j hj).2]; rfl

/-- `8347681 · 2³² mod q`, in each doubleword. -/
abbrev scaleV : BitVec 128 := bc 16382#32

/-- The register the last pass of `NTT⁻¹` leaves. -/
def scaleX (x : BitVec 128) : BitVec 128 := csubV (montV x scaleV)

theorem scale_lanes : PassLane 256 scaleX (· * c256) := fun x ys h j hj => by
  have hb : ∀ i < 4, (dword x i).toNat * (dword scaleV (2 * (i / 2))).toNat < q * 2 ^ 32 := fun i hi => by
    have := (h i hi).1
    rw [dword_bc _ (by omega_using [hi]), show (16382#32 : BitVec 32).toNat = 16382 from rfl]
    rw [q_eq] at this ⊢
    omega_using [this]
  have e := dword_montV hb hj
  rw [dword_bc _ (by omega_using [hj]), show (16382#32 : BitVec 32).toNat = 16382 from rfl] at e
  obtain ⟨s1, s2⟩ := scale_ok (h j hj)
  rw [scaleX, dword_csubV _ hj, csubL_toNat (by rw [e]; exact s1), e, condSub_eq s1, s2]

end VG.Proof.MlDsa.X86.Arith
