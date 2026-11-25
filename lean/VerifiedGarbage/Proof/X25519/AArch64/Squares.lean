module

-- separate module: the vector code is checked apart from the scalar code of an iteration, which changes apart from it.

public import VerifiedGarbage.Impl.X25519.AArch64.Squares
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
public import VerifiedGarbage.Spec.X25519
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Range

/-!
# The squares modulo 2²⁵⁵ - 19 in AdvSIMD

Untrusted: everything here is checked by Lean. `squares_ok`: the two results,
five limbs each, are the squares modulo `P`, their limbs just above 51 bits.
First the arithmetic in numbers: an element's limbs `l k` (low) and `h k`
(high) are at bits `51 k` and `51 k + 26`; then the 64-bit lanes (`D`) and
32-bit words (`W`) of the operations' results, the parts of the code one by
one, and the constants and callee-saved registers in the working space.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Squares

open VG VG.AArch64 VG.Impl.X25519.AArch64.Squares
open VG.Spec.X25519 (P)
open VG.Proof.Curve448.AArch64.Neon (trn1_0 trn1_1 trn2_0 trn2_1 uzp1_0 uzp1_1 uzp1_2 uzp1_3 vword_lo vdword_and
  map2_0 map2_1 extv ext8_0 ext8_1 ext8_2 ext8_3 umlal_lane umull_lane)
open VG.Proof.Ed25519.AArch64 (Scr off word fe Outside workSize workSize_ge workSize_le contains_scWith ofs ofs_off ofs_off')
open VG.Proof.Ed25519.Word64

variable {large : Bool}

/-! ## The arithmetic -/

/-- The element of the limbs `l k` and `h k`. -/
def limbs (l0 h0 l1 h1 l2 h2 l3 h3 l4 h4 : Nat) : Nat :=
  (l0 + 2 ^ 26 * h0) + 2 ^ 51 * (l1 + 2 ^ 26 * h1) + 2 ^ 102 * (l2 + 2 ^ 26 * h2) + 2 ^ 153 * (l3 + 2 ^ 26 * h3) +
    2 ^ 204 * (l4 + 2 ^ 26 * h4)

/-- The value of the columns. -/
def colVal (e0 c0 e1 c1 e2 c2 e3 c3 e4 c4 : Nat) : Nat := limbs e0 c0 e1 c1 e2 c2 e3 c3 e4 c4

/-- A square's columns. -/
theorem columns_value (l0 h0 l1 h1 l2 h2 l3 h3 l4 h4 : Nat) :
    colVal
      (2 * (2 * h0 * (19 * h4) + 2 * h1 * (19 * h3) + h2 * (19 * h2)) + (l0 * l0 + 2 * l1 * (19 * l4) + 2 * l2 * (19 * l3)))
      (2 * h0 * l0 + 2 * h1 * (19 * l4) + 2 * l1 * (19 * h4) + 2 * h2 * (19 * l3) + 2 * l2 * (19 * h3))
      (2 * (h0 * h0 + 2 * h1 * (19 * h4) + 2 * h2 * (19 * h3)) + (2 * l0 * l1 + 2 * l2 * (19 * l4) + l3 * (19 * l3)))
      (2 * h0 * l1 + 2 * l0 * h1 + 2 * h2 * (19 * l4) + 2 * l2 * (19 * h4) + 2 * h3 * (19 * l3))
      (2 * (2 * h0 * h1 + 2 * h2 * (19 * h4) + h3 * (19 * h3)) + (2 * l0 * l2 + l1 * l1 + 2 * l3 * (19 * l4)))
      (2 * h0 * l2 + 2 * l0 * h2 + 2 * h1 * l1 + 2 * h3 * (19 * l4) + 2 * l3 * (19 * h4))
      (2 * (2 * h0 * h2 + h1 * h1 + 2 * h3 * (19 * h4)) + (2 * l0 * l3 + 2 * l1 * l2 + l4 * (19 * l4)))
      (2 * h0 * l3 + 2 * l0 * h3 + 2 * h1 * l2 + 2 * l1 * h2 + 2 * h4 * (19 * l4))
      (2 * (2 * h0 * h3 + 2 * h1 * h2 + h4 * (19 * h4)) + (2 * l0 * l4 + 2 * l1 * l3 + l2 * l2))
      (2 * h0 * l4 + 2 * l0 * h4 + 2 * h1 * l3 + 2 * l1 * h3 + 2 * h2 * l2) % P =
    limbs l0 h0 l1 h1 l2 h2 l3 h3 l4 h4 * limbs l0 h0 l1 h1 l2 h2 l3 h3 l4 h4 % P := by
  rw [← Nat.add_mul_mod_self_left _ P (
      2 ^ 1 * (2 * h0 * h4) + 2 ^ 1 * (2 * h1 * h3) + 2 ^ 0 * (2 * l1 * l4) + 2 ^ 26 * (2 * l1 * h4 + 2 * h1 *
        l4) + 2 ^ 52 * (2 * h1 * h4) + 2 ^ 1 * (h2 * h2) + 2 ^ 0 * (2 * l2 * l3) + 2 ^ 26 * (2 * l2 * h3 + 2 *
        h2 * l3) + 2 ^ 52 * (2 * h2 * h3) + 2 ^ 51 * (2 * l2 * l4) + 2 ^ 77 * (2 * l2 * h4 + 2 * h2 * l4) + 2 ^
        103 * (2 * h2 * h4) + 2 ^ 51 * (l3 * l3) + 2 ^ 77 * (2 * l3 * h3) + 2 ^ 103 * (h3 * h3) + 2 ^ 102 * (2 *
        l3 * l4) + 2 ^ 128 * (2 * l3 * h4 + 2 * h3 * l4) + 2 ^ 154 * (2 * h3 * h4) + 2 ^ 153 * (l4 * l4) + 2 ^
        179 * (2 * l4 * h4) + 2 ^ 205 * (h4 * h4))]
  refine congrArg (· % P) ?_
  simp only [colVal, limbs, P]
  ring

/-! ## The carries -/

theorem carry1_value (e0 c0 e1 c1 e2 c2 e3 c3 e4 c4 : Nat) :
    (e0 % 2 ^ 26 + 19 * (c4 / 2 ^ 25) + 2 ^ 26 * (c0 % 2 ^ 25 + e0 / 2 ^ 26)) +
      2 ^ 51 * (e1 % 2 ^ 26 + c0 / 2 ^ 25 + 2 ^ 26 * (c1 % 2 ^ 25 + e1 / 2 ^ 26)) +
      2 ^ 102 * (e2 % 2 ^ 26 + c1 / 2 ^ 25 + 2 ^ 26 * (c2 % 2 ^ 25 + e2 / 2 ^ 26)) +
      2 ^ 153 * (e3 % 2 ^ 26 + c2 / 2 ^ 25 + 2 ^ 26 * (c3 % 2 ^ 25 + e3 / 2 ^ 26)) +
      2 ^ 204 * (e4 % 2 ^ 26 + c3 / 2 ^ 25 + 2 ^ 26 * (c4 % 2 ^ 25 + e4 / 2 ^ 26)) + P * (c4 / 2 ^ 25) =
    colVal e0 c0 e1 c1 e2 c2 e3 c3 e4 c4 := by
  simp only [colVal, limbs, P]
  omega_using []

theorem carry2_value (l0 l1 l2 l3 l4 : Nat) :
    (l0 % 2 ^ 51 + 19 * (l4 / 2 ^ 51)) + 2 ^ 51 * (l1 % 2 ^ 51 + l0 / 2 ^ 51) + 2 ^ 102 * (l2 % 2 ^ 51 + l1 / 2 ^ 51) +
      2 ^ 153 * (l3 % 2 ^ 51 + l2 / 2 ^ 51) + 2 ^ 204 * (l4 % 2 ^ 51 + l3 / 2 ^ 51) + P * (l4 / 2 ^ 51) =
    l0 + 2 ^ 51 * l1 + 2 ^ 102 * l2 + 2 ^ 153 * l3 + 2 ^ 204 * l4 := by
  simp only [P]
  omega_using []

/-- The limbs of the words `w0`–`w3`. -/
theorem split_value {w0 w1 w2 w3 : Nat} (h0 : w0 < 2 ^ 64) (h2 : w2 < 2 ^ 64) :
    limbs (w0 % 2 ^ 26) (w0 / 2 ^ 26 % 2 ^ 25) ((w1 * 2 ^ 13 % 2 ^ 64 + w0 / 2 ^ 51) % 2 ^ 26) (w1 / 2 ^ 13 % 2 ^ 25)
      (w1 / 2 ^ 38) (w2 % 2 ^ 25) (w2 / 2 ^ 25 % 2 ^ 26) ((w3 * 2 ^ 13 % 2 ^ 64 + w2 / 2 ^ 51) % 2 ^ 25)
      (w3 / 2 ^ 12 % 2 ^ 26) (w3 / 2 ^ 38) = w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3 := by
  have e1 : (w1 * 2 ^ 13 % 2 ^ 64 + w0 / 2 ^ 51) % 2 ^ 26 = w0 / 2 ^ 51 + 2 ^ 13 * (w1 % 2 ^ 13) := by omega_using [h0]
  have e3 : (w3 * 2 ^ 13 % 2 ^ 64 + w2 / 2 ^ 51) % 2 ^ 25 = w2 / 2 ^ 51 + 2 ^ 13 * (w3 % 2 ^ 12) := by omega_using [h2]
  have d0 : w0 = w0 % 2 ^ 26 + 2 ^ 26 * (w0 / 2 ^ 26 % 2 ^ 25) + 2 ^ 51 * (w0 / 2 ^ 51) := by omega_using []
  have d1 : w1 = w1 % 2 ^ 13 + 2 ^ 13 * (w1 / 2 ^ 13 % 2 ^ 25) + 2 ^ 38 * (w1 / 2 ^ 38) := by omega_using []
  have d2 : w2 = w2 % 2 ^ 25 + 2 ^ 25 * (w2 / 2 ^ 25 % 2 ^ 26) + 2 ^ 51 * (w2 / 2 ^ 51) := by omega_using []
  have d3 : w3 = w3 % 2 ^ 12 + 2 ^ 12 * (w3 / 2 ^ 12 % 2 ^ 26) + 2 ^ 38 * (w3 / 2 ^ 38) := by omega_using []
  rw [e1, e3, limbs]
  generalize w0 % 2 ^ 26 = a0 at *
  generalize w0 / 2 ^ 26 % 2 ^ 25 = a1 at *
  generalize w0 / 2 ^ 51 = a2 at *
  generalize w1 % 2 ^ 13 = b0 at *
  generalize w1 / 2 ^ 13 % 2 ^ 25 = b1 at *
  generalize w1 / 2 ^ 38 = b2 at *
  generalize w2 % 2 ^ 25 = c0 at *
  generalize w2 / 2 ^ 25 % 2 ^ 26 = c1 at *
  generalize w2 / 2 ^ 51 = c2 at *
  generalize w3 % 2 ^ 12 = f0 at *
  generalize w3 / 2 ^ 12 % 2 ^ 26 = f1 at *
  generalize w3 / 2 ^ 38 = f2 at *
  clear e1 e3
  subst d0 d1 d2 d3
  omega_using []

/-! ## Lanes -/

/-- The 64-bit lane `e`, the 32-bit word `c`. -/
def D (x : BitVec 128) (e : Nat) : Nat := (vdword x e).toNat
def W (x : BitVec 128) (c : Nat) : Nat := (vword x c).toNat

theorem D_lt (x : BitVec 128) (e : Nat) : D x e < 2 ^ 64 := (vdword x e).isLt

theorem lanes2 {e : Nat} (he : e < 2) : e = 0 ∨ e = 1 := by omega_using [he]

theorem map2_d {f : (w : Nat) → BitVec w → BitVec w → BitVec w} {x y : BitVec 128} {e : Nat} (he : e < 2) :
    vdword (VArr.d2.map2 f x y) e = f 64 (vdword x e) (vdword y e) := by
  rcases lanes2 he with rfl | rfl
  · exact map2_0 _ _ _
  · exact map2_1 _ _ _

theorem D_add (x y : BitVec 128) {e : Nat} (he : e < 2) :
    D (VArr.d2.map2 (fun _ a b => a + b) x y) e = (D x e + D y e) % 2 ^ 64 := by
  rw [D, map2_d he, BitVec.toNat_add]; rfl

theorem D_ushr (y x : BitVec 128) (k : Nat) {e : Nat} (he : e < 2) :
    D (VArr.d2.map2 (fun w a b => VShiftOp.eval .ushr k w a b) y x) e = D x e / 2 ^ k := by
  rw [D, map2_d he]
  simp only [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, D]

theorem D_shl (y x : BitVec 128) (k : Nat) {e : Nat} (he : e < 2) :
    D (VArr.d2.map2 (fun w a b => VShiftOp.eval .shl k w a b) y x) e = D x e * 2 ^ k % 2 ^ 64 := by
  rw [D, map2_d he]
  simp only [VShiftOp.eval, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, D]

theorem sri_bits (x : BitVec 64) : ((x <<< 13) &&& ~~~(BitVec.allOnes 64 >>> 51)) = x <<< 13 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_allOnes, hi, decide_true, Bool.true_and]
  by_cases h : i < 13
  · simp only [h, decide_true, Bool.not_true, Bool.false_and]
  · rw [decide_eq_false (by omega_using [h] : ¬ 51 + i < 64), Bool.not_false, Bool.and_true]

/-- `shl 13`, then `sri 51` of another register. -/
theorem D_sri (z x y : BitVec 128) {e : Nat} (he : e < 2) :
    D (VArr.d2.map2 (fun w a b => VShiftOp.eval .sri 51 w a b)
      (VArr.d2.map2 (fun w a b => VShiftOp.eval .shl 13 w a b) z x) y) e = D x e * 2 ^ 13 % 2 ^ 64 + D y e / 2 ^ 51 := by
  rw [D, map2_d he, map2_d he]
  simp only [VShiftOp.eval]
  have h := (vdword y e).isLt
  rw [sri_bits, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, show 2 ^ 64 = 2 ^ 51 * 2 ^ 13 from rfl, Nat.mul_mod_mul_right]
  rw [show (vdword x e).toNat % 2 ^ 51 * 2 ^ 13 = ((vdword x e).toNat % 2 ^ 51) <<< 13 from (Nat.shiftLeft_eq _ _).symm,
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega_using [h]), Nat.shiftLeft_eq, D, D, Nat.mul_mod_mul_right]

theorem D_and (x m : BitVec 128) {k e : Nat} (hm : D m e = 2 ^ k - 1) : D (x &&& m) e = D x e % 2 ^ k := by
  rw [D, vdword_and, BitVec.toNat_and, show (vdword m e).toNat = 2 ^ k - 1 from hm, Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem D_trn1 (x y : BitVec 128) {e : Nat} (he : e < 2) :
    D (VPermOp.eval .trn1 .d2 x y) e = if e = 0 then D x 0 else D y 0 := by
  rcases lanes2 he with rfl | rfl
  · rw [D, trn1_0]; rfl
  · rw [D, trn1_1]; rfl

theorem D_trn2 (x y : BitVec 128) {e : Nat} (he : e < 2) :
    D (VPermOp.eval .trn2 .d2 x y) e = if e = 0 then D x 1 else D y 1 := by
  rcases lanes2 he with rfl | rfl
  · rw [D, trn2_0]; rfl
  · rw [D, trn2_1]; rfl

/-- `uzp1` of the low and high limbs: the low halves' words, then the high halves'. -/
theorem W_uzp (x y : BitVec 128) {e : Nat} (he : e < 2) (hx : D x e < 2 ^ 32) (hy : D y e < 2 ^ 32) :
    W (VPermOp.eval .uzp1 .s4 x y) e = D x e ∧ W (VPermOp.eval .uzp1 .s4 x y) (2 + e) = D y e := by
  simp only [W, D] at *
  rcases lanes2 he with rfl | rfl
  · rw [uzp1_0, show (2 + 0) = 2 from rfl, uzp1_2, vword_lo x 0, vword_lo y 0, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
    exact ⟨rfl, rfl⟩
  · rw [uzp1_1, show (2 + 1) = 3 from rfl, uzp1_3, show (2 : Nat) = 2 * 1 from rfl, vword_lo x 1, vword_lo y 1,
      Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
    exact ⟨rfl, rfl⟩

theorem W_dbl (x : BitVec 128) {c : Nat} (hc : c < 4) (h : W x c < 2 ^ 31) :
    W (VArr.s4.map2 (fun _ a b => a + b) x x) c = 2 * W x c := by
  simp only [W] at *
  rw [vword_map2 _ _ _ hc, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega_using [h])]
  omega_using []

theorem W_ext (x : BitVec 128) : W (((x ++ x) >>> (8 * 8)).extractLsb' 0 128) 0 = W x 2 ∧
    W (((x ++ x) >>> (8 * 8)).extractLsb' 0 128) 1 = W x 3 ∧ W (((x ++ x) >>> (8 * 8)).extractLsb' 0 128) 2 = W x 0 ∧
    W (((x ++ x) >>> (8 * 8)).extractLsb' 0 128) 3 = W x 1 :=
  ⟨congrArg _ (ext8_0 x x), congrArg _ (ext8_1 x x), congrArg _ (ext8_2 x x), congrArg _ (ext8_3 x x)⟩

theorem W_mul (x k : BitVec 128) {c : Nat} (hc : c < 4) (hk : W k c = 19) (h : W x c < 2 ^ 27) :
    W (VArr.s4.map2 (fun _ a b => a * b) x k) c = 19 * W x c := by
  simp only [W] at *
  rw [vword_map2 _ _ _ hc, BitVec.toNat_mul, hk, Nat.mod_eq_of_lt (by omega_using [h])]
  omega_using []

/-! ## Vector code -/

/-- Only the vector registers `ds` change. -/
structure VK (ds : List VReg) (s t : State) : Prop where
  v : ∀ r, r ∉ ds → t.v r = s.v r
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem VK.trans {ds : List VReg} {s t u : State} (h : VK ds s t) (k : VK ds t u) : VK ds s u :=
  ⟨fun r hr => (k.v r hr).trans (h.v r hr), k.gpr.trans h.gpr, k.mem.trans h.mem, k.rd.trans h.rd, k.wr.trans h.wr,
    k.sp.trans h.sp⟩

theorem VK.mono {ds ds' : List VReg} {s t : State} (h : VK ds s t) (hd : ∀ r ∈ ds, r ∈ ds') : VK ds' s t :=
  ⟨fun r hr => h.v r fun hm => hr (hd r hm), h.gpr, h.mem, h.rd, h.wr, h.sp⟩

theorem exec_vo {op : VOp} {s : State} {d : VReg} {x : BitVec 128} (h : op.eval s = some (d, x)) :
    isa.exec (.vop op) s = some (s.setV d x) := by
  show (op.eval s).map (fun p => s.setV p.1 p.2) = _
  rw [h]; rfl

/-! ## The products -/

abbrev hp (hi : Bool) : Nat := if hi then 2 else 0

/-- Lane `e` of a product, and of a sum of products. -/
def tval (v : VReg → BitVec 128) (p : Term) (e : Nat) : Nat := W (v p.2.1) (hp p.1 + e) * W (v p.2.2) (hp p.1 + e)
def tsum (v : VReg → BitVec 128) (ps : List Term) (e : Nat) : Nat := (ps.map fun p => tval v p e).sum

theorem vdword_of (a b : BitVec 64) {e : Nat} (he : e < 2) : vdword (ofVDwords a b) e = if e = 0 then a else b := by
  rcases lanes2 he with rfl | rfl
  · rw [vdword_ofVDwords_0]; rfl
  · rw [vdword_ofVDwords_1]; rfl

theorem mla_D (s : State) (d : VReg) (p : Term) : ∃ x, isa.exec (mla d p) s = some (s.setV d x) ∧
    ∀ e < 2, D x e = (D (s.v d) e + tval s.v p e) % 2 ^ 64 := by
  refine ⟨_, exec_vo rfl, fun e he => ?_⟩
  rcases lanes2 he with rfl | rfl <;>
    simp only [D, vdword_of _ _ he, ite_true, show (1 : Nat) ≠ 0 by decide, ite_false, umlal_lane, tval, W]

theorem mul_D (s : State) (d : VReg) (p : Term) :
    ∃ x, isa.exec (vo (.umull p.1 d p.2.1 p.2.2)) s = some (s.setV d x) ∧ ∀ e < 2, D x e = tval s.v p e := by
  refine ⟨_, exec_vo rfl, fun e he => ?_⟩
  rcases lanes2 he with rfl | rfl <;>
    simp only [D, vdword_of _ _ he, ite_true, show (1 : Nat) ≠ 0 by decide, ite_false, umull_lane, tval, W]

/-- The products `ps` read no register `d`. -/
abbrev Apart (d : VReg) (ps : List Term) : Prop := ∀ p ∈ ps, p.2.1 ≠ d ∧ p.2.2 ≠ d

theorem tsum_congr {v v' : VReg → BitVec 128} {d : VReg} {ps : List Term} (h : Apart d ps)
    (hv : ∀ r, r ≠ d → v' r = v r) (e : Nat) : tsum v' ps e = tsum v ps e := by
  refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
  rw [tval, tval, hv _ (h p hp).1, hv _ (h p hp).2]

theorem mlas_ok (d : VReg) : ∀ (ps : List Term) (s : State), Apart d ps →
    WP isa (.block (ps.map (mla d))) s fun t => VK [d] s t ∧
      ∀ e < 2, D (t.v d) e % 2 ^ 64 = (D (s.v d) e + tsum s.v ps e) % 2 ^ 64
  | [], s, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩, fun e _ => by simp [tsum]⟩
  | p :: ps, s, h => by
    obtain ⟨x, hx, lx⟩ := mla_D s d p
    refine WP.block_cons_iff.mpr ⟨_, hx, ?_⟩
    refine WP.mono (mlas_ok d ps _ fun q hq => h q (List.mem_cons_of_mem _ hq)) fun t ⟨k, l⟩ => ⟨⟨fun r hr => ?_, k.gpr,
      k.mem, k.rd, k.wr, k.sp⟩, fun e he => ?_⟩
    · rw [k.v r hr, RegUpd.v_setV_of_ne _ _ (by simpa using hr)]
    · rw [l e he, RegUpd.v_setV_self, lx e he, tsum_congr (fun q hq => h q (List.mem_cons_of_mem _ hq))
        (fun r hr => RegUpd.v_setV_of_ne _ _ hr) e, Nat.mod_add_mod, Nat.add_assoc]
      rfl

theorem msum_ok (d : VReg) {ps : List Term} (hps : ps ≠ []) (s : State) (h : Apart d ps) :
    WP isa (.block (msum d ps)) s fun t => VK [d] s t ∧ ∀ e < 2, D (t.v d) e = tsum s.v ps e % 2 ^ 64 := by
  cases ps with
  | nil => exact absurd rfl hps
  | cons p ps =>
    obtain ⟨x, hx, lx⟩ := mul_D s d p
    refine WP.block_cons_iff.mpr ⟨_, hx, ?_⟩
    refine WP.mono (mlas_ok d ps _ fun q hq => h q (List.mem_cons_of_mem _ hq)) fun t ⟨k, l⟩ => ⟨⟨fun r hr => ?_, k.gpr,
      k.mem, k.rd, k.wr, k.sp⟩, fun e he => ?_⟩
    · rw [k.v r hr, RegUpd.v_setV_of_ne _ _ (by simpa using hr)]
    · have e1 := l e he
      rw [Nat.mod_eq_of_lt (D_lt _ _), RegUpd.v_setV_self, lx e he, tsum_congr (fun q hq => h q (List.mem_cons_of_mem _ hq))
        (fun r hr => RegUpd.v_setV_of_ne _ _ hr) e] at e1
      exact e1

/-! ## The working space -/

/-- The constants in the working space. -/
structure Consts (m : Mem) (base : Addr) : Prop where
  k51 : ∀ e < 2, D (m.read (off base K51) 16) e = 2 ^ 51 - 1
  k26 : ∀ e < 2, D (m.read (off base K26) 16) e = 2 ^ 26 - 1
  k25 : ∀ e < 2, D (m.read (off base K25) 16) e = 2 ^ 25 - 1
  k19 : ∀ c < 4, W (m.read (off base K19) 16) c = 19

theorem read16_outside {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 16 ≤ o ∨ o + n ≤ d) (hd' : d + 16 < 2 ^ 64) : m'.read (off base d) 16 = m.read (off base d) 16 :=
  (Mem.read_congr fun i hi => (h _ (by rw [ofs_off base (by omega_using [hd', hi])]; omega_using [hd, hi])).symm).symm

theorem Consts.outside {base : Addr} {m m' : Mem} (h : Consts m base) (ho : Outside base 64 1056 m m') : Consts m' base := by
  refine ⟨fun e he => ?_, fun e he => ?_, fun e he => ?_, fun c hc => ?_⟩
  · rw [read16_outside ho (by decide) (by decide)]; exact h.k51 e he
  · rw [read16_outside ho (by decide) (by decide)]; exact h.k26 e he
  · rw [read16_outside ho (by decide) (by decide)]; exact h.k25 e he
  · rw [read16_outside ho (by decide) (by decide)]; exact h.k19 c hc

theorem exec_ldq {s : State} {base : Addr} (hs : Scr s base large) (t : VReg) {d : Nat} (h16 : d % 16 = 0)
    (hd : d + 16 ≤ 4096) : isa.exec (ldq t d) s = some (s.setV t (s.mem.read (off base d) 16)) := by
  have hr : InRegions (s.rd ++ s.wr) (off base d) 16 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_scWith (large := large) (Nat.le_trans hd (workSize_ge large))⟩
  simp only [ldq, reduceExec, addr, show d % 16 = 0 ∧ d < 4096 * 16 from ⟨h16, by omega_using [hd]⟩, and_self, ite_true,
    Option.bind_some, State.load, hs.x0]
  rw [ite_eq_left_iff.mpr fun h => absurd hr h]
  rfl

theorem exec_stq {s : State} {base : Addr} (hs : Scr s base large) (t : VReg) {d : Nat} (h16 : d % 16 = 0)
    (hd : d + 16 ≤ 4096) :
    isa.exec (stq t d) s = some { s with mem := s.mem.write (off base d) 16 (s.v t) } := by
  have hw : InRegions s.wr (off base d) 16 :=
    ⟨_, hs.wr, contains_scWith (large := large) (Nat.le_trans hd (workSize_ge large))⟩
  simp only [stq, reduceExec, addr, show d % 16 = 0 ∧ d < 4096 * 16 from ⟨h16, by omega_using [hd]⟩, and_self, ite_true,
    Option.bind_some, State.store, hs.x0]
  rw [ite_eq_left_iff.mpr fun h => absurd hw h]

theorem D_read (m : Mem) (base : Addr) (d : Nat) {e : Nat} (he : e < 2) :
    D (m.read (off base d) 16) e = (word m base (d + 8 * e)).toNat := by
  rw [D, vdword_read16 _ _ he, off, Offset.add_add]

/-- The offset of element `e`. -/
abbrev el (a b e : Nat) : Nat := if e = 0 then a else b

theorem VK.scr {ds : List VReg} {s t : State} {base : Addr} (h : VK ds s t) (hs : Scr s base large) : Scr t base large :=
  ⟨by rw [h.gpr]; exact hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem scr_setV {s : State} {base : Addr} (hs : Scr s base large) (r : VReg) (x : BitVec 128) :
    Scr (s.setV r x) base large := ⟨hs.x0, hs.wr, hs.nowrap⟩

theorem words_ok {s : State} {base : Addr} (hs : Scr s base large) (hc : Consts s.mem base) {a b : Nat}
    (ha : a % 16 = 0) (ha' : a + 32 ≤ 1024) (hb : b % 16 = 0) (hb' : b + 32 ≤ 1024) :
    WP isa (.block (words a b)) s fun t =>
      VK [.v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v30, .v31] s t ∧
      ∀ e < 2, D (t.v .v31) e = 2 ^ 26 - 1 ∧ D (t.v .v30) e = 2 ^ 25 - 1 ∧
        D (t.v .v24) e = (word s.mem base (el a b e)).toNat ∧ D (t.v .v25) e = (word s.mem base (el a b e + 8)).toNat ∧
        D (t.v .v26) e = (word s.mem base (el a b e + 16)).toNat ∧
        D (t.v .v27) e = (word s.mem base (el a b e + 24)).toNat := by
  simp only [words]
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq hs .v31 (by decide) (by decide), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (scr_setV hs _ _) .v30 (by decide) (by decide), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (scr_setV (scr_setV hs _ _) _ _) .v20 ha (by omega_using [ha']), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (scr_setV (scr_setV (scr_setV hs _ _) _ _) _ _) .v21 hb (by omega_using [hb']), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (scr_setV (scr_setV (scr_setV (scr_setV hs _ _) _ _) _ _) _ _) .v22
    (by omega_using [ha]) (by omega_using [ha']), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (scr_setV (scr_setV (scr_setV (scr_setV (scr_setV hs _ _) _ _) _ _) _ _) _ _) .v23
    (by omega_using [hb]) (by omega_using [hb']), ?_⟩
  simp only [RegUpd.mem_setV]
  generalize hA : s.mem.read (off base a) 16 = A
  generalize hB : s.mem.read (off base b) 16 = B
  generalize hA' : s.mem.read (off base (a + 16)) 16 = A'
  generalize hB' : s.mem.read (off base (b + 16)) 16 = B'
  apply WP.of_runBlock
  simp only [trn1, trn2, vo, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.eval, RegUpd.v_setV, reduceCtorEq,
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, by simp only [RegUpd.gpr_setV], by simp only [RegUpd.mem_setV], by simp only [RegUpd.rd_setV],
    by simp only [RegUpd.wr_setV], by simp only [RegUpd.sp_setV]⟩, fun e he => ⟨hc.k26 e he, hc.k25 e he, ?_, ?_, ?_, ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.v_setV, hr, ite_false]
  all_goals
    simp only [D_trn1 _ _ he, D_trn2 _ _ he, ← hA, ← hB, ← hA', ← hB', D_read _ _ _ (show 0 < 2 by decide),
      D_read _ _ _ (show 1 < 2 by decide)]
    rcases lanes2 he with rfl | rfl <;> rfl

/-- The low and the high limb `k` of element `e`. -/
def lo (v : VReg → BitVec 128) (k e : Nat) : Nat := W (v (av k)) e
def hi (v : VReg → BitVec 128) (k e : Nat) : Nat := W (v (av k)) (2 + e)

theorem split_ok (s : State) (h26 : ∀ e < 2, D (s.v .v31) e = 2 ^ 26 - 1) (h25 : ∀ e < 2, D (s.v .v30) e = 2 ^ 25 - 1) :
    WP isa (.block split) s fun t =>
      VK [.v0, .v1, .v2, .v3, .v4, .v20, .v21] s t ∧ ∀ e < 2,
        (lo t.v 0 e = D (s.v .v24) e % 2 ^ 26 ∧ hi t.v 0 e = D (s.v .v24) e / 2 ^ 26 % 2 ^ 25) ∧
        (lo t.v 1 e = (D (s.v .v25) e * 2 ^ 13 % 2 ^ 64 + D (s.v .v24) e / 2 ^ 51) % 2 ^ 26 ∧
          hi t.v 1 e = D (s.v .v25) e / 2 ^ 13 % 2 ^ 25) ∧
        (lo t.v 2 e = D (s.v .v25) e / 2 ^ 38 ∧ hi t.v 2 e = D (s.v .v26) e % 2 ^ 25) ∧
        (lo t.v 3 e = D (s.v .v26) e / 2 ^ 25 % 2 ^ 26 ∧
          hi t.v 3 e = (D (s.v .v27) e * 2 ^ 13 % 2 ^ 64 + D (s.v .v26) e / 2 ^ 51) % 2 ^ 25) ∧
        (lo t.v 4 e = D (s.v .v27) e / 2 ^ 12 % 2 ^ 26 ∧ hi t.v 4 e = D (s.v .v27) e / 2 ^ 38) := by
  apply WP.of_runBlock
  simp only [split, band, ushr, shl, sri, uzp, vo, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.eval,
    VShiftOp.ok, VArr.esize, show (decide (13 < 64)) = true by decide,
    show (decide (1 ≤ 26) && decide (26 ≤ 64)) = true by decide, show (decide (1 ≤ 51) && decide (51 ≤ 64)) = true by decide,
    show (decide (1 ≤ 13) && decide (13 ≤ 64)) = true by decide, show (decide (1 ≤ 38) && decide (38 ≤ 64)) = true by decide,
    show (decide (1 ≤ 25) && decide (25 ≤ 64)) = true by decide, show (decide (1 ≤ 12) && decide (12 ≤ 64)) = true by decide,
    RegUpd.v_setV, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, by simp only [RegUpd.gpr_setV], by simp only [RegUpd.mem_setV], by simp only [RegUpd.rd_setV],
    by simp only [RegUpd.wr_setV], by simp only [RegUpd.sp_setV]⟩, fun e he => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.v_setV, hr, ite_false]
  simp only [lo, hi, av, RegUpd.v_setV, reduceCtorEq, ite_true, ite_false]
  have l24 := D_lt (s.v .v24) e
  have l25 := D_lt (s.v .v25) e
  have l26 := D_lt (s.v .v26) e
  have l27 := D_lt (s.v .v27) e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · refine And.imp (fun h => h.trans ?_) (fun h => h.trans ?_) (W_uzp _ _ he ?_ ?_) <;>
        simp only [D_sri _ _ _ he, D_ushr _ _ _ he, D_and _ _ (h26 e he), D_and _ _ (h25 e he)] <;> omega_using [l24, l25, l26, l27]

/-- The registers of the limbs' multiples. -/
def mregs : List VReg :=
  [.v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19, .v31]

theorem multiples_ok {s : State} {base : Addr} (hs : Scr s base large) (hc : Consts s.mem base)
    (hb : ∀ k < 5, ∀ c < 4, W (s.v (av k)) c < 2 ^ 26) :
    WP isa (.block multiples) s fun t => VK mregs s t ∧ ∀ k < 5,
      (∀ c < 4, W (t.v (dv k)) c = 2 * W (s.v (av k)) c ∧ W (t.v (nv k)) c = 19 * W (s.v (av k)) c) ∧
      ∀ e < 2, W (t.v (xv k)) e = 2 * W (s.v (av k)) (2 + e) ∧ W (t.v (xv k)) (2 + e) = 2 * W (s.v (av k)) e := by
  simp only [multiples]
  rw [WP.block_append_iff]
  have h1 : WP isa (.block ((List.range 5).map fun k => vo (.add .s4 (dv k) (av k) (av k)))) s fun t =>
      VK [.v10, .v11, .v12, .v13, .v14] s t ∧
      ∀ k < 5, t.v (dv k) = VArr.s4.map2 (fun _ a b => a + b) (s.v (av k)) (s.v (av k)) := by
    apply WP.of_runBlock
    simp only [vo, List.range, List.range.loop, List.map, dv, av, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.eval,
      RegUpd.v_setV, reduceCtorEq, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨fun r hr => ?_, by simp only [RegUpd.gpr_setV], by simp only [RegUpd.mem_setV], by simp only [RegUpd.rd_setV],
      by simp only [RegUpd.wr_setV], by simp only [RegUpd.sp_setV]⟩, fun k hk => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.v_setV, hr, ite_false]
    · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega_using [hk]) with rfl | rfl | rfl | rfl | rfl <;>
        simp only [reduceCtorEq, ite_true, ite_false]
  refine WP.mono h1 fun t1 ⟨k1, d1⟩ => ?_
  rw [WP.block_append_iff]
  have h2 : WP isa (.block ((List.range 5).map fun k => vo (.ext (xv k) (dv k) (dv k) 8))) t1 fun t =>
      VK [.v5, .v6, .v7, .v8, .v9] t1 t ∧
      ∀ k < 5, t.v (xv k) = ((t1.v (dv k) ++ t1.v (dv k)) >>> (8 * 8)).extractLsb' 0 128 := by
    apply WP.of_runBlock
    simp only [vo, List.range, List.range.loop, List.map, dv, xv, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.eval,
      show (8 < 16) = True from eq_true (by decide),
      RegUpd.v_setV, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨fun r hr => ?_, by simp only [RegUpd.gpr_setV], by simp only [RegUpd.mem_setV], by simp only [RegUpd.rd_setV],
      by simp only [RegUpd.wr_setV], by simp only [RegUpd.sp_setV]⟩, fun k hk => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.v_setV, hr, ite_false]
    · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega_using [hk]) with rfl | rfl | rfl | rfl | rfl <;>
        simp only [reduceCtorEq, ite_true, ite_false]
  refine WP.mono h2 fun t2 ⟨k2, x2⟩ => ?_
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (k2.scr (k1.scr hs)) .v31 (by decide) (by decide), ?_⟩
  have h3 : ∀ u : State, WP isa (.block ((List.range 5).map fun k => vo (.mul (nv k) (av k) .v31))) u fun t =>
      VK [.v15, .v16, .v17, .v18, .v19] u t ∧
      ∀ k < 5, t.v (nv k) = VArr.s4.map2 (fun _ a b => a * b) (u.v (av k)) (u.v .v31) := by
    intro u
    apply WP.of_runBlock
    simp only [vo, List.range, List.range.loop, List.map, nv, av, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.eval,
      RegUpd.v_setV, reduceCtorEq, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨fun r hr => ?_, by simp only [RegUpd.gpr_setV], by simp only [RegUpd.mem_setV], by simp only [RegUpd.rd_setV],
      by simp only [RegUpd.wr_setV], by simp only [RegUpd.sp_setV]⟩, fun k hk => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.v_setV, hr, ite_false]
    · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega_using [hk]) with rfl | rfl | rfl | rfl | rfl <;>
        simp only [reduceCtorEq, ite_true, ite_false]
  refine WP.mono (h3 _) fun t ⟨k3, n3⟩ => ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩, fun k hk => ⟨fun c hc' => ⟨?_, ?_⟩, fun e he => ?_⟩⟩
  · have hm : ∀ q ∈ [VReg.v15, .v16, .v17, .v18, .v19], q ∈ mregs := by decide
    have hm2 : ∀ q ∈ [VReg.v5, .v6, .v7, .v8, .v9], q ∈ mregs := by decide
    have hm1 : ∀ q ∈ [VReg.v10, .v11, .v12, .v13, .v14], q ∈ mregs := by decide
    rw [k3.v r fun h => hr (hm r h), RegUpd.v_setV_of_ne _ _ (fun h => hr (by rw [h]; decide)), k2.v r fun h => hr (hm2 r h),
      k1.v r fun h => hr (hm1 r h)]
  · rw [k3.gpr, RegUpd.gpr_setV, k2.gpr, k1.gpr]
  · rw [k3.mem, RegUpd.mem_setV, k2.mem, k1.mem]
  · rw [k3.rd, RegUpd.rd_setV, k2.rd, k1.rd]
  · rw [k3.wr, RegUpd.wr_setV, k2.wr, k1.wr]
  · rw [k3.sp, RegUpd.sp_setV, k2.sp, k1.sp]
  · have n1 : ∀ k < 5, dv k ∉ [VReg.v15, .v16, .v17, .v18, .v19] ∧ dv k ≠ .v31 ∧ dv k ∉ [VReg.v5, .v6, .v7, .v8, .v9] := by decide
    rw [k3.v _ (n1 k hk).1, RegUpd.v_setV_of_ne _ _ (n1 k hk).2.1, k2.v _ (n1 k hk).2.2, d1 k hk,
      W_dbl _ hc' (Nat.lt_trans (hb k hk c hc') (by decide))]
  · have n1 : ∀ k < 5, av k ≠ .v31 ∧ av k ∉ [VReg.v5, .v6, .v7, .v8, .v9] ∧ av k ∉ [VReg.v10, .v11, .v12, .v13, .v14] := by decide
    rw [n3 k hk, RegUpd.v_setV_self, RegUpd.v_setV_of_ne _ _ (n1 k hk).1, k2.v _ (n1 k hk).2.1, k1.v _ (n1 k hk).2.2,
      k2.mem, k1.mem, W_mul _ _ hc' (hc.k19 c hc') (Nat.lt_trans (hb k hk c hc') (by decide))]
  · have n1 : ∀ k < 5, xv k ∉ [VReg.v15, .v16, .v17, .v18, .v19] ∧ xv k ≠ .v31 := by decide
    rw [k3.v _ (n1 k hk).1, RegUpd.v_setV_of_ne _ _ (n1 k hk).2, x2 k hk]
    obtain ⟨w0, w1, w2, w3⟩ := W_ext (t1.v (dv k))
    have dd : ∀ c < 4, W (t1.v (dv k)) c = 2 * W (s.v (av k)) c := fun c hc' => by
      rw [d1 k hk, W_dbl _ hc' (Nat.lt_trans (hb k hk c hc') (by decide))]
    rcases lanes2 he with rfl | rfl
    · exact ⟨w0.trans (dd 2 (by decide)), w2.trans (dd 0 (by decide))⟩
    · exact ⟨w1.trans (dd 3 (by decide)), w3.trans (dd 1 (by decide))⟩

/-! ## The columns -/

def cregs : List VReg := [.v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29]

/-- The products `ps` read no column. -/
abbrev Reads (ps : List Term) : Prop := ∀ p ∈ ps, p.2.1 ∉ cregs ∧ p.2.2 ∉ cregs

theorem column_reads : ∀ m < 5, Reads (highs m) ∧ Reads (lows m) ∧ Reads (crosses m) := by decide
theorem column_nonempty : ∀ m < 5, highs m ≠ [] ∧ crosses m ≠ [] := by decide
theorem column_regs : ∀ m < 5, ev m ∈ cregs ∧ cv m ∈ cregs := by decide
theorem column_ne : ∀ m < 5, ∀ n < 5, (m ≠ n → ev m ≠ ev n ∧ cv m ≠ cv n) ∧ ev m ≠ cv n := by decide

theorem tsum_keep {v v' : VReg → BitVec 128} {ps : List Term} (h : Reads ps)
    (hv : ∀ r, r ∉ cregs → v' r = v r) (e : Nat) : tsum v' ps e = tsum v ps e := by
  refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
  rw [tval, tval, hv _ (h p hp).1, hv _ (h p hp).2]

theorem apart_of {ps : List Term} (h : Reads ps) {d : VReg} (hd : d ∈ cregs) : Apart d ps :=
  fun p hp => ⟨fun e => (h p hp).1 (e ▸ hd), fun e => (h p hp).2 (e ▸ hd)⟩

/-- Column `m` of the products of the registers of `v`. -/
abbrev colE (v : VReg → BitVec 128) (m e : Nat) : Nat := 2 * tsum v (highs m) e + tsum v (lows m) e
abbrev colC (v : VReg → BitVec 128) (m e : Nat) : Nat := tsum v (crosses m) e

theorem column_ok {m : Nat} (hm : m < 5) (s : State) :
    WP isa (.block (column m)) s fun t => VK [ev m, cv m] s t ∧ ∀ e < 2,
      D (t.v (ev m)) e = colE s.v m e % 2 ^ 64 ∧ D (t.v (cv m)) e = colC s.v m e % 2 ^ 64 := by
  obtain ⟨nh, nc⟩ := column_nonempty m hm
  obtain ⟨me, mc⟩ := column_regs m hm
  obtain ⟨rh, rl, rc⟩ := column_reads m hm
  have ec : ev m ≠ cv m := (column_ne m hm m hm).2
  rw [column, WP.block_append_iff]
  refine WP.mono (msum_ok _ nh s (apart_of rh me)) fun a ⟨ka, la⟩ => ?_
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (mlas_ok _ (lows m) _ (apart_of rl me)) fun b ⟨kb, lb⟩ => ?_
  refine WP.mono (msum_ok _ nc b (apart_of rc mc)) fun t ⟨kt, lt⟩ => ?_
  have va : ∀ r, r ∉ cregs → a.v r = s.v r := fun r hr => ka.v r fun h => hr (by
    rw [List.mem_singleton.mp h]; exact me)
  have vb : ∀ r, r ∉ cregs → b.v r = s.v r := fun r hr => by
    have hne : r ≠ ev m := fun h => hr (by rw [h]; exact me)
    rw [kb.v r (by simpa using hne), RegUpd.v_setV_of_ne _ _ hne, va r hr]
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩, fun e he => ⟨?_, ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kt.v r (by simpa using hr.2), kb.v r (by simpa using hr.1), RegUpd.v_setV_of_ne _ _ hr.1, ka.v r (by simpa using hr.1)]
  · rw [kt.gpr, kb.gpr, RegUpd.gpr_setV, ka.gpr]
  · rw [kt.mem, kb.mem, RegUpd.mem_setV, ka.mem]
  · rw [kt.rd, kb.rd, RegUpd.rd_setV, ka.rd]
  · rw [kt.wr, kb.wr, RegUpd.wr_setV, ka.wr]
  · rw [kt.sp, kb.sp, RegUpd.sp_setV, ka.sp]
  · have e1 := lb e he
    rw [Nat.mod_eq_of_lt (D_lt _ _), RegUpd.v_setV_self, D_add _ _ he, la e he,
      tsum_keep (v := s.v) rl (fun r hr => by rw [RegUpd.v_setV_of_ne _ _ (fun h => hr (by rw [h]; exact me)), va r hr])] at e1
    rw [kt.v _ (by simpa using ec), e1, colE]
    omega_using []
  · rw [lt e he, tsum_keep (v := s.v) rc vb]

theorem columns_ok (s : State) : WP isa (.block columns) s fun t => VK cregs s t ∧ ∀ m < 5, ∀ e < 2,
    D (t.v (ev m)) e = colE s.v m e % 2 ^ 64 ∧ D (t.v (cv m)) e = colC s.v m e % 2 ^ 64 := by
  refine wp_range_flatMap (M := isa) (N := 5) (fun n t => VK cregs s t ∧ ∀ m < n, ∀ e < 2,
    D (t.v (ev m)) e = colE s.v m e % 2 ^ 64 ∧ D (t.v (cv m)) e = colC s.v m e % 2 ^ 64)
    (fun n t hn ⟨kt, ht⟩ => ?_) 5 (by decide) s ⟨⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨me, mc⟩ := column_regs n hn
  obtain ⟨rh, rl, rc⟩ := column_reads n hn
  refine WP.mono (column_ok hn t) fun u ⟨ku, hu⟩ => ⟨kt.trans (ku.mono fun r hr => ?_), fun m hm e he => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact me
    · exact mc
  by_cases h : m = n
  · subst h
    obtain ⟨h1, h2⟩ := hu e he
    rw [colE, tsum_keep rh kt.v, tsum_keep rl kt.v] at h1
    rw [colC, tsum_keep rc kt.v] at h2
    exact ⟨h1, h2⟩
  · have hmn : m < n := by omega_using [hm, h]
    obtain ⟨n1, n2⟩ := column_ne m (Nat.lt_trans hmn hn) n hn
    obtain ⟨n1, n3⟩ := n1 h
    have n4 : ev n ≠ cv m := (column_ne n hn m (Nat.lt_trans hmn hn)).2
    rw [ku.v _ (by simp [n1, n2]), ku.v _ (by simp [n4.symm, n3])]
    exact ht m hmn e he

/-! ## The carries -/

theorem carry1_ok {s : State} {base : Addr} (hs : Scr s base large) (hc : Consts s.mem base) :
    WP isa (.block carry1) s fun t =>
      VK ([.v0, .v1, .v2, .v3, .v4] ++ cregs) s t ∧ ∀ e < 2, (∀ r, D (s.v r) e < 2 ^ 62 ∨ r ∉ cregs) →
        (D (t.v .v20) e = D (s.v .v20) e % 2 ^ 26 + 19 * (D (s.v .v29) e / 2 ^ 25) ∧
          D (t.v .v21) e = D (s.v .v21) e % 2 ^ 26 + D (s.v .v25) e / 2 ^ 25 ∧
          D (t.v .v22) e = D (s.v .v22) e % 2 ^ 26 + D (s.v .v26) e / 2 ^ 25 ∧
          D (t.v .v23) e = D (s.v .v23) e % 2 ^ 26 + D (s.v .v27) e / 2 ^ 25 ∧
          D (t.v .v24) e = D (s.v .v24) e % 2 ^ 26 + D (s.v .v28) e / 2 ^ 25) ∧
        (D (t.v .v25) e = D (s.v .v25) e % 2 ^ 25 + D (s.v .v20) e / 2 ^ 26 ∧
          D (t.v .v26) e = D (s.v .v26) e % 2 ^ 25 + D (s.v .v21) e / 2 ^ 26 ∧
          D (t.v .v27) e = D (s.v .v27) e % 2 ^ 25 + D (s.v .v22) e / 2 ^ 26 ∧
          D (t.v .v28) e = D (s.v .v28) e % 2 ^ 25 + D (s.v .v23) e / 2 ^ 26 ∧
          D (t.v .v29) e = D (s.v .v29) e % 2 ^ 25 + D (s.v .v24) e / 2 ^ 26) := by
  simp only [carry1]
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq hs .v3 (by decide) (by decide), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (scr_setV hs _ _) .v4 (by decide) (by decide), ?_⟩
  simp only [RegUpd.mem_setV]
  obtain h26 := hc.k26
  obtain h25 := hc.k25
  generalize s.mem.read (off base K26) 16 = m26 at *
  generalize s.mem.read (off base K25) 16 = m25 at *
  apply WP.of_runBlock
  simp only [band, ushr, shl, add2, vo, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.eval,
    VShiftOp.ok, VArr.esize, show (decide (1 < 64)) = true by decide, show (decide (4 < 64)) = true by decide,
    show (decide (1 ≤ 25) && decide (25 ≤ 64)) = true by decide,
    show (decide (1 ≤ 26) && decide (26 ≤ 64)) = true by decide,
    RegUpd.v_setV, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, by simp only [RegUpd.gpr_setV], by simp only [RegUpd.mem_setV], by simp only [RegUpd.rd_setV],
    by simp only [RegUpd.wr_setV], by simp only [RegUpd.sp_setV]⟩, fun e he hb => ?_⟩
  · simp only [cregs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.v_setV, hr, ite_false]
  have b : ∀ r ∈ cregs, D (s.v r) e < 2 ^ 62 := fun r hr => (hb r).resolve_right fun h => h hr
  have b20 := b .v20 (by decide)
  have b21 := b .v21 (by decide)
  have b22 := b .v22 (by decide)
  have b23 := b .v23 (by decide)
  have b24 := b .v24 (by decide)
  have b25 := b .v25 (by decide)
  have b26 := b .v26 (by decide)
  have b27 := b .v27 (by decide)
  have b28 := b .v28 (by decide)
  have b29 := b .v29 (by decide)
  clear b hb
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    (simp only [D_add _ _ he, D_ushr _ _ _ he, D_shl _ _ _ he, D_and _ _ (h26 e he), D_and _ _ (h25 e he)]
     clear h26 h25 hs hc
     omega_using [b20, b21, b22, b23, b24, b25, b26, b27, b28, b29])

theorem join_ok (s : State) : WP isa (.block join) s fun t => VK cregs s t ∧ ∀ e < 2,
    (∀ r ∈ cregs, D (s.v r) e < 2 ^ 37 ∨ r ∈ [VReg.v20, .v21, .v22, .v23, .v24] ∧ D (s.v r) e < 2 ^ 62) →
      D (t.v .v20) e = D (s.v .v20) e + 2 ^ 26 * D (s.v .v25) e ∧ D (t.v .v21) e = D (s.v .v21) e + 2 ^ 26 * D (s.v .v26) e ∧
      D (t.v .v22) e = D (s.v .v22) e + 2 ^ 26 * D (s.v .v27) e ∧ D (t.v .v23) e = D (s.v .v23) e + 2 ^ 26 * D (s.v .v28) e ∧
      D (t.v .v24) e = D (s.v .v24) e + 2 ^ 26 * D (s.v .v29) e := by
  apply WP.of_runBlock
  simp only [join, List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    ev, cv, shl, add2, vo, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.eval,
    VShiftOp.ok, VArr.esize, show (decide (26 < 64)) = true by decide,
    RegUpd.v_setV, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, by simp only [RegUpd.gpr_setV], by simp only [RegUpd.mem_setV], by simp only [RegUpd.rd_setV],
    by simp only [RegUpd.wr_setV], by simp only [RegUpd.sp_setV]⟩, fun e he hb => ?_⟩
  · simp only [cregs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.v_setV, hr, ite_false]
  simp only [cregs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, reduceCtorEq, or_true,
    true_and, false_and] at hb
  simp only [D_add _ _ he, D_shl _ _ _ he]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega_using [hb]

theorem carry2_ok {s : State} {base : Addr} (hs : Scr s base large) (hc : Consts s.mem base) :
    WP isa (.block carry2) s fun t =>
      VK ([.v0, .v2, .v5] ++ cregs) s t ∧ ∀ e < 2,
        D (t.v .v20) e = D (s.v .v20) e % 2 ^ 51 + 19 * (D (s.v .v24) e / 2 ^ 51) ∧
        D (t.v .v21) e = D (s.v .v21) e % 2 ^ 51 + D (s.v .v20) e / 2 ^ 51 ∧
        D (t.v .v22) e = D (s.v .v22) e % 2 ^ 51 + D (s.v .v21) e / 2 ^ 51 ∧
        D (t.v .v23) e = D (s.v .v23) e % 2 ^ 51 + D (s.v .v22) e / 2 ^ 51 ∧
        D (t.v .v24) e = D (s.v .v24) e % 2 ^ 51 + D (s.v .v23) e / 2 ^ 51 := by
  simp only [carry2, List.cons_append]
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq hs .v5 (by decide) (by decide), ?_⟩
  obtain h51 := hc.k51
  generalize s.mem.read (off base K51) 16 = m51 at *
  apply WP.of_runBlock
  simp only [List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    ev, cv, band, ushr, shl, add2, vo, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.eval,
    VShiftOp.ok, VArr.esize, show (decide (1 < 64)) = true by decide, show (decide (4 < 64)) = true by decide,
    show (decide (1 ≤ 51) && decide (51 ≤ 64)) = true by decide,
    RegUpd.v_setV, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, by simp only [RegUpd.gpr_setV], by simp only [RegUpd.mem_setV], by simp only [RegUpd.rd_setV],
    by simp only [RegUpd.wr_setV], by simp only [RegUpd.sp_setV]⟩, fun e he => ?_⟩
  · simp only [cregs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.v_setV, hr, ite_false]
  have b20 := D_lt (s.v .v20) e
  have b21 := D_lt (s.v .v21) e
  have b22 := D_lt (s.v .v22) e
  have b23 := D_lt (s.v .v23) e
  have b24 := D_lt (s.v .v24) e
  simp only [D_add _ _ he, D_ushr _ _ _ he, D_shl _ _ _ he, D_and _ _ (h51 e he)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega_using [b20, b21, b22, b23, b24]

/-! ## The results -/

theorem write16_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 128) (h : d + 16 ≤ 4096) :
    Outside base d 16 m (m.write (off base d) 16 v) := by
  intro x hx
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega_using [h])]
  simp only [ofs] at hx
  omega_using [hx]

theorem word_write16 (m : Mem) (base : Addr) (d : Nat) (v : BitVec 128) :
    (word (m.write (off base d) 16 v) base d).toNat = D v 0 ∧ (word (m.write (off base d) 16 v) base (d + 8)).toNat = D v 1 := by
  have h : ∀ e < 2, (word (m.write (off base d) 16 v) base (d + 8 * e)).toNat = D v e := fun e he => by
    rw [← D_read _ _ _ he]
    have := Mem.readW_writeW_self m (off base d) 16 v (by decide)
    simp only [Mem.readW, Mem.writeW, BitVec.setWidth_eq] at this
    rw [show (m.write (off base d) 16 v).read (off base d) 16 = v by simpa using this]
  exact ⟨h 0 (by decide), h 1 (by decide)⟩

/-- What storing the limbs in `p` and `q` at `o` does. -/
structure Stored (base : Addr) (p q : VReg) (o : Nat) (s t : State) : Prop where
  here : ∀ e < 2, (word t.mem base (o + 48 * e)).toNat = D (s.v p) e ∧ (word t.mem base (o + 48 * e + 8)).toNat = D (s.v q) e
  other : ∀ d, (d + 8 ≤ o ∨ o + 16 ≤ d) → (d + 8 ≤ o + 48 ∨ o + 64 ≤ d) → d + 8 ≤ 4096 → word t.mem base d = word s.mem base d
  mem : Outside base OUT 96 s.mem t.mem
  v : ∀ r, r ∉ [VReg.v0, .v1] → t.v r = s.v r
  gpr : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem store_ok {s : State} {base : Addr} (hs : Scr s base large) (p q : VReg) (hp : p ≠ .v0) (hq : q ≠ .v0) {o : Nat}
    (h16 : o % 16 = 0) (ho : OUT ≤ o) (ho' : o + 64 ≤ OUT + 96) (is : List Instr) (Q : State → Prop)
    (h : ∀ t, Stored base p q o s t → WP isa (.block is) t Q) :
    WP isa (.block (trn1 .v0 p q :: trn2 .v1 p q :: stq .v0 o :: stq .v1 (o + 48) :: is)) s Q := by
  have hO : OUT = 1024 := rfl
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩⟩
  simp only [RegUpd.v_setV_of_ne _ _ hp, RegUpd.v_setV_of_ne _ _ hq]
  have e0 := fun e he => D_trn1 (s.v p) (s.v q) (e := e) he
  have e1 := fun e he => D_trn2 (s.v p) (s.v q) (e := e) he
  generalize VPermOp.eval .trn1 .d2 (s.v p) (s.v q) = x at *
  generalize VPermOp.eval .trn2 .d2 (s.v p) (s.v q) = y at *
  generalize hu : (s.setV .v0 x).setV .v1 y = u
  have us : Scr u base large := by subst hu; exact scr_setV (scr_setV hs _ _) _ _
  have u0 : u.v .v0 = x := by subst hu; rw [RegUpd.v_setV_of_ne _ _ (by decide), RegUpd.v_setV_self]
  have u1 : u.v .v1 = y := by subst hu; rw [RegUpd.v_setV_self]
  have uv : ∀ r, r ∉ [VReg.v0, .v1] → u.v r = s.v r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    subst hu; rw [RegUpd.v_setV_of_ne _ _ hr.2, RegUpd.v_setV_of_ne _ _ hr.1]
  have um : u.mem = s.mem := by subst hu; simp only [RegUpd.mem_setV]
  have ug : u.gpr = s.gpr := by subst hu; simp only [RegUpd.gpr_setV]
  have ur : u.rd = s.rd := by subst hu; simp only [RegUpd.rd_setV]
  have uw : u.wr = s.wr := by subst hu; simp only [RegUpd.wr_setV]
  have up : u.sp = s.sp := by subst hu; simp only [RegUpd.sp_setV]
  refine WP.block_cons_iff.mpr ⟨_, exec_stq us .v0 h16 (by omega_using [ho', hO]), ?_⟩
  rw [u0, um]
  have m1 := write16_outside s.mem base x (d := o) (by omega_using [ho', hO])
  have w1 := word_write16 s.mem base o x
  generalize s.mem.write (off base o) 16 x = m at *
  refine WP.block_cons_iff.mpr ⟨_, exec_stq (us.setMem m) .v1 (by omega_using [h16]) (by omega_using [ho', hO]), ?_⟩
  have m2 := write16_outside m base y (d := o + 48) (by omega_using [ho', hO])
  have w2 := word_write16 m base (o + 48) y
  rw [← u1] at m2 w2
  generalize m.write (off base (o + 48)) 16 (u.v .v1) = m' at *
  refine h _ ⟨fun e he => ?_, fun d d1 d2 d3 => ?_, ?_, uv, ug, ur, uw, up⟩
  · show (word m' base _).toNat = _ ∧ (word m' base _).toNat = _
    rcases lanes2 he with rfl | rfl
    · rw [Nat.mul_zero, Nat.add_zero, m2.word (by omega_using []) (by omega_using [ho', hO]),
        m2.word (by omega_using []) (by omega_using [ho', hO]), w1.1, w1.2, e0 0 he, e0 1 (by decide)]
      exact ⟨rfl, rfl⟩
    · rw [Nat.mul_one, w2.1, w2.2, u1, e1 0 (by decide), e1 1 he]
      exact ⟨rfl, rfl⟩
  · show word m' base _ = _
    rw [m2.word (by omega_using [d2]) (by omega_using [d3]), m1.word d1 (by omega_using [d3])]
  · show Outside base OUT 96 s.mem m'
    exact (m1.mono ho (by omega_using [ho'])).trans (m2.mono (by omega_using [ho]) (by omega_using [ho']))

/-- Limb `k` of result `e`. -/
abbrev out (m : Mem) (base : Addr) (e k : Nat) : Nat := (word m base (OUT + 48 * e + 8 * k)).toNat

theorem stores_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block stores) s fun t => (∀ e < 2, out t.mem base e 0 = D (s.v .v20) e ∧ out t.mem base e 1 = D (s.v .v21) e ∧
        out t.mem base e 2 = D (s.v .v22) e ∧ out t.mem base e 3 = D (s.v .v23) e ∧ out t.mem base e 4 = D (s.v .v24) e) ∧
      Outside base OUT 96 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hO : OUT = 1024 := rfl
  rw [stores]
  refine store_ok hs .v20 .v21 (by decide) (by decide) (by decide) (by decide) (by decide) _ _ fun a sa => ?_
  have ha : Scr a base large := ⟨by rw [sa.gpr]; exact hs.x0, sa.wr ▸ hs.wr, hs.nowrap⟩
  refine store_ok ha .v22 .v23 (by decide) (by decide) (by decide) (by decide) (by decide) _ _ fun b sb => ?_
  have hb : Scr b base large := ⟨by rw [sb.gpr]; exact ha.x0, sb.wr ▸ ha.wr, hs.nowrap⟩
  refine store_ok hb .v24 .v24 (by decide) (by decide) (by decide) (by decide) (by decide) _ _ fun c sc => ?_
  refine WP.block_nil ⟨fun e he => ?_, sa.mem.trans (sb.mem.trans sc.mem), by rw [sc.gpr, sb.gpr, sa.gpr],
    by rw [sc.rd, sb.rd, sa.rd], by rw [sc.wr, sb.wr, sa.wr], by rw [sc.sp, sb.sp, sa.sp]⟩
  have ka := sa.here e he
  have kb := sb.here e he
  have kc := (sc.here e he).1
  have oa : ∀ d, (d = OUT + 48 * e ∨ d = OUT + 48 * e + 8) → word c.mem base d = word a.mem base d := fun d hd => by
    rw [sc.other d (by omega_using [hd, he, hO]) (by omega_using [hd, he, hO]) (by omega_using [hd, he, hO]),
      sb.other d (by omega_using [hd, he, hO]) (by omega_using [hd, he, hO]) (by omega_using [hd, he, hO])]
  have ob : ∀ d, (d = OUT + 16 + 48 * e ∨ d = OUT + 16 + 48 * e + 8) → word c.mem base d = word b.mem base d := fun d hd =>
    sc.other d (by omega_using [hd, he, hO]) (by omega_using [hd, he, hO]) (by omega_using [hd, he, hO])
  rw [sa.v _ (by decide), sa.v _ (by decide)] at kb
  rw [sb.v _ (by decide), sa.v _ (by decide)] at kc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [out, Nat.mul_zero, Nat.add_zero, oa _ (Or.inl rfl)]; exact ka.1
  · rw [out, Nat.mul_one, oa _ (Or.inr rfl)]; exact ka.2
  · rw [out, show OUT + 48 * e + 8 * 2 = OUT + 16 + 48 * e by omega_using [], ob _ (Or.inl rfl)]; exact kb.1
  · rw [out, show OUT + 48 * e + 8 * 3 = OUT + 16 + 48 * e + 8 by omega_using [], ob _ (Or.inr rfl)]; exact kb.2
  · rw [out, show OUT + 48 * e + 8 * 4 = OUT + 32 + 48 * e by omega_using []]; exact kc

/-! ## The columns' values -/

/-- The words of the limbs `l`, `h` and their multiples, in lane `e`. -/
structure Mult (v : VReg → BitVec 128) (e : Nat) (l h : Nat → Nat) : Prop where
  al : ∀ k < 5, W (v (av k)) (0 + e) = l k
  ah : ∀ k < 5, W (v (av k)) (2 + e) = h k
  dl : ∀ k < 5, W (v (dv k)) (0 + e) = 2 * l k
  dh : ∀ k < 5, W (v (dv k)) (2 + e) = 2 * h k
  nl : ∀ k < 5, W (v (nv k)) (0 + e) = 19 * l k
  nh : ∀ k < 5, W (v (nv k)) (2 + e) = 19 * h k
  xl : ∀ k < 5, W (v (xv k)) (0 + e) = 2 * h k
  xh : ∀ k < 5, W (v (xv k)) (2 + e) = 2 * l k

theorem highs_0 : highs 0 = [(true, dv 0, nv 4), (true, dv 1, nv 3), (true, av 2, nv 2)] := by decide
theorem highs_1 : highs 1 = [(true, av 0, av 0), (true, dv 1, nv 4), (true, dv 2, nv 3)] := by decide
theorem highs_2 : highs 2 = [(true, dv 0, av 1), (true, dv 2, nv 4), (true, av 3, nv 3)] := by decide
theorem highs_3 : highs 3 = [(true, dv 0, av 2), (true, av 1, av 1), (true, dv 3, nv 4)] := by decide
theorem highs_4 : highs 4 = [(true, dv 0, av 3), (true, dv 1, av 2), (true, av 4, nv 4)] := by decide
theorem lows_0 : lows 0 = [(false, av 0, av 0), (false, dv 1, nv 4), (false, dv 2, nv 3)] := by decide
theorem lows_1 : lows 1 = [(false, dv 0, av 1), (false, dv 2, nv 4), (false, av 3, nv 3)] := by decide
theorem lows_2 : lows 2 = [(false, dv 0, av 2), (false, av 1, av 1), (false, dv 3, nv 4)] := by decide
theorem lows_3 : lows 3 = [(false, dv 0, av 3), (false, dv 1, av 2), (false, av 4, nv 4)] := by decide
theorem lows_4 : lows 4 = [(false, dv 0, av 4), (false, dv 1, av 3), (false, av 2, av 2)] := by decide
theorem crosses_0 : crosses 0 = [(false, xv 0, av 0), (false, xv 1, nv 4), (true, xv 1, nv 4), (false, xv 2, nv 3), (true, xv 2, nv 3)] := by decide
theorem crosses_1 : crosses 1 = [(false, xv 0, av 1), (true, xv 0, av 1), (false, xv 2, nv 4), (true, xv 2, nv 4), (false, xv 3, nv 3)] := by decide
theorem crosses_2 : crosses 2 = [(false, xv 0, av 2), (true, xv 0, av 2), (false, xv 1, av 1), (false, xv 3, nv 4), (true, xv 3, nv 4)] := by decide
theorem crosses_3 : crosses 3 = [(false, xv 0, av 3), (true, xv 0, av 3), (false, xv 1, av 2), (true, xv 1, av 2), (false, xv 4, nv 4)] := by decide
theorem crosses_4 : crosses 4 = [(false, xv 0, av 4), (true, xv 0, av 4), (false, xv 1, av 3), (true, xv 1, av 3), (false, xv 2, av 2)] := by decide

theorem sum3 (x y z : Nat) : [x, y, z].sum = x + y + z := by
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc]

theorem sum5 (x y z u w : Nat) : [x, y, z, u, w].sum = x + y + z + u + w := by
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc]

theorem colE_0 {v : VReg → BitVec 128} {e : Nat} {l h : Nat → Nat} (H : Mult v e l h) :
    colE v 0 e = 2 * (2 * h 0 * (19 * h 4) + 2 * h 1 * (19 * h 3) + h 2 * (19 * h 2)) + (l 0 * l 0 + 2 * l 1 * (19 * l 4) + 2 * l 2 * (19 * l 3)) := by
  simp (disch := decide) only [colE, tsum, highs_0, lows_0, List.map_cons, List.map_nil, sum3, tval, hp, ite_true, ite_false,
    Bool.false_eq_true, H.al, H.ah, H.dl, H.dh, H.nl, H.nh]
theorem colC_0 {v : VReg → BitVec 128} {e : Nat} {l h : Nat → Nat} (H : Mult v e l h) :
    colC v 0 e = 2 * h 0 * l 0 + 2 * h 1 * (19 * l 4) + 2 * l 1 * (19 * h 4) + 2 * h 2 * (19 * l 3) + 2 * l 2 * (19 * h 3) := by
  simp (disch := decide) only [colC, tsum, crosses_0, List.map_cons, List.map_nil, sum5, tval, hp, ite_true, ite_false,
    Bool.false_eq_true, H.al, H.nl, H.nh, H.xl, H.xh]

theorem colE_1 {v : VReg → BitVec 128} {e : Nat} {l h : Nat → Nat} (H : Mult v e l h) :
    colE v 1 e = 2 * (h 0 * h 0 + 2 * h 1 * (19 * h 4) + 2 * h 2 * (19 * h 3)) + (2 * l 0 * l 1 + 2 * l 2 * (19 * l 4) + l 3 * (19 * l 3)) := by
  simp (disch := decide) only [colE, tsum, highs_1, lows_1, List.map_cons, List.map_nil, sum3, tval, hp, ite_true, ite_false,
    Bool.false_eq_true, H.al, H.ah, H.dl, H.dh, H.nl, H.nh]
theorem colC_1 {v : VReg → BitVec 128} {e : Nat} {l h : Nat → Nat} (H : Mult v e l h) :
    colC v 1 e = 2 * h 0 * l 1 + 2 * l 0 * h 1 + 2 * h 2 * (19 * l 4) + 2 * l 2 * (19 * h 4) + 2 * h 3 * (19 * l 3) := by
  simp (disch := decide) only [colC, tsum, crosses_1, List.map_cons, List.map_nil, sum5, tval, hp, ite_true, ite_false,
    Bool.false_eq_true, H.al, H.ah, H.nl, H.nh, H.xl, H.xh]

theorem colE_2 {v : VReg → BitVec 128} {e : Nat} {l h : Nat → Nat} (H : Mult v e l h) :
    colE v 2 e = 2 * (2 * h 0 * h 1 + 2 * h 2 * (19 * h 4) + h 3 * (19 * h 3)) + (2 * l 0 * l 2 + l 1 * l 1 + 2 * l 3 * (19 * l 4)) := by
  simp (disch := decide) only [colE, tsum, highs_2, lows_2, List.map_cons, List.map_nil, sum3, tval, hp, ite_true, ite_false,
    Bool.false_eq_true, H.al, H.ah, H.dl, H.dh, H.nl, H.nh]
theorem colC_2 {v : VReg → BitVec 128} {e : Nat} {l h : Nat → Nat} (H : Mult v e l h) :
    colC v 2 e = 2 * h 0 * l 2 + 2 * l 0 * h 2 + 2 * h 1 * l 1 + 2 * h 3 * (19 * l 4) + 2 * l 3 * (19 * h 4) := by
  simp (disch := decide) only [colC, tsum, crosses_2, List.map_cons, List.map_nil, sum5, tval, hp, ite_true, ite_false,
    Bool.false_eq_true, H.al, H.ah, H.nl, H.nh, H.xl, H.xh]

theorem colE_3 {v : VReg → BitVec 128} {e : Nat} {l h : Nat → Nat} (H : Mult v e l h) :
    colE v 3 e = 2 * (2 * h 0 * h 2 + h 1 * h 1 + 2 * h 3 * (19 * h 4)) + (2 * l 0 * l 3 + 2 * l 1 * l 2 + l 4 * (19 * l 4)) := by
  simp (disch := decide) only [colE, tsum, highs_3, lows_3, List.map_cons, List.map_nil, sum3, tval, hp, ite_true, ite_false,
    Bool.false_eq_true, H.al, H.ah, H.dl, H.dh, H.nl, H.nh]
theorem colC_3 {v : VReg → BitVec 128} {e : Nat} {l h : Nat → Nat} (H : Mult v e l h) :
    colC v 3 e = 2 * h 0 * l 3 + 2 * l 0 * h 3 + 2 * h 1 * l 2 + 2 * l 1 * h 2 + 2 * h 4 * (19 * l 4) := by
  simp (disch := decide) only [colC, tsum, crosses_3, List.map_cons, List.map_nil, sum5, tval, hp, ite_true, ite_false,
    Bool.false_eq_true, H.al, H.ah, H.nl, H.xl, H.xh]

theorem colE_4 {v : VReg → BitVec 128} {e : Nat} {l h : Nat → Nat} (H : Mult v e l h) :
    colE v 4 e = 2 * (2 * h 0 * h 3 + 2 * h 1 * h 2 + h 4 * (19 * h 4)) + (2 * l 0 * l 4 + 2 * l 1 * l 3 + l 2 * l 2) := by
  simp (disch := decide) only [colE, tsum, highs_4, lows_4, List.map_cons, List.map_nil, sum3, tval, hp, ite_true, ite_false,
    Bool.false_eq_true, H.al, H.ah, H.dl, H.dh, H.nh]
theorem colC_4 {v : VReg → BitVec 128} {e : Nat} {l h : Nat → Nat} (H : Mult v e l h) :
    colC v 4 e = 2 * h 0 * l 4 + 2 * l 0 * h 4 + 2 * h 1 * l 3 + 2 * l 1 * h 3 + 2 * h 2 * l 2 := by
  simp (disch := decide) only [colC, tsum, crosses_4, List.map_cons, List.map_nil, sum5, tval, hp, ite_true, ite_false,
    Bool.false_eq_true, H.al, H.ah, H.xl, H.xh]

/-- The registers of the first and of the second factors. -/
def firsts : List VReg := [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14]
def seconds : List VReg := [.v0, .v1, .v2, .v3, .v4, .v15, .v16, .v17, .v18, .v19]

theorem col_factors : ∀ m < 5, (∀ p ∈ highs m, p.2.1 ∈ firsts ∧ p.2.2 ∈ seconds) ∧
    (∀ p ∈ lows m, p.2.1 ∈ firsts ∧ p.2.2 ∈ seconds) ∧ (∀ p ∈ crosses m, p.2.1 ∈ firsts ∧ p.2.2 ∈ seconds) := by decide

theorem col_length : ∀ m < 5, (highs m).length = 3 ∧ (lows m).length = 3 ∧ (crosses m).length = 5 := by decide

theorem hp_lt (h : Bool) {e : Nat} (he : e < 2) : hp h + e < 4 := by cases h <;> simp only [hp, ite_true, ite_false, Bool.false_eq_true] <;> omega_using [he]

theorem tsum_le {v : VReg → BitVec 128} {e : Nat} (he : e < 2) (hf : ∀ r ∈ firsts, ∀ c < 4, W (v r) c < 2 ^ 27)
    (hs : ∀ r ∈ seconds, ∀ c < 4, W (v r) c < 2 ^ 31) : ∀ ps : List Term, (∀ p ∈ ps, p.2.1 ∈ firsts ∧ p.2.2 ∈ seconds) →
      tsum v ps e ≤ ps.length * 2 ^ 58
  | [], _ => Nat.zero_le _
  | p :: ps, h => by
    obtain ⟨h1, h2⟩ := h p List.mem_cons_self
    have hc := hp_lt p.1 he
    have a := Nat.mul_lt_mul'' (hf _ h1 _ hc) (hs _ h2 _ hc)
    have b := tsum_le he hf hs ps fun q hq => h q (List.mem_cons_of_mem _ hq)
    show tval v p e + tsum v ps e ≤ (ps.length + 1) * 2 ^ 58
    rw [Nat.add_mul, Nat.add_comm, Nat.one_mul]
    exact Nat.add_le_add b (Nat.le_of_lt (Nat.lt_of_lt_of_le a (by decide)))

theorem firsts_eq : ∀ r ∈ firsts, ∃ k, k < 5 ∧ (r = av k ∨ r = xv k ∨ r = dv k) := by
  intro r hr
  simp only [firsts, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩,
    ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩]

theorem seconds_eq : ∀ r ∈ seconds, ∃ k, k < 5 ∧ (r = av k ∨ r = nv k) := by
  intro r hr
  simp only [seconds, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩,
    ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩]

theorem col_lt {v : VReg → BitVec 128} {e : Nat} (he : e < 2) (hf : ∀ r ∈ firsts, ∀ c < 4, W (v r) c < 2 ^ 27)
    (hs : ∀ r ∈ seconds, ∀ c < 4, W (v r) c < 2 ^ 31) : ∀ m < 5, colE v m e < 2 ^ 62 ∧ colC v m e < 2 ^ 62 := by
  intro m hm
  obtain ⟨f1, f2, f3⟩ := col_factors m hm
  obtain ⟨l1, l2, l3⟩ := col_length m hm
  have a := tsum_le he hf hs _ f1
  have b := tsum_le he hf hs _ f2
  have c := tsum_le he hf hs _ f3
  rw [l1] at a
  rw [l2] at b
  rw [l3] at c
  simp only [colE, colC]
  omega_using [a, b, c]

/-! ## The squares -/

theorem reduce_lt {e0 c0 e1 c1 e2 c2 e3 c3 e4 c4 l0 l1 l2 l3 l4 : Nat} (b0 : e0 < 2 ^ 62) (b1 : e1 < 2 ^ 62) (b2 : e2 < 2 ^ 62)
    (b3 : e3 < 2 ^ 62) (b4 : e4 < 2 ^ 62) (d0 : c0 < 2 ^ 62) (d1 : c1 < 2 ^ 62) (d2 : c2 < 2 ^ 62)
    (d3 : c3 < 2 ^ 62) (d4 : c4 < 2 ^ 62)
    (h0 : l0 = e0 % 2 ^ 26 + 19 * (c4 / 2 ^ 25) + 2 ^ 26 * (c0 % 2 ^ 25 + e0 / 2 ^ 26))
    (h1 : l1 = e1 % 2 ^ 26 + c0 / 2 ^ 25 + 2 ^ 26 * (c1 % 2 ^ 25 + e1 / 2 ^ 26))
    (h2 : l2 = e2 % 2 ^ 26 + c1 / 2 ^ 25 + 2 ^ 26 * (c2 % 2 ^ 25 + e2 / 2 ^ 26))
    (h3 : l3 = e3 % 2 ^ 26 + c2 / 2 ^ 25 + 2 ^ 26 * (c3 % 2 ^ 25 + e3 / 2 ^ 26))
    (h4 : l4 = e4 % 2 ^ 26 + c3 / 2 ^ 25 + 2 ^ 26 * (c4 % 2 ^ 25 + e4 / 2 ^ 26)) :
    l0 < 2 ^ 63 ∧ l1 < 2 ^ 63 ∧ l2 < 2 ^ 63 ∧ l3 < 2 ^ 63 ∧ l4 < 2 ^ 63 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    omega_using [b0, b1, b2, b3, b4, d0, d1, d2, d3, d4, h0, h1, h2, h3, h4]

/-- Result `e`. -/
def outVal (m : Mem) (base : Addr) (e : Nat) : Nat :=
  out m base e 0 + 2 ^ 51 * out m base e 1 + 2 ^ 102 * out m base e 2 + 2 ^ 153 * out m base e 3 + 2 ^ 204 * out m base e 4

theorem squares_ok {s : State} {base : Addr} (hs : Scr s base large) (hc : Consts s.mem base) {a b : Nat}
    (ha : a % 16 = 0) (ha' : a + 32 ≤ 1024) (hb : b % 16 = 0) (hb' : b + 32 ≤ 1024) :
    WP isa (.block (squares a b)) s fun t => (∀ e < 2, (∀ k < 5, out t.mem base e k < 2 ^ 51 + 2 ^ 17) ∧
        outVal t.mem base e % VG.Spec.X25519.P =
          fe s.mem base (el a b e) * fe s.mem base (el a b e) % VG.Spec.X25519.P) ∧
      Outside base OUT 96 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rw [squares, WP.block_append_iff]
  refine WP.mono (words_ok hs hc ha ha' hb hb') fun t0 ⟨k0, w0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (split_ok t0 (fun e he => (w0 e he).1) (fun e he => (w0 e he).2.1)) fun t1 ⟨k1, w1⟩ => ?_
  have s1 : Scr t1 base large := k1.scr (k0.scr hs)
  have c1 : Consts t1.mem base := by rw [k1.mem, k0.mem]; exact hc
  have lim : ∀ k < 5, ∀ e < 2, lo t1.v k e < 2 ^ 26 ∧ hi t1.v k e < 2 ^ 26 := by
    intro k hk e he
    obtain ⟨a0, a1, a2, a3, a4⟩ := w1 e he
    have b24 := D_lt (t0.v .v24) e
    have b25 := D_lt (t0.v .v25) e
    have b26 := D_lt (t0.v .v26) e
    have b27 := D_lt (t0.v .v27) e
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega_using [hk]) with rfl | rfl | rfl | rfl | rfl
    · rw [a0.1, a0.2]; omega_using [b24]
    · rw [a1.1, a1.2]; omega_using [b24]
    · rw [a2.1, a2.2]; omega_using [b25]
    · rw [a3.1, a3.2]; omega_using [b24]
    · rw [a4.1, a4.2]; omega_using [b27]
  have limW : ∀ k < 5, ∀ c < 4, W (t1.v (av k)) c < 2 ^ 26 := by
    intro k hk c hc'
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega_using [hc']) with rfl | rfl | rfl | rfl
    · exact (lim k hk 0 (by decide)).1
    · exact (lim k hk 1 (by decide)).1
    · exact (lim k hk 0 (by decide)).2
    · exact (lim k hk 1 (by decide)).2
  rw [WP.block_append_iff]
  refine WP.mono (multiples_ok s1 c1 limW) fun t2 ⟨k2, w2⟩ => ?_
  have s2 : Scr t2 base large := k2.scr s1
  have avk : ∀ k < 5, t2.v (av k) = t1.v (av k) := fun k hk => k2.v _ ((by decide : ∀ k < 5, av k ∉ mregs) k hk)
  rw [WP.block_append_iff]
  refine WP.mono (columns_ok t2) fun t3 ⟨k3, w3⟩ => ?_
  have s3 : Scr t3 base large := k3.scr s2
  have c3 : Consts t3.mem base := by rw [k3.mem, k2.mem]; exact c1
  rw [WP.block_append_iff]
  refine WP.mono (carry1_ok s3 c3) fun t4 ⟨k4, w4⟩ => ?_
  have s4 : Scr t4 base large := k4.scr s3
  have c4 : Consts t4.mem base := by rw [k4.mem]; exact c3
  rw [WP.block_append_iff]
  refine WP.mono (join_ok t4) fun t5 ⟨k5, w5⟩ => ?_
  have s5 : Scr t5 base large := k5.scr s4
  have c5 : Consts t5.mem base := by rw [k5.mem]; exact c4
  rw [WP.block_append_iff]
  refine WP.mono (carry2_ok s5 c5) fun t6 ⟨k6, w6⟩ => ?_
  refine WP.mono (stores_ok (k6.scr s5)) fun t ⟨wt, om, og, or, ow, op⟩ => ?_
  have m0 : t6.mem = s.mem := by rw [k6.mem, k5.mem, k4.mem, k3.mem, k2.mem, k1.mem, k0.mem]
  refine ⟨fun e he => ?_, by rw [← m0]; exact om, by rw [og, k6.gpr, k5.gpr, k4.gpr, k3.gpr, k2.gpr, k1.gpr, k0.gpr],
    by rw [or, k6.rd, k5.rd, k4.rd, k3.rd, k2.rd, k1.rd, k0.rd], by rw [ow, k6.wr, k5.wr, k4.wr, k3.wr, k2.wr, k1.wr, k0.wr],
    by rw [op, k6.sp, k5.sp, k4.sp, k3.sp, k2.sp, k1.sp, k0.sp]⟩
  -- The columns.
  have hM : Mult t2.v e (fun k => lo t1.v k e) (fun k => hi t1.v k e) := {
    al := fun k hk => by rw [avk k hk, Nat.zero_add]; rfl
    ah := fun k hk => by rw [avk k hk]; rfl
    dl := fun k hk => by rw [((w2 k hk).1 (0 + e) (by omega_using [he])).1, Nat.zero_add]; rfl
    dh := fun k hk => ((w2 k hk).1 (2 + e) (by omega_using [he])).1
    nl := fun k hk => by rw [((w2 k hk).1 (0 + e) (by omega_using [he])).2, Nat.zero_add]; rfl
    nh := fun k hk => ((w2 k hk).1 (2 + e) (by omega_using [he])).2
    xl := fun k hk => by rw [Nat.zero_add]; exact ((w2 k hk).2 e he).1
    xh := fun k hk => ((w2 k hk).2 e he).2 }
  have hf : ∀ r ∈ firsts, ∀ c < 4, W (t2.v r) c < 2 ^ 27 := by
    intro r hr c hc'
    obtain ⟨k, hk, rfl | rfl | rfl⟩ := firsts_eq r hr
    · rw [avk k hk]; have := limW k hk c hc'; omega_using [this]
    · rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega_using [hc']) with rfl | rfl | rfl | rfl
      · have : W (t2.v (xv k)) 0 = 2 * W (t1.v (av k)) 2 := ((w2 k hk).2 0 (by decide)).1; have l := limW k hk 2 (by decide); rw [this]; omega_using [l]
      · have : W (t2.v (xv k)) 1 = 2 * W (t1.v (av k)) 3 := ((w2 k hk).2 1 (by decide)).1; have l := limW k hk 3 (by decide); rw [this]; omega_using [l]
      · have : W (t2.v (xv k)) 2 = 2 * W (t1.v (av k)) 0 := ((w2 k hk).2 0 (by decide)).2; have l := limW k hk 0 (by decide); rw [this]; omega_using [l]
      · have : W (t2.v (xv k)) 3 = 2 * W (t1.v (av k)) 1 := ((w2 k hk).2 1 (by decide)).2; have l := limW k hk 1 (by decide); rw [this]; omega_using [l]
    · rw [((w2 k hk).1 c hc').1]; have := limW k hk c hc'; omega_using [this]
  have hg : ∀ r ∈ seconds, ∀ c < 4, W (t2.v r) c < 2 ^ 31 := by
    intro r hr c hc'
    obtain ⟨k, hk, rfl | rfl⟩ := seconds_eq r hr
    · rw [avk k hk]; have := limW k hk c hc'; omega_using [this]
    · rw [((w2 k hk).1 c hc').2]; have := limW k hk c hc'; omega_using [this]
  have cl := col_lt he hf hg
  have w3' : ∀ m < 5, D (t3.v (ev m)) e = colE t2.v m e ∧ D (t3.v (cv m)) e = colC t2.v m e := fun m hm => by
    obtain ⟨x, y⟩ := w3 m hm e he
    obtain ⟨p, q⟩ := cl m hm
    exact ⟨x.trans (Nat.mod_eq_of_lt (Nat.lt_trans p (by decide))), y.trans (Nat.mod_eq_of_lt (Nat.lt_trans q (by decide)))⟩
  obtain ⟨E0, C0⟩ := w3' 0 (by decide)
  obtain ⟨E1, C1⟩ := w3' 1 (by decide)
  obtain ⟨E2, C2⟩ := w3' 2 (by decide)
  obtain ⟨E3, C3⟩ := w3' 3 (by decide)
  obtain ⟨E4, C4⟩ := w3' 4 (by decide)
  obtain ⟨e0l, c0l⟩ := cl 0 (by decide)
  obtain ⟨e1l, c1l⟩ := cl 1 (by decide)
  obtain ⟨e2l, c2l⟩ := cl 2 (by decide)
  obtain ⟨e3l, c3l⟩ := cl 3 (by decide)
  obtain ⟨e4l, c4l⟩ := cl 4 (by decide)
  simp only [ev, cv] at E0 C0 E1 C1 E2 C2 E3 C3 E4 C4
  have val := columns_value (lo t1.v 0 e) (hi t1.v 0 e) (lo t1.v 1 e) (hi t1.v 1 e) (lo t1.v 2 e) (hi t1.v 2 e)
    (lo t1.v 3 e) (hi t1.v 3 e) (lo t1.v 4 e) (hi t1.v 4 e)
  simp only [← colE_0 hM, ← colE_1 hM, ← colE_2 hM, ← colE_3 hM, ← colE_4 hM, ← colC_0 hM, ← colC_1 hM, ← colC_2 hM,
    ← colC_3 hM, ← colC_4 hM] at val
  -- The element.
  obtain ⟨a0, a1, a2, a3, a4⟩ := w1 e he
  obtain ⟨-, -, x0, x1, x2, x3⟩ := w0 e he
  have sv := split_value (w1 := D (t0.v .v25) e) (w3 := D (t0.v .v27) e) (D_lt (t0.v .v24) e) (D_lt (t0.v .v26) e)
  rw [← a0.1, ← a0.2, ← a1.1, ← a1.2, ← a2.1, ← a2.2, ← a3.1, ← a3.2, ← a4.1, ← a4.2, x0, x1, x2, x3] at sv
  rw [sv] at val
  clear sv a0 a1 a2 a3 a4 x0 x1 x2 x3 w0 w1 w2 w3 w3' hM hf hg cl lim limW avk
  generalize colE t2.v 0 e = e0 at *
  generalize colE t2.v 1 e = e1 at *
  generalize colE t2.v 2 e = e2 at *
  generalize colE t2.v 3 e = e3 at *
  generalize colE t2.v 4 e = e4 at *
  generalize colC t2.v 0 e = c0 at *
  generalize colC t2.v 1 e = c1 at *
  generalize colC t2.v 2 e = c2 at *
  generalize colC t2.v 3 e = c3 at *
  generalize colC t2.v 4 e = c4 at *
  -- The carries.
  obtain ⟨⟨f0, f1, f2, f3, f4⟩, ⟨g0, g1, g2, g3, g4⟩⟩ := w4 e he fun r => by
    by_cases hr : r ∈ cregs
    · refine Or.inl ?_
      simp only [cregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [E0]; exact e0l
      · rw [E1]; exact e1l
      · rw [E2]; exact e2l
      · rw [E3]; exact e3l
      · rw [E4]; exact e4l
      · rw [C0]; exact c0l
      · rw [C1]; exact c1l
      · rw [C2]; exact c2l
      · rw [C3]; exact c3l
      · rw [C4]; exact c4l
    · exact Or.inr hr
  rw [E0, C4] at f0
  rw [E1, C0] at f1
  rw [E2, C1] at f2
  rw [E3, C2] at f3
  rw [E4, C3] at f4
  rw [C0, E0] at g0
  rw [C1, E1] at g1
  rw [C2, E2] at g2
  rw [C3, E3] at g3
  rw [C4, E4] at g4
  obtain ⟨p0, p1, p2, p3, p4⟩ := w5 e he fun r hr => by
    simp only [cregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨by decide, by rw [f0]; omega_using [c4l]⟩
    · exact Or.inr ⟨by decide, by rw [f1]; omega_using [c0l]⟩
    · exact Or.inr ⟨by decide, by rw [f2]; omega_using [c1l]⟩
    · exact Or.inr ⟨by decide, by rw [f3]; omega_using [c2l]⟩
    · exact Or.inr ⟨by decide, by rw [f4]; omega_using [c3l]⟩
    · exact Or.inl (by rw [g0]; omega_using [e0l])
    · exact Or.inl (by rw [g1]; omega_using [e1l])
    · exact Or.inl (by rw [g2]; omega_using [e2l])
    · exact Or.inl (by rw [g3]; omega_using [e3l])
    · exact Or.inl (by rw [g4]; omega_using [e4l])
  rw [f0, g0] at p0
  rw [f1, g1] at p1
  rw [f2, g2] at p2
  rw [f3, g3] at p3
  rw [f4, g4] at p4
  obtain ⟨b0, b1, b2, b3, b4⟩ := reduce_lt e0l e1l e2l e3l e4l c0l c1l c2l c3l c4l p0 p1 p2 p3 p4
  obtain ⟨q0, q1, q2, q3, q4⟩ := w6 e he
  obtain ⟨o0, o1, o2, o3, o4⟩ := wt e he
  rw [← o0] at q0
  rw [← o1] at q1
  rw [← o2] at q2
  rw [← o3] at q3
  rw [← o4] at q4
  have v2 := carry2_value (D (t5.v .v20) e) (D (t5.v .v21) e) (D (t5.v .v22) e) (D (t5.v .v23) e) (D (t5.v .v24) e)
  have v1 := carry1_value e0 c0 e1 c1 e2 c2 e3 c3 e4 c4
  rw [← q0, ← q1, ← q2, ← q3, ← q4] at v2
  rw [← p0, ← p1, ← p2, ← p3, ← p4] at v1
  refine ⟨fun k hk => ?_, ?_⟩
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega_using [hk]) with rfl | rfl | rfl | rfl | rfl
    · rw [q0]; omega_using [b4]
    · rw [q1]; omega_using [b0]
    · rw [q2]; omega_using [b1]
    · rw [q3]; omega_using [b2]
    · rw [q4]; omega_using [b3]
  · rw [outVal, ← Nat.add_mul_mod_self_left _ VG.Spec.X25519.P (D (t5.v .v24) e / 2 ^ 51), v2,
      ← Nat.add_mul_mod_self_left _ VG.Spec.X25519.P (c4 / 2 ^ 25), v1]
    exact val

/-! ## The constants, and the callee-saved registers -/

theorem scr_of {s t : State} {base : Addr} (hs : Scr s base large) (h0 : t.gpr .x0 = s.gpr .x0) (hw : t.wr = s.wr) :
    Scr t base large := ⟨h0.trans hs.x0, hw ▸ hs.wr, hs.nowrap⟩

/-- A vector stored at `o`, in a state `t` that keeps all registers but `x4` and `v0`. -/
structure Const (base : Addr) (o : Nat) (x : BitVec 128) (s t : State) : Prop where
  here : t.mem.read (off base o) 16 = x
  mem : Outside base o 16 s.mem t.mem
  gpr : ∀ r, r ≠ .x4 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  v : ∀ r, r ≠ .v0 → t.v r = s.v r

theorem read16_write (m : Mem) (p : Addr) (v : BitVec 128) : (m.write p 16 v).read p 16 = v := by
  have := Mem.readW_writeW_self m p 16 v (by decide)
  simpa [Mem.readW, Mem.writeW] using this

theorem constant_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat} (h16 : o % 16 = 0) (ho : o + 16 ≤ 4096)
    (x : BitVec 64) : WP isa (.block (constant o x)) s (Const base o (ofVDwords x x) s) := by
  rw [show constant o x = [.movz .x .x4 (x.extractLsb' 0 16) 0, .movk .x .x4 (x.extractLsb' 16 16) 1,
    .movk .x .x4 (x.extractLsb' 32 16) 2, .movk .x .x4 (x.extractLsb' 48 16) 3] ++ [vo (.dup .d2 .v0 .x4), stq .v0 o] from rfl,
    WP.block_append_iff]
  have h1 : WP isa (.block [.movz .x .x4 (x.extractLsb' 0 16) 0, .movk .x .x4 (x.extractLsb' 16 16) 1,
      .movk .x .x4 (x.extractLsb' 32 16) 2, .movk .x .x4 (x.extractLsb' 48 16) 3]) s fun t =>
      t.gpr .x4 = x ∧ t.mem = s.mem ∧ (∀ r, r ≠ .x4 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.v = s.v := by
    refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_cons_iff.mpr ⟨_, rfl, WP.block_cons_iff.mpr ⟨_, rfl,
      WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ⟨?_, rfl, fun r hr => ?_, rfl, rfl, rfl⟩⟩⟩⟩⟩
    · simp only [State.write, State.read, Size.bits, BitVec.setWidth_eq, ite_true]
      exact movz_movk64' x
    · simp only [State.write, hr, ite_false]
  refine WP.mono h1 fun t ⟨t4, tm, tg, tr, tw, tv⟩ => ?_
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  rw [t4]
  refine WP.block_cons_iff.mpr ⟨_, exec_stq (scr_setV (scr_of hs (tg _ (by decide)) tw) _ _) .v0 h16 ho, WP.block_nil ?_⟩
  rw [RegUpd.v_setV_self, RegUpd.mem_setV, tm]
  exact ⟨read16_write _ _ _, write16_outside _ _ _ ho, tg, tr, tw,
    fun r hr => (RegUpd.v_setV_of_ne _ _ hr).trans (congrFun tv r)⟩

theorem D_dup (x : BitVec 64) {e : Nat} (he : e < 2) : D (ofVDwords x x) e = x.toNat := by
  rw [D, vdword_of _ _ he, ite_self]

theorem W19 : ∀ c < 4, W (ofVDwords 0x1300000013 0x1300000013) c = 19 := by decide

/-- The constants of the squares. -/
theorem constants_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block constants) s fun t => Consts t.mem base ∧ Outside base 1120 64 s.mem t.mem ∧
      (∀ r, r ≠ .x4 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ ∀ r, r ≠ .v0 → t.v r = s.v r := by
  rw [constants, WP.block_append_iff]
  refine WP.mono (constant_ok hs (by decide) (by decide) _) fun a ca => ?_
  have ha : Scr a base large := scr_of hs (ca.gpr _ (by decide)) ca.wr
  rw [WP.block_append_iff]
  refine WP.mono (constant_ok ha (by decide) (by decide) _) fun b cb => ?_
  have hb : Scr b base large := scr_of ha (cb.gpr _ (by decide)) cb.wr
  rw [WP.block_append_iff]
  refine WP.mono (constant_ok hb (by decide) (by decide) _) fun c cc => ?_
  have hc : Scr c base large := scr_of hb (cc.gpr _ (by decide)) cc.wr
  refine WP.mono (constant_ok hc (by decide) (by decide) _) fun t ct => ?_
  refine ⟨⟨fun e he => ?_, fun e he => ?_, fun e he => ?_, fun c hc' => ?_⟩, ?_, fun r hr => ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [read16_outside ct.mem (by decide) (by decide), read16_outside cc.mem (by decide) (by decide),
      read16_outside cb.mem (by decide) (by decide), ca.here, D_dup _ he]
    decide
  · rw [read16_outside ct.mem (by decide) (by decide), read16_outside cc.mem (by decide) (by decide), cb.here, D_dup _ he]
    decide
  · rw [read16_outside ct.mem (by decide) (by decide), cc.here, D_dup _ he]
    decide
  · rw [ct.here]
    exact W19 c hc'
  · exact (ca.mem.mono (by decide) (by decide)).trans ((cb.mem.mono (by decide) (by decide)).trans
      ((cc.mem.mono (by decide) (by decide)).trans (ct.mem.mono (by decide) (by decide))))
  · rw [ct.gpr r hr, cc.gpr r hr, cb.gpr r hr, ca.gpr r hr]
  · rw [ct.rd, cc.rd, cb.rd, ca.rd]
  · rw [ct.wr, cc.wr, cb.wr, ca.wr]
  · rw [ct.v r hr, cc.v r hr, cb.v r hr, ca.v r hr]

/-- The low halves of `v8`–`v15`, saved in the working space. -/
def SavedV (base : Addr) (v : VReg → BitVec 128) (m : Mem) : Prop :=
  ∀ k < 8, (m.read (off base (VSAVE + 16 * k)) 16).extractLsb' 0 64 = (v (vsaved k)).extractLsb' 0 64

theorem SavedV.outside {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : SavedV base v m) {o n : Nat}
    (ho : Outside base o n m m') (hx : o + n ≤ VSAVE ∨ VSAVE + 128 ≤ o) : SavedV base v m' := fun k hk => by
  have hV : VSAVE = 1184 := rfl
  rw [read16_outside ho (by omega_using [hx, hk]) (by omega_using [hk, hV])]
  exact h k hk

theorem vsaved_ne : ∀ k < 8, ∀ j < 8, k ≠ j → vsaved k ≠ vsaved j := by decide

theorem vsave_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block vsave) s fun t => SavedV base s.v t.mem ∧ Outside base VSAVE 128 s.mem t.mem ∧ t.gpr = s.gpr ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have hV : VSAVE = 1184 := rfl
  let inv := fun n (t : State) =>
    (∀ k < n, t.mem.read (off base (VSAVE + 16 * k)) 16 = s.v (vsaved k)) ∧
    Outside base VSAVE 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.v = s.v ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tO, tg, tvv, tr, tw⟩ => ?_) 8
    (by decide) s ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, rfl, rfl, rfl, rfl⟩)
    fun t ⟨tv, tO, tg, _, tr, tw⟩ => ⟨fun k hk => by rw [tv k hk], tO, tg, tr, tw⟩
  have ts : Scr t base large := scr_of hs (by rw [tg]) tw
  have wo := write16_outside t.mem base (t.v (vsaved n)) (d := VSAVE + 16 * n) (by omega_using [hV, hn])
  refine WP.block_cons_iff.mpr ⟨_, exec_stq ts (vsaved n) (d := VSAVE + 16 * n) (by omega_using [hV]) (by omega_using [hV, hn]),
    WP.block_nil ⟨fun k hk => ?_, tO.trans (wo.mono (by omega_using []) (by omega_using [hn])), tg, tvv, tr, tw⟩⟩
  show (t.mem.write _ 16 _).read _ 16 = _
  by_cases h : k = n
  · subst h; rw [read16_write, tvv]
  · rw [read16_outside wo (by omega_using [h]) (by omega_using [hV, hn, hk])]
    exact tv k (by omega_using [hk, h])

theorem vrestore_ok {s : State} {base : Addr} (hs : Scr s base large) {v : VReg → BitVec 128} (hv : SavedV base v s.mem) :
    WP isa (.block vrestore) s fun t =>
      (∀ k < 8, (t.v (vsaved k)).extractLsb' 0 64 = (v (vsaved k)).extractLsb' 0 64) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hV : VSAVE = 1184 := rfl
  let inv := fun n (t : State) =>
    (∀ k < n, (t.v (vsaved k)).extractLsb' 0 64 = (v (vsaved k)).extractLsb' 0 64) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tm, tg, tr, tw⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl, rfl, rfl⟩
  have ts : Scr t base large := scr_of hs (by rw [tg]) tw
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq ts (vsaved n) (d := VSAVE + 16 * n) (by omega_using [hV]) (by omega_using [hV, hn]),
    WP.block_nil ⟨fun k hk => ?_, by rw [RegUpd.mem_setV, tm], by rw [RegUpd.gpr_setV, tg], by rw [RegUpd.rd_setV, tr],
      by rw [RegUpd.wr_setV, tw]⟩⟩
  by_cases h : k = n
  · subst h; rw [RegUpd.v_setV_self, tm]; exact hv k hn
  · rw [RegUpd.v_setV_of_ne _ _ (vsaved_ne k (by omega_using [hk, hn]) n hn h)]
    exact tv k (by omega_using [hk, h])

end VG.Proof.X25519.AArch64.Squares
