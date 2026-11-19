module

public import VerifiedGarbage.Proof.Poly1305.X86.Blocks
public import VerifiedGarbage.Proof.Poly1305.Limbs26
public import VerifiedGarbage.Proof.Poly1305.Horner
public import VerifiedGarbage.Proof.Aes.X86.Common
import VerifiedGarbage.Proof.Mont.X86.Sse2.Lanes
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Poly1305 on x86: sixteen blocks or more, in two lanes with SSE2

Untrusted: everything here is checked by Lean. `pairs` (`Impl/Poly1305/X86.lean`)
absorbs pairs of blocks in the two 64-bit lanes of `xmm0`, …, `xmm4`.

## Lanes

A lane of a register is a natural number (`lane`); the instructions' effects
on it, without wrapping where the bounds say so.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Poly1305.X86.Sse2

open VG VG.X86

/-- Lane `l` (0 or 1) of a 128-bit value. -/
def lane (v : BitVec 128) (l : Nat) : Nat := (qword v l).toNat

theorem lane_eq (v : BitVec 128) (l : Nat) : lane v l = v.toNat / 2 ^ (64 * l) % 2 ^ 64 := by
  simp only [lane, qword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem lane_lt (v : BitVec 128) (l : Nat) : lane v l < 2 ^ 64 := (qword v l).isLt

theorem lane_append (x y : BitVec 64) : lane (x ++ y) 0 = y.toNat ∧ lane (x ++ y) 1 = x.toNat := by
  simp only [lane, Proof.Mont.X86.Sse2.qword_append_0, Proof.Mont.X86.Sse2.qword_append_1, and_self]

theorem lane_movdqa (a b : BitVec 128) (l : Nat) : lane (XBinOp.eval .movdqa a b) l = lane b l := rfl

theorem lane_paddq (a b : BitVec 128) {l : Nat} (hl : l < 2) :
    lane (XBinOp.eval .paddq a b) l = (lane a l + lane b l) % 2 ^ 64 := by
  simp only [lane, Proof.Mont.X86.Sse2.qword_paddq a b hl, BitVec.toNat_add]

/-- `paddq` where the sum does not wrap. -/
theorem lane_paddq' (a b : BitVec 128) {l : Nat} (hl : l < 2) (h : lane a l + lane b l < 2 ^ 64) :
    lane (XBinOp.eval .paddq a b) l = lane a l + lane b l := by
  rw [lane_paddq a b hl, Nat.mod_eq_of_lt h]

theorem lane_pand (a b : BitVec 128) (l : Nat) :
    lane (XBinOp.eval .pand a b) l = lane a l &&& lane b l := by
  show (qword (a &&& b) l).toNat = _
  simp only [lane, qword, BitVec.extractLsb'_and, BitVec.toNat_and]

theorem lane_punpcklqdq (a b : BitVec 128) :
    lane (XBinOp.eval .punpcklqdq a b) 0 = lane a 0 ∧ lane (XBinOp.eval .punpcklqdq a b) 1 = lane b 0 :=
  lane_append _ _

theorem lane_pmuludq (a b : BitVec 128) {l : Nat} (hl : l < 2) :
    lane (pmuludq a b) l = lane a l % 2 ^ 32 * (lane b l % 2 ^ 32) := by
  have e : ∀ (x : BitVec 128) (i : Nat), (dword x i).toNat = x.toNat / 2 ^ (32 * i) % 2 ^ 32 := fun x i => by
    simp only [dword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hm : ∀ x y : BitVec 32, (x.setWidth 64 * y.setWidth 64).toNat = x.toNat * y.toNat := fun x y => by
    rw [Proof.Mont.X86.Sse2.mul_setWidth, BitVec.toNat_ofNat]
    have hx := x.isLt
    have hy := y.isLt
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hx hy) (by decide))
  rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
  · rw [lane, Proof.Mont.X86.Sse2.qword_pmuludq_0, hm, e, e, lane_eq, lane_eq,
      show a.toNat / 2 ^ (64 * 0) % 2 ^ 64 % 2 ^ 32 = a.toNat / 2 ^ (32 * 0) % 2 ^ 32 by omega_arith,
      show b.toNat / 2 ^ (64 * 0) % 2 ^ 64 % 2 ^ 32 = b.toNat / 2 ^ (32 * 0) % 2 ^ 32 by omega_arith]
  · rw [lane, Proof.Mont.X86.Sse2.qword_pmuludq_1, hm, e, e, lane_eq, lane_eq,
      show a.toNat / 2 ^ (64 * 1) % 2 ^ 64 % 2 ^ 32 = a.toNat / 2 ^ (32 * 2) % 2 ^ 32 by omega_arith,
      show b.toNat / 2 ^ (64 * 1) % 2 ^ 64 % 2 ^ 32 = b.toNat / 2 ^ (32 * 2) % 2 ^ 32 by omega_arith]

theorem lane_psrlq (a : BitVec 128) (n : BitVec 8) (hn : n.toNat ≤ 63) {l : Nat} (hl : l < 2) :
    lane (XShiftOp.eval .psrlq a n) l = lane a l / 2 ^ n.toNat := by
  have e : XShiftOp.eval .psrlq a n = (qword a 1 >>> n.toNat) ++ (qword a 0 >>> n.toNat) := by
    change (if 63 < n.toNat then 0 else (qword a 1 >>> n.toNat) ++ (qword a 0 >>> n.toNat)) = _
    rw [ite_eq_right (by omega_using [hn])]
  rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
  · rw [e, (lane_append _ _).1, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; rfl
  · rw [e, (lane_append _ _).2, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; rfl

theorem lane_psllq (a : BitVec 128) (n : BitVec 8) (hn : n.toNat ≤ 63) {l : Nat} (hl : l < 2) :
    lane (XShiftOp.eval .psllq a n) l = lane a l * 2 ^ n.toNat % 2 ^ 64 := by
  have e : XShiftOp.eval .psllq a n = (qword a 1 <<< n.toNat) ++ (qword a 0 <<< n.toNat) := by
    change (if 63 < n.toNat then 0 else (qword a 1 <<< n.toNat) ++ (qword a 0 <<< n.toNat)) = _
    rw [ite_eq_right (by omega_using [hn])]
  rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
  · rw [e, (lane_append _ _).1, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; rfl
  · rw [e, (lane_append _ _).2, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; rfl

/-- The high lane moved to the low one. -/
theorem lane_psrldq8 (a : BitVec 128) :
    lane (XShiftOp.eval .psrldq a 8) 0 = lane a 1 ∧ lane (XShiftOp.eval .psrldq a 8) 1 = 0 := by
  have e : XShiftOp.eval .psrldq a 8 = a >>> 64 := rfl
  have ha := a.isLt
  simp only [e, lane_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega_using [ha]

/-- `movq` from memory and `movd` from a register: the high lane is zero. -/
theorem lane_movq (v : BitVec 64) : lane ((0 : BitVec 64) ++ v) 0 = v.toNat ∧ lane ((0 : BitVec 64) ++ v) 1 = 0 :=
  lane_append _ _

theorem lane_movd (r : BitVec 32) : lane ((0 : BitVec 96) ++ r) 0 = r.toNat ∧ lane ((0 : BitVec 96) ++ r) 1 = 0 := by
  have hr := r.isLt
  have h0 : ((0 : BitVec 96) ++ r).toNat = r.toNat := by
    rw [BitVec.toNat_append]
    show (0 : Nat) <<< 32 ||| r.toNat = r.toNat
    rw [Nat.zero_shiftLeft, Nat.zero_or]
  simp only [lane_eq, h0]
  omega_using [hr]

/-! ## The arithmetic of a lane

Five limbs `a 0`, …, `a 4` stand for `Limbs26.val a`. -/

open VG.Proof.Poly1305.Limbs26 (val)
open VG.Spec.Poly1305 (P)

/-- The limbs of a number: 26 bits each, the fifth with all the rest. -/
def lim (X : Nat) : Nat → Nat
  | 0 => X % 2 ^ 26
  | 1 => X / 2 ^ 26 % 2 ^ 26
  | 2 => X / 2 ^ 52 % 2 ^ 26
  | 3 => X / 2 ^ 78 % 2 ^ 26
  | _ => X / 2 ^ 104

theorem val_lim (X : Nat) : val (lim X) = X := by
  simp only [val, lim]
  omega_arith

theorem lim_lt (X : Nat) {k : Nat} (hk : k < 4) : lim X k < 2 ^ 26 := by
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    simp only [lim] <;> omega_arith

theorem lim4_lt {X B : Nat} (h : X < 2 ^ 104 * B) : lim X 4 < B := by
  simp only [lim]
  exact Nat.div_lt_of_lt_mul h

/-- A block's limbs with its `2¹²⁸`: only the fifth changes, by `2²⁴`. -/
theorem lim_pad (X : Nat) (k : Nat) :
    lim (X + 2 ^ 128) k = lim X k + (if k < 4 then 0 else 2 ^ 24) := by
  rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | rfl | rfl | h
  · simp only [lim, Nat.reduceLT, ite_true]; omega_arith
  · simp only [lim, Nat.reduceLT, ite_true]; omega_arith
  · simp only [lim, Nat.reduceLT, ite_true]; omega_arith
  · simp only [lim, Nat.reduceLT, ite_true]; omega_arith
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega_using [h]⟩
    simp only [lim, show ¬ j + 4 < 4 by omega_arith, ite_false]
    omega_arith

theorem val_add (a b : Nat → Nat) : val (fun k => a k + b k) = val a + val b := by
  simp only [val]
  omega_arith

/-- The multiplier of limb `i` in the sum `k`: a limb of `b`, or five times
one (as `x + x · 2²`, which is what the tables hold). -/
def cf (b : Nat → Nat) (k i : Nat) : Nat :=
  if i ≤ k then b (k - i) else b (k + 5 - i) + b (k + 5 - i) * 2 ^ 2

/-- The sums of products, in the order the code adds them. -/
def ds (a b : Nat → Nat) (k : Nat) : Nat :=
  cf b k 0 * a 0 + cf b k 1 * a 1 + cf b k 2 * a 2 + cf b k 3 * a 3 + cf b k 4 * a 4

theorem ds_mod (a b : Nat → Nat) : val (ds a b) % P = val a * val b % P := by
  have h := Limbs26.pd_val a b
  have e : val (ds a b) = val (Limbs26.pd a b) := by
    simp only [val, ds, cf, Limbs26.pd]
    simp only [Nat.zero_le, Nat.le_refl, ite_true, show ¬ (1 ≤ 0) by decide, show ¬ (2 ≤ 0) by decide,
      show ¬ (3 ≤ 0) by decide, show ¬ (4 ≤ 0) by decide, show ¬ (2 ≤ 1) by decide, show ¬ (3 ≤ 1) by decide,
      show ¬ (4 ≤ 1) by decide, show ¬ (3 ≤ 2) by decide, show ¬ (4 ≤ 2) by decide, show ¬ (4 ≤ 3) by decide,
      show (1 ≤ 1) by decide, show (1 ≤ 2) by decide, show (1 ≤ 3) by decide, show (1 ≤ 4) by decide,
      show (2 ≤ 2) by decide, show (2 ≤ 3) by decide, show (2 ≤ 4) by decide, show (3 ≤ 3) by decide,
      show (3 ≤ 4) by decide, show (4 ≤ 4) by decide, ite_false]
    grind
  rw [e, ← h, Nat.add_mul_mod_self_left]

theorem ds_lt {a b : Nat → Nat} {A B : Nat} (ha : ∀ k < 5, a k < A) (hb : ∀ k < 5, b k < B) {k : Nat} (hk : k < 5) :
    ds a b k < 25 * (A * B) + 1 := by
  have hc : ∀ i < 5, cf b k i ≤ 5 * B := fun i hi => by
    simp only [cf]
    by_cases hik : i ≤ k
    · rw [ite_eq_left hik]
      have := hb (k - i) (by omega_using [hk]); omega_using [this]
    · rw [ite_eq_right hik]
      have := hb (k + 5 - i) (by omega_using [hk, hi, hik]); omega_using [this]
  have hm : ∀ i < 5, cf b k i * a i ≤ 5 * B * A := fun i hi =>
    Nat.mul_le_mul (hc i hi) (Nat.le_of_lt (ha i hi))
  have h0 := hm 0 (by decide)
  have h1 := hm 1 (by decide)
  have h2 := hm 2 (by decide)
  have h3 := hm 3 (by decide)
  have h4 := hm 4 (by decide)
  simp only [ds]
  rw [show 25 * (A * B) = 5 * (5 * B * A) by grind]
  generalize 5 * B * A = Z at *
  omega_using [h0, h1, h2, h3, h4]

/-! The carries, in the order of `carryV`: `d0 → d1`, `d3 → d4`, `d1 → d2`,
`d4 → d0` (times 5), `d2 → d3`, `d0 → d1`, `d3 → d4`. -/

section
variable (d : Nat → Nat)

def x1 : Nat := d 1 + d 0 / 2 ^ 26
def x4 : Nat := d 4 + d 3 / 2 ^ 26
def x2 : Nat := d 2 + x1 d / 2 ^ 26
def z0 : Nat := d 0 % 2 ^ 26 + (x4 d / 2 ^ 26 + x4 d / 2 ^ 26 * 2 ^ 2)
def z3 : Nat := d 3 % 2 ^ 26 + x2 d / 2 ^ 26

/-- The limbs after the carries. -/
def cv : Nat → Nat
  | 0 => z0 d % 2 ^ 26
  | 1 => x1 d % 2 ^ 26 + z0 d / 2 ^ 26
  | 2 => x2 d % 2 ^ 26
  | 3 => z3 d % 2 ^ 26
  | _ => x4 d % 2 ^ 26 + z3 d / 2 ^ 26

theorem cv_val : val (cv d) + P * (x4 d / 2 ^ 26) = val d := by
  simp only [val, cv, z0, z3, x2, x4, x1, Limbs26.P_eq]
  omega_arith

theorem cv_mod : val (cv d) % P = val d % P := by
  rw [← cv_val d, Nat.add_mul_mod_self_left]

theorem cv_lt (h : ∀ k < 5, d k < 2 ^ 62) {k : Nat} (hk : k < 5) : cv d k < 2 ^ 26 + 2 ^ 14 := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [cv, z0, z3, x2, x4, x1] <;> omega_using [h0, h1, h2, h3, h4]

end

/-- A number whose limbs are all below `2²⁶ + 2¹⁴` is below `5 · 2¹²⁸`. -/
theorem val_lt_of_limbs {a : Nat → Nat} (h : ∀ k < 5, a k < 2 ^ 26 + 2 ^ 14) : val a < 5 * 2 ^ 128 := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  simp only [val]
  omega_using [h0, h1, h2, h3, h4]

/-! ## Two lanes

`A r² + B r` is the accumulator, for the lanes `A` and `B`. -/

open VG.Proof.Poly1305 (mv add_mod_congr mul_mod_congr absorbAll)

/-- The first pair of blocks: `A = h + m₁`, `B = m₂`. -/
theorem pair_init {r r2 h X : Nat} {b1 b2 : List Byte} (h1 : b1.length = 16) (h2 : b2.length = 16)
    (hr : r2 % P = r * r % P) (hh : h % P = X % P) :
    ((h + mv b1) * r2 + mv b2 * r) % P = absorbAll r X (b1 ++ b2) % P := by
  rw [Poly1305.absorbAll_append (x := b1) (y := b2) (by omega_using [h1]),
    Poly1305.absorbAll_block (b := b1) (by omega_using [h1]) (by omega_using [h1]),
    Poly1305.absorbAll_block (b := b2) (by omega_using [h2]) (by omega_using [h2]), Nat.mod_mod]
  have e1 : (r * (r * (X + mv b1) % P + mv b2)) % P = (r * (r * (h + mv b1) + mv b2)) % P :=
    mul_mod_congr r (add_mod_congr ((Nat.mod_mod _ _).trans (mul_mod_congr r (add_mod_congr hh.symm rfl))) rfl)
  rw [e1, show r * (r * (h + mv b1) + mv b2) = (h + mv b1) * (r * r) + mv b2 * r by grind,
    show (h + mv b1) * r2 + mv b2 * r = mv b2 * r + (h + mv b1) * r2 by grind,
    show (h + mv b1) * (r * r) + mv b2 * r = mv b2 * r + (h + mv b1) * (r * r) by grind]
  exact add_mod_congr rfl (mul_mod_congr _ hr)

/-- A further pair: `A' = A r² + m`, `B' = B r² + m'`. -/
theorem pair_step {r r2 A B A' B' X : Nat} {x b1 b2 : List Byte} (hx : x.length % 16 = 0) (h1 : b1.length = 16)
    (h2 : b2.length = 16) (hr : r2 % P = r * r % P) (hS : (A * r2 + B * r) % P = absorbAll r X x % P)
    (hA : A' % P = (A * r2 + mv b1) % P) (hB : B' % P = (B * r2 + mv b2) % P) :
    (A' * r2 + B' * r) % P = absorbAll r X (x ++ b1 ++ b2) % P := by
  rw [List.append_assoc, Poly1305.absorbAll_append hx]
  refine Eq.trans ?_ (pair_init (h := A * r2 + B * r) h1 h2 hr hS)
  have e : (A' * r2 + B' * r) % P = ((A * r2 + mv b1) * r2 + (B * r2 + mv b2) * r) % P := by
    rw [Nat.mul_comm A', Nat.mul_comm B', Nat.mul_comm (A * r2 + mv b1), Nat.mul_comm (B * r2 + mv b2)]
    exact add_mod_congr (mul_mod_congr _ hA) (mul_mod_congr _ hB)
  rw [e]
  congr 1
  grind

/-! ## Blocks of SSE instructions -/

open VG.X86.RegUpd
open VG.Impl.Poly1305.X86

/-- Lane `l` of register `x`. -/
abbrev ln (s : State) (x : XReg) (l : Nat) : Nat := lane (s.xmm x) l

/-- What a block of SSE instructions on the registers `xs` keeps. -/
structure Xk (xs : List XReg) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mcdt : s'.mcdt = s.mcdt
  xmm : ∀ r, r ∉ xs → s'.xmm r = s.xmm r

theorem Xk.refl (xs : List XReg) (s : State) : Xk xs s s := ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Xk.trans {xs ys : List XReg} {s s' s'' : State} (h : Xk xs s s') (h' : Xk ys s' s'') :
    Xk (xs ++ ys) s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.mcdt.trans h.mcdt, fun r hr => by
    simp only [List.mem_append, not_or] at hr
    exact (h'.xmm r hr.2).trans (h.xmm r hr.1)⟩

theorem Xk.mono {xs ys : List XReg} {s s' : State} (h : Xk xs s s') (hs : ∀ r ∈ xs, r ∈ ys) : Xk ys s s' :=
  ⟨h.gpr, h.rd, h.wr, h.mcdt, fun r hr => h.xmm r fun h' => hr (hs r h')⟩

/-- Limb `k` of a block, from its 8 bytes `q` from byte `lbyte k` on. -/
def limbv (q k : Nat) : Nat := q / 2 ^ lshift k % 2 ^ 26

theorem lshift_le (k : Nat) : lshift k ≤ 40 := by
  rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | rfl | rfl | h
  · decide
  · decide
  · decide
  · decide
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega_using [h]⟩
    show (40 : Nat) ≤ 40; decide

theorem setXmm_xk (s : State) (x : XReg) (v : BitVec 128) : Xk [x] s (s.setXmm x v) :=
  ⟨rfl, rfl, rfl, rfl, fun r hr => xmm_setXmm_of_ne _ _ (by simpa only [List.mem_singleton] using hr)⟩

theorem and_mask (x : Nat) : x &&& (2 ^ 26 - 1) = x % 2 ^ 26 := Nat.and_two_pow_sub_one_eq_mod x 26

/-- `limb`: 8 bytes (or twice 8 bytes), shifted and masked, into the lanes of `xmm6`. -/
theorem limb_ok (b : Reg) (d n : Nat) (hn : n ≤ 63) (two : Bool) (s : State)
    (hm : ∀ l < 2, ln s .xmm5 l = 2 ^ 26 - 1)
    (h0 : InRegions (s.rd ++ s.wr) (addr (s.gpr b) d) 8)
    (h1 : two = true → InRegions (s.rd ++ s.wr) (addr (s.gpr b) (d + 16)) 8) :
    WP isa (.block (limb b d n two)) s fun s' =>
      ln s' .xmm6 0 = (s.mem.readW (addr (s.gpr b) d) 64).toNat / 2 ^ n % 2 ^ 26 ∧
      ln s' .xmm6 1 = (if two = true then (s.mem.readW (addr (s.gpr b) (d + 16)) 64).toNat / 2 ^ n % 2 ^ 26
        else 0) ∧ s'.mem = s.mem ∧ Xk [.xmm6, .xmm7] s s' := by
  have e0 : s.ea (at_ b d) = addr (s.gpr b) d := rfl
  have m0 := hm 0 (by decide)
  have m1 := hm 1 (by decide)
  have hs : (BitVec.ofNat 8 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hn])
  have hsh : (BitVec.ofNat 8 n).toNat ≤ 63 := by rw [hs]; exact hn
  cases two
  · apply WP.of_runBlock
    simp only [limb, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.nil_append, List.cons_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load64, e0, h0, Option.map_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, ?_, rfl, ?_⟩
    · simp only [ln, xmm_setXmm_self, xmm_setXmm, reduceCtorEq, ↓reduceIte, lane_pand, lane_psrlq _ _ hsh
        (show 0 < 2 by decide), (lane_movq _).1, hs, and_mask, show lane (s.xmm .xmm5) 0 = 2 ^ 26 - 1 from m0]
    · simp only [ln, xmm_setXmm_self, xmm_setXmm, reduceCtorEq, ↓reduceIte, lane_pand, lane_psrlq _ _ hsh
        (show 1 < 2 by decide), (lane_movq _).2, Nat.zero_and, Nat.zero_div]
    · refine ⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [xmm_setXmm, hr.1, hr.2, ↓reduceIte]
  · have h1' := h1 rfl
    have e1 : ∀ v, (s.setXmm .xmm6 v).ea (at_ b (d + 16)) = addr (s.gpr b) (d + 16) := fun _ => rfl
    apply WP.of_runBlock
    simp only [limb, ↓reduceIte, List.append_nil, List.nil_append, List.cons_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load64, e0, h0, Option.map_some,
      Option.some.injEq, exists_eq_left', e1, rd_setXmm, wr_setXmm, mem_setXmm, h1']
    refine ⟨?_, ?_, trivial, ?_⟩
    · simp only [ln, xmm_setXmm_self, xmm_setXmm, reduceCtorEq, ↓reduceIte, lane_pand, lane_psrlq _ _ hsh
        (show 0 < 2 by decide), (lane_punpcklqdq _ _).1, (lane_movq _).1, hs, and_mask,
        show lane (s.xmm .xmm5) 0 = 2 ^ 26 - 1 from m0]
    · simp only [ln, xmm_setXmm_self, xmm_setXmm, reduceCtorEq, ↓reduceIte, lane_pand, lane_psrlq _ _ hsh
        (show 1 < 2 by decide), (lane_punpcklqdq _ _).2, (lane_movq _).1, hs, and_mask,
        show lane (s.xmm .xmm5) 1 = 2 ^ 26 - 1 from m1]
    · refine ⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [xmm_setXmm, hr.1, hr.2, ↓reduceIte]

/-! ### A block's limbs -/

open VG.Spec.Poly1305 (leNum bytesAt)

theorem leNum_bytes_lt (m : Mem) (p : Addr) (n : Nat) : leNum (bytesAt m p n) < 2 ^ (8 * n) := by
  rw [Poly1305.leNum_bytesAt_read]; exact (m.read p n).isLt

theorem readW64_num (m : Mem) (p : Addr) : (m.readW p 64).toNat = leNum (bytesAt m p 8) := by
  rw [Poly1305.leNum_bytesAt_read]; simp only [Nat.reduceMul, Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

/-- The 8 bytes from byte 0, 6 and 8 of 16 bytes, as parts of their number. -/
theorem read64_0 (m : Mem) (a : Addr) : (m.readW a 64).toNat = leNum (bytesAt m a 16) % 2 ^ 64 := by
  have h := leNum_bytes_lt m a 8
  rw [show 16 = 8 + 8 from rfl, Poly1305.bytesAt_add, Poly1305.leNum_append, Poly1305.length_bytesAt, readW64_num]
  omega_using [h]

theorem read64_8 (m : Mem) (a : Addr) :
    (m.readW (a + BitVec.ofNat 64 8) 64).toNat = leNum (bytesAt m a 16) / 2 ^ 64 % 2 ^ 64 := by
  have h := leNum_bytes_lt m a 8
  have h' := leNum_bytes_lt m (a + BitVec.ofNat 64 8) 8
  rw [show 16 = 8 + 8 from rfl, Poly1305.bytesAt_add, Poly1305.leNum_append, Poly1305.length_bytesAt, readW64_num]
  omega_using [h, h']

theorem read64_6 (m : Mem) (a : Addr) :
    (m.readW (a + BitVec.ofNat 64 6) 64).toNat = leNum (bytesAt m a 16) / 2 ^ 48 % 2 ^ 64 := by
  have h := leNum_bytes_lt m a 6
  have h' := leNum_bytes_lt m (a + BitVec.ofNat 64 6) 8
  rw [show 16 = 6 + (8 + 2) from rfl, Poly1305.bytesAt_add, Poly1305.bytesAt_add, Poly1305.leNum_append,
    Poly1305.leNum_append, Poly1305.length_bytesAt, Poly1305.length_bytesAt, readW64_num]
  generalize leNum (bytesAt m (a + BitVec.ofNat 64 6 + BitVec.ofNat 64 8) 2) = z
  omega_using [h, h']

theorem lbyte_le (k : Nat) : lbyte k ≤ 8 := by
  rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | rfl | h
  · decide
  · decide
  · decide
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega_using [h]⟩
    show (8 : Nat) ≤ 8; decide

/-- The limbs the code extracts are the limbs of the 16 bytes' number. -/
theorem limbv_read (m : Mem) (a : Addr) {k : Nat} (hk : k < 5) :
    limbv (m.readW (a + BitVec.ofNat 64 (lbyte k)) 64).toNat k = lim (leNum (bytesAt m a 16)) k := by
  have hX := leNum_bytes_lt m a 16
  have e0 := read64_0 m a
  have e6 := read64_6 m a
  have e8 := read64_8 m a
  generalize leNum (bytesAt m a 16) = X at *
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
  · simp only [limbv, lbyte, lshift, lim, BitVec.add_zero, e0]; omega_using [hX]
  · simp only [limbv, lbyte, lshift, lim, BitVec.add_zero, e0]; omega_using [hX]
  · simp only [limbv, lbyte, lshift, lim, e6]; omega_using [hX]
  · simp only [limbv, lbyte, lshift, lim, e8]; omega_using [hX]
  · simp only [limbv, lbyte, lshift, lim, e8]; omega_using [hX]

/-- An address at an offset of an address at an offset. -/
theorem addr_add {x : BitVec 32} {d j : Nat} (h : x.toNat + d + j < 2 ^ 32) :
    addr x (d + j) = addr x d + BitVec.ofNat 64 j := by
  rw [addr_eq (by omega_using [h]), addr_eq (by omega_using [h]), BitVec.add_assoc, ← BitVec.ofNat_add]

theorem lreg_ne (k : Nat) : lreg k ≠ .xmm5 ∧ lreg k ≠ .xmm6 ∧ lreg k ≠ .xmm7 := by
  rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | rfl | rfl | h
  · decide
  · decide
  · decide
  · decide
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega_using [h]⟩
    exact ⟨by show XReg.xmm4 ≠ _; decide, by show XReg.xmm4 ≠ _; decide, by show XReg.xmm4 ≠ _; decide⟩

/-- The number of the 16 bytes of block `l` (0 or 1) at `dp`. -/
abbrev blkN (m : Mem) (dp : BitVec 32) (l : Nat) : Nat :=
  leNum (bytesAt m (dp.setWidth 64 + BitVec.ofNat 64 (16 * l)) 16)

/-- `[esp + o + d]` is the byte `d` of the frame at `B`. -/
theorem ea_fs {s : State} {o : Nat} {B : BitVec 32} (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) (d : Nat) :
    s.ea (fs o d) = addr B d := by
  simp only [fs, at_, State.ea, addr, ← hsp, BitVec.ofNat_add, BitVec.add_assoc]

/-- `x += y` on the lanes, where the sums do not wrap. -/
theorem paddq_ok (x y : XReg) (s : State) (h : ∀ l < 2, ln s x l + ln s y l < 2 ^ 64) :
    WP isa (.block [.xop (.bin .paddq x y)]) s fun s' =>
      (∀ l < 2, ln s' x l = ln s x l + ln s y l) ∧ s'.mem = s.mem ∧ Xk [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, Option.some.injEq, exists_eq_left']
  exact ⟨fun l hl => by rw [ln, xmm_setXmm_self, lane_paddq' _ _ hl (h l hl)], rfl, setXmm_xk _ _ _⟩

/-- The limbs `k` of the two blocks at `esi`, added to the lanes of limb `k`. -/
theorem addLimb_ok (dp : BitVec 32) (k : Nat) (hk : k < 5) (s : State) (hesi : s.gpr .esi = dp)
    (hfit : dp.toNat + 32 ≤ 2 ^ 32) (hrd : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (addr dp d) 8)
    (hm : ∀ l < 2, ln s .xmm5 l = 2 ^ 26 - 1) (hb : ∀ l < 2, ln s (lreg k) l < 2 ^ 63) :
    WP isa (.block (limb .esi (lbyte k) (lshift k) true ++ ([.xop (.bin .paddq (lreg k) .xmm6)] : List Instr))) s fun s' =>
      (∀ l < 2, ln s' (lreg k) l = ln s (lreg k) l + lim (blkN s.mem dp l) k) ∧ s'.mem = s.mem ∧
      Xk [.xmm6, .xmm7, lreg k] s s' := by
  have hl := lbyte_le k
  obtain ⟨n5, n6, n7⟩ := lreg_ne k
  have hsl := lshift_le k
  refine WP.block_append (WP.mono (limb_ok .esi (lbyte k) (lshift k) (by omega_using [hsl]) true s hm
    (by rw [hesi]; exact hrd _ (by omega_using [hl])) (fun _ => by rw [hesi]; exact hrd _ (by omega_using [hl])))
    fun s₁ ⟨a0, a1, m₁, k₁⟩ => ?_)
  have v0 : ln s₁ .xmm6 0 = lim (blkN s.mem dp 0) k := by
    rw [a0, hesi, ← limbv_read _ _ hk, Nat.mul_zero, BitVec.add_zero, addr_eq (by omega_using [hfit, hl])]
    rfl
  have v1 : ln s₁ .xmm6 1 = lim (blkN s.mem dp 1) k := by
    rw [a1, ite_eq_left rfl, hesi, ← limbv_read _ _ hk, Nat.mul_one, Nat.add_comm (lbyte k) 16,
      addr_add (by omega_using [hfit, hl]), addr_eq (by omega_using [hfit])]
    rfl
  have hx : ∀ l < 2, ln s₁ (lreg k) l = ln s (lreg k) l := fun l _ => by
    rw [ln, k₁.xmm _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨n6, n7⟩)]
  have hv : ∀ l < 2, ln s₁ .xmm6 l = lim (blkN s.mem dp l) k := fun l hl' => by
    rcases (by omega_using [hl'] : l = 0 ∨ l = 1) with rfl | rfl
    · exact v0
    · exact v1
  have hlt : ∀ l < 2, lim (blkN s.mem dp l) k < 2 ^ 26 := fun l _ => by
    rcases (by omega_using [hk] : k < 4 ∨ k = 4) with h | rfl
    · exact lim_lt _ h
    · exact Nat.lt_of_lt_of_le (lim4_lt (B := 2 ^ 24) (by have := leNum_bytes_lt s.mem (dp.setWidth 64 + BitVec.ofNat 64 (16 * l)) 16; omega_using [this])) (by decide)
  refine WP.mono (paddq_ok (lreg k) .xmm6 s₁ fun l hl' => by
    rw [hx l hl', hv l hl']; have := hb l hl'; have := hlt l hl'; omega_arith) fun s₂ ⟨a₂, m₂, k₂⟩ => ?_
  exact ⟨fun l hl' => by rw [a₂ l hl', hx l hl', hv l hl'], m₂.trans m₁, k₁.trans k₂⟩

/-! ### The frame's slots -/

/-- The frame at `B` does not wrap around. -/
abbrev Fit (B : BitVec 32) : Prop := B.toNat + 512 ≤ 2 ^ 32

theorem slot_same (m : Mem) (a : Addr) (v : BitVec 128) : (m.writeW a v).readW a 128 = v :=
  Mem.readW_writeW_self m a 16 v (by decide)

theorem slot_other {B : BitVec 32} (hB : Fit B) (m : Mem) (v : BitVec 128) {d e : Nat} (hd : d + 16 ≤ 512)
    (he : e + 16 ≤ 512) (h : d + 16 ≤ e ∨ e + 16 ≤ d) :
    (m.writeW (addr B e) v).readW (addr B d) 128 = m.readW (addr B d) 128 :=
  Mem.readW_writeW_sep ((Proof.Aes.X86.part_disj hB hd he h).sep (Region.contains_self _ _)
    (Region.contains_self _ _)) (by decide)

/-- The frame is writable. -/
theorem fr_in {B : BitVec 32} (hB : Fit B) {rs : List Region} (hr : Proof.Aes.X86.reg32 B 512 ∈ rs) {d n : Nat}
    (hd : d + n ≤ 512) (hn : 0 < n) : InRegions rs (addr B d) n :=
  Proof.Aes.X86.in_reg hr hB hd hn

theorem mcdt_setXmm (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).mcdt = s.mcdt := rfl

/-- A slot of the frame into a register. -/
theorem loadSlot_ok (x : XReg) {o : Nat} {B : BitVec 32} (d : Nat) (s : State)
    (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) (hin : InRegions (s.rd ++ s.wr) (addr B d) 16) :
    WP isa (.block [.movdquLoad x (fs o d)]) s fun s' =>
      s'.xmm x = s.mem.readW (addr B d) 128 ∧ s'.mem = s.mem ∧ Xk [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, ea_fs hsp, hin, ↓reduceIte,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨xmm_setXmm_self _ _ _, rfl, setXmm_xk _ _ _⟩

/-- A register into a slot of the frame. -/
theorem storeSlot_ok (x : XReg) {o : Nat} {B : BitVec 32} (d : Nat) (s : State)
    (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) (hin : InRegions s.wr (addr B d) 16) :
    WP isa (.block [.movdquStore (fs o d) x]) s fun s' =>
      s'.mem = s.mem.writeW (addr B d) (s.xmm x) ∧ Xk [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store128, ea_fs hsp, hin, ↓reduceIte,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- The tables in the frame: the limbs `tb t l k` of the multiplier of lane
`l` in table `t` and their multiples by 5, the mask and the bit `2²⁴`. -/
structure Tab (m : Mem) (B : BitVec 32) (tb : Nat → Nat → Nat → Nat) : Prop where
  rs : ∀ t < 2, ∀ k < 5, ∀ l < 2, lane (m.readW (addr B (rSlot t k)) 128) l = tb t l k
  ss : ∀ t < 2, ∀ k < 5, ∀ l < 2,
    lane (m.readW (addr B (sSlot t k)) 128) l = tb t l k + tb t l k * 2 ^ 2
  mask : ∀ l < 2, lane (m.readW (addr B maskSlot) 128) l = 2 ^ 26 - 1
  hibit : ∀ l < 2, lane (m.readW (addr B hibitSlot) 128) l = 2 ^ 24

/-- The tables are in the slots before slot 22. -/
theorem Tab.congr {m m' : Mem} {B : BitVec 32} {tb : Nat → Nat → Nat → Nat} (h : Tab m B tb)
    (he : ∀ j < 22, m'.readW (addr B (slot j)) 128 = m.readW (addr B (slot j)) 128) : Tab m' B tb :=
  ⟨fun t ht k hk l hl => by rw [rSlot, he _ (by omega_using [ht, hk])]; exact h.rs t ht k hk l hl,
    fun t ht k hk l hl => by rw [sSlot, he _ (by omega_using [ht, hk])]; exact h.ss t ht k hk l hl,
    fun l hl => by rw [maskSlot, he _ (by decide)]; exact h.mask l hl,
    fun l hl => by rw [hibitSlot, he _ (by decide)]; exact h.hibit l hl⟩

/-- A store to a slot from 22 on keeps the tables. -/
theorem Tab.store {m : Mem} {B : BitVec 32} {tb : Nat → Nat → Nat → Nat} (h : Tab m B tb) (hB : Fit B) {e : Nat}
    (he : 416 ≤ e) (he' : e + 16 ≤ 512) (v : BitVec 128) : Tab (m.writeW (addr B e) v) B tb :=
  h.congr fun j hj => slot_other hB m v (by simp only [slot]; omega_using [hj]) he'
    (.inl (by simp only [slot]; omega_using [hj, he]))

/-- The multiplier of limb `i` in the sum `k`. -/
theorem Tab.mul {m : Mem} {B : BitVec 32} {tb : Nat → Nat → Nat → Nat} (h : Tab m B tb) {t k i l : Nat}
    (ht : t < 2) (hk : k < 5) (_hi : i < 5) (hl : l < 2) :
    lane (m.readW (addr B (mslot t k i)) 128) l = cf (tb t l) k i := by
  simp only [Impl.Poly1305.X86.mslot, cf]
  by_cases hik : i ≤ k
  · rw [ite_eq_left hik, ite_eq_left hik]; exact h.rs t ht _ (by omega_using [hk]) l hl
  · rw [ite_eq_right hik, ite_eq_right hik]
    exact h.ss t ht _ (by omega_using [hik, hk]) l hl

theorem mslot_le (t k i : Nat) (ht : t < 2) (hk : k < 5) (hi : i < 5) : mslot t k i + 16 ≤ 416 := by
  simp only [mslot, rSlot, sSlot, slot]
  by_cases hik : i ≤ k
  · rw [ite_eq_left hik]; omega_using [ht, hk, hi, hik]
  · rw [ite_eq_right hik]; omega_using [ht, hk, hi, hik]

/-! ### The message -/

theorem lreg_inj {j k : Nat} (hj : j < 5) (hk : k < 5) (h : lreg j = lreg k) : j = k := by
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl <;>
  first | rfl | exact absurd h (by decide)

/-- The registers of the limbs, and the two temporaries. -/
abbrev lregs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm6, .xmm7]

theorem lreg_mem {k : Nat} : lreg k ∈ lregs := by
  rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | rfl | rfl | h
  · decide
  · decide
  · decide
  · decide
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega_using [h]⟩
    show XReg.xmm4 ∈ lregs; decide

/-- After the limbs before `j` of the two blocks have been added. -/
structure AMInv (dp : BitVec 32) (s : State) (j : Nat) (s' : State) : Prop where
  add : ∀ l < 2, ∀ k < 5, ln s' (lreg k) l = ln s (lreg k) l + (if k < j then lim (blkN s.mem dp l) k else 0)
  mem : s'.mem = s.mem
  keep : Xk lregs s s'

theorem addLimb_step (dp : BitVec 32) {j : Nat} (hj : j < 5) {s s₁ : State} (hesi : s.gpr .esi = dp)
    (hfit : dp.toNat + 32 ≤ 2 ^ 32) (hrd : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (addr dp d) 8)
    (hm : ∀ l < 2, ln s .xmm5 l = 2 ^ 26 - 1) (hb : ∀ l < 2, ∀ k < 5, ln s (lreg k) l < 2 ^ 63)
    (h : AMInv dp s j s₁) :
    WP isa (.block (limb .esi (lbyte j) (lshift j) true ++ ([.xop (.bin .paddq (lreg j) .xmm6)] : List Instr))) s₁
      (AMInv dp s (j + 1)) := by
  have x5 : s₁.xmm .xmm5 = s.xmm .xmm5 := h.keep.xmm _ (by decide)
  refine WP.mono (addLimb_ok dp j hj s₁ (by rw [h.keep.gpr]; exact hesi) hfit
    (by rw [h.keep.rd, h.keep.wr]; exact hrd) (fun l hl => by rw [ln, x5]; exact hm l hl)
    (fun l hl => by rw [h.add l hl j hj, ite_eq_right (Nat.lt_irrefl j), Nat.add_zero]; exact hb l hl j hj))
    fun s₂ ⟨a₂, m₂, k₂⟩ => ?_
  refine ⟨fun l hl k hk => ?_, by rw [m₂, h.mem], (h.keep.trans k₂).mono fun r hr => ?_⟩
  · by_cases hkj : k = j
    · subst hkj
      rw [a₂ l hl, h.add l hl k hk, ite_eq_right (Nat.lt_irrefl k), Nat.add_zero,
        ite_eq_left (Nat.lt_succ_self k), h.mem]
    · have hne : lreg k ≠ lreg j := fun e => hkj (lreg_inj hk hj e)
      obtain ⟨-, n6, n7⟩ := lreg_ne k
      have e₂ : ln s₂ (lreg k) l = ln s₁ (lreg k) l := by
        rw [ln, k₂.xmm _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨n6, n7, hne⟩)]
      rw [e₂, h.add l hl k hk]
      by_cases hlt : k < j
      · rw [ite_eq_left hlt, ite_eq_left (by omega_using [hlt])]
      · rw [ite_eq_right hlt, ite_eq_right (by omega_using [hlt, hkj])]
  · rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · decide
      · decide
      · exact lreg_mem

/-- `addMsg`: the limbs of the two blocks at `esi`, with their `2¹²⁸`, added
to the lanes. -/
theorem addMsg_ok {o : Nat} {B dp : BitVec 32} {tb : Nat → Nat → Nat → Nat} (s : State)
    (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) (hB : Fit B) (hfr : Proof.Aes.X86.reg32 B 512 ∈ s.wr)
    (hesi : s.gpr .esi = dp) (hfit : dp.toNat + 32 ≤ 2 ^ 32)
    (hrd : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (addr dp d) 8) (ht : Tab s.mem B tb)
    (hm : ∀ l < 2, ln s .xmm5 l = 2 ^ 26 - 1) (hb : ∀ l < 2, ∀ k < 5, ln s (lreg k) l < 2 ^ 62) :
    WP isa (.block (addMsg o)) s fun s' =>
      (∀ l < 2, ∀ k < 5, ln s' (lreg k) l = ln s (lreg k) l + lim (blkN s.mem dp l + 2 ^ 128) k) ∧
      s'.mem = s.mem ∧ Xk lregs s s' := by
  have hb' : ∀ l < 2, ∀ k < 5, ln s (lreg k) l < 2 ^ 63 := fun l hl k hk =>
    Nat.lt_trans (hb l hl k hk) (by decide)
  have e : addMsg o = (limb .esi (lbyte 0) (lshift 0) true ++ ([.xop (.bin .paddq (lreg 0) .xmm6)] : List Instr)) ++
      ((limb .esi (lbyte 1) (lshift 1) true ++ ([.xop (.bin .paddq (lreg 1) .xmm6)] : List Instr)) ++
      ((limb .esi (lbyte 2) (lshift 2) true ++ ([.xop (.bin .paddq (lreg 2) .xmm6)] : List Instr)) ++
      ((limb .esi (lbyte 3) (lshift 3) true ++ ([.xop (.bin .paddq (lreg 3) .xmm6)] : List Instr)) ++
      ((limb .esi (lbyte 4) (lshift 4) true ++ ([.xop (.bin .paddq (lreg 4) .xmm6)] : List Instr)) ++
      (([.movdquLoad .xmm7 (fs o hibitSlot)] : List Instr) ++ [.xop (.bin .paddq .xmm4 .xmm7)]))))) := by
    simp only [addMsg, List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  have i0 : AMInv dp s 0 s := ⟨fun _ _ _ _ => by rw [ite_eq_right (Nat.not_lt_zero _), Nat.add_zero], rfl, Xk.refl _ _⟩
  refine WP.block_append (WP.mono (addLimb_step dp (by decide) hesi hfit hrd hm hb' i0) fun s₁ i₁ => ?_)
  refine WP.block_append (WP.mono (addLimb_step dp (by decide) hesi hfit hrd hm hb' i₁) fun s₂ i₂ => ?_)
  refine WP.block_append (WP.mono (addLimb_step dp (by decide) hesi hfit hrd hm hb' i₂) fun s₃ i₃ => ?_)
  refine WP.block_append (WP.mono (addLimb_step dp (by decide) hesi hfit hrd hm hb' i₃) fun s₄ i₄ => ?_)
  refine WP.block_append (WP.mono (addLimb_step dp (by decide) hesi hfit hrd hm hb' i₄) fun s₅ i₅ => ?_)
  have hsp₅ : s₅.gpr .esp + BitVec.ofNat 32 o = B := by rw [i₅.keep.gpr]; exact hsp
  have hin₅ : InRegions (s₅.rd ++ s₅.wr) (addr B hibitSlot) 16 := by
    rw [i₅.keep.rd, i₅.keep.wr]
    exact Proof.Aes.X86.in_rd (fr_in hB hfr (show hibitSlot + 16 ≤ 512 by decide) (by decide))
  refine WP.block_append (WP.mono (loadSlot_ok .xmm7 hibitSlot s₅ hsp₅ hin₅)
    fun s₆ ⟨v₆, m₆, k₆⟩ => ?_)
  have h7 : ∀ l < 2, ln s₆ .xmm7 l = 2 ^ 24 := fun l hl => by rw [ln, v₆, i₅.mem]; exact ht.hibit l hl
  have h4 : ∀ l < 2, ln s₆ .xmm4 l = ln s .xmm4 l + lim (blkN s.mem dp l) 4 := fun l hl => by
    rw [ln, k₆.xmm _ (by decide)]
    exact (i₅.add l hl 4 (by decide)).trans (by rw [ite_eq_left (by decide)]; rfl)
  have hl4 : ∀ l < 2, lim (blkN s.mem dp l) 4 < 2 ^ 24 := fun l _ =>
    lim4_lt (by have := leNum_bytes_lt s.mem (dp.setWidth 64 + BitVec.ofNat 64 (16 * l)) 16; omega_using [this])
  refine WP.mono (paddq_ok .xmm4 .xmm7 s₆ fun l hl => by
    rw [h4 l hl, h7 l hl]; have := hb l hl 4 (by decide); have := hl4 l hl
    show ln s (lreg 4) l + _ + _ < _; omega_arith) fun s₇ ⟨a₇, m₇, k₇⟩ => ?_
  refine ⟨fun l hl k hk => ?_, by rw [m₇, m₆, i₅.mem], ((i₅.keep.trans k₆).trans k₇).mono fun r hr => ?_⟩
  · rw [lim_pad]
    by_cases hk4 : k = 4
    · subst hk4
      rw [show ln s₇ (lreg 4) l = ln s₇ .xmm4 l from rfl, a₇ l hl, h4 l hl, h7 l hl,
        ite_eq_right (Nat.lt_irrefl 4), Nat.add_assoc]
      rfl
    · have hne : lreg k ≠ .xmm4 := fun e => hk4 (lreg_inj hk (by decide) e)
      obtain ⟨-, -, n7⟩ := lreg_ne k
      rw [ln, k₇.xmm _ (by simpa only [List.mem_singleton] using hne),
        k₆.xmm _ (by simpa only [List.mem_singleton] using n7)]
      exact (i₅.add l hl k hk).trans (by
        rw [ite_eq_left hk, ite_eq_left (by omega_using [hk, hk4]), Nat.add_zero])
  · rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · rw [List.mem_singleton.mp hr]; decide
    · rw [List.mem_singleton.mp hr]; decide

/-! ### The products -/

theorem Xk.lane {xs : List XReg} {s s' : State} (h : Xk xs s s') {x : XReg} (hx : x ∉ xs) (l : Nat) :
    Sse2.ln s' x l = Sse2.ln s x l := by
  rw [Sse2.ln, h.xmm x hx]

/-- The first product of a sum: a slot times the first limb. -/
theorem mfirst_ok {o : Nat} {B : BitVec 32} (d : Nat) (s : State) (hsp : s.gpr .esp + BitVec.ofNat 32 o = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B d) 16) (hmc : 0 < s.mcdt) :
    WP isa (.block [.movdquLoad .xmm5 (fs o d), .pmuludq .xmm5 .xmm0]) s fun s' =>
      (∀ l < 2, ln s' .xmm5 l = lane (s.mem.readW (addr B d) 128) l % 2 ^ 32 * (ln s .xmm0 l % 2 ^ 32)) ∧
      s'.mem = s.mem ∧ Xk [.xmm5] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, ea_fs hsp, hin, ↓reduceIte,
    Option.map_some, mcdt_setXmm, hmc, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, rfl, rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · simp only [ln, xmm_setXmm_self, xmm_setXmm, reduceCtorEq, ↓reduceIte, lane_pmuludq _ _ hl]
  · simp only [List.mem_singleton] at hr
    simp only [xmm_setXmm, hr, ↓reduceIte]

/-- A further product: a slot times the limb in `x`, added. -/
theorem mterm_ok {o : Nat} {B : BitVec 32} (d : Nat) (x : XReg) (hx6 : x ≠ .xmm6) (s : State)
    (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) (hin : InRegions (s.rd ++ s.wr) (addr B d) 16)
    (hmc : 0 < s.mcdt) :
    WP isa (.block [.movdquLoad .xmm6 (fs o d), .pmuludq .xmm6 x, .xop (.bin .paddq .xmm5 .xmm6)]) s fun s' =>
      (∀ l < 2, ln s' .xmm5 l =
        (ln s .xmm5 l + lane (s.mem.readW (addr B d) 128) l % 2 ^ 32 * (ln s x l % 2 ^ 32)) % 2 ^ 64) ∧
      s'.mem = s.mem ∧ Xk [.xmm5, .xmm6] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load128, ea_fs hsp, hin, ↓reduceIte,
    Option.map_some, mcdt_setXmm, hmc, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, rfl, rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · simp only [ln, xmm_setXmm_self, xmm_setXmm, reduceCtorEq, ↓reduceIte, hx6, lane_paddq _ _ hl,
      lane_pmuludq _ _ hl]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [xmm_setXmm, hr.1, hr.2, ↓reduceIte]

theorem cf_lt {b : Nat → Nat} {N : Nat} (hb : ∀ i < 5, b i < N) {k i : Nat} (hk : k < 5) (hi : i < 5) :
    cf b k i < 5 * N := by
  simp only [cf]
  by_cases hik : i ≤ k
  · rw [ite_eq_left hik]
    have := hb (k - i) (by omega_using [hk]); omega_using [this]
  · rw [ite_eq_right hik]
    have := hb (k + 5 - i) (by omega_using [hk, hi, hik]); omega_using [this]

/-- `dsumV`: the sum `k` of products of the lanes with table `t`, into `xmm5`. -/
theorem dsumV_ok {o : Nat} {B : BitVec 32} {tb : Nat → Nat → Nat → Nat} (t k : Nat) (ht : t < 2) (hk : k < 5)
    (s : State) (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) (hB : Fit B)
    (hfr : Proof.Aes.X86.reg32 B 512 ∈ s.wr) (hmc : 0 < s.mcdt) (hT : Tab s.mem B tb)
    (ha : ∀ l < 2, ∀ i < 5, ln s (lreg i) l < 2 ^ 28) (hb : ∀ l < 2, ∀ i < 5, tb t l i < 2 ^ 27) :
    WP isa (.block (dsumV o t k)) s fun s' =>
      (∀ l < 2, ln s' .xmm5 l = ds (fun i => ln s (lreg i) l) (tb t l) k) ∧ s'.mem = s.mem ∧
      Xk [.xmm5, .xmm6] s s' := by
  have e : dsumV o t k = ([.movdquLoad .xmm5 (fs o (mslot t k 0)), .pmuludq .xmm5 .xmm0] : List Instr) ++
      (([.movdquLoad .xmm6 (fs o (mslot t k 1)), .pmuludq .xmm6 (lreg 1), .xop (.bin .paddq .xmm5 .xmm6)] : List Instr) ++
      (([.movdquLoad .xmm6 (fs o (mslot t k 2)), .pmuludq .xmm6 (lreg 2), .xop (.bin .paddq .xmm5 .xmm6)] : List Instr) ++
      (([.movdquLoad .xmm6 (fs o (mslot t k 3)), .pmuludq .xmm6 (lreg 3), .xop (.bin .paddq .xmm5 .xmm6)] : List Instr) ++
      ([.movdquLoad .xmm6 (fs o (mslot t k 4)), .pmuludq .xmm6 (lreg 4), .xop (.bin .paddq .xmm5 .xmm6)] : List Instr)))) := by
    simp only [dsumV, List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.cons_append, List.nil_append]
  have hin : ∀ (u : State) (i : Nat), i < 5 → u.rd = s.rd → u.wr = s.wr →
      InRegions (u.rd ++ u.wr) (addr B (mslot t k i)) 16 := fun u i hi h₁ h₂ => by
    rw [h₁, h₂]
    exact Proof.Aes.X86.in_rd (fr_in hB hfr (by have := mslot_le t k i ht hk hi; omega_using [this]) (by decide))
  -- The multipliers and the products' bounds, per lane.
  have hc : ∀ l < 2, ∀ i < 5, lane (s.mem.readW (addr B (mslot t k i)) 128) l = cf (tb t l) k i :=
    fun l hl i hi => hT.mul ht hk hi hl
  have hcl : ∀ l < 2, ∀ i < 5, cf (tb t l) k i < 2 ^ 30 := fun l hl i hi =>
    Nat.lt_of_lt_of_le (cf_lt (hb l hl) hk hi) (by decide)
  have hp : ∀ l < 2, ∀ i < 5, cf (tb t l) k i * ln s (lreg i) l < 2 ^ 58 := fun l hl i hi =>
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' (hcl l hl i hi) (ha l hl i hi)) (by decide)
  have hm : ∀ l < 2, ∀ i < 5, cf (tb t l) k i % 2 ^ 32 * (ln s (lreg i) l % 2 ^ 32) =
      cf (tb t l) k i * ln s (lreg i) l := fun l hl i hi => by
    rw [Nat.mod_eq_of_lt (Nat.lt_trans (hcl l hl i hi) (by decide)),
      Nat.mod_eq_of_lt (Nat.lt_trans (ha l hl i hi) (by decide))]
  rw [e]
  refine WP.block_append (WP.mono (mfirst_ok _ s hsp (hin s 0 (by decide) rfl rfl) hmc) fun s₁ ⟨a₁, m₁, k₁⟩ => ?_)
  have step : ∀ (i : Nat) (hi : i < 5) (hi0 : 0 < i) (u : State) (acc : Nat → Nat), u.mem = s.mem → Xk [.xmm5, .xmm6] s u →
      (∀ l < 2, ln u .xmm5 l = acc l) → (∀ l < 2, acc l < 2 ^ 58 * i) →
      WP isa (.block [.movdquLoad .xmm6 (fs o (mslot t k i)), .pmuludq .xmm6 (lreg i),
        .xop (.bin .paddq .xmm5 .xmm6)]) u fun u' => u'.mem = s.mem ∧ Xk [.xmm5, .xmm6] s u' ∧
        (∀ l < 2, ln u' .xmm5 l = acc l + cf (tb t l) k i * ln s (lreg i) l) := fun i hi hi0 u acc hm' hk' hacc hlt => by
    obtain ⟨n5, n6, -⟩ := lreg_ne i
    refine WP.mono (mterm_ok _ (lreg i) n6 u (by rw [hk'.gpr]; exact hsp) (hin u i hi hk'.rd hk'.wr)
      (by rw [hk'.mcdt]; exact hmc)) fun u' ⟨a', m', k''⟩ => ⟨m'.trans hm', ?_, fun l hl => ?_⟩
    · exact (hk'.trans k'').mono fun r hr => by
        rcases List.mem_append.mp hr with h | h <;> exact h
    · rw [a' l hl, hacc l hl, hm', hc l hl i hi,
        hk'.lane (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨n5, n6⟩), hm l hl i hi]
      have h1 := hlt l hl
      have h2 := hp l hl i hi
      exact Nat.mod_eq_of_lt (by omega_using [h1, h2, hi])
  have a₁' : ∀ l < 2, ln s₁ .xmm5 l = cf (tb t l) k 0 * ln s (lreg 0) l := fun l hl => by
    rw [a₁ l hl, hc l hl 0 (by decide)]; exact hm l hl 0 (by decide)
  have k₁' : Xk [.xmm5, .xmm6] s s₁ := k₁.mono fun r hr => by rw [List.mem_singleton.mp hr]; decide
  refine WP.block_append (WP.mono (step 1 (by decide) (by decide) s₁ _ m₁ k₁' a₁'
    (fun l hl => by have := hp l hl 0 (by decide); omega_using [this])) fun s₂ ⟨m₂, k₂, a₂⟩ => ?_)
  refine WP.block_append (WP.mono (step 2 (by decide) (by decide) s₂ _ m₂ k₂ a₂
    (fun l hl => by have := hp l hl 0 (by decide); have := hp l hl 1 (by decide); omega_arith)) fun s₃ ⟨m₃, k₃, a₃⟩ => ?_)
  refine WP.block_append (WP.mono (step 3 (by decide) (by decide) s₃ _ m₃ k₃ a₃
    (fun l hl => by
      have := hp l hl 0 (by decide); have := hp l hl 1 (by decide); have := hp l hl 2 (by decide)
      omega_arith)) fun s₄ ⟨m₄, k₄, a₄⟩ => ?_)
  refine WP.mono (step 4 (by decide) (by decide) s₄ _ m₄ k₄ a₄
    (fun l hl => by
      have := hp l hl 0 (by decide); have := hp l hl 1 (by decide); have := hp l hl 2 (by decide)
      have := hp l hl 3 (by decide)
      omega_arith)) fun s₅ ⟨m₅, k₅, a₅⟩ => ⟨fun l hl => ?_, m₅, k₅⟩
  rw [a₅ l hl]
  rfl

/-- All the SSE registers. -/
abbrev xall : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7]

theorem Xk.all {xs : List XReg} {s s' : State} (h : Xk xs s s') : Xk xall s s' :=
  ⟨h.gpr, h.rd, h.wr, h.mcdt, fun r hr => absurd (by cases r <;> decide) hr⟩

theorem mv_ok (x y : XReg) (s : State) :
    WP isa (.block [.xop (.bin .movdqa x y)]) s fun s' =>
      s'.xmm x = s.xmm y ∧ s'.mem = s.mem ∧ Xk [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, Option.some.injEq, exists_eq_left']
  exact ⟨xmm_setXmm_self _ _ _, rfl, setXmm_xk _ _ _⟩

/-- The slots where three of the sums are kept. -/
abbrev dR (B : BitVec 32) : Region := ⟨addr B 416, 48⟩

theorem dR_contains {B : BitVec 32} (hB : Fit B) {d : Nat} (h₁ : 416 ≤ d) (h₂ : d + 16 ≤ 464) :
    (dR B).Contains (addr B d) (128 / 8) :=
  Proof.Aes.X86.part_contains (N := 512) (a := 416) (k := 48) hB (by decide) h₁ (by omega_using [h₂]) (by decide)

/-- `mulV`: the lanes multiplied by table `t`. -/
theorem mulV_ok {o : Nat} {B : BitVec 32} {tb : Nat → Nat → Nat → Nat} (t : Nat) (ht : t < 2)
    (s : State) (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) (hB : Fit B)
    (hfr : Proof.Aes.X86.reg32 B 512 ∈ s.wr) (hmc : 0 < s.mcdt) (hT : Tab s.mem B tb)
    (ha : ∀ l < 2, ∀ i < 5, ln s (lreg i) l < 2 ^ 28) (hb : ∀ l < 2, ∀ i < 5, tb t l i < 2 ^ 27) :
    WP isa (.block (mulV o t)) s fun s' =>
      (∀ l < 2, ∀ k < 5, ln s' (lreg k) l = ds (fun i => ln s (lreg i) l) (tb t l) k) ∧
      (∀ l < 2, ln s' .xmm5 l = 2 ^ 26 - 1) ∧ Tab s'.mem B tb ∧ Frame [dR B] s.mem s'.mem ∧ Xk xall s s' := by
  -- A sum, from a state whose limbs are those of `s`.
  have hd : ∀ (k : Nat), k < 5 → ∀ u : State, Xk [.xmm5, .xmm6, .xmm7] s u → Tab u.mem B tb →
      WP isa (.block (dsumV o t k)) u fun u' =>
        (∀ l < 2, ln u' .xmm5 l = ds (fun i => ln s (lreg i) l) (tb t l) k) ∧ u'.mem = u.mem ∧
        u'.xmm .xmm7 = u.xmm .xmm7 ∧ Xk [.xmm5, .xmm6, .xmm7] s u' := fun k hk u ku hTu => by
    have hl : ∀ (i l : Nat), ln u (lreg i) l = ln s (lreg i) l := fun i l => by
      obtain ⟨n5, n6, n7⟩ := lreg_ne i
      exact ku.lane (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨n5, n6, n7⟩) l
    refine WP.mono (dsumV_ok t k ht hk u (by rw [ku.gpr]; exact hsp) hB (by rw [ku.wr]; exact hfr)
      (by rw [ku.mcdt]; exact hmc) hTu (fun l hl' i hi => by rw [hl]; exact ha l hl' i hi) hb)
      fun u' ⟨a', m', k'⟩ => ⟨fun l hl' => ?_, m', k'.xmm _ (by decide), (ku.trans k').mono fun r hr => ?_⟩
    · rw [a' l hl']; simp only [hl]
    · rcases List.mem_append.mp hr with h | h
      · exact h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> decide
  -- Keeping a sum in the frame.
  have hst : ∀ (d : Nat), 416 ≤ d → d + 16 ≤ 464 → ∀ u : State, Xk [.xmm5, .xmm6, .xmm7] s u →
      WP isa (.block [.movdquStore (fs o d) .xmm5]) u fun u' =>
        u'.mem = u.mem.writeW (addr B d) (u.xmm .xmm5) ∧ u'.xmm = u.xmm ∧ Xk [.xmm5, .xmm6, .xmm7] s u' :=
    fun d h₁ h₂ u ku => by
      refine WP.mono (storeSlot_ok .xmm5 d u (by rw [ku.gpr]; exact hsp)
        (by rw [ku.wr]; exact fr_in hB hfr (by omega_using [h₂]) (by decide))) fun u' ⟨m', k'⟩ =>
        ⟨m', funext fun r => k'.xmm r (List.not_mem_nil), (ku.trans k').mono fun r hr => by simpa using hr⟩
  have kd : ∀ (m : Mem) (v : BitVec 128) (d : Nat), 416 ≤ d → d + 16 ≤ 464 → Tab m B tb →
      Tab (m.writeW (addr B d) v) B tb := fun m v d h₁ h₂ hTm => hTm.store hB h₁ (by omega_using [h₂]) v
  simp only [mulV, List.append_assoc]
  refine WP.block_append (WP.mono (hd 1 (by decide) s (Xk.refl _ _) hT) fun u₁ ⟨a₁, m₁, _, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (hst (dSlot 1) (by decide) (by decide) u₁ k₁) fun u₂ ⟨m₂, x₂, k₂⟩ => ?_)
  rw [m₁] at m₂
  refine WP.block_append (WP.mono (hd 2 (by decide) u₂ k₂ (by rw [m₂]; exact kd _ _ _ (by decide) (by decide) hT))
    fun u₃ ⟨a₃, m₃, _, k₃⟩ => ?_)
  refine WP.block_append (WP.mono (hst (dSlot 2) (by decide) (by decide) u₃ k₃) fun u₄ ⟨m₄, x₄, k₄⟩ => ?_)
  rw [m₃, m₂] at m₄
  have T₄ : Tab u₄.mem B tb := by
    rw [m₄]; exact kd _ _ _ (by decide) (by decide) (kd _ _ _ (by decide) (by decide) hT)
  refine WP.block_append (WP.mono (hd 3 (by decide) u₄ k₄ T₄) fun u₅ ⟨a₅, m₅, _, k₅⟩ => ?_)
  refine WP.block_append (WP.mono (hst (dSlot 3) (by decide) (by decide) u₅ k₅) fun u₆ ⟨m₆, x₆, k₆⟩ => ?_)
  rw [m₅, m₄] at m₆
  have T₆ : Tab u₆.mem B tb := by
    rw [m₆]
    exact kd _ _ _ (by decide) (by decide) (kd _ _ _ (by decide) (by decide) (kd _ _ _ (by decide) (by decide) hT))
  refine WP.block_append (WP.mono (hd 0 (by decide) u₆ k₆ T₆) fun u₇ ⟨a₇, m₇, _, k₇⟩ => ?_)
  refine WP.block_append (WP.mono (mv_ok .xmm7 .xmm5 u₇) fun u₈ ⟨v₈, m₈, k₈⟩ => ?_)
  have k₈' : Xk [.xmm5, .xmm6, .xmm7] s u₈ := (k₇.trans k₈).mono fun r hr => by
    rcases List.mem_append.mp hr with h | h
    · exact h
    · rw [List.mem_singleton.mp h]; decide
  have T₈ : Tab u₈.mem B tb := by rw [m₈, m₇]; exact T₆
  refine WP.block_append (WP.mono (hd 4 (by decide) u₈ k₈' T₈) fun u₉ ⟨a₉, m₉, x₉, k₉⟩ => ?_)
  have hm₉ : u₉.mem = u₆.mem := by rw [m₉, m₈, m₇]
  -- The sums, where they were kept.
  have r1 : u₉.mem.readW (addr B (dSlot 1)) 128 = u₁.xmm .xmm5 := by
    rw [hm₉, m₆, slot_other hB _ _ (by decide) (by decide) (by decide),
      slot_other hB _ _ (by decide) (by decide) (by decide), slot_same]
  have r2 : u₉.mem.readW (addr B (dSlot 2)) 128 = u₃.xmm .xmm5 := by
    rw [hm₉, m₆, slot_other hB _ _ (by decide) (by decide) (by decide), slot_same]
  have r3 : u₉.mem.readW (addr B (dSlot 3)) 128 = u₅.xmm .xmm5 := by
    rw [hm₉, m₆, slot_same]
  have hin : ∀ (u : State) (d : Nat), d + 16 ≤ 512 → u.rd = s.rd → u.wr = s.wr →
      InRegions (u.rd ++ u.wr) (addr B d) 16 := fun u d hd' h₁ h₂ => by
    rw [h₁, h₂]; exact Proof.Aes.X86.in_rd (fr_in hB hfr hd' (by decide))
  show WP isa (.block (([.xop (.bin .movdqa .xmm4 .xmm5)] : List Instr) ++
    (([.xop (.bin .movdqa .xmm0 .xmm7)] : List Instr) ++ (([.movdquLoad .xmm1 (fs o (dSlot 1))] : List Instr) ++
    (([.movdquLoad .xmm2 (fs o (dSlot 2))] : List Instr) ++ (([.movdquLoad .xmm3 (fs o (dSlot 3))] : List Instr) ++
    [.movdquLoad .xmm5 (fs o maskSlot)])))))) u₉ _
  refine WP.block_append (WP.mono (mv_ok .xmm4 .xmm5 u₉) fun w₁ ⟨v₁, n₁, j₁⟩ => ?_)
  refine WP.block_append (WP.mono (mv_ok .xmm0 .xmm7 w₁) fun w₂ ⟨v₂, n₂, j₂⟩ => ?_)
  have g₂ : Xk xall s w₂ := (k₉.all.trans (j₁.trans j₂)).all
  have hsp₂ : w₂.gpr .esp + BitVec.ofNat 32 o = B := by rw [g₂.gpr]; exact hsp
  refine WP.block_append (WP.mono (loadSlot_ok .xmm1 (dSlot 1) w₂ hsp₂ (hin w₂ _ (by decide) g₂.rd g₂.wr))
    fun w₃ ⟨v₃, n₃, j₃⟩ => ?_)
  have g₃ : Xk xall s w₃ := (g₂.trans j₃).all
  refine WP.block_append (WP.mono (loadSlot_ok .xmm2 (dSlot 2) w₃ (by rw [g₃.gpr]; exact hsp)
    (hin w₃ _ (by decide) g₃.rd g₃.wr)) fun w₄ ⟨v₄, n₄, j₄⟩ => ?_)
  have g₄ : Xk xall s w₄ := (g₃.trans j₄).all
  refine WP.block_append (WP.mono (loadSlot_ok .xmm3 (dSlot 3) w₄ (by rw [g₄.gpr]; exact hsp)
    (hin w₄ _ (by decide) g₄.rd g₄.wr)) fun w₅ ⟨v₅, n₅, j₅⟩ => ?_)
  have g₅ : Xk xall s w₅ := (g₄.trans j₅).all
  refine WP.mono (loadSlot_ok .xmm5 maskSlot w₅ (by rw [g₅.gpr]; exact hsp)
    (hin w₅ _ (by decide) g₅.rd g₅.wr)) fun w₆ ⟨v₆, n₆, j₆⟩ => ?_
  have hmem : w₆.mem = u₉.mem := by rw [n₆, n₅, n₄, n₃, n₂, n₁]
  have T : Tab w₆.mem B tb := by rw [hmem, hm₉]; exact T₆
  -- The registers at the end.
  have e0 : w₆.xmm .xmm0 = u₇.xmm .xmm5 := by
    rw [j₆.xmm _ (by decide), j₅.xmm _ (by decide), j₄.xmm _ (by decide), j₃.xmm _ (by decide), v₂,
      j₁.xmm _ (by decide), x₉, v₈]
  have e1 : w₆.xmm .xmm1 = u₁.xmm .xmm5 := by
    rw [j₆.xmm _ (by decide), j₅.xmm _ (by decide), j₄.xmm _ (by decide), v₃, n₂, n₁, r1]
  have e2 : w₆.xmm .xmm2 = u₃.xmm .xmm5 := by
    rw [j₆.xmm _ (by decide), j₅.xmm _ (by decide), v₄, n₃, n₂, n₁, r2]
  have e3 : w₆.xmm .xmm3 = u₅.xmm .xmm5 := by
    rw [j₆.xmm _ (by decide), v₅, n₄, n₃, n₂, n₁, r3]
  have e4 : w₆.xmm .xmm4 = u₉.xmm .xmm5 := by
    rw [j₆.xmm _ (by decide), j₅.xmm _ (by decide), j₄.xmm _ (by decide), j₃.xmm _ (by decide),
      j₂.xmm _ (by decide), v₁]
  refine ⟨fun l hl k hk => ?_, fun l hl => ?_, T, ?_, (g₅.trans j₆).all⟩
  · rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
    · exact (congrArg (lane · l) e0).trans (a₇ l hl)
    · exact (congrArg (lane · l) e1).trans (a₁ l hl)
    · exact (congrArg (lane · l) e2).trans (a₃ l hl)
    · exact (congrArg (lane · l) e3).trans (a₅ l hl)
    · exact (congrArg (lane · l) e4).trans (a₉ l hl)
  · rw [ln, v₆, n₅, n₄, n₃, n₂, n₁]
    exact (by rw [hm₉]; exact T₆ : Tab u₉.mem B tb).mask l hl
  · rw [hmem, hm₉, m₆]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (dR_contains hB (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (dR_contains hB (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (dR_contains hB (by decide) (by decide))

/-! ### The carries -/

/-- The limbs of lane `l` are `f`. -/
def Ls (s : State) (l : Nat) (f : Nat → Nat) : Prop := ∀ k < 5, ln s (lreg k) l = f k

/-- A carry from limb `i` into limb `j`. -/
def cup (f : Nat → Nat) (i j : Nat) : Nat → Nat :=
  fun k => if k = i then f i % 2 ^ 26 else if k = j then f j + f i / 2 ^ 26 else f k

/-- The carry from the fifth limb into the first, times 5. -/
def cup5 (f : Nat → Nat) : Nat → Nat :=
  fun k => if k = 4 then f 4 % 2 ^ 26 else if k = 0 then f 0 + (f 4 / 2 ^ 26 + f 4 / 2 ^ 26 * 2 ^ 2) else f k

theorem cup_lt {f : Nat → Nat} {N : Nat} (hf : ∀ k < 5, f k < N) (hN : N ≤ 2 ^ 63) (i j : Nat) (hi : i < 5)
    {k : Nat} (hk : k < 5) : cup f i j k < N + 2 ^ 37 := by
  have h1 := hf i hi
  have h2 := hf k hk
  simp only [cup]
  split
  · omega_using [h1, hN]
  · split
    · rename_i _ h; subst h; omega_using [h1, h2, hN]
    · omega_using [h2]

theorem cup5_lt {f : Nat → Nat} {N : Nat} (hf : ∀ k < 5, f k < N) (hN : N ≤ 2 ^ 63) {k : Nat} (hk : k < 5) :
    cup5 f k < N + 2 ^ 40 := by
  have h1 := hf 4 (by decide)
  have h2 := hf k hk
  simp only [cup5]
  split
  · omega_using [h1, hN]
  · split
    · rename_i _ h; subst h; omega_using [h1, h2, hN]
    · omega_using [h2]

theorem psrlq_ok (x : XReg) (n : BitVec 8) (hn : n.toNat ≤ 63) (s : State) :
    WP isa (.block [.xop (.shift .psrlq x n)]) s fun s' =>
      (∀ l < 2, ln s' x l = ln s x l / 2 ^ n.toNat) ∧ s'.mem = s.mem ∧ Xk [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, Option.some.injEq, exists_eq_left']
  exact ⟨fun l hl => by rw [ln, xmm_setXmm_self, lane_psrlq _ _ hn hl], rfl, setXmm_xk _ _ _⟩

theorem pand_ok (x : XReg) (s : State) (hm : ∀ l < 2, ln s .xmm5 l = 2 ^ 26 - 1) :
    WP isa (.block [.xop (.bin .pand x .xmm5)]) s fun s' =>
      (∀ l < 2, ln s' x l = ln s x l % 2 ^ 26) ∧ s'.mem = s.mem ∧ Xk [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, rfl, setXmm_xk _ _ _⟩
  rw [ln, xmm_setXmm_self, lane_pand, show lane (s.xmm .xmm5) l = 2 ^ 26 - 1 from hm l hl, and_mask]

/-- `cstep i j` for `i < 4`. -/
theorem cstep_ok (i j : Nat) (hi : i < 4) (hj : j < 5) (hij : i ≠ j) (s : State)
    (hm : ∀ l < 2, ln s .xmm5 l = 2 ^ 26 - 1) (f : Nat → Nat → Nat) (hf : ∀ l < 2, Ls s l (f l))
    (hb : ∀ l < 2, ∀ k < 5, f l k < 2 ^ 63) :
    WP isa (.block (cstep i j)) s fun s' =>
      (∀ l < 2, Ls s' l (cup (f l) i j)) ∧ s'.mem = s.mem ∧ Xk lregs s s' := by
  have hi5 : i < 5 := by omega_using [hi]
  obtain ⟨i5, i6, i7⟩ := lreg_ne i
  obtain ⟨j5, j6, j7⟩ := lreg_ne j
  have hne : lreg i ≠ lreg j := fun e => hij (lreg_inj hi5 hj e)
  have e : cstep i j = ([.xop (.bin .movdqa .xmm6 (lreg i))] : List Instr) ++
      (([.xop (.shift .psrlq .xmm6 26)] : List Instr) ++ (([.xop (.bin .pand (lreg i) .xmm5)] : List Instr) ++
      [.xop (.bin .paddq (lreg j) .xmm6)])) := by
    simp only [cstep, show ¬ i = 4 by omega_using [hi], ↓reduceIte, List.append_nil, List.cons_append,
      List.nil_append]
  rw [e]
  refine WP.block_append (WP.mono (mv_ok .xmm6 (lreg i) s) fun s₁ ⟨v₁, m₁, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (psrlq_ok .xmm6 26 (by decide) s₁) fun s₂ ⟨a₂, m₂, k₂⟩ => ?_)
  have h6 : ∀ l < 2, ln s₂ .xmm6 l = f l i / 2 ^ 26 := fun l hl => by
    rw [a₂ l hl, ln, v₁]; exact congrArg (· / 2 ^ 26) (hf l hl i hi5)
  have k₁₂ : Xk [.xmm6] s s₂ := (k₁.trans k₂).mono fun r hr => by
    rcases List.mem_append.mp hr with h | h <;> exact h
  refine WP.block_append (WP.mono (pand_ok (lreg i) s₂ fun l hl => by
    rw [k₁₂.lane (by decide)]; exact hm l hl) fun s₃ ⟨a₃, m₃, k₃⟩ => ?_)
  have hx : ∀ l < 2, ln s₃ (lreg i) l = f l i % 2 ^ 26 := fun l hl => by
    rw [a₃ l hl, k₁₂.lane (by simpa only [List.mem_singleton] using i6)]
    exact congrArg (· % 2 ^ 26) (hf l hl i hi5)
  have hy : ∀ l < 2, ln s₃ (lreg j) l = f l j := fun l hl => by
    rw [k₃.lane (by simpa only [List.mem_singleton] using Ne.symm hne),
      k₁₂.lane (by simpa only [List.mem_singleton] using j6)]
    exact hf l hl j hj
  have h6' : ∀ l < 2, ln s₃ .xmm6 l = f l i / 2 ^ 26 := fun l hl => by
    rw [k₃.lane (by simpa only [List.mem_singleton] using Ne.symm i6)]; exact h6 l hl
  refine WP.mono (paddq_ok (lreg j) .xmm6 s₃ fun l hl => by
    rw [hy l hl, h6' l hl]; have := hb l hl i hi5; have := hb l hl j hj; omega_arith) fun s₄ ⟨a₄, m₄, k₄⟩ => ?_
  have kk : Xk [.xmm6, lreg i, lreg j] s s₄ := ((k₁₂.trans k₃).trans k₄).mono fun r hr => by
    simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] using hr
  refine ⟨fun l hl k hk => ?_, by rw [m₄, m₃, m₂, m₁], kk.mono fun r hr => ?_⟩
  · simp only [cup]
    by_cases hki : k = i
    · subst hki
      rw [ite_eq_left rfl, k₄.lane (by simpa only [List.mem_singleton] using hne)]; exact hx l hl
    · rw [ite_eq_right hki]
      by_cases hkj : k = j
      · subst hkj
        rw [ite_eq_left rfl, a₄ l hl, hy l hl, h6' l hl]
      · rw [ite_eq_right hkj]
        obtain ⟨-, n6, -⟩ := lreg_ne k
        have n1 : lreg k ≠ lreg i := fun e => hki (lreg_inj hk hi5 e)
        have n2 : lreg k ≠ lreg j := fun e => hkj (lreg_inj hk hj e)
        rw [kk.lane (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨n6, n1, n2⟩)]
        exact hf l hl k hk
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · exact lreg_mem
    · exact lreg_mem

theorem psllq_ok (x : XReg) (n : BitVec 8) (hn : n.toNat ≤ 63) (s : State)
    (h : ∀ l < 2, ln s x l * 2 ^ n.toNat < 2 ^ 64) :
    WP isa (.block [.xop (.shift .psllq x n)]) s fun s' =>
      (∀ l < 2, ln s' x l = ln s x l * 2 ^ n.toNat) ∧ s'.mem = s.mem ∧ Xk [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, Option.some.injEq, exists_eq_left']
  exact ⟨fun l hl => by rw [ln, xmm_setXmm_self, lane_psllq _ _ hn hl, Nat.mod_eq_of_lt (h l hl)], rfl,
    setXmm_xk _ _ _⟩

/-- `cstep 4 0`: the carry out of the fifth limb, times 5, into the first. -/
theorem cstep5_ok (s : State) (hm : ∀ l < 2, ln s .xmm5 l = 2 ^ 26 - 1) (f : Nat → Nat → Nat)
    (hf : ∀ l < 2, Ls s l (f l)) (hb : ∀ l < 2, ∀ k < 5, f l k < 2 ^ 63) :
    WP isa (.block (cstep 4 0)) s fun s' =>
      (∀ l < 2, Ls s' l (cup5 (f l))) ∧ s'.mem = s.mem ∧ Xk lregs s s' := by
  have e : cstep 4 0 = ([.xop (.bin .movdqa .xmm6 .xmm4)] : List Instr) ++
      (([.xop (.shift .psrlq .xmm6 26)] : List Instr) ++ (([.xop (.bin .pand .xmm4 .xmm5)] : List Instr) ++
      (([.xop (.bin .movdqa .xmm7 .xmm6)] : List Instr) ++ (([.xop (.shift .psllq .xmm7 2)] : List Instr) ++
      (([.xop (.bin .paddq .xmm6 .xmm7)] : List Instr) ++ [.xop (.bin .paddq .xmm0 .xmm6)]))))) := rfl
  rw [e]
  have f4 : ∀ l < 2, ln s .xmm4 l = f l 4 := fun l hl => hf l hl 4 (by decide)
  have f0 : ∀ l < 2, ln s .xmm0 l = f l 0 := fun l hl => hf l hl 0 (by decide)
  refine WP.block_append (WP.mono (mv_ok .xmm6 .xmm4 s) fun s₁ ⟨v₁, m₁, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (psrlq_ok .xmm6 26 (by decide) s₁) fun s₂ ⟨a₂, m₂, k₂⟩ => ?_)
  have k₁₂ : Xk [.xmm6] s s₂ := (k₁.trans k₂).mono fun r hr => by
    rcases List.mem_append.mp hr with h | h <;> exact h
  have h6 : ∀ l < 2, ln s₂ .xmm6 l = f l 4 / 2 ^ 26 := fun l hl => by
    rw [a₂ l hl, ln, v₁]; exact congrArg (· / 2 ^ 26) (f4 l hl)
  refine WP.block_append (WP.mono (pand_ok .xmm4 s₂ fun l hl => by
    rw [k₁₂.lane (by decide)]; exact hm l hl) fun s₃ ⟨a₃, m₃, k₃⟩ => ?_)
  refine WP.block_append (WP.mono (mv_ok .xmm7 .xmm6 s₃) fun s₄ ⟨v₄, m₄, k₄⟩ => ?_)
  have h6₄ : ∀ l < 2, ln s₄ .xmm6 l = f l 4 / 2 ^ 26 := fun l hl => by
    rw [k₄.lane (by decide), k₃.lane (by decide)]; exact h6 l hl
  have h7₄ : ∀ l < 2, ln s₄ .xmm7 l = f l 4 / 2 ^ 26 := fun l hl => by
    rw [ln, v₄]; exact (k₃.lane (by decide) l).trans (h6 l hl)
  refine WP.block_append (WP.mono (psllq_ok .xmm7 2 (by decide) s₄ fun l hl => by
    rw [h7₄ l hl]; have := hb l hl 4 (by decide); show _ * 2 ^ 2 < _; omega_arith) fun s₅ ⟨a₅, m₅, k₅⟩ => ?_)
  have h7₅ : ∀ l < 2, ln s₅ .xmm7 l = f l 4 / 2 ^ 26 * 2 ^ 2 := fun l hl => by
    rw [a₅ l hl, h7₄ l hl]; rfl
  have h6₅ : ∀ l < 2, ln s₅ .xmm6 l = f l 4 / 2 ^ 26 := fun l hl => by
    rw [k₅.lane (by decide)]; exact h6₄ l hl
  refine WP.block_append (WP.mono (paddq_ok .xmm6 .xmm7 s₅ fun l hl => by
    rw [h6₅ l hl, h7₅ l hl]; have := hb l hl 4 (by decide); omega_arith) fun s₆ ⟨a₆, m₆, k₆⟩ => ?_)
  have h6₆ : ∀ l < 2, ln s₆ .xmm6 l = f l 4 / 2 ^ 26 + f l 4 / 2 ^ 26 * 2 ^ 2 := fun l hl => by
    rw [a₆ l hl, h6₅ l hl, h7₅ l hl]
  have h0₆ : ∀ l < 2, ln s₆ .xmm0 l = f l 0 := fun l hl => by
    rw [k₆.lane (by decide), k₅.lane (by decide), k₄.lane (by decide), k₃.lane (by decide), k₁₂.lane (by decide)]
    exact f0 l hl
  refine WP.mono (paddq_ok .xmm0 .xmm6 s₆ fun l hl => by
    rw [h0₆ l hl, h6₆ l hl]; have := hb l hl 4 (by decide); have := hb l hl 0 (by decide); omega_arith)
    fun s₇ ⟨a₇, m₇, k₇⟩ => ?_
  have kk : Xk [.xmm6, .xmm4, .xmm7, .xmm0] s s₇ :=
    ((((k₁₂.trans k₃).trans k₄).trans k₅).trans (k₆.trans k₇)).mono fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (((h | h) | h) | h) | (h | h) <;> simp [h]
  refine ⟨fun l hl k hk => ?_, by rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁], kk.mono fun r hr => ?_⟩
  · simp only [cup5]
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
    · show ln s₇ .xmm0 l = _
      rw [a₇ l hl, h0₆ l hl, h6₆ l hl]; rfl
    · exact (kk.lane (show lreg 1 ∉ _ by decide) l).trans (hf l hl 1 (by decide))
    · exact (kk.lane (show lreg 2 ∉ _ by decide) l).trans (hf l hl 2 (by decide))
    · exact (kk.lane (show lreg 3 ∉ _ by decide) l).trans (hf l hl 3 (by decide))
    · show ln s₇ .xmm4 l = _
      rw [k₇.lane (by decide), k₆.lane (by decide), k₅.lane (by decide), k₄.lane (by decide), a₃ l hl,
        k₁₂.lane (by decide), f4 l hl]
      rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide

/-- `carryV`: the limbs after the carries. -/
theorem carryV_ok (s : State) (hm : ∀ l < 2, ln s .xmm5 l = 2 ^ 26 - 1)
    (hd : ∀ l < 2, ∀ k < 5, ln s (lreg k) l < 2 ^ 62) :
    WP isa (.block carryV) s fun s' =>
      (∀ l < 2, ∀ k < 5, ln s' (lreg k) l = cv (fun i => ln s (lreg i) l) k) ∧ s'.mem = s.mem ∧
      Xk lregs s s' := by
  have m5 : ∀ {u : State}, Xk lregs s u → ∀ l < 2, ln u .xmm5 l = 2 ^ 26 - 1 := fun ku l hl => by
    rw [ku.lane (by decide)]; exact hm l hl
  have tr : ∀ {u u' : State}, Xk lregs s u → Xk lregs u u' → Xk lregs s u' := fun h h' =>
    (h.trans h').mono fun r hr => by rcases List.mem_append.mp hr with h | h <;> exact h
  let f0 : Nat → Nat → Nat := fun l i => ln s (lreg i) l
  have b0 : ∀ l < 2, ∀ k < 5, f0 l k < 2 ^ 62 := hd
  simp only [carryV, List.append_assoc]
  refine WP.block_append (WP.mono (cstep_ok 0 1 (by decide) (by decide) (by decide) s hm f0
    (fun _ _ _ _ => rfl) fun l hl k hk => Nat.lt_trans (b0 l hl k hk) (by decide)) fun s₁ ⟨a₁, m₁, k₁⟩ => ?_)
  have b1 : ∀ l < 2, ∀ k < 5, cup (f0 l) 0 1 k < 2 ^ 62 + 2 ^ 37 := fun l hl k hk =>
    cup_lt (b0 l hl) (by decide) 0 1 (by decide) hk
  refine WP.block_append (WP.mono (cstep_ok 3 4 (by decide) (by decide) (by decide) s₁ (m5 k₁) _ a₁
    fun l hl k hk => Nat.lt_trans (b1 l hl k hk) (by decide)) fun s₂ ⟨a₂, m₂, k₂⟩ => ?_)
  have b2 : ∀ l < 2, ∀ k < 5, cup (cup (f0 l) 0 1) 3 4 k < 2 ^ 62 + 2 ^ 37 + 2 ^ 37 := fun l hl k hk =>
    cup_lt (b1 l hl) (by decide) 3 4 (by decide) hk
  have k₂' := tr k₁ k₂
  refine WP.block_append (WP.mono (cstep_ok 1 2 (by decide) (by decide) (by decide) s₂ (m5 k₂') _ a₂
    fun l hl k hk => Nat.lt_trans (b2 l hl k hk) (by decide)) fun s₃ ⟨a₃, m₃, k₃⟩ => ?_)
  have b3 : ∀ l < 2, ∀ k < 5, cup (cup (cup (f0 l) 0 1) 3 4) 1 2 k < 2 ^ 62 + 2 ^ 37 + 2 ^ 37 + 2 ^ 37 :=
    fun l hl k hk => cup_lt (b2 l hl) (by decide) 1 2 (by decide) hk
  have k₃' := tr k₂' k₃
  refine WP.block_append (WP.mono (cstep5_ok s₃ (m5 k₃') _ a₃
    fun l hl k hk => Nat.lt_trans (b3 l hl k hk) (by decide)) fun s₄ ⟨a₄, m₄, k₄⟩ => ?_)
  have b4 : ∀ l < 2, ∀ k < 5, cup5 (cup (cup (cup (f0 l) 0 1) 3 4) 1 2) k <
      2 ^ 62 + 2 ^ 37 + 2 ^ 37 + 2 ^ 37 + 2 ^ 40 := fun l hl k hk => cup5_lt (b3 l hl) (by decide) hk
  have k₄' := tr k₃' k₄
  refine WP.block_append (WP.mono (cstep_ok 2 3 (by decide) (by decide) (by decide) s₄ (m5 k₄') _ a₄
    fun l hl k hk => Nat.lt_trans (b4 l hl k hk) (by decide)) fun s₅ ⟨a₅, m₅, k₅⟩ => ?_)
  have b5 : ∀ l < 2, ∀ k < 5, cup (cup5 (cup (cup (cup (f0 l) 0 1) 3 4) 1 2)) 2 3 k <
      2 ^ 62 + 2 ^ 37 + 2 ^ 37 + 2 ^ 37 + 2 ^ 40 + 2 ^ 37 := fun l hl k hk =>
    cup_lt (b4 l hl) (by decide) 2 3 (by decide) hk
  have k₅' := tr k₄' k₅
  refine WP.block_append (WP.mono (cstep_ok 0 1 (by decide) (by decide) (by decide) s₅ (m5 k₅') _ a₅
    fun l hl k hk => Nat.lt_trans (b5 l hl k hk) (by decide)) fun s₆ ⟨a₆, m₆, k₆⟩ => ?_)
  have b6 : ∀ l < 2, ∀ k < 5, cup (cup (cup5 (cup (cup (cup (f0 l) 0 1) 3 4) 1 2)) 2 3) 0 1 k <
      2 ^ 62 + 2 ^ 37 + 2 ^ 37 + 2 ^ 37 + 2 ^ 40 + 2 ^ 37 + 2 ^ 37 := fun l hl k hk =>
    cup_lt (b5 l hl) (by decide) 0 1 (by decide) hk
  have k₆' := tr k₅' k₆
  refine WP.mono (cstep_ok 3 4 (by decide) (by decide) (by decide) s₆ (m5 k₆') _ a₆
    fun l hl k hk => Nat.lt_trans (b6 l hl k hk) (by decide)) fun s₇ ⟨a₇, m₇, k₇⟩ => ?_
  refine ⟨fun l hl k hk => ?_, by rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁], tr k₆' k₇⟩
  rw [a₇ l hl k hk]
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [cup, cup5, cv, z0, z3, x2, x4, x1, f0, Nat.reduceEqDiff, ↓reduceIte, Nat.zero_ne_one,
      Nat.one_ne_zero]

/-! ### The lanes' sum, and its limbs into the frame -/

theorem psrldq8_ok (x : XReg) (s : State) :
    WP isa (.block [.xop (.shift .psrldq x 8)]) s fun s' =>
      ln s' x 0 = ln s x 1 ∧ ln s' x 1 = 0 ∧ s'.mem = s.mem ∧ Xk [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, Option.some.injEq, exists_eq_left']
  exact ⟨by rw [ln, xmm_setXmm_self, (lane_psrldq8 _).1], by rw [ln, xmm_setXmm_self, (lane_psrldq8 _).2], rfl,
    setXmm_xk _ _ _⟩

/-- After the high lanes of the limbs before `j` have been added to the low ones. -/
structure SLInv (f : Nat → Nat → Nat) (s : State) (j : Nat) (s' : State) : Prop where
  lo : ∀ k < 5, ln s' (lreg k) 0 = f 0 k + (if k < j then f 1 k else 0)
  hi : ∀ k < 5, ln s' (lreg k) 1 = f 1 k
  mem : s'.mem = s.mem
  keep : Xk lregs s s'

theorem sumLimb_step {f : Nat → Nat → Nat} {s s₁ : State} {j : Nat} (hj : j < 5)
    (hb : ∀ k < 5, f 0 k + f 1 k < 2 ^ 64) (h : SLInv f s j s₁) :
    WP isa (.block [.xop (.bin .movdqa .xmm6 (lreg j)), .xop (.shift .psrldq .xmm6 8),
      .xop (.bin .paddq (lreg j) .xmm6)]) s₁ (SLInv f s (j + 1)) := by
  obtain ⟨-, j6, -⟩ := lreg_ne j
  show WP isa (.block (([.xop (.bin .movdqa .xmm6 (lreg j))] : List Instr) ++
    (([.xop (.shift .psrldq .xmm6 8)] : List Instr) ++ [.xop (.bin .paddq (lreg j) .xmm6)]))) s₁ _
  refine WP.block_append (WP.mono (mv_ok .xmm6 (lreg j) s₁) fun s₂ ⟨v₂, m₂, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (psrldq8_ok .xmm6 s₂) fun s₃ ⟨a₃, b₃, m₃, k₃⟩ => ?_)
  have k₂₃ : Xk [.xmm6] s₁ s₃ := (k₂.trans k₃).mono fun r hr => by
    rcases List.mem_append.mp hr with h | h <;> exact h
  have hx : ∀ l, ln s₃ (lreg j) l = ln s₁ (lreg j) l := fun l =>
    k₂₃.lane (by simpa only [List.mem_singleton] using j6) l
  have h60 : ln s₃ .xmm6 0 = f 1 j := by rw [a₃, ln, v₂]; exact h.hi j hj
  have hlo : ln s₁ (lreg j) 0 = f 0 j := by
    rw [h.lo j hj, ite_eq_right (Nat.lt_irrefl j), Nat.add_zero]
  refine WP.mono (paddq_ok (lreg j) .xmm6 s₃ fun l hl => by
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
    · rw [hx, hlo, h60]; exact hb j hj
    · rw [hx, b₃, Nat.add_zero]; exact lane_lt _ _) fun s₄ ⟨a₄, m₄, k₄⟩ => ?_
  have kk : Xk [.xmm6, lreg j] s₁ s₄ := (k₂₃.trans k₄).mono fun r hr => by
    simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] using hr
  refine ⟨fun k hk => ?_, fun k hk => ?_, by rw [m₄, m₃, m₂, h.mem], (h.keep.trans kk).mono fun r hr => ?_⟩
  · by_cases hkj : k = j
    · subst hkj
      rw [a₄ 0 (by decide), hx, hlo, h60, ite_eq_left (Nat.lt_succ_self k)]
    · obtain ⟨-, n6, -⟩ := lreg_ne k
      have hne : lreg k ≠ lreg j := fun e => hkj (lreg_inj hk hj e)
      rw [kk.lane (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨n6, hne⟩), h.lo k hk]
      by_cases hlt : k < j
      · rw [ite_eq_left hlt, ite_eq_left (by omega_using [hlt])]
      · rw [ite_eq_right hlt, ite_eq_right (by omega_using [hlt, hkj])]
  · by_cases hkj : k = j
    · subst hkj
      rw [a₄ 1 (by decide), hx, b₃, Nat.add_zero]; exact h.hi k hk
    · obtain ⟨-, n6, -⟩ := lreg_ne k
      have hne : lreg k ≠ lreg j := fun e => hkj (lreg_inj hk hj e)
      rw [kk.lane (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨n6, hne⟩)]
      exact h.hi k hk
  · rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · decide
      · exact lreg_mem

/-- `sumLanes`: the low lanes become the sums of the two. -/
theorem sumLanes_ok (s : State) (f : Nat → Nat → Nat) (hf : ∀ l < 2, Ls s l (f l))
    (hb : ∀ k < 5, f 0 k + f 1 k < 2 ^ 64) :
    WP isa (.block sumLanes) s fun s' =>
      Ls s' 0 (fun k => f 0 k + f 1 k) ∧ Ls s' 1 (f 1) ∧ s'.mem = s.mem ∧ Xk lregs s s' := by
  have e : sumLanes = ([.xop (.bin .movdqa .xmm6 (lreg 0)), .xop (.shift .psrldq .xmm6 8),
        .xop (.bin .paddq (lreg 0) .xmm6)] : List Instr) ++
      (([.xop (.bin .movdqa .xmm6 (lreg 1)), .xop (.shift .psrldq .xmm6 8),
        .xop (.bin .paddq (lreg 1) .xmm6)] : List Instr) ++
      (([.xop (.bin .movdqa .xmm6 (lreg 2)), .xop (.shift .psrldq .xmm6 8),
        .xop (.bin .paddq (lreg 2) .xmm6)] : List Instr) ++
      (([.xop (.bin .movdqa .xmm6 (lreg 3)), .xop (.shift .psrldq .xmm6 8),
        .xop (.bin .paddq (lreg 3) .xmm6)] : List Instr) ++
      [.xop (.bin .movdqa .xmm6 (lreg 4)), .xop (.shift .psrldq .xmm6 8),
        .xop (.bin .paddq (lreg 4) .xmm6)]))) := rfl
  rw [e]
  have i0 : SLInv f s 0 s := ⟨fun k hk => by
    rw [ite_eq_right (Nat.not_lt_zero _), Nat.add_zero]; exact hf 0 (by decide) k hk,
    fun k hk => hf 1 (by decide) k hk, rfl, Xk.refl _ _⟩
  refine WP.block_append (WP.mono (sumLimb_step (by decide) hb i0) fun s₁ i₁ => ?_)
  refine WP.block_append (WP.mono (sumLimb_step (by decide) hb i₁) fun s₂ i₂ => ?_)
  refine WP.block_append (WP.mono (sumLimb_step (by decide) hb i₂) fun s₃ i₃ => ?_)
  refine WP.block_append (WP.mono (sumLimb_step (by decide) hb i₃) fun s₄ i₄ => ?_)
  refine WP.mono (sumLimb_step (by decide) hb i₄) fun s₅ i₅ => ?_
  exact ⟨fun k hk => by rw [i₅.lo k hk, ite_eq_left hk], i₅.hi, i₅.mem, i₅.keep⟩

/-- The limbs' 8 bytes each in the frame. -/
abbrev oR (B : BitVec 32) : Region := ⟨addr B 464, 40⟩

theorem out_same (m : Mem) (a : Addr) (v : BitVec 64) : ((m.writeW a v).readW a 32).toNat = v.toNat % 2 ^ 32 := by
  rw [← Proof.Mont.X86.Sse2.readW64_lo, Mem.readW_writeW_self64, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

theorem out_other {B : BitVec 32} (hB : Fit B) (m : Mem) (v : BitVec 64) {d e : Nat} (hd : d + 4 ≤ 512)
    (he : e + 8 ≤ 512) (h : d + 4 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (addr B e) v).readW (addr B d) 32 = m.readW (addr B d) 32 :=
  Mem.readW_writeW_sep ((Proof.Aes.X86.part_disj hB hd he h).sep (Region.contains_self _ _)
    (Region.contains_self _ _)) (by decide)

theorem storeQ_ok (x : XReg) {o : Nat} {B : BitVec 32} (d : Nat) (s : State)
    (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) (hin : InRegions s.wr (addr B d) 8) :
    WP isa (.block [.movqStore (fs o d) x]) s fun s' =>
      s'.mem = s.mem.writeW (addr B d) (qword (s.xmm x) 0) ∧ Xk [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_fs hsp, hin, ↓reduceIte,
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem oR_contains {B : BitVec 32} (hB : Fit B) {d : Nat} (h₁ : 464 ≤ d) (h₂ : d + 8 ≤ 504) :
    (oR B).Contains (addr B d) (64 / 8) :=
  Proof.Aes.X86.part_contains (N := 512) (a := 464) (k := 40) hB (by decide) h₁ (by omega_using [h₂]) (by decide)

/-- `storeOut`: the low lanes of the limbs into the frame, read back as words. -/
theorem storeOut_ok {o : Nat} {B : BitVec 32} (s : State) (hsp : s.gpr .esp + BitVec.ofNat 32 o = B)
    (hB : Fit B) (hfr : Proof.Aes.X86.reg32 B 512 ∈ s.wr) :
    WP isa (.block (storeOut o)) s fun s' =>
      (∀ k < 5, (s'.mem.readW (addr B (outOff k)) 32).toNat = ln s (lreg k) 0 % 2 ^ 32) ∧
      Frame [oR B] s.mem s'.mem ∧ Xk [] s s' := by
  have e : storeOut o = ([.movqStore (fs o (outOff 0)) (lreg 0)] : List Instr) ++
      (([.movqStore (fs o (outOff 1)) (lreg 1)] : List Instr) ++ (([.movqStore (fs o (outOff 2)) (lreg 2)] : List Instr) ++
      (([.movqStore (fs o (outOff 3)) (lreg 3)] : List Instr) ++ [.movqStore (fs o (outOff 4)) (lreg 4)]))) := rfl
  rw [e]
  have st : ∀ (k : Nat), k < 5 → ∀ u : State, Xk [] s u →
      WP isa (.block [.movqStore (fs o (outOff k)) (lreg k)]) u fun u' =>
        u'.mem = u.mem.writeW (addr B (outOff k)) (qword (s.xmm (lreg k)) 0) ∧ Xk [] s u' := fun k hk u ku => by
    have hsu : u.gpr .esp + BitVec.ofNat 32 o = B := by rw [ku.gpr]; exact hsp
    have hiu : InRegions u.wr (addr B (outOff k)) 8 := by
      rw [ku.wr]; exact fr_in hB hfr (by simp only [outOff]; omega_using [hk]) (by decide)
    refine WP.mono (storeQ_ok (lreg k) (outOff k) u hsu hiu)
      fun u' ⟨m', k'⟩ => ⟨by rw [m', ku.xmm _ List.not_mem_nil], (ku.trans k').mono fun r hr => by simp at hr⟩
  refine WP.block_append (WP.mono (st 0 (by decide) s (Xk.refl _ _)) fun s₁ ⟨m₁, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (st 1 (by decide) s₁ k₁) fun s₂ ⟨m₂, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (st 2 (by decide) s₂ k₂) fun s₃ ⟨m₃, k₃⟩ => ?_)
  refine WP.block_append (WP.mono (st 3 (by decide) s₃ k₃) fun s₄ ⟨m₄, k₄⟩ => ?_)
  refine WP.mono (st 4 (by decide) s₄ k₄) fun s₅ ⟨m₅, k₅⟩ => ?_
  rw [m₄, m₃, m₂, m₁] at m₅
  refine ⟨fun k hk => ?_, ?_, k₅⟩
  · rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [m₅, out_other hB _ _ (by decide) (by decide) (by decide), out_other hB _ _ (by decide) (by decide) (by decide),
        out_other hB _ _ (by decide) (by decide) (by decide), out_other hB _ _ (by decide) (by decide) (by decide),
        out_same]; rfl
    · rw [m₅, out_other hB _ _ (by decide) (by decide) (by decide), out_other hB _ _ (by decide) (by decide) (by decide),
        out_other hB _ _ (by decide) (by decide) (by decide), out_same]; rfl
    · rw [m₅, out_other hB _ _ (by decide) (by decide) (by decide), out_other hB _ _ (by decide) (by decide) (by decide),
        out_same]; rfl
    · rw [m₅, out_other hB _ _ (by decide) (by decide) (by decide), out_same]; rfl
    · rw [m₅, out_same]; rfl
  · rw [m₅]
    exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (oR_contains hB (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (oR_contains hB (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (oR_contains hB (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (oR_contains hB (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (oR_contains hB (by decide) (by decide))

/-! ### The tables -/

/-- The slots of the tables, the mask and the bit `2²⁴`. -/
abbrev tR (B : BitVec 32) : Region := ⟨addr B 64, 352⟩

theorem tR_contains {B : BitVec 32} (hB : Fit B) {d : Nat} (h₁ : 64 ≤ d) (h₂ : d + 16 ≤ 416) :
    (tR B).Contains (addr B d) (128 / 8) :=
  Proof.Aes.X86.part_contains (N := 512) (a := 64) (k := 352) hB (by decide) h₁ (by omega_using [h₂]) (by decide)

theorem punpck_ok (x y : XReg) (s : State) :
    WP isa (.block [.xop (.bin .punpcklqdq x y)]) s fun s' =>
      ln s' x 0 = ln s x 0 ∧ ln s' x 1 = ln s y 0 ∧ s'.mem = s.mem ∧ Xk [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, Option.some.injEq, exists_eq_left']
  exact ⟨by rw [ln, xmm_setXmm_self, (lane_punpcklqdq _ _).1], by rw [ln, xmm_setXmm_self, (lane_punpcklqdq _ _).2],
    rfl, setXmm_xk _ _ _⟩

/-- `times5`: five times the lanes of `x` into a slot. -/
theorem times5_ok {o : Nat} {B : BitVec 32} (d : Nat) (x : XReg) (hx : x ≠ .xmm7) (s : State)
    (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) (hin : InRegions s.wr (addr B d) 16)
    (hb : ∀ l < 2, ln s x l < 2 ^ 61) :
    WP isa (.block (times5 o d x)) s fun s' =>
      (∃ v, s'.mem = s.mem.writeW (addr B d) v ∧ ∀ l < 2, lane v l = ln s x l + ln s x l * 2 ^ 2) ∧
      Xk [.xmm7] s s' := by
  show WP isa (.block (([.xop (.bin .movdqa .xmm7 x)] : List Instr) ++ (([.xop (.shift .psllq .xmm7 2)] : List Instr) ++
    (([.xop (.bin .paddq .xmm7 x)] : List Instr) ++ [.movdquStore (fs o d) .xmm7])))) s _
  have n7 : x ∉ [XReg.xmm7] := by simpa only [List.mem_singleton] using hx
  refine WP.block_append (WP.mono (mv_ok .xmm7 x s) fun s₁ ⟨v₁, m₁, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (psllq_ok .xmm7 2 (by decide) s₁ fun l hl => by
    rw [show ln s₁ .xmm7 l = ln s x l from congrArg (lane · l) v₁]
    have := hb l hl; show _ * 2 ^ 2 < _; omega_arith) fun s₂ ⟨a₂, m₂, k₂⟩ => ?_)
  have h7 : ∀ l < 2, ln s₂ .xmm7 l = ln s x l * 2 ^ 2 := fun l hl => by
    rw [a₂ l hl, ln, v₁]; rfl
  have hx₂ : ∀ l, ln s₂ x l = ln s x l := fun l => (k₂.lane n7 l).trans (k₁.lane n7 l)
  refine WP.block_append (WP.mono (paddq_ok .xmm7 x s₂ fun l hl => by
    rw [h7 l hl, hx₂]; have := hb l hl; omega_arith) fun s₃ ⟨a₃, m₃, k₃⟩ => ?_)
  have k₁₃ : Xk [.xmm7] s s₃ := ((k₁.trans k₂).trans k₃).mono fun r hr => by
    simp only [List.mem_append, List.mem_singleton, or_self] at hr; rw [hr]; decide
  have hs₃ : s₃.gpr .esp + BitVec.ofNat 32 o = B := by rw [k₁₃.gpr]; exact hsp
  have hi₃ : InRegions s₃.wr (addr B d) 16 := by rw [k₁₃.wr]; exact hin
  refine WP.mono (storeSlot_ok .xmm7 d s₃ hs₃ hi₃) fun s₄ ⟨m₄, k₄⟩ => ?_
  refine ⟨⟨s₃.xmm .xmm7, by rw [m₄, m₃, m₂, m₁], fun l hl => ?_⟩, (k₁₃.trans k₄).mono fun r hr => by
    simpa only [List.append_nil] using hr⟩
  show ln s₃ .xmm7 l = _
  rw [a₃ l hl, h7 l hl, hx₂, Nat.add_comm]

/-- The value in lane `l` of table `t`: `r` in the high lane of table 1, `r²` elsewhere. -/
def tbl (b c : Nat → Nat) (t l : Nat) : Nat → Nat := if t = 1 ∧ l = 1 then c else b

theorem qshift_le (k : Nat) : qshift k ≤ 26 ∧ qbyte k ≤ 13 := by
  rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | rfl | rfl | h
  · decide
  · decide
  · decide
  · decide
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega_using [h]⟩
    exact ⟨by show (0 : Nat) ≤ 26; decide, by show (13 : Nat) ≤ 13; decide⟩

/-- `tableLimb`: the four slots of limb `k`. -/
theorem tableLimb_ok {o : Nat} {B st : BitVec 32} (k : Nat) (hk : k < 5) (bk ck : Nat) (s : State)
    (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) (hB : Fit B) (hfr : Proof.Aes.X86.reg32 B 512 ∈ s.wr)
    (hedi : s.gpr .edi = st) (hin : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (addr st d) 8)
    (hm : ∀ l < 2, ln s .xmm5 l = 2 ^ 26 - 1)
    (hq : (s.mem.readW (addr st (qbyte k)) 64).toNat / 2 ^ qshift k % 2 ^ 26 = bk)
    (hr : (s.mem.readW (addr st (rOff 0 + lbyte k)) 64).toNat / 2 ^ lshift k % 2 ^ 26 = ck) :
    WP isa (.block (tableLimb o k)) s fun s' =>
      (∀ t < 2, ∀ l < 2, lane (s'.mem.readW (addr B (rSlot t k)) 128) l = (if t = 1 ∧ l = 1 then ck else bk)) ∧
      (∀ t < 2, ∀ l < 2, lane (s'.mem.readW (addr B (sSlot t k)) 128) l =
        (if t = 1 ∧ l = 1 then ck else bk) + (if t = 1 ∧ l = 1 then ck else bk) * 2 ^ 2) ∧
      (∀ j < 28, j ≠ k → j ≠ 10 + k → j ≠ 5 + k → j ≠ 15 + k →
        s'.mem.readW (addr B (slot j)) 128 = s.mem.readW (addr B (slot j)) 128) ∧
      Frame [tR B] s.mem s'.mem ∧ Xk [.xmm0, .xmm1, .xmm6, .xmm7] s s' := by
  obtain ⟨hqs, hqb⟩ := qshift_le k
  have hls := lshift_le k
  have hlb := lbyte_le k
  have hbk : bk < 2 ^ 26 := by rw [← hq]; exact Nat.mod_lt _ (by decide)
  have hck : ck < 2 ^ 26 := by rw [← hr]; exact Nat.mod_lt _ (by decide)
  have hw : ∀ (u : State) (d : Nat), d + 16 ≤ 512 → u.wr = s.wr → InRegions u.wr (addr B d) 16 :=
    fun u d hd h => by rw [h]; exact fr_in hB hfr hd (by decide)
  simp only [tableLimb, List.append_assoc]
  refine WP.block_append (WP.mono (limb_ok .edi (qbyte k) (qshift k) (by omega_using [hqs]) false s hm
    (by rw [hedi]; exact hin _ (by omega_using [hqb])) (fun h => absurd h (by decide))) fun s₁ ⟨a₁, b₁, m₁, k₁⟩ => ?_)
  rw [hedi, hq] at a₁
  rw [ite_eq_right (by decide)] at b₁
  refine WP.block_append (WP.mono (mv_ok .xmm0 .xmm6 s₁) fun s₂ ⟨v₂, m₂, k₂⟩ => ?_)
  have k₁₂ : Xk [.xmm0, .xmm6, .xmm7] s s₂ := (k₁.trans k₂).mono fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl <;> decide
  refine WP.block_append (WP.mono (limb_ok .edi (rOff 0 + lbyte k) (lshift k) (by omega_using [hls]) false s₂
    (fun l hl => by rw [k₁₂.lane (by decide)]; exact hm l hl)
    (by rw [k₁₂.gpr, k₁₂.rd, k₁₂.wr, hedi]; exact hin _ (by simp only [rOff]; omega_using [hlb]))
    (fun h => absurd h (by decide))) fun s₃ ⟨a₃, b₃, m₃, k₃⟩ => ?_)
  rw [k₁₂.gpr, hedi, m₂, m₁, hr] at a₃
  rw [ite_eq_right (by decide)] at b₃
  have x0₃ : ∀ l, ln s₃ .xmm0 l = ln s₁ .xmm6 l := fun l => by
    rw [k₃.lane (by decide), ln, v₂]
  show WP isa (.block (([.xop (.bin .movdqa .xmm1 .xmm0)] : List Instr) ++
    (([.xop (.bin .punpcklqdq .xmm1 .xmm1)] : List Instr) ++ (([.movdquStore (fs o (rSlot 0 k)) .xmm1] : List Instr) ++
    (([.xop (.bin .punpcklqdq .xmm0 .xmm6)] : List Instr) ++ (([.movdquStore (fs o (rSlot 1 k)) .xmm0] : List Instr) ++
    (times5 o (sSlot 0 k) .xmm1 ++ times5 o (sSlot 1 k) .xmm0))))))) s₃ _
  refine WP.block_append (WP.mono (mv_ok .xmm1 .xmm0 s₃) fun s₄ ⟨v₄, m₄, k₄⟩ => ?_)
  refine WP.block_append (WP.mono (punpck_ok .xmm1 .xmm1 s₄) fun s₅ ⟨a₅, b₅, m₅, k₅⟩ => ?_)
  have x1₅ : ∀ l < 2, ln s₅ .xmm1 l = bk := fun l hl => by
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
    · rw [a₅, ln, v₄]; exact (x0₃ 0).trans a₁
    · rw [b₅, ln, v₄]; exact (x0₃ 0).trans a₁
  have k₃₅ : Xk [.xmm0, .xmm1, .xmm6, .xmm7] s s₅ := ((k₁₂.trans k₃).trans (k₄.trans k₅)).mono fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ((rfl | rfl | rfl) | (rfl | rfl)) | (rfl | rfl) <;> decide
  have hs₅ : s₅.gpr .esp + BitVec.ofNat 32 o = B := by rw [k₃₅.gpr]; exact hsp
  have hr0 : rSlot 0 k + 16 ≤ 512 := by simp only [rSlot, slot]; omega_using [hk]
  have hr1 : rSlot 1 k + 16 ≤ 512 := by simp only [rSlot, slot]; omega_using [hk]
  have hs0 : sSlot 0 k + 16 ≤ 512 := by simp only [sSlot, slot]; omega_using [hk]
  have hs1 : sSlot 1 k + 16 ≤ 512 := by simp only [sSlot, slot]; omega_using [hk]
  refine WP.block_append (WP.mono (storeSlot_ok .xmm1 (rSlot 0 k) s₅ hs₅ (hw s₅ _ hr0 k₃₅.wr))
    fun s₆ ⟨m₆, k₆⟩ => ?_)
  refine WP.block_append (WP.mono (punpck_ok .xmm0 .xmm6 s₆) fun s₇ ⟨a₇, b₇, m₇, k₇⟩ => ?_)
  have x0₇ : ∀ l < 2, ln s₇ .xmm0 l = (if l = 1 then ck else bk) := fun l hl => by
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
    · rw [a₇, k₆.lane List.not_mem_nil, k₅.lane (by decide), k₄.lane (by decide), x0₃, ite_eq_right (by decide)]
      exact a₁
    · rw [b₇, k₆.lane List.not_mem_nil, k₅.lane (by decide), k₄.lane (by decide), ite_eq_left rfl]
      exact a₃
  have x1₇ : ∀ l < 2, ln s₇ .xmm1 l = bk := fun l hl => by
    rw [k₇.lane (by decide), k₆.lane List.not_mem_nil]; exact x1₅ l hl
  have k₅₇ : Xk [.xmm0, .xmm1, .xmm6, .xmm7] s s₇ := (k₃₅.trans (k₆.trans k₇)).mono fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.nil_append] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl <;> decide
  have hs₇ : s₇.gpr .esp + BitVec.ofNat 32 o = B := by rw [k₅₇.gpr]; exact hsp
  refine WP.block_append (WP.mono (storeSlot_ok .xmm0 (rSlot 1 k) s₇ hs₇ (hw s₇ _ hr1 k₅₇.wr))
    fun s₈ ⟨m₈, k₈⟩ => ?_)
  have k₈' : Xk [.xmm0, .xmm1, .xmm6, .xmm7] s s₈ := (k₅₇.trans k₈).mono fun r hr => by
    simpa only [List.append_nil] using hr
  have hs₈ : s₈.gpr .esp + BitVec.ofNat 32 o = B := by rw [k₈'.gpr]; exact hsp
  refine WP.block_append (WP.mono (times5_ok (sSlot 0 k) .xmm1 (by decide) s₈ hs₈ (hw s₈ _ hs0 k₈'.wr)
    fun l hl => by rw [k₈.lane List.not_mem_nil, x1₇ l hl]; exact Nat.lt_trans hbk (by decide))
    fun s₉ ⟨⟨w₉, m₉, l₉⟩, k₉⟩ => ?_)
  have k₉' : Xk [.xmm0, .xmm1, .xmm6, .xmm7] s s₉ := (k₈'.trans k₉).mono fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl <;> decide
  have hs₉ : s₉.gpr .esp + BitVec.ofNat 32 o = B := by rw [k₉'.gpr]; exact hsp
  refine WP.mono (times5_ok (sSlot 1 k) .xmm0 (by decide) s₉ hs₉ (hw s₉ _ hs1 k₉'.wr)
    fun l hl => by
      rw [k₉.lane (by decide), k₈.lane List.not_mem_nil, x0₇ l hl]
      split <;> [exact Nat.lt_trans hck (by decide); exact Nat.lt_trans hbk (by decide)])
    fun s' ⟨⟨w', m', l'⟩, k'⟩ => ?_
  -- The memory: four slots written.
  have hmem : s'.mem = (((s.mem.writeW (addr B (rSlot 0 k)) (s₅.xmm .xmm1)).writeW (addr B (rSlot 1 k))
      (s₇.xmm .xmm0)).writeW (addr B (sSlot 0 k)) w₉).writeW (addr B (sSlot 1 k)) w' := by
    rw [m', m₉, m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁]
  have so : ∀ (m : Mem) (v : BitVec 128) (d e : Nat), d + 16 ≤ 512 → e + 16 ≤ 512 → (d + 16 ≤ e ∨ e + 16 ≤ d) →
      (m.writeW (addr B e) v).readW (addr B d) 128 = m.readW (addr B d) 128 := fun m v d e hd he h =>
    slot_other hB m v hd he h
  refine ⟨fun t ht l hl => ?_, fun t ht l hl => ?_, fun j hj n1 n2 n3 n4 => ?_, ?_,
    (k₉'.trans k').mono fun r hr => ?_⟩
  · rcases (by omega_using [ht] : t = 0 ∨ t = 1) with rfl | rfl
    · rw [hmem, so _ _ _ _ hr0 hs1 (by simp only [rSlot, sSlot, slot]; omega_arith),
        so _ _ _ _ hr0 hs0 (by simp only [rSlot, sSlot, slot]; omega_arith),
        so _ _ _ _ hr0 hr1 (by simp only [rSlot, slot]; omega_arith), slot_same,
        ite_eq_right (fun h => absurd h.1 (by decide))]
      exact x1₅ l hl
    · rw [hmem, so _ _ _ _ hr1 hs1 (by simp only [rSlot, sSlot, slot]; omega_arith),
        so _ _ _ _ hr1 hs0 (by simp only [rSlot, sSlot, slot]; omega_arith), slot_same]
      refine (x0₇ l hl).trans ?_
      by_cases h1 : l = 1
      · rw [ite_eq_left h1, ite_eq_left ⟨rfl, h1⟩]
      · rw [ite_eq_right h1, ite_eq_right (fun h => h1 h.2)]
  · rcases (by omega_using [ht] : t = 0 ∨ t = 1) with rfl | rfl
    · rw [hmem, so _ _ _ _ hs0 hs1 (by simp only [sSlot, slot]; omega_arith), slot_same, l₉ l hl,
        k₈.lane List.not_mem_nil, x1₇ l hl, ite_eq_right (fun h => absurd h.1 (by decide))]
    · rw [hmem, slot_same, l' l hl, k₉.lane (by decide), k₈.lane List.not_mem_nil, x0₇ l hl]
      by_cases h1 : l = 1
      · rw [ite_eq_left h1, ite_eq_left ⟨rfl, h1⟩]
      · rw [ite_eq_right h1, ite_eq_right (fun h => h1 h.2)]
  · have hj' : slot j + 16 ≤ 512 := by simp only [slot]; omega_using [hj]
    rw [hmem, so _ _ _ _ hj' hs1 (by simp only [sSlot, slot]; omega_using [n4]),
      so _ _ _ _ hj' hs0 (by simp only [sSlot, slot]; omega_using [n3]),
      so _ _ _ _ hj' hr1 (by simp only [rSlot, slot]; omega_using [n2]),
      so _ _ _ _ hj' hr0 (by simp only [rSlot, slot]; omega_using [n1])]
  · rw [hmem]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (tR_contains hB (by simp only [rSlot, slot]; omega_arith) (by simp only [rSlot, slot]; omega_using [hk]))).writeW
      (List.mem_singleton_self _) _
      (tR_contains hB (by simp only [rSlot, slot]; omega_arith) (by simp only [rSlot, slot]; omega_using [hk]))).writeW
      (List.mem_singleton_self _) _
      (tR_contains hB (by simp only [sSlot, slot]; omega_arith) (by simp only [sSlot, slot]; omega_using [hk]))).writeW
      (List.mem_singleton_self _) _
      (tR_contains hB (by simp only [sSlot, slot]; omega_arith) (by simp only [sSlot, slot]; omega_using [hk]))
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl <;> decide

/-- As `Xk`, but `eax` may change too. -/
structure Xe (xs : List XReg) (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mcdt : s'.mcdt = s.mcdt
  xmm : ∀ r, r ∉ xs → s'.xmm r = s.xmm r

theorem Xk.xe {xs : List XReg} {s s' : State} (h : Xk xs s s') : Xe xs s s' :=
  ⟨fun r _ => congrFun h.gpr r, h.rd, h.wr, h.mcdt, h.xmm⟩

theorem Xe.trans {xs ys : List XReg} {s s' s'' : State} (h : Xe xs s s') (h' : Xe ys s' s'') :
    Xe (xs ++ ys) s s'' :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.rd.trans h.rd, h'.wr.trans h.wr, h'.mcdt.trans h.mcdt,
    fun r hr => by
      simp only [List.mem_append, not_or] at hr
      exact (h'.xmm r hr.2).trans (h.xmm r hr.1)⟩

theorem Xe.mono {xs ys : List XReg} {s s' : State} (h : Xe xs s s') (hs : ∀ r ∈ xs, r ∈ ys) : Xe ys s s' :=
  ⟨h.gpr, h.rd, h.wr, h.mcdt, fun r hr => h.xmm r fun h' => hr (hs r h')⟩

theorem Xe.lane {xs : List XReg} {s s' : State} (h : Xe xs s s') {x : XReg} (hx : x ∉ xs) (l : Nat) :
    Sse2.ln s' x l = Sse2.ln s x l := by
  rw [Sse2.ln, h.xmm x hx]

theorem Xe.all {xs : List XReg} {s s' : State} (h : Xe xs s s') : Xe xall s s' :=
  ⟨h.gpr, h.rd, h.wr, h.mcdt, fun r hr => absurd (by cases r <;> decide) hr⟩

theorem Xe.sp {xs : List XReg} {s s' : State} {o : Nat} {B : BitVec 32} (h : Xe xs s s')
    (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) : s'.gpr .esp + BitVec.ofNat 32 o = B := by
  rw [h.gpr _ (by decide)]; exact hsp

/-- A constant into both lanes of `x`, through `eax`. -/
theorem cst_ok (x : XReg) (c : BitVec 32) (s : State) :
    WP isa (.block [.mov .eax (.imm c), .xop (.movd x .eax), .xop (.bin .punpcklqdq x x)]) s fun s' =>
      (∀ l < 2, ln s' x l = c.toNat) ∧ s'.mem = s.mem ∧ Xe [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, XOp.exec, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, rfl, fun r hr => ?_, rfl, rfl, rfl, fun r hr => ?_⟩
  · have e : ((s.setReg .eax c).setXmm x ((0 : BitVec 96) ++ (s.setReg .eax c).gpr .eax)).xmm x =
        (0 : BitVec 96) ++ c := by rw [xmm_setXmm_self, gpr_setReg_self]
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
    · rw [ln, xmm_setXmm_self, (lane_punpcklqdq _ _).1, e, (lane_movd c).1]
    · rw [ln, xmm_setXmm_self, (lane_punpcklqdq _ _).2, e, (lane_movd c).1]
  · rw [gpr_setXmm, gpr_setXmm, gpr_setReg_of_ne _ _ hr]
  · simp only [List.mem_singleton] at hr
    rw [xmm_setXmm_of_ne _ _ hr, xmm_setXmm_of_ne _ _ hr]; rfl

/-- `consts`: the mask in `xmm5` and its slot, and the bit `2²⁴` in its slot. -/
theorem consts_ok {o : Nat} {B : BitVec 32} (s : State) (hsp : s.gpr .esp + BitVec.ofNat 32 o = B)
    (hB : Fit B) (hfr : Proof.Aes.X86.reg32 B 512 ∈ s.wr) :
    WP isa (.block (consts o)) s fun s' =>
      (∀ l < 2, ln s' .xmm5 l = 2 ^ 26 - 1) ∧
      (∀ l < 2, lane (s'.mem.readW (addr B maskSlot) 128) l = 2 ^ 26 - 1) ∧
      (∀ l < 2, lane (s'.mem.readW (addr B hibitSlot) 128) l = 2 ^ 24) ∧
      Frame [tR B] s.mem s'.mem ∧ Xe [.xmm5, .xmm6] s s' := by
  show WP isa (.block (([.mov .eax (.imm 0x3ffffff), .xop (.movd .xmm5 .eax),
      .xop (.bin .punpcklqdq .xmm5 .xmm5)] : List Instr) ++ (([.movdquStore (fs o maskSlot) .xmm5] : List Instr) ++
    (([.mov .eax (.imm 0x1000000), .xop (.movd .xmm6 .eax), .xop (.bin .punpcklqdq .xmm6 .xmm6)] : List Instr) ++
    [.movdquStore (fs o hibitSlot) .xmm6])))) s _
  refine WP.block_append (WP.mono (cst_ok .xmm5 0x3ffffff s) fun s₁ ⟨a₁, m₁, k₁⟩ => ?_)
  have hs₁ := k₁.sp hsp
  have hw₁ : InRegions s₁.wr (addr B maskSlot) 16 := by
    rw [k₁.wr]; exact fr_in hB hfr (show maskSlot + 16 ≤ 512 by decide) (by decide)
  refine WP.block_append (WP.mono (storeSlot_ok .xmm5 maskSlot s₁ hs₁ hw₁) fun s₂ ⟨m₂, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (cst_ok .xmm6 0x1000000 s₂) fun s₃ ⟨a₃, m₃, k₃⟩ => ?_)
  have k₁₃ : Xe [.xmm5, .xmm6] s s₃ := ((k₁.trans k₂.xe).trans k₃).mono fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  have hs₃ := k₁₃.sp hsp
  have hw₃ : InRegions s₃.wr (addr B hibitSlot) 16 := by
    rw [k₁₃.wr]; exact fr_in hB hfr (show hibitSlot + 16 ≤ 512 by decide) (by decide)
  refine WP.mono (storeSlot_ok .xmm6 hibitSlot s₃ hs₃ hw₃) fun s₄ ⟨m₄, k₄⟩ => ?_
  have hmem : s₄.mem = (s.mem.writeW (addr B maskSlot) (s₁.xmm .xmm5)).writeW (addr B hibitSlot) (s₃.xmm .xmm6) := by
    rw [m₄, m₃, m₂, m₁]
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, ?_, (k₁₃.trans k₄.xe).mono fun r hr => by
    simpa only [List.append_nil] using hr⟩
  · rw [k₄.lane List.not_mem_nil, k₃.lane (by decide), k₂.lane List.not_mem_nil, a₁ l hl]; rfl
  · rw [hmem, slot_other hB _ _ (by decide) (by decide) (by decide), slot_same]
    exact (a₁ l hl).trans rfl
  · rw [hmem, slot_same]
    exact (a₃ l hl).trans rfl
  · rw [hmem]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (tR_contains hB (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (tR_contains hB (by decide) (by decide))

theorem tbl_apply (b c : Nat → Nat) (t l k : Nat) : tbl b c t l k = if t = 1 ∧ l = 1 then c k else b k := by
  simp only [tbl]; split <;> rfl

/-- After the limbs before `j` of the tables. -/
structure TInv (B : BitVec 32) (b c : Nat → Nat) (s : State) (j : Nat) (u : State) : Prop where
  rs : ∀ k < j, ∀ t < 2, ∀ l < 2, lane (u.mem.readW (addr B (rSlot t k)) 128) l = tbl b c t l k
  ss : ∀ k < j, ∀ t < 2, ∀ l < 2,
    lane (u.mem.readW (addr B (sSlot t k)) 128) l = tbl b c t l k + tbl b c t l k * 2 ^ 2
  mask : ∀ l < 2, lane (u.mem.readW (addr B maskSlot) 128) l = 2 ^ 26 - 1
  hibit : ∀ l < 2, lane (u.mem.readW (addr B hibitSlot) 128) l = 2 ^ 24
  frame : Frame [tR B] s.mem u.mem
  keep : Xk [.xmm0, .xmm1, .xmm6, .xmm7] s u

/-- `tables`: the tables, from `r²` (reduced) in `h` and `r`. -/
theorem tables_ok {o : Nat} {B st : BitVec 32} (b c : Nat → Nat) (s : State)
    (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) (hB : Fit B) (hfr : Proof.Aes.X86.reg32 B 512 ∈ s.wr)
    (hedi : s.gpr .edi = st) (hst : st.toNat + 128 ≤ 2 ^ 32)
    (hin : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (addr st d) 8)
    (hdj : (sR st).Disjoint (tR B))
    (hm : ∀ l < 2, ln s .xmm5 l = 2 ^ 26 - 1)
    (hmk : ∀ l < 2, lane (s.mem.readW (addr B maskSlot) 128) l = 2 ^ 26 - 1)
    (hhb : ∀ l < 2, lane (s.mem.readW (addr B hibitSlot) 128) l = 2 ^ 24)
    (hq : ∀ k < 5, (s.mem.readW (addr st (qbyte k)) 64).toNat / 2 ^ qshift k % 2 ^ 26 = b k)
    (hr : ∀ k < 5, (s.mem.readW (addr st (rOff 0 + lbyte k)) 64).toNat / 2 ^ lshift k % 2 ^ 26 = c k) :
    WP isa (.block (tables o)) s fun s' =>
      Tab s'.mem B (tbl b c) ∧ Frame [tR B] s.mem s'.mem ∧ Xk [.xmm0, .xmm1, .xmm6, .xmm7] s s' := by
  have step : ∀ (j : Nat), j < 5 → ∀ u : State, TInv B b c s j u →
      WP isa (.block (tableLimb o j)) u (TInv B b c s (j + 1)) := fun j hj u hu => by
    have rdst : ∀ d, d + 8 ≤ 128 → u.mem.readW (addr st d) 64 = s.mem.readW (addr st d) 64 := fun d hd =>
      hu.frame.readW (r := sR st) (Proof.Poly1305.X86.sR_contains hst hd (by decide))
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hdj) (by decide)
    have hqb := (qshift_le j).2
    have hlb := lbyte_le j
    have hsp' : u.gpr .esp + BitVec.ofNat 32 o = B := by rw [hu.keep.gpr]; exact hsp
    have hedi' : u.gpr .edi = st := by rw [hu.keep.gpr]; exact hedi
    refine WP.mono (tableLimb_ok j hj (b j) (c j) u hsp' hB
      (by rw [hu.keep.wr]; exact hfr) hedi'
      (by rw [hu.keep.rd, hu.keep.wr]; exact hin)
      (fun l hl => by rw [hu.keep.lane (by decide)]; exact hm l hl)
      (by rw [rdst _ (by omega_using [hqb])]; exact hq j hj)
      (by rw [rdst _ (by simp only [rOff]; omega_using [hlb])]; exact hr j hj))
      fun u' ⟨r', s', o', f', k'⟩ => ?_
    refine ⟨fun k hk t ht l hl => ?_, fun k hk t ht l hl => ?_, fun l hl => ?_, fun l hl => ?_,
      hu.frame.trans f', (hu.keep.trans k').mono fun r hr => by
        rcases List.mem_append.mp hr with h | h <;> exact h⟩
    · rw [tbl_apply]
      by_cases hkj : k = j
      · subst hkj; exact r' t ht l hl
      · rw [rSlot, o' _ (by omega_using [ht, hk, hj]) (by omega_using [ht, hk, hj, hkj])
          (by omega_using [ht, hk, hj, hkj]) (by omega_using [ht, hk, hj, hkj]) (by omega_using [ht, hk, hj, hkj]),
          ← tbl_apply]
        exact hu.rs k (by omega_using [hk, hkj]) t ht l hl
    · rw [tbl_apply]
      by_cases hkj : k = j
      · subst hkj; exact s' t ht l hl
      · rw [sSlot, o' _ (by omega_using [ht, hk, hj]) (by omega_using [ht, hk, hj, hkj])
          (by omega_using [ht, hk, hj, hkj]) (by omega_using [ht, hk, hj, hkj]) (by omega_using [ht, hk, hj, hkj]),
          ← tbl_apply]
        exact hu.ss k (by omega_using [hk, hkj]) t ht l hl
    · rw [maskSlot, o' 20 (by decide) (by omega_using [hj]) (by omega_using [hj]) (by omega_using [hj])
        (by omega_using [hj])]
      exact hu.mask l hl
    · rw [hibitSlot, o' 21 (by decide) (by omega_using [hj]) (by omega_using [hj]) (by omega_using [hj])
        (by omega_using [hj])]
      exact hu.hibit l hl
  have e : tables o = tableLimb o 0 ++ (tableLimb o 1 ++ (tableLimb o 2 ++ (tableLimb o 3 ++ tableLimb o 4))) := by
    simp only [tables, List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [e]
  have i0 : TInv B b c s 0 s := ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    hmk, hhb, Frame.refl _ _, Xk.refl _ _⟩
  refine WP.block_append (WP.mono (step 0 (by decide) s i0) fun s₁ i₁ => ?_)
  refine WP.block_append (WP.mono (step 1 (by decide) s₁ i₁) fun s₂ i₂ => ?_)
  refine WP.block_append (WP.mono (step 2 (by decide) s₂ i₂) fun s₃ i₃ => ?_)
  refine WP.block_append (WP.mono (step 3 (by decide) s₃ i₃) fun s₄ i₄ => ?_)
  refine WP.mono (step 4 (by decide) s₄ i₄) fun s₅ i₅ => ?_
  exact ⟨⟨fun t ht k hk l hl => i₅.rs k hk t ht l hl, fun t ht k hk l hl => i₅.ss k hk t ht l hl, i₅.mask,
    i₅.hibit⟩, i₅.frame, i₅.keep⟩

/-! ### The accumulator into the lanes -/

/-- `[esp + o + d]`, as an address of the frame. -/
theorem addr_sp {s : State} {o : Nat} {B : BitVec 32} (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) (d : Nat) :
    addr (s.gpr .esp) (o + d) = addr B d := by
  rw [← hsp, Proof.Aes.X86.addr_add]

/-- After the limbs before `j` of `initH`. -/
structure IHInv (X : Nat) (s : State) (j : Nat) (s' : State) : Prop where
  lo : ∀ k < j, ln s' (lreg k) 0 = lim X k
  hi : ∀ k < j, ln s' (lreg k) 1 = 0
  mem : s'.mem = s.mem
  keep : Xk lregs s s'

theorem initLimb_step {o : Nat} {B : BitVec 32} {j : Nat} (hj : j < 5) {s s₁ : State}
    (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) (hB : Fit B) (hfr : Proof.Aes.X86.reg32 B 512 ∈ s.wr)
    (hm : ∀ l < 2, ln s .xmm5 l = 2 ^ 26 - 1)
    (h : IHInv (leNum (bytesAt s.mem (B.setWidth 64) 16)) s j s₁) :
    WP isa (.block (limb .esp (o + lbyte j) (lshift j) false ++
      ([.xop (.bin .movdqa (lreg j) .xmm6)] : List Instr))) s₁
      (IHInv (leNum (bytesAt s.mem (B.setWidth 64) 16)) s (j + 1)) := by
  have hl := lbyte_le j
  have hsl := lshift_le j
  obtain ⟨-, n6, n7⟩ := lreg_ne j
  have hsp₁ : s₁.gpr .esp + BitVec.ofNat 32 o = B := by rw [h.keep.gpr]; exact hsp
  have hin : InRegions (s₁.rd ++ s₁.wr) (addr (s₁.gpr .esp) (o + lbyte j)) 8 := by
    rw [addr_sp hsp₁, h.keep.rd, h.keep.wr]
    exact Proof.Aes.X86.in_rd (fr_in hB hfr (by omega_using [hl]) (by decide))
  refine WP.block_append (WP.mono (limb_ok .esp (o + lbyte j) (lshift j) (by omega_using [hsl]) false s₁
    (fun l hl' => by rw [h.keep.lane (by decide)]; exact hm l hl') hin (fun h' => absurd h' (by decide)))
    fun s₂ ⟨a0, a1, m₂, k₂⟩ => ?_)
  refine WP.mono (mv_ok (lreg j) .xmm6 s₂) fun s₃ ⟨v₃, m₃, k₃⟩ => ?_
  have v0 : ln s₃ (lreg j) 0 = lim (leNum (bytesAt s.mem (B.setWidth 64) 16)) j := by
    rw [ln, v₃]
    refine a0.trans ?_
    rw [addr_sp hsp₁, h.mem, ← limbv_read _ _ hj, addr_eq (by omega_using [hB, hl])]
    rfl
  have v1 : ln s₃ (lreg j) 1 = 0 := by
    rw [ln, v₃]
    exact a1.trans (ite_eq_right (by decide))
  have ho : ∀ k < 5, k ≠ j → ∀ l, ln s₃ (lreg k) l = ln s₁ (lreg k) l := fun k hk hkj l => by
    have hne : lreg k ≠ lreg j := fun e => hkj (lreg_inj hk hj e)
    obtain ⟨-, m6, m7⟩ := lreg_ne k
    rw [k₃.lane (by simpa only [List.mem_singleton] using hne),
      k₂.lane (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨m6, m7⟩)]
  refine ⟨fun k hk => ?_, fun k hk => ?_, by rw [m₃, m₂, h.mem], (h.keep.trans (k₂.trans k₃)).mono fun r hr => ?_⟩
  · by_cases hkj : k = j
    · subst hkj; exact v0
    · rw [ho k (by omega_using [hk, hj]) hkj]; exact h.lo k (by omega_using [hk, hkj])
  · by_cases hkj : k = j
    · subst hkj; exact v1
    · rw [ho k (by omega_using [hk, hj]) hkj]; exact h.hi k (by omega_using [hk, hkj])
  · rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl
      · decide
      · decide
      · exact lreg_mem

theorem and7 (v : BitVec 32) : (v &&& 7).toNat = v.toNat % 8 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod v.toNat 3

/-- The low three bits of a word of the frame, into the low lane of `xmm6`
(through `eax`). -/
theorem topWord_ok {o : Nat} {B : BitVec 32} (d : Nat) (s : State) (hsp : s.gpr .esp + BitVec.ofNat 32 o = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B d) 4) :
    WP isa (.block [.mov .eax (.mem (fs o d)), .alu .and .eax (.imm 7), .xop (.movd .xmm6 .eax)]) s fun s' =>
      ln s' .xmm6 0 = (s.mem.readW (addr B d) 32).toNat % 8 ∧ ln s' .xmm6 1 = 0 ∧ s'.mem = s.mem ∧
      Xe [.xmm6] s s' := by
  have e := ea_fs hsp d
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load32, e, hin, ↓reduceIte,
    XOp.exec, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, rfl, fun r hr => ?_, rfl, rfl, rfl, fun r hr => ?_⟩
  · rw [ln, xmm_setXmm_self, gpr_setReg_self, (lane_movd _).1, gpr_setReg_self, and7]
  · rw [ln, xmm_setXmm_self, (lane_movd _).2]
  · rw [gpr_setXmm, gpr_setReg_of_ne _ _ hr]
    exact gpr_setReg_of_ne _ _ hr
  · simp only [List.mem_singleton] at hr
    rw [xmm_setXmm_of_ne _ _ hr]; rfl

/-- `initH`: the limbs of the 16 bytes at the frame's start in the low lanes,
the fifth with the low three bits of the word after them, times `2²⁴`. -/
theorem initH_ok {o : Nat} {B : BitVec 32} (s : State) (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) (hB : Fit B)
    (hfr : Proof.Aes.X86.reg32 B 512 ∈ s.wr) (hm : ∀ l < 2, ln s .xmm5 l = 2 ^ 26 - 1) :
    WP isa (.block (initH o)) s fun s' =>
      (∀ k < 5, ln s' (lreg k) 0 = lim (leNum (bytesAt s.mem (B.setWidth 64) 16)) k +
        (if k < 4 then 0 else (s.mem.readW (addr B (svOff 4)) 32).toNat % 8 * 2 ^ 24)) ∧
      (∀ k < 5, ln s' (lreg k) 1 = 0) ∧ s'.mem = s.mem ∧ Xe lregs s s' := by
  have e : initH o = (limb .esp (o + lbyte 0) (lshift 0) false ++ ([.xop (.bin .movdqa (lreg 0) .xmm6)] : List Instr)) ++
      ((limb .esp (o + lbyte 1) (lshift 1) false ++ ([.xop (.bin .movdqa (lreg 1) .xmm6)] : List Instr)) ++
      ((limb .esp (o + lbyte 2) (lshift 2) false ++ ([.xop (.bin .movdqa (lreg 2) .xmm6)] : List Instr)) ++
      ((limb .esp (o + lbyte 3) (lshift 3) false ++ ([.xop (.bin .movdqa (lreg 3) .xmm6)] : List Instr)) ++
      ((limb .esp (o + lbyte 4) (lshift 4) false ++ ([.xop (.bin .movdqa (lreg 4) .xmm6)] : List Instr)) ++
      (([.mov .eax (.mem (fs o (svOff 4))), .alu .and .eax (.imm 7), .xop (.movd .xmm6 .eax)] : List Instr) ++
      (([.xop (.shift .psllq .xmm6 24)] : List Instr) ++ [.xop (.bin .paddq .xmm4 .xmm6)])))))) := by
    simp only [initH, List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  have i0 : IHInv (leNum (bytesAt s.mem (B.setWidth 64) 16)) s 0 s :=
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _), rfl, Xk.refl _ _⟩
  refine WP.block_append (WP.mono (initLimb_step (by decide) hsp hB hfr hm i0) fun s₁ i₁ => ?_)
  refine WP.block_append (WP.mono (initLimb_step (by decide) hsp hB hfr hm i₁) fun s₂ i₂ => ?_)
  refine WP.block_append (WP.mono (initLimb_step (by decide) hsp hB hfr hm i₂) fun s₃ i₃ => ?_)
  refine WP.block_append (WP.mono (initLimb_step (by decide) hsp hB hfr hm i₃) fun s₄ i₄ => ?_)
  refine WP.block_append (WP.mono (initLimb_step (by decide) hsp hB hfr hm i₄) fun s₅ i₅ => ?_)
  have hsp₅ : s₅.gpr .esp + BitVec.ofNat 32 o = B := by rw [i₅.keep.gpr]; exact hsp
  have hin₅ : InRegions (s₅.rd ++ s₅.wr) (addr B (svOff 4)) 4 := by
    rw [i₅.keep.rd, i₅.keep.wr]
    exact Proof.Aes.X86.in_rd (fr_in hB hfr (show svOff 4 + 4 ≤ 512 by decide) (by decide))
  refine WP.block_append (WP.mono (topWord_ok (svOff 4) s₅ hsp₅ hin₅) fun s₆ ⟨a₆, b₆, m₆, k₆⟩ => ?_)
  have hT : (s₅.mem.readW (addr B (svOff 4)) 32).toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  refine WP.block_append (WP.mono (psllq_ok .xmm6 24 (by decide) s₆ fun l hl => by
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
    · rw [a₆]; show _ * 2 ^ 24 < _; omega_using [hT]
    · rw [b₆]; decide) fun s₇ ⟨a₇, m₇, k₇⟩ => ?_)
  have h4 : ∀ l, ln s₇ .xmm4 l = ln s₅ .xmm4 l := fun l => by
    rw [k₇.lane (by decide), k₆.lane (by decide)]
  have lo4 : ln s₅ .xmm4 0 = lim (leNum (bytesAt s.mem (B.setWidth 64) 16)) 4 := i₅.lo 4 (by decide)
  have hi4 : ln s₅ .xmm4 1 = 0 := i₅.hi 4 (by decide)
  have hl4 : lim (leNum (bytesAt s.mem (B.setWidth 64) 16)) 4 < 2 ^ 24 :=
    lim4_lt (by have := leNum_bytes_lt s.mem (B.setWidth 64) 16; omega_using [this])
  have v0 : ln s₇ .xmm6 0 = (s₅.mem.readW (addr B (svOff 4)) 32).toNat % 8 * 2 ^ 24 := by
    rw [a₇ 0 (by decide), a₆]; rfl
  have v1 : ln s₇ .xmm6 1 = 0 := by rw [a₇ 1 (by decide), b₆]; rfl
  refine WP.mono (paddq_ok .xmm4 .xmm6 s₇ fun l hl => by
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
    · rw [h4, lo4, v0]; omega_using [hT, hl4]
    · rw [h4, hi4, v1]; decide) fun s₈ ⟨a₈, m₈, k₈⟩ => ?_
  have ho : ∀ k < 5, k ≠ 4 → ∀ l, ln s₈ (lreg k) l = ln s₅ (lreg k) l := fun k hk hk4 l => by
    have hne : lreg k ≠ .xmm4 := fun e => hk4 (lreg_inj hk (by decide) e)
    obtain ⟨-, n6, -⟩ := lreg_ne k
    rw [k₈.lane (by simpa only [List.mem_singleton] using hne),
      k₇.lane (by simpa only [List.mem_singleton] using n6), k₆.lane (by simpa only [List.mem_singleton] using n6)]
  refine ⟨fun k hk => ?_, fun k hk => ?_, by rw [m₈, m₇, m₆, i₅.mem],
    (((i₅.keep.xe.trans k₆).trans k₇.xe).trans k₈.xe).mono fun r hr => ?_⟩
  · by_cases hk4 : k = 4
    · subst hk4
      rw [show ln s₈ (lreg 4) 0 = ln s₈ .xmm4 0 from rfl, a₈ 0 (by decide), h4, lo4, v0,
        ite_eq_right (Nat.lt_irrefl 4), i₅.mem]
    · rw [ho k hk hk4, i₅.lo k hk, ite_eq_left (by omega_using [hk, hk4]), Nat.add_zero]
  · by_cases hk4 : k = 4
    · subst hk4
      rw [show ln s₈ (lreg 4) 1 = ln s₈ .xmm4 1 from rfl, a₈ 1 (by decide), h4, hi4, v1]
    · rw [ho k hk hk4, i₅.hi k hk]
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ((hr | rfl) | rfl) | rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hr
    · decide
    · decide
    · decide

/-! ### The general registers between the vector steps -/

/-- What instructions on the general registers `rs` (and the flags) keep. -/
structure Gk (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mcdt : s'.mcdt = s.mcdt
  xmm : s'.xmm = s.xmm

theorem Gk.trans {rs rs' : List Reg} {s s' s'' : State} (h : Gk rs s s') (h' : Gk rs' s' s'') :
    Gk (rs ++ rs') s s'' :=
  ⟨fun r hr => by
      simp only [List.mem_append, not_or] at hr
      exact (h'.gpr r hr.2).trans (h.gpr r hr.1),
    h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.mcdt.trans h.mcdt, h'.xmm.trans h.xmm⟩

theorem Gk.sp {rs : List Reg} {s s' : State} {o : Nat} {B : BitVec 32} (h : Gk rs s s') (hr : Reg.esp ∉ rs)
    (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) : s'.gpr .esp + BitVec.ofNat 32 o = B := by
  rw [h.gpr _ hr]; exact hsp

theorem Gk.lane {rs : List Reg} {s s' : State} (h : Gk rs s s') (x : XReg) (l : Nat) :
    Sse2.ln s' x l = Sse2.ln s x l := by
  rw [Sse2.ln, h.xmm]

/-- `mov d, [esp + o + e]` -/
theorem gLoad_ok {o : Nat} {B : BitVec 32} (d : Reg) (e : Nat) (s : State)
    (hsp : s.gpr .esp + BitVec.ofNat 32 o = B) (hin : InRegions (s.rd ++ s.wr) (addr B e) 4) :
    WP isa (.block [.mov d (.mem (fs o e))]) s fun s' =>
      s'.gpr d = s.mem.readW (addr B e) 32 ∧ Gk [d] s s' := by
  have e' := ea_fs hsp e
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load32, e', hin, ↓reduceIte,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨gpr_setReg_self _ _ _, fun r hr => gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr),
    rfl, rfl, rfl, rfl, rfl⟩

/-- `add d, v` -/
theorem gAdd_ok (d : Reg) (v : BitVec 32) (s : State) :
    WP isa (.block [.alu .add d (.imm v)]) s fun s' => s'.gpr d = s.gpr d + v ∧ Gk [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨gpr_setReg_self _ _ _, fun r hr => gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr),
    rfl, rfl, rfl, rfl, rfl⟩

/-- `sub d, v`, and the zero flag. -/
theorem gSub_ok (d : Reg) (v : BitVec 32) (s : State) :
    WP isa (.block [.alu .sub d (.imm v)]) s fun s' =>
      s'.gpr d = s.gpr d - v ∧ s'.zf = some (s.gpr d - v == 0) ∧ Gk [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨gpr_setReg_self _ _ _, rfl,
    fun r hr => gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr), rfl, rfl, rfl, rfl, rfl⟩

/-! ## The lanes' loop

`lanes`, in a state `s` with the frame at `B = esp + 12` (`LPre`). -/

theorem val_congr {a a' : Nat → Nat} (h : ∀ k < 5, a k = a' k) : val a = val a' := by
  simp only [val, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]

theorem val_top (T : Nat) : val (fun k => if k < 4 then 0 else T) = 2 ^ 104 * T := by
  simp only [val, show (0 : Nat) < 4 by decide, show (1 : Nat) < 4 by decide, show (2 : Nat) < 4 by decide,
    show (3 : Nat) < 4 by decide, Nat.lt_irrefl, ite_true, ite_false]
  omega_arith

theorem mv_bytes (m : Mem) (a : Addr) : mv (bytesAt m a 16) = leNum (bytesAt m a 16) + 2 ^ 128 := by
  rw [mv, Poly1305.leNum_append, Poly1305.length_bytesAt]
  rfl

/-- The limbs of a block with its `2¹²⁸` are below `2²⁶`. -/
theorem lim_blk_lt {N : Nat} (hN : N < 2 ^ 128) {k : Nat} (hk : k < 5) : lim (N + 2 ^ 128) k < 2 ^ 26 := by
  rcases (by omega_using [hk] : k < 4 ∨ k = 4) with h | rfl
  · exact lim_lt _ h
  · exact Nat.lt_trans (lim4_lt (B := 2 ^ 25) (by omega_using [hN])) (by decide)

/-- A lane after a pair: multiplied, carried, and a block added. -/
theorem lane_step (a b : Nat → Nat) (N : Nat) :
    val (fun k => cv (ds a b) k + lim (N + 2 ^ 128) k) % P = (val a * val b + (N + 2 ^ 128)) % P := by
  rw [val_add, val_lim]
  exact add_mod_congr ((cv_mod _).trans (ds_mod a b)) rfl

theorem lane_step_lt {a b : Nat → Nat} {N : Nat} (ha : ∀ k < 5, a k < 2 ^ 28) (hb : ∀ k < 5, b k < 2 ^ 26)
    (hN : N < 2 ^ 128) {k : Nat} (hk : k < 5) : cv (ds a b) k + lim (N + 2 ^ 128) k < 2 ^ 28 := by
  have h₁ := cv_lt (d := ds a b) (fun i hi => Nat.lt_trans (ds_lt ha hb hi) (by decide)) hk
  have h₂ := lim_blk_lt hN hk
  omega_using [h₁, h₂]

theorem leNum_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region} {a : Addr} {n : Nat}
    (ha : R.Contains a n) (hd : ∀ r' ∈ rs, R.Disjoint r') (hn : n < 2 ^ 64) :
    leNum (bytesAt m' a n) = leNum (bytesAt m a n) := by
  rw [Poly1305.leNum_bytesAt_read, Poly1305.leNum_bytesAt_read, hf.read ha hd hn]

/-- The frame of `pairs`. -/
abbrev fR (B : BitVec 32) : Region := Proof.Aes.X86.reg32 B 512

/-- What `lanes` starts from: its frame at `B`, the state at `st` and `p`
pairs of blocks at `dp`, both apart from the frame, and the number of pairs
in the frame. -/
structure LPre (B st dp : BitVec 32) (p : Nat) (s : State) : Prop where
  sp : s.gpr .esp + BitVec.ofNat 32 12 = B
  fit : Fit B
  fr : fR B ∈ s.wr
  mcdt : 0 < s.mcdt
  edi : s.gpr .edi = st
  sfit : st.toNat + 128 ≤ 2 ^ 32
  sin : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (addr st d) 8
  sdj : (sR st).Disjoint (fR B)
  esi : s.gpr .esi = dp
  two : 2 ≤ p
  dfit : dp.toNat + 32 * p ≤ 2 ^ 32
  din : ∀ d, d + 8 ≤ 32 * p → InRegions (s.rd ++ s.wr) (addr dp d) 8
  ddj : (Proof.Aes.X86.reg32 dp (32 * p)).Disjoint (fR B)
  cnt : s.mem.readW (addr B cntOff) 32 = BitVec.ofNat 32 p

/-- The number of the block `l` of pair `j`. -/
abbrev pblk (m : Mem) (dp : BitVec 32) (j l : Nat) : Nat :=
  leNum (bytesAt m (dp.setWidth 64 + BitVec.ofNat 64 (32 * j + 16 * l)) 16)

namespace LPre
variable {B st dp : BitVec 32} {p : Nat} {s : State} (hp : LPre B st dp p s)
include hp

/-- A block of the data, in memory that differs from `s`'s in the frame. -/
theorem blk {m : Mem} (hf : Frame [fR B] s.mem m) {j l : Nat} (hj : j < p) (hl : l < 2) :
    pblk m dp j l = pblk s.mem dp j l := by
  have hd := hp.dfit
  refine leNum_frame hf (R := Proof.Aes.X86.reg32 dp (32 * p)) ?_ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hp.ddj) (by decide)
  rw [← addr_eq (by omega_using [hd, hj, hl])]
  exact Proof.Aes.X86.reg_contains hd (by omega_using [hj, hl]) (by decide)

/-- A word of the state, in memory that differs from `s`'s in the frame. -/
theorem sword {m : Mem} (hf : Frame [fR B] s.mem m) {d : Nat} (hd : d + 8 ≤ 128) :
    m.readW (addr st d) 64 = s.mem.readW (addr st d) 64 :=
  hf.readW (r := sR st) (Proof.Poly1305.X86.sR_contains hp.sfit hd (by decide))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.sdj) (by decide)

end LPre

/-- A part of the frame is in the frame. -/
theorem sub_fR {B : BitVec 32} (hB : Fit B) {a n : Nat} (h : a + n ≤ 512) : Region.Sub ⟨addr B a, n⟩ (fR B) :=
  Proof.Aes.X86.part_sub_reg hB h

theorem frame_fR {B : BitVec 32} (hB : Fit B) {a n : Nat} (h : a + n ≤ 512) {m m' : Mem}
    (hf : Frame [⟨addr B a, n⟩] m m') : Frame [fR B] m m' :=
  hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact sub_fR hB h⟩

/-- The blocks of a pair added to the lanes, in a state whose memory differs
from `s`'s in the frame. -/
theorem addPair_ok {B st dp : BitVec 32} {p : Nat} {s : State} (hp : LPre B st dp p s)
    {tb : Nat → Nat → Nat → Nat} {j : Nat} (hj : j < p) (u : State) (hsp : u.gpr .esp = s.gpr .esp)
    (hesi : u.gpr .esi = dp + BitVec.ofNat 32 (32 * j)) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr)
    (hf : Frame [fR B] s.mem u.mem) (ht : Tab u.mem B tb) (hm : ∀ l < 2, ln u .xmm5 l = 2 ^ 26 - 1)
    (hb : ∀ l < 2, ∀ k < 5, ln u (lreg k) l < 2 ^ 62) :
    WP isa (.block (addMsg 12)) u fun u' =>
      (∀ l < 2, ∀ k < 5, ln u' (lreg k) l = ln u (lreg k) l + lim (pblk s.mem dp j l + 2 ^ 128) k) ∧
      u'.mem = u.mem ∧ Xk lregs u u' := by
  have hd := hp.dfit
  have hdj : (dp + BitVec.ofNat 32 (32 * j)).toNat = dp.toNat + 32 * j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 32 * j) (by omega_using [hd, hj]),
      Nat.mod_eq_of_lt (by omega_using [hd, hj])]
  refine WP.mono (addMsg_ok (tb := tb) u (by rw [hsp]; exact hp.sp) hp.fit (by rw [hwr]; exact hp.fr) hesi
    (by rw [hdj]; omega_using [hd, hj]) (fun d hd' => by
      rw [hrd, hwr, Proof.Aes.X86.addr_add]; exact hp.din _ (by omega_using [hd', hj])) ht hm hb)
    fun u' ⟨a, m, k⟩ => ⟨fun l hl k' hk' => ?_, m, k⟩
  rw [a l hl k' hk', ← hp.blk hf hj hl]
  have e : (dp + BitVec.ofNat 32 (32 * j)).setWidth 64 + BitVec.ofNat 64 (16 * l) =
      dp.setWidth 64 + BitVec.ofNat 64 (32 * j + 16 * l) := by
    rw [← addr_eq (by rw [hdj]; omega_using [hd, hj, hl]), Proof.Aes.X86.addr_add,
      addr_eq (by omega_using [hd, hj, hl])]
  show _ + lim (leNum (bytesAt u.mem ((dp + BitVec.ofNat 32 (32 * j)).setWidth 64 + BitVec.ofNat 64 (16 * l)) 16) +
    2 ^ 128) k' = _
  rw [e]

/-- The limbs of `r²` and of `r` as `tables` reads them from the state, and
the accumulator as `initH` reads it from the frame. -/
abbrev rdb (m : Mem) (st : BitVec 32) (k : Nat) : Nat :=
  (m.readW (addr st (qbyte k)) 64).toNat / 2 ^ qshift k % 2 ^ 26
abbrev rdc (m : Mem) (st : BitVec 32) (k : Nat) : Nat :=
  (m.readW (addr st (rOff 0 + lbyte k)) 64).toNat / 2 ^ lshift k % 2 ^ 26
abbrev rdh (m : Mem) (B : BitVec 32) : Nat :=
  leNum (bytesAt m (B.setWidth 64) 16) + 2 ^ 128 * ((m.readW (addr B (svOff 4)) 32).toNat % 8)

theorem pairs_succ (m : Mem) (a : Addr) (j : Nat) :
    bytesAt m a (32 * (j + 1)) = bytesAt m a (32 * j) ++ bytesAt m (a + BitVec.ofNat 64 (32 * j + 16 * 0)) 16 ++
      bytesAt m (a + BitVec.ofNat 64 (32 * j + 16 * 1)) 16 := by
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  rw [show 32 * (j + 1) = 32 * j + (16 + 16) by omega_arith, Poly1305.bytesAt_add, Poly1305.bytesAt_add,
    add_ofNat_add, List.append_assoc]

/-- The lanes at the head of the loop, after `j` pairs. -/
structure LInv (B dp : BitVec 32) (p : Nat) (b c : Nat → Nat) (C : Prop) (R X : Nat) (s : State) (j : Nat)
    (u : State) : Prop where
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → u.gpr r = s.gpr r
  esi : u.gpr .esi = dp + BitVec.ofNat 32 (32 * j)
  ecx : u.gpr .ecx = BitVec.ofNat 32 (p - j)
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mcdt : u.mcdt = s.mcdt
  frame : Frame [fR B] s.mem u.mem
  tab : Tab u.mem B (tbl b c)
  mask : ∀ l < 2, ln u .xmm5 l = 2 ^ 26 - 1
  lt : ∀ l < 2, ∀ k < 5, ln u (lreg k) l < 2 ^ 28
  acc : C → (val (fun k => ln u (lreg k) 0) * val b + val (fun k => ln u (lreg k) 1) * val c) % P =
    absorbAll R X (bytesAt s.mem (dp.setWidth 64) (32 * j)) % P

theorem lanesInit_ok {B st dp : BitVec 32} {p : Nat} {s : State} (hp : LPre B st dp p s) {C : Prop} {R X : Nat}
    (hC : C → val (rdb s.mem st) % P = R * R % P ∧ val (rdc s.mem st) = R ∧ rdh s.mem B % P = X % P) :
    WP isa (.block (consts 12 ++ (tables 12 ++ (initH 12 ++ (addMsg 12 ++ (([.alu .add .esi (.imm 32)] : List Instr) ++
      (([.mov .ecx (.mem (fs 12 cntOff))] : List Instr) ++ [.alu .sub .ecx (.imm 1)]))))))) s
      (LInv B dp p (rdb s.mem st) (rdc s.mem st) C R X s 1) := by
  have hB := hp.fit
  have hlow : ∀ {m : Mem}, Frame [tR B] s.mem m →
      leNum (bytesAt m (B.setWidth 64) 16) = leNum (bytesAt s.mem (B.setWidth 64) 16) ∧
      (∀ d, d + 4 ≤ 64 → m.readW (addr B d) 32 = s.mem.readW (addr B d) 32) := fun {m} hf => by
    have hdj : ∀ r ∈ [tR B], Region.Disjoint ⟨addr B 0, 64⟩ r := fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Proof.Aes.X86.part_disj hB (by decide) (by decide) (.inl (by decide))
    refine ⟨leNum_frame hf (R := ⟨addr B 0, 64⟩) ?_ hdj (by decide), fun d hd => ?_⟩
    · rw [← Proof.Aes.X86.addr_zero B]
      exact Proof.Aes.X86.part_contains hB (by decide) (Nat.le_refl 0) (by decide) (by decide)
    · exact hf.readW (r := ⟨addr B 0, 64⟩)
        (Proof.Aes.X86.part_contains hB (by decide) (Nat.zero_le d) (by omega_using [hd]) (by decide)) hdj (by decide)
  refine WP.block_append (WP.mono (consts_ok s hp.sp hB hp.fr) fun s₁ ⟨m5, mk, hb, f₁, k₁⟩ => ?_)
  have hsp₁ := k₁.sp hp.sp
  have hedi₁ : s₁.gpr .edi = st := by rw [k₁.gpr _ (by decide)]; exact hp.edi
  refine WP.block_append (WP.mono (tables_ok (rdb s.mem st) (rdc s.mem st) s₁ hsp₁ hB (by rw [k₁.wr]; exact hp.fr)
    hedi₁ hp.sfit (by rw [k₁.rd, k₁.wr]; exact hp.sin)
    (hp.sdj.sub_right (sub_fR hB (by decide))) m5 mk hb
    (fun k _ => by rw [hp.sword (frame_fR hB (by decide) f₁) (by have := (qshift_le k).2; omega_using [this])])
    (fun k _ => by
      rw [hp.sword (frame_fR hB (by decide) f₁) (by have := lbyte_le k; simp only [rOff]; omega_using [this])]))
    fun s₂ ⟨T₂, f₂, k₂⟩ => ?_)
  have hsp₂ : s₂.gpr .esp + BitVec.ofNat 32 12 = B := by rw [k₂.gpr]; exact hsp₁
  have f₁₂ := f₁.trans f₂
  refine WP.block_append (WP.mono (initH_ok s₂ hsp₂ hB (by rw [k₂.wr, k₁.wr]; exact hp.fr)
    (fun l hl => by rw [k₂.lane (by decide)]; exact m5 l hl)) fun s₃ ⟨lo₃, hi₃, m₃, k₃⟩ => ?_)
  obtain ⟨eX, eW⟩ := hlow f₁₂
  rw [eX, eW _ (show svOff 4 + 4 ≤ 64 by decide)] at lo₃
  have hT : (s.mem.readW (addr B (svOff 4)) 32).toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  have hX := leNum_bytes_lt s.mem (B.setWidth 64) 16
  have hlim : ∀ k < 5, lim (leNum (bytesAt s.mem (B.setWidth 64) 16)) k < 2 ^ 26 := fun k hk => by
    rcases (by omega_using [hk] : k < 4 ∨ k = 4) with h | rfl
    · exact lim_lt _ h
    · exact Nat.lt_trans (lim4_lt (B := 2 ^ 24) (by omega_using [hX])) (by decide)
  have hlo : ∀ k < 5, ln s₃ (lreg k) 0 < 2 ^ 26 + 7 * 2 ^ 24 := fun k hk => by
    rw [lo₃ k hk]
    have := hlim k hk
    by_cases h4 : k < 4
    · rw [ite_eq_left h4]; omega_using [this]
    · rw [ite_eq_right h4]; omega_using [this, hT]
  have hm₃ : ∀ l < 2, ln s₃ .xmm5 l = 2 ^ 26 - 1 := fun l hl => by
    rw [k₃.lane (by decide), k₂.lane (by decide)]; exact m5 l hl
  have hmem₃ : s₃.mem = s₂.mem := m₃
  refine WP.block_append (WP.mono (addPair_ok hp (tb := tbl (rdb s.mem st) (rdc s.mem st)) (j := 0)
    (by have := hp.two; omega_using [this]) s₃
    (by rw [k₃.gpr _ (by decide), k₂.gpr, k₁.gpr _ (by decide)])
    (by rw [k₃.gpr _ (by decide), k₂.gpr, k₁.gpr _ (by decide), hp.esi, Nat.mul_zero, BitVec.add_zero])
    (by rw [k₃.rd, k₂.rd, k₁.rd]) (by rw [k₃.wr, k₂.wr, k₁.wr])
    (by rw [hmem₃]; exact frame_fR hB (by decide) f₁₂) (by rw [hmem₃]; exact T₂) hm₃
    (fun l hl k hk => by
      rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
      · exact Nat.lt_trans (hlo k hk) (by decide)
      · rw [hi₃ k hk]; decide)) fun s₄ ⟨a₄, m₄, k₄⟩ => ?_)
  refine WP.block_append (WP.mono (gAdd_ok .esi 32 s₄) fun s₅ ⟨e₅, g₅⟩ => ?_)
  have hmem₅ : s₅.mem = s₂.mem := by rw [g₅.mem, m₄, hmem₃]
  have hsp₄ : s₄.gpr .esp + BitVec.ofNat 32 12 = B := by rw [k₄.gpr, k₃.gpr _ (by decide)]; exact hsp₂
  have hsp₅ : s₅.gpr .esp + BitVec.ofNat 32 12 = B := g₅.sp (by decide) hsp₄
  have hin₅ : InRegions (s₅.rd ++ s₅.wr) (addr B cntOff) 4 := by
    rw [g₅.rd, g₅.wr, k₄.rd, k₄.wr, k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr]
    exact Proof.Aes.X86.in_rd (fr_in hB hp.fr (show cntOff + 4 ≤ 512 by decide) (by decide))
  refine WP.block_append (WP.mono (gLoad_ok .ecx cntOff s₅ hsp₅ hin₅) fun s₆ ⟨e₆, g₆⟩ => ?_)
  refine WP.mono (gSub_ok .ecx 1 s₆) fun s₇ ⟨e₇, _, g₇⟩ => ?_
  have hmem₇ : s₇.mem = s₂.mem := by rw [g₇.mem, g₆.mem, hmem₅]
  have hln : ∀ x l, ln s₇ x l = ln s₄ x l := fun x l => by rw [g₇.lane, g₆.lane, g₅.lane]
  have hN : ∀ l, pblk s.mem dp 0 l < 2 ^ 128 := fun l => leNum_bytes_lt _ _ 16
  refine ⟨fun r h₁ h₂ h₃ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun l hl => ?_, fun l hl k hk => ?_, fun hc => ?_⟩
  · rw [g₇.gpr _ (by simpa only [List.mem_singleton] using h₂), g₆.gpr _ (by simpa only [List.mem_singleton] using h₂),
      g₅.gpr _ (by simpa only [List.mem_singleton] using h₃), k₄.gpr, k₃.gpr _ h₁, k₂.gpr, k₁.gpr _ h₁]
  · rw [g₇.gpr _ (by decide), g₆.gpr _ (by decide), e₅, k₄.gpr, k₃.gpr _ (by decide), k₂.gpr, k₁.gpr _ (by decide),
      hp.esi]
    rfl
  · rw [e₇, e₆, g₅.mem, m₄, hmem₃, (hlow f₁₂).2 _ (show cntOff + 4 ≤ 64 by decide), hp.cnt]
    exact VG.X86.Wp.ofNat_pred (by have := hp.two; omega_using [this])
  · rw [g₇.rd, g₆.rd, g₅.rd, k₄.rd, k₃.rd, k₂.rd, k₁.rd]
  · rw [g₇.wr, g₆.wr, g₅.wr, k₄.wr, k₃.wr, k₂.wr, k₁.wr]
  · rw [g₇.mcdt, g₆.mcdt, g₅.mcdt, k₄.mcdt, k₃.mcdt, k₂.mcdt, k₁.mcdt]
  · rw [hmem₇]; exact frame_fR hB (by decide) f₁₂
  · rw [hmem₇]; exact T₂
  · rw [hln, k₄.lane (by decide)]; exact hm₃ l hl
  · rw [hln, a₄ l hl k hk]
    have h₂ := lim_blk_lt (hN l) hk
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
    · have := hlo k hk; omega_using [this, h₂]
    · rw [hi₃ k hk]; omega_using [h₂]
  · obtain ⟨hr2, hr, hh⟩ := hC hc
    have eA : val (fun k => ln s₇ (lreg k) 0) = rdh s.mem B + mv (bytesAt s.mem (dp.setWidth 64 +
        BitVec.ofNat 64 (32 * 0 + 16 * 0)) 16) := by
      rw [val_congr (a' := fun k => (lim (leNum (bytesAt s.mem (B.setWidth 64) 16)) k +
          (if k < 4 then 0 else (s.mem.readW (addr B (svOff 4)) 32).toNat % 8 * 2 ^ 24)) +
          lim (pblk s.mem dp 0 0 + 2 ^ 128) k) fun k hk => by rw [hln, a₄ 0 (by decide) k hk, lo₃ k hk],
        val_add, val_add, val_lim, val_lim, val_top, mv_bytes]
      simp only [rdh, pblk]
      generalize (s.mem.readW (addr B (svOff 4)) 32).toNat % 8 = T
      omega_arith
    have eB : val (fun k => ln s₇ (lreg k) 1) = mv (bytesAt s.mem (dp.setWidth 64 +
        BitVec.ofNat 64 (32 * 0 + 16 * 1)) 16) := by
      rw [val_congr (a' := fun k => lim (pblk s.mem dp 0 1 + 2 ^ 128) k) fun k hk => by
          rw [hln, a₄ 1 (by decide) k hk, hi₃ k hk, Nat.zero_add], val_lim, mv_bytes]
    rw [eA, eB, hr, pairs_succ, show bytesAt s.mem (dp.setWidth 64) (32 * 0) = [] from rfl, List.nil_append]
    exact pair_init (Poly1305.length_bytesAt _ _ _) (Poly1305.length_bytesAt _ _ _) hr2 hh

theorem tbl_zero (b c : Nat → Nat) (l : Nat) : tbl b c 0 l = b := by
  unfold tbl; exact ite_eq_right fun h => absurd h.1 (by decide)

theorem tbl_one0 (b c : Nat → Nat) : tbl b c 1 0 = b := by
  unfold tbl; exact ite_eq_right fun h => absurd h.2 (by decide)

theorem tbl_one1 (b c : Nat → Nat) : tbl b c 1 1 = c := by
  unfold tbl; exact ite_eq_left ⟨rfl, rfl⟩

theorem cv_congr {d d' : Nat → Nat} (h : ∀ k < 5, d k = d' k) (k : Nat) : cv d k = cv d' k := by
  rcases k with _ | _ | _ | _ | k <;>
    simp only [cv, z0, z3, x2, x4, x1, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
      h 4 (by decide)]

/-- A turn of the loop: the lanes times `r²`, carried, plus a pair of blocks. -/
theorem lanesBody_ok {B st dp : BitVec 32} {p : Nat} {s : State} (hp : LPre B st dp p s) {b c : Nat → Nat}
    (hb : ∀ k < 5, b k < 2 ^ 26) {C : Prop} {R X : Nat} (hC : C → val b % P = R * R % P ∧ val c = R)
    {j : Nat} (hj : j < p) {u : State} (h : LInv B dp p b c C R X s j u) :
    WP isa (.block (mulV 12 0 ++ (carryV ++ (addMsg 12 ++ (([.alu .add .esi (.imm 32)] : List Instr) ++
      [.alu .sub .ecx (.imm 1)]))))) u fun u' =>
      LInv B dp p b c C R X s (j + 1) u' ∧ u'.zf = some (BitVec.ofNat 32 (p - j) - 1 == 0) := by
  have hB := hp.fit
  have hsp : u.gpr .esp + BitVec.ofNat 32 12 = B := by
    rw [h.gpr _ (by decide) (by decide) (by decide)]; exact hp.sp
  have hfr : fR B ∈ u.wr := by rw [h.wr]; exact hp.fr
  refine WP.block_append (WP.mono (mulV_ok 0 (by decide) u hsp hB hfr (by rw [h.mcdt]; exact hp.mcdt) h.tab h.lt
    (fun l _ i hi => by rw [tbl_zero]; exact Nat.lt_trans (hb i hi) (by decide)))
    fun u₁ ⟨a₁, m5₁, T₁, f₁, k₁⟩ => ?_)
  have a₁' : ∀ l < 2, ∀ k < 5, ln u₁ (lreg k) l = ds (fun i => ln u (lreg i) l) b k := fun l hl k hk => by
    rw [a₁ l hl k hk, tbl_zero]
  have hds : ∀ l < 2, ∀ k < 5, ds (fun i => ln u (lreg i) l) b k < 2 ^ 62 := fun l hl k hk =>
    Nat.lt_trans (ds_lt (h.lt l hl) hb hk) (by decide)
  refine WP.block_append (WP.mono (carryV_ok u₁ m5₁ fun l hl k hk => by rw [a₁' l hl k hk]; exact hds l hl k hk)
    fun u₂ ⟨a₂, m₂, k₂⟩ => ?_)
  have a₂' : ∀ l < 2, ∀ k < 5, ln u₂ (lreg k) l = cv (ds (fun i => ln u (lreg i) l) b) k := fun l hl k hk => by
    rw [a₂ l hl k hk]; exact cv_congr (fun i hi => a₁' l hl i hi) k
  have hcv : ∀ l < 2, ∀ k < 5, cv (ds (fun i => ln u (lreg i) l) b) k < 2 ^ 26 + 2 ^ 14 := fun l hl k hk =>
    cv_lt (d := ds (fun i => ln u (lreg i) l) b) (hds l hl) hk
  have hm₂ : ∀ l < 2, ln u₂ .xmm5 l = 2 ^ 26 - 1 := fun l hl => by rw [k₂.lane (by decide)]; exact m5₁ l hl
  have hf₂ : Frame [fR B] s.mem u₂.mem := by
    rw [m₂]; exact h.frame.trans (frame_fR hB (by decide) f₁)
  refine WP.block_append (WP.mono (addPair_ok hp hj u₂
    (by rw [k₂.gpr, k₁.gpr]; exact h.gpr _ (by decide) (by decide) (by decide))
    (by rw [k₂.gpr, k₁.gpr]; exact h.esi) (by rw [k₂.rd, k₁.rd, h.rd]) (by rw [k₂.wr, k₁.wr, h.wr]) hf₂
    (by rw [m₂]; exact T₁) hm₂
    (fun l hl k hk => by rw [a₂' l hl k hk]; exact Nat.lt_trans (hcv l hl k hk) (by decide)))
    fun u₃ ⟨a₃, m₃, k₃⟩ => ?_)
  refine WP.block_append (WP.mono (gAdd_ok .esi 32 u₃) fun u₄ ⟨e₄, g₄⟩ => ?_)
  refine WP.mono (gSub_ok .ecx 1 u₄) fun u₅ ⟨e₅, z₅, g₅⟩ => ?_
  have hmem : u₅.mem = u₁.mem := by rw [g₅.mem, g₄.mem, m₃, m₂]
  have hln : ∀ l < 2, ∀ k < 5, ln u₅ (lreg k) l =
      cv (ds (fun i => ln u (lreg i) l) b) k + lim (pblk s.mem dp j l + 2 ^ 128) k := fun l hl k hk => by
    rw [g₅.lane, g₄.lane, a₃ l hl k hk, a₂' l hl k hk]
  have hN : ∀ l, pblk s.mem dp j l < 2 ^ 128 := fun l => leNum_bytes_lt _ _ 16
  refine ⟨⟨fun r h₁ h₂ h₃ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun l hl => ?_, fun l hl k hk => ?_, fun hc => ?_⟩, ?_⟩
  · rw [g₅.gpr _ (by simpa only [List.mem_singleton] using h₂), g₄.gpr _ (by simpa only [List.mem_singleton] using h₃),
      k₃.gpr, k₂.gpr, k₁.gpr]
    exact h.gpr r h₁ h₂ h₃
  · rw [g₅.gpr _ (by decide), e₄, k₃.gpr, k₂.gpr, k₁.gpr, h.esi]
    show dp + BitVec.ofNat 32 (32 * j) + BitVec.ofNat 32 32 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    rfl
  · rw [e₅, g₄.gpr _ (by decide), k₃.gpr, k₂.gpr, k₁.gpr, h.ecx]
    exact VG.X86.Wp.ofNat_pred (by omega_using [hj])
  · rw [g₅.rd, g₄.rd, k₃.rd, k₂.rd, k₁.rd, h.rd]
  · rw [g₅.wr, g₄.wr, k₃.wr, k₂.wr, k₁.wr, h.wr]
  · rw [g₅.mcdt, g₄.mcdt, k₃.mcdt, k₂.mcdt, k₁.mcdt, h.mcdt]
  · rw [hmem]; exact h.frame.trans (frame_fR hB (by decide) f₁)
  · rw [hmem]; exact T₁
  · rw [g₅.lane, g₄.lane, k₃.lane (by decide)]; exact hm₂ l hl
  · rw [hln l hl k hk]; exact lane_step_lt (h.lt l hl) hb (hN l) hk
  · obtain ⟨hr2, hr⟩ := hC hc
    subst hr
    rw [pairs_succ, val_congr (hln 0 (by decide)), val_congr (hln 1 (by decide))]
    refine pair_step (by rw [Poly1305.length_bytesAt]; omega_arith) (Poly1305.length_bytesAt _ _ _)
      (Poly1305.length_bytesAt _ _ _) hr2 (h.acc hc) ?_ ?_
    · rw [lane_step, mv_bytes]
    · rw [lane_step, mv_bytes]
  · rw [z₅, g₄.gpr _ (by decide), k₃.gpr, k₂.gpr, k₁.gpr, h.ecx]

/-- After the loop: the lanes times `(r², r)`, summed and carried, and the
limbs stored. -/
theorem lanesEnd_ok {B st dp : BitVec 32} {p : Nat} {s : State} (hp : LPre B st dp p s) {b c : Nat → Nat}
    (hb : ∀ k < 5, b k < 2 ^ 26) (hcl : ∀ k < 5, c k < 2 ^ 26) {C : Prop} {R X : Nat}
    {u : State} (h : LInv B dp p b c C R X s p u) :
    WP isa (.block (mulV 12 1 ++ (sumLanes ++ (carryV ++ storeOut 12)))) u fun u' =>
      u'.gpr = u.gpr ∧ u'.rd = s.rd ∧ u'.wr = s.wr ∧ u'.mcdt = s.mcdt ∧ Frame [fR B] s.mem u'.mem ∧
      ∃ f : Nat → Nat, (∀ k < 5, f k < 2 ^ 26 + 2 ^ 14) ∧
        (∀ k < 5, (u'.mem.readW (addr B (outOff k)) 32).toNat = f k) ∧
        (C → val f % P = absorbAll R X (bytesAt s.mem (dp.setWidth 64) (32 * p)) % P) := by
  have hB := hp.fit
  have hsp : u.gpr .esp + BitVec.ofNat 32 12 = B := by
    rw [h.gpr _ (by decide) (by decide) (by decide)]; exact hp.sp
  have hfr : fR B ∈ u.wr := by rw [h.wr]; exact hp.fr
  have htb : ∀ l < 2, ∀ i < 5, tbl b c 1 l i < 2 ^ 26 := fun l hl i hi => by
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
    · rw [tbl_one0]; exact hb i hi
    · rw [tbl_one1]; exact hcl i hi
  refine WP.block_append (WP.mono (mulV_ok 1 (by decide) u hsp hB hfr (by rw [h.mcdt]; exact hp.mcdt) h.tab h.lt
    (fun l hl i hi => Nat.lt_trans (htb l hl i hi) (by decide))) fun u₁ ⟨a₁, m5₁, _, f₁, k₁⟩ => ?_)
  have hds : ∀ l < 2, ∀ k < 5, ds (fun i => ln u (lreg i) l) (tbl b c 1 l) k < 2 ^ 59 := fun l hl k hk =>
    Nat.lt_trans (ds_lt (h.lt l hl) (htb l hl) hk) (by decide)
  refine WP.block_append (WP.mono (sumLanes_ok u₁ (fun l => ds (fun i => ln u (lreg i) l) (tbl b c 1 l))
    (fun l hl k hk => a₁ l hl k hk)
    (fun k hk => by have h₀ := hds 0 (by decide) k hk; have h₁ := hds 1 (by decide) k hk; omega_using [h₀, h₁]))
    fun u₂ ⟨a₂, b₂, m₂, k₂⟩ => ?_)
  have hsum : ∀ k < 5, ds (fun i => ln u (lreg i) 0) (tbl b c 1 0) k + ds (fun i => ln u (lreg i) 1) (tbl b c 1 1) k <
      2 ^ 62 := fun k hk => by
    have h₀ := hds 0 (by decide) k hk; have h₁ := hds 1 (by decide) k hk; omega_using [h₀, h₁]
  refine WP.block_append (WP.mono (carryV_ok u₂ (fun l hl => by rw [k₂.lane (by decide)]; exact m5₁ l hl)
    fun l hl k hk => by
      rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
      · rw [a₂ k hk]; exact hsum k hk
      · rw [b₂ k hk]; exact Nat.lt_trans (hds 1 (by decide) k hk) (by decide))
    fun u₃ ⟨a₃, m₃, k₃⟩ => ?_)
  have hsp₃ : u₃.gpr .esp + BitVec.ofNat 32 12 = B := by rw [k₃.gpr, k₂.gpr, k₁.gpr]; exact hsp
  have hfr₃ : fR B ∈ u₃.wr := by rw [k₃.wr, k₂.wr, k₁.wr]; exact hfr
  refine WP.mono (storeOut_ok u₃ hsp₃ hB hfr₃) fun u₄ ⟨o₄, f₄, k₄⟩ => ?_
  have hlt : ∀ k < 5, cv (fun i => ds (fun i => ln u (lreg i) 0) (tbl b c 1 0) i +
      ds (fun i => ln u (lreg i) 1) (tbl b c 1 1) i) k < 2 ^ 26 + 2 ^ 14 := fun k hk =>
    cv_lt (d := fun i => ds (fun i => ln u (lreg i) 0) (tbl b c 1 0) i +
      ds (fun i => ln u (lreg i) 1) (tbl b c 1 1) i) hsum hk
  refine ⟨by rw [k₄.gpr, k₃.gpr, k₂.gpr, k₁.gpr], by rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd, h.rd],
    by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr, h.wr], by rw [k₄.mcdt, k₃.mcdt, k₂.mcdt, k₁.mcdt, h.mcdt],
    (h.frame.trans (frame_fR hB (by decide) f₁)).trans (by rw [← m₂, ← m₃]; exact frame_fR hB (by decide) f₄),
    _, hlt, fun k hk => ?_, fun hc => ?_⟩
  · rw [o₄ k hk, a₃ 0 (by decide) k hk, cv_congr (fun i hi => a₂ i hi) k]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (hlt k hk) (by decide))
  · rw [cv_mod, val_add, tbl_one0, tbl_one1]
    exact (add_mod_congr (ds_mod _ _) (ds_mod _ _)).trans (h.acc hc)

theorem lanes_eq : Impl.Poly1305.X86.lanes = .seq (.block (consts 12 ++ (tables 12 ++ (initH 12 ++ (addMsg 12 ++
      (([.alu .add .esi (.imm 32)] : List Instr) ++ (([.mov .ecx (.mem (fs 12 cntOff))] : List Instr) ++
        [.alu .sub .ecx (.imm 1)])))))))
    (.seq (.loop (.block (mulV 12 0 ++ (carryV ++ (addMsg 12 ++ (([.alu .add .esi (.imm 32)] : List Instr) ++
      [.alu .sub .ecx (.imm 1)]))))) .ne)
      (.block (mulV 12 1 ++ (sumLanes ++ (carryV ++ storeOut 12))))) := by
  simp only [Impl.Poly1305.X86.lanes, List.append_assoc, List.cons_append, List.nil_append]

/-- `lanes`: the limbs it leaves in the frame are, modulo `p`, the
accumulator after the `2 p` blocks, where `C` says what the state and the
frame hold. Only `eax`, `ecx` and `esi`, the `xmm` registers and the frame
change. -/
theorem lanes_ok {B st dp : BitVec 32} {p : Nat} {s : State} (hp : LPre B st dp p s) {C : Prop} {R X : Nat}
    (hC : C → val (rdb s.mem st) % P = R * R % P ∧ val (rdc s.mem st) = R ∧ rdh s.mem B % P = X % P) :
    WP isa Impl.Poly1305.X86.lanes s fun s' =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mcdt = s.mcdt ∧ Frame [fR B] s.mem s'.mem ∧
      ∃ f : Nat → Nat, (∀ k < 5, f k < 2 ^ 26 + 2 ^ 14) ∧
        (∀ k < 5, (s'.mem.readW (addr B (outOff k)) 32).toNat = f k) ∧
        (C → val f % P = absorbAll R X (bytesAt s.mem (dp.setWidth 64) (32 * p)) % P) := by
  have hb : ∀ k < 5, rdb s.mem st k < 2 ^ 26 := fun _ _ => Nat.mod_lt _ (by decide)
  have hcl : ∀ k < 5, rdc s.mem st k < 2 ^ 26 := fun _ _ => Nat.mod_lt _ (by decide)
  have hpl : p ≤ 2 ^ 27 := by have := hp.dfit; omega_using [this]
  rw [lanes_eq]
  refine WP.seq (WP.mono (lanesInit_ok hp hC) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := LInv B dp p (rdb s.mem st) (rdc s.mem st) C R X s p) ?_ fun s₂ h₂ =>
    WP.mono (lanesEnd_ok hp hb hcl h₂) fun s₃ ⟨g, rd, wr, mc, fr, f, hf, ho, hv⟩ =>
      ⟨fun r h₁ h₂' h₃ => by rw [g]; exact h₂.gpr r h₁ h₂' h₃, rd, wr, mc, fr, f, hf, ho, hv⟩)
  let Inv : Nat → State → Prop := fun m u =>
    ∃ j, m = p - j ∧ j < p ∧ LInv B dp p (rdb s.mem st) (rdc s.mem st) C R X s j u
  refine WP.loop (M := isa) Inv (fun m u ⟨j, hm, hj, hL⟩ => ?_) (p - 1) s₁
    ⟨1, rfl, by have := hp.two; omega_using [this], h₁⟩
  refine WP.mono (lanesBody_ok hp hb (fun hc => ⟨(hC hc).1, (hC hc).2.1⟩) hj hL) fun u' ⟨hL', hz⟩ => ?_
  have he : eval .ne u' = some (!decide (p - j - 1 = 0)) := by
    show u'.zf.map (!·) = _
    rw [hz, VG.X86.Wp.ofNat_pred (by omega_using [hj]), VG.X86.Wp.ofNat_beq_zero (by omega_using [hpl])]
    rfl
  by_cases hlast : j + 1 = p
  · refine .inl ⟨he.trans (by rw [decide_eq_true (by omega_using [hlast])]; rfl), hlast ▸ hL'⟩
  · exact .inr ⟨he.trans (by rw [decide_eq_false (by omega_using [hlast, hj])]; rfl), p - (j + 1),
      by omega_using [hm, hj], j + 1, rfl, by omega_using [hlast, hj], hL'⟩

end VG.Proof.Poly1305.X86.Sse2
