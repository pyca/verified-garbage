module

public import VerifiedGarbage.Proof.Poly1305.X86.Blocks
public import VerifiedGarbage.Proof.Poly1305.Limbs26
public import VerifiedGarbage.Proof.Poly1305.Horner
import VerifiedGarbage.Proof.Mont.X86.Sse2.Lanes
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
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

theorem lshift_le (k : Nat) : (BitVec.ofNat 8 (lshift k)).toNat = lshift k ∧ lshift k ≤ 63 := by
  rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | rfl | rfl | h
  · decide
  · decide
  · decide
  · decide
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega_using [h]⟩
    exact ⟨rfl, by show (40 : Nat) ≤ 63; decide⟩

theorem setXmm_xk (s : State) (x : XReg) (v : BitVec 128) : Xk [x] s (s.setXmm x v) :=
  ⟨rfl, rfl, rfl, rfl, fun r hr => xmm_setXmm_of_ne _ _ (by simpa only [List.mem_singleton] using hr)⟩

theorem and_mask (x : Nat) : x &&& (2 ^ 26 - 1) = x % 2 ^ 26 := Nat.and_two_pow_sub_one_eq_mod x 26

/-- `limb`: the limbs `k` of one or two blocks into the lanes of `xmm6`. -/
theorem limb_ok (b : Reg) (off k : Nat) (two : Bool) (s : State)
    (hm : ∀ l < 2, ln s .xmm5 l = 2 ^ 26 - 1)
    (h0 : InRegions (s.rd ++ s.wr) (addr (s.gpr b) (off + lbyte k)) 8)
    (h1 : two = true → InRegions (s.rd ++ s.wr) (addr (s.gpr b) (off + 16 + lbyte k)) 8) :
    WP isa (.block (limb b off k two)) s fun s' =>
      ln s' .xmm6 0 = limbv (s.mem.readW (addr (s.gpr b) (off + lbyte k)) 64).toNat k ∧
      ln s' .xmm6 1 = (if two = true then limbv (s.mem.readW (addr (s.gpr b) (off + 16 + lbyte k)) 64).toNat k
        else 0) ∧ s'.mem = s.mem ∧ Xk [.xmm6, .xmm7] s s' := by
  have e0 : s.ea (at_ b (off + lbyte k)) = addr (s.gpr b) (off + lbyte k) := rfl
  have m0 := hm 0 (by decide)
  have m1 := hm 1 (by decide)
  obtain ⟨hs, hs'⟩ := lshift_le k
  have hsh : (BitVec.ofNat 8 (lshift k)).toNat ≤ 63 := by rw [hs]; exact hs'
  cases two
  · apply WP.of_runBlock
    simp only [limb, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.nil_append, List.cons_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load64, e0, h0, Option.map_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, ?_, rfl, ?_⟩
    · simp only [ln, xmm_setXmm_self, xmm_setXmm, reduceCtorEq, ↓reduceIte, lane_pand, lane_psrlq _ _ hsh
        (show 0 < 2 by decide), (lane_movq _).1, limbv, hs, and_mask, show lane (s.xmm .xmm5) 0 = 2 ^ 26 - 1 from m0]
    · simp only [ln, xmm_setXmm_self, xmm_setXmm, reduceCtorEq, ↓reduceIte, lane_pand, lane_psrlq _ _ hsh
        (show 1 < 2 by decide), (lane_movq _).2, Nat.zero_and, Nat.zero_div]
    · refine ⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [xmm_setXmm, hr.1, hr.2, ↓reduceIte]
  · have h1' := h1 rfl
    have e1 : ∀ v, (s.setXmm .xmm6 v).ea (at_ b (off + 16 + lbyte k)) = addr (s.gpr b) (off + 16 + lbyte k) :=
      fun _ => rfl
    apply WP.of_runBlock
    simp only [limb, ↓reduceIte, List.append_nil, List.nil_append, List.cons_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load64, e0, h0, Option.map_some,
      Option.some.injEq, exists_eq_left', e1, rd_setXmm, wr_setXmm, mem_setXmm, h1']
    refine ⟨?_, ?_, trivial, ?_⟩
    · simp only [ln, xmm_setXmm_self, xmm_setXmm, reduceCtorEq, ↓reduceIte, lane_pand, lane_psrlq _ _ hsh
        (show 0 < 2 by decide), (lane_punpcklqdq _ _).1, (lane_movq _).1, limbv, hs, and_mask,
        show lane (s.xmm .xmm5) 0 = 2 ^ 26 - 1 from m0]
    · simp only [ln, xmm_setXmm_self, xmm_setXmm, reduceCtorEq, ↓reduceIte, lane_pand, lane_psrlq _ _ hsh
        (show 1 < 2 by decide), (lane_punpcklqdq _ _).2, (lane_movq _).1, limbv, hs, and_mask,
        show lane (s.xmm .xmm5) 1 = 2 ^ 26 - 1 from m1]
    · refine ⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [xmm_setXmm, hr.1, hr.2, ↓reduceIte]

end VG.Proof.Poly1305.X86.Sse2
