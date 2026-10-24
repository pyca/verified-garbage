module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Arith
public import VerifiedGarbage.Proof.MlDsa.Arith.Zq
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA on PPC64LE: the arithmetic modulo `q`

The values the pieces of `Impl/MlDsa/PPC64LE/Arith.lean` compute:

* `loadImm r v` leaves `v < 2³¹` in `r` (`loadImm_val`), and `consts` leaves
  `⌊2⁶⁴ / q⌋` in `r8` and `q` in `r9` (`consts_r8`);
* `fixup` leaves `fixd u`: `u + q` if `u` is negative, `u` otherwise, which
  reduces a sum or a difference of reduced values (`fixd_add`, `fixd_sub`);
* `reduce` leaves `red x = x mod q` for every 64-bit `x` (`red_toNat`),
  through the Barrett reduction `VG.Proof.MlDsa.Arith.barrett`;
* `table T b` stores the 256 entries of `T`, each less than `2²³`
  (`table_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Arith

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Arith
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

/-! ## Constants -/

/-- `⌊2⁶⁴ / q⌋`. -/
def M : BitVec 64 := 2201172575745

/-- `lis` and `ori` of `v < 2³¹`: its high half, shifted up, and its low half. -/
theorem loadImm_val {v : Nat} (hv : v < 2 ^ 31) :
    (BitVec.ofNat 16 (v / 65536) ++ (0 : BitVec 16)).signExtend 64 ||| (BitVec.ofNat 16 (v % 65536)).setWidth 64 =
      BitVec.ofNat 64 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h31 : v.testBit 31 = false := Nat.testBit_lt_two_pow (by omega)
  have hd : ∀ j, (v / 65536).testBit j = v.testBit (j + 16) := fun j => by
    rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.testBit_div_two_pow]
  have hm : ∀ j, (v % 65536).testBit j = (decide (j < 16) && v.testBit j) := fun j => by
    rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.testBit_mod_two_pow]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_ofNat, BitVec.msb_append, hd, hm]
  by_cases h16 : i < 16
  · simp [h16, show i < 32 by omega, hi]
  by_cases h32 : i < 32
  · simp [h16, h32, hi, show i - 16 < 16 by omega, show i - 16 + 16 = i by omega]
  · have : v.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega)))
    have h15 : (BitVec.ofNat 16 (v / 65536))[15] = false := by
      rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, hd]; simp [h31]
    simp [h16, h32, hi, this, BitVec.msb_eq_getLsbD_last, h15]

/-- The four instructions of `consts` that build `⌊2⁶⁴ / q⌋`. -/
theorem consts_r8 :
    (((0x200 : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 ||| (0x801C : BitVec 16).setWidth 64) <<< 16 |||
      (0x0601 : BitVec 16).setWidth 64 = M := by
  decide

theorem M_toNat : M.toNat = barrettM := rfl

/-! ## Reduction modulo `q` -/

/-- What `fixup` leaves: `u + q` if `u` is negative, `u` otherwise. -/
def fixd (u : BitVec 64) : BitVec 64 := u + (u >>> 63) * 8380417

theorem fixd_toNat {u : BitVec 64} (h : u.toNat < 8380417 ∨ 2 ^ 64 - 8380417 ≤ u.toNat) :
    (fixd u).toNat = if u.toNat < 8380417 then u.toNat else u.toNat + 8380417 - 2 ^ 64 := by
  unfold fixd
  have hs : u >>> 63 = 0 ∨ u >>> 63 = 1 := by bv_omega
  rcases hs with hs | hs <;> rw [hs] <;> split <;> bv_omega

/-- `fixd (a + b - q)`: the sum of reduced values, reduced. -/
theorem fixd_add {a b : BitVec 64} (ha : a.toNat < q) (hb : b.toNat < q) :
    (fixd (a + b - 8380417)).toNat = (a.toNat + b.toNat) % q := by
  rw [q_eq] at *
  rw [fixd_toNat (by bv_omega)]
  split <;> bv_omega

/-- `fixd (a - b)`: the difference of reduced values, reduced. -/
theorem fixd_sub {a b : BitVec 64} (ha : a.toNat < q) (hb : b.toNat < q) :
    (fixd (a - b)).toNat = (a.toNat + q - b.toNat) % q := by
  rw [q_eq] at *
  rw [fixd_toNat (by bv_omega)]
  split <;> bv_omega

/-- `fixd (x - q)` of `x < 2q`: `x` reduced. -/
theorem fixd_subq {x : BitVec 64} (hx : x.toNat < 2 * q) : (fixd (x - 8380417)).toNat = x.toNat % q := by
  rw [q_eq] at *
  rw [fixd_toNat (by bv_omega)]
  split <;> bv_omega

/-- What the Barrett step of `reduce` leaves. -/
def bar (x : BitVec 64) : BitVec 64 := x - BitVec.ofNat 64 (x.toNat * M.toNat / 2 ^ 64) * 8380417

/-- What `reduce` leaves. -/
def red (x : BitVec 64) : BitVec 64 := fixd (bar x - 8380417)

theorem bar_toNat (x : BitVec 64) : (bar x).toNat = barrett x.toNat := by
  obtain ⟨b1, b2⟩ := barrett_bounds x.isLt
  have hT : (BitVec.ofNat 64 (x.toNat * M.toNat / 2 ^ 64)).toNat = barrettQuot x.toNat := by
    rw [BitVec.toNat_ofNat, M_toNat, Nat.mod_eq_of_lt (by
      unfold barrettM; have := x.isLt; omega)]
    rfl
  unfold bar barrett
  generalize BitVec.ofNat 64 (x.toNat * M.toNat / 2 ^ 64) = T at hT
  rw [q_eq] at b1 b2 ⊢
  bv_omega

theorem red_toNat (x : BitVec 64) : (red x).toNat = x.toNat % q := by
  have h1 := barrett_lt x.isLt
  unfold red
  rw [fixd_subq (by rw [bar_toNat]; exact h1), bar_toNat, ← reduce_barrett x.isLt, condSub_eq h1]

theorem red_lt (x : BitVec 64) : (red x).toNat < q := by
  rw [red_toNat]; exact Nat.mod_lt _ (by decide)

theorem toNat_val64 (x : Zq) : (BitVec.ofNat 64 x.val).toNat = x.val := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega)]

/-- A product of reduced values, reduced. -/
theorem red_mul (a b : Zq) : (red (BitVec.ofNat 64 a.val * BitVec.ofNat 64 b.val)).toNat = (a * b).val := by
  have ha := val_lt a
  have hb := val_lt b
  have hp : (BitVec.ofNat 64 a.val * BitVec.ofNat 64 b.val).toNat = a.val * b.val := by
    rw [BitVec.toNat_mul, toNat_val64, toNat_val64]
    exact Nat.mod_eq_of_lt (by have := mul_lt_q2 ha hb; omega)
  rw [red_toNat, hp, val_mul]

/-- A product of reduced values plus a reduced value, reduced. -/
theorem red_mulAdd (a b c : Zq) :
    (red (BitVec.ofNat 64 a.val * BitVec.ofNat 64 b.val + BitVec.ofNat 64 c.val)).toNat = (c + a * b).val := by
  have ha := val_lt a
  have hb := val_lt b
  have hc := val_lt c
  have hp : (BitVec.ofNat 64 a.val * BitVec.ofNat 64 b.val + BitVec.ofNat 64 c.val).toNat =
      a.val * b.val + c.val := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, toNat_val64, toNat_val64, toNat_val64]
    have := mul_lt_q2 ha hb
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [red_toNat, hp, val_add', val_mul, Nat.add_comm (a.val * b.val), Nat.add_mod_mod]

/-! ## Words -/

/-- A word, zero-extended, as `lwz` loads it. -/
theorem toNat_setWidth64 (v : BitVec 32) : (v.setWidth 64).toNat = v.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := v.isLt; omega)

/-- A word, zero-extended. -/
theorem setWidth64_ofNat {v : Nat} (hv : v < 2 ^ 32) : (BitVec.ofNat 32 v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_setWidth64, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (by omega)]

/-- A doubleword below `2³²`, as `stw` stores it. -/
theorem setWidth32_ofNat {x : BitVec 64} {v : Nat} (h : x.toNat = v) (hv : v < 2 ^ 32) :
    x.setWidth 32 = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

/-- A reduced coefficient, as loaded. -/
theorem coeff64 (x : Zq) : (BitVec.ofNat 32 x.val).setWidth 64 = BitVec.ofNat 64 x.val :=
  setWidth64_ofNat (by have := val_lt x; omega)

/-! ## Tables -/

/-- After the first `k` entries of a table at `B`. -/
structure TabInv (T : Nat → Nat) (B : Addr) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  frame : Frame [⟨B, 1024⟩] s₀.mem s.mem
  tab : ∀ j < k, s.mem.readW (B + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (T j)

/-- `table T b` stores the table `T` at `b`. -/
theorem table_ok (T : Nat → Nat) (hT : ∀ k, T k < 2 ^ 23) {b : Reg} (hb : b ≠ .r12)
    (hb0 : b ≠ .r0) {s₀ : State} {B : Addr} (hB : s₀.gpr b = B)
    (hwr : ∀ k < 256, InRegions s₀.wr (B + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (table T b)) s₀ (TabInv T B s₀ 256) := by
  refine wp_range_flatMap (M := isa) (TabInv T B s₀) (fun k s hk h => ?_) 256 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have hTk := hT k
  let s₁ := s.write .r12 ((BitVec.ofNat 16 (T k / 65536) ++ (0 : BitVec 16)).signExtend 64)
  let s₂ := s₁.write .r12 (s₁.gpr .r12 ||| (BitVec.ofNat 16 (T k % 65536)).setWidth 64)
  have v2 : s₂.gpr .r12 = BitVec.ofNat 64 (T k) := by
    simp only [s₂, s₁, State.write, ite_true]; exact loadImm_val (by omega)
  have e : s₂.gpr b + BitVec.ofNat 64 (4 * k) = B + BitVec.ofNat 64 (4 * k) := by
    simp only [s₂, s₁, State.write, hb, ite_false, h.gpr b hb, hB]
  refine WP.cons exec_lis (WP.cons exec_ori (WP.cons (exec_store_w hb0 (show 4 * k < 2 ^ 15 by omega)
    (by show InRegions s₂.wr _ 4; rw [e]; exact h.wr ▸ hwr k hk)) (wp_nil ?_)))
  show TabInv T B s₀ (k + 1)
    { s₂ with mem := (s₂.mem.writeW (s₂.gpr b + BitVec.ofNat 64 (4 * k)) ((s₂.gpr .r12).setWidth 32)) }
  rw [e, v2, setWidth32_ofNat (v := T k) (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega))
    (by omega)]
  refine ⟨fun r hr => ?_, h.rd, h.wr, h.sp, h.lr, ?_, fun j hj => ?_⟩
  · simp only [s₂, s₁, State.write, hr, ite_false]; exact h.gpr r hr
  · exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · show (s.mem.writeW _ _).readW _ 32 = _
    by_cases ej : j = k
    · subst ej; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.tab j (by omega)

end VG.Proof.MlDsa.PPC64LE.Arith
