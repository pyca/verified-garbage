module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen5
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Mul
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Fn
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Fn
public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words

/-!
# Arithmetic modulo a five-word modulus on RISC-V: the functions

`fn core` (`Impl/Weierstrass/RISCV64/Gen5.lean`) from a state with the
working space at `W` in `a0` and the offsets' low words in `a1`–`a3`
(`fn_ok`), as P-384's (`Proof/Weierstrass/RISCV64/P384Field/Fn.lean`), with
five words where those have six:

* the product: P-384's pipelined columns (`P384Field.pipe_ok`) of the terms
  of five words, whose columns 10 and 11 are empty (`product_ok`), and the
  square, the cross products' columns doubled with the squares in ten steps
  (`square_ok`);
* the final subtraction by a mask (`csubWith_ok`), the copies of the
  operands (`copyIn_ok`), and the product reduced by a reduction the
  caller gives (`mulWithF_ok`);
* the sums and differences (`addSum_ok`, `subWith_ok`), the byte-wise copies
  of the operands at offsets not multiples of 8, and the entry (`fn_ok`,
  `fnA_ok`).
-/

@[expose] public section

/-! ## Arithmetic modulo a five-word modulus on RISC-V: the product -/

namespace VG.Proof.Weierstrass.RISCV64.Gen5

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.Gen5
open VG.Impl.Weierstrass.RISCV64.P384Field (X XC XR pipe terms)
open VG.Proof.Weierstrass.RISCV64.P384Field (AR ColInv Tab pipe_ok mulF tsum_mul_lt6 sqF DblInv dbls_ok
  colsV_lt_of)
open VG.Proof.X25519.RISCV64 (Ctx Rest WP.append)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok clob64 dw_write_self dw_write_other dw_frame colsV
  colsV_add tsum dbw dq dbw_lt dq_lt colsV_dbw)
open VG.Proof.X25519.RISCV64.R64 (accW accW_lt accW_congr accW_eq)

/-- Five doublewords, lowest first. -/
def val5 (f : Nat → Nat) : Nat :=
  f 0 + 2 ^ 64 * (f 1 + 2 ^ 64 * (f 2 + 2 ^ 64 * (f 3 + 2 ^ 64 * f 4)))

theorem val5_congr {f g : Nat → Nat} (h : ∀ i < 5, f i = g i) : val5 f = val5 g := by
  unfold val5
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]

theorem val5_lt {f : Nat → Nat} (h : ∀ i < 5, f i < 2 ^ 64) : val5 f < (2 ^ 64) ^ 5 := by
  have := h 0 (by decide); have := h 1 (by decide); have := h 2 (by decide)
  have := h 3 (by decide); have := h 4 (by decide)
  unfold val5; omega_arith

/-- The number of the five doublewords at `o`. -/
abbrev E5 (m : Mem) (b : Addr) (o : Nat) : Nat := val5 fun i => dw m b (o + 8 * i)

theorem two320 : (2 : Nat) ^ 320 = (2 ^ 64) ^ 5 := by omega_using []

/-- Word `j` of the product at `ACC`. -/
abbrev T (m : Mem) (b : Addr) (j : Nat) : Nat := dw m b (ACC + 8 * j)

/-- The `n` words of the product from word `j`. -/
def upW (m : Mem) (b : Addr) (j : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => T m b j + 2 ^ 64 * upW m b (j + 1) n

/-- The product's twelve words. -/
abbrev prodV (m : Mem) (b : Addr) : Nat := upW m b 0 12

theorem upW_append (m : Mem) (b : Addr) :
    ∀ n j k, upW m b j (n + k) = upW m b j n + (2 ^ 64) ^ n * upW m b (j + n) k
  | 0, j, k => by simp [upW]
  | n + 1, j, k => by
    rw [show n + 1 + k = (n + k) + 1 by omega_using []]
    simp only [upW]
    rw [upW_append m b n (j + 1) k, show j + 1 + n = j + (n + 1) by omega_using [],
      show ((2 : Nat) ^ 64) ^ (n + 1) = 2 ^ 64 * (2 ^ 64) ^ n from Nat.pow_succ']
    generalize ((2 : Nat) ^ 64) ^ n = P
    generalize (2 : Nat) ^ 64 = W
    rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- A product below `2⁶⁴⁰` has its top two words zero. -/
theorem upW_hi_zero {m : Mem} {b : Addr} (h : prodV m b < (2 ^ 64) ^ 10) : upW m b 10 2 = 0 := by
  have e := upW_append m b 10 0 2
  rw [Nat.zero_add] at e
  rw [prodV, show (12 : Nat) = 10 + 2 from rfl, e] at h
  rcases Nat.eq_zero_or_pos (upW m b 10 2) with hz | hp
  · exact hz
  · have : (2 ^ 64) ^ 10 ≤ (2 ^ 64) ^ 10 * upW m b 10 2 := Nat.le_mul_of_pos_right _ hp
    exact absurd h (Nat.not_lt.mpr (Nat.le_trans this (Nat.le_add_left _ _)))

/-- The result words of a reduction or a sum. -/
abbrev xv (s : State) : Nat := colsV (fun k => (s.gpr (X k)).toNat) 5

theorem X_facts : ∀ j < 5, X j ≠ .a2 ∧ X j ≠ .a5 ∧ X j ≠ .a6 ∧ X j ≠ .a7 ∧ X j ≠ .t0 ∧ X j ≠ .a0 ∧
    X j ≠ .a3 ∧ X j ≠ .t2 ∧ X j ≠ .t1 ∧ X j ∈ clob64 ∧ ∀ k < 5, k ≠ j → X k ≠ X j := by decide

theorem tab_mul : Tab (terms colPairs) colPairs :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem tab_sq : Tab (terms sqPairs) sqPairs :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

section
variable {acc : Nat} {b : Addr}

def mulCs (X Y : Nat → Nat) (k : Nat) : Nat := tsum (mulF X Y) (colPairs k)

def sqCs (X : Nat → Nat) (k : Nat) : Nat := tsum (sqF X) (sqPairs k)

theorem sqCs_eq (X : Nat → Nat) : sqCs X = fun k => tsum (mulF X X) (sqPairs k) := by
  funext k; unfold sqCs tsum; congr 1; exact List.map_congr_left fun p _ => Nat.mul_comm _ _

/-- The columns sum to the product. -/
theorem mulCols_sum (X Y : Nat → Nat) : colsV (mulCs X Y) 12 = val5 X * val5 Y := by
  simp only [colsV, val5]
  generalize 2 ^ 64 = B
  simp only [mulCs, colPairs, tsum, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.reverse_cons, List.reverse_nil, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mulF, Nat.reduceSub,
    Nat.reduceLeDiff, Nat.reduceLT, and_self, and_true, and_false, decide_true, decide_false,
    Bool.false_eq_true, ↓reduceIte]
  grind

/-- `product acc x y`: the twelve words of `[x] · [y]` at `acc`. -/
theorem product_ok {x y : Nat} (hx : x + 48 ≤ acc) (hy : y + 48 ≤ acc) (hA : acc + 96 ≤ 2048)
    (hA8 : acc % 8 = 0) (hx8 : x % 8 = 0) (hy8 : y % 8 = 0) {s0 : State} (hc : Ctx b s0) :
    WP isa (.block (product acc x y)) s0 fun s' => Ctx b s' ∧ Rest clob64 s0 s' ∧
      Frame [AR acc b] s0.mem s'.mem ∧ accW acc s'.mem b 12 = E5 s0.mem b x * E5 s0.mem b y := by
  refine WP.mono (pipe_ok hx hx8 hy hy8 hA hA8 tab_mul hc) fun s3 h3 => ⟨h3.ctx, h3.rest, h3.frame, ?_⟩
  have e : (fun c => tsum (mulF (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j))) (colPairs c)) =
      mulCs (fun i => dw s0.mem b (x + 8 * i)) (fun j => dw s0.mem b (y + 8 * j)) := rfl
  rw [e] at h3
  have hlt : val5 (fun i => dw s0.mem b (x + 8 * i)) * val5 (fun j => dw s0.mem b (y + 8 * j)) <
      (2 ^ 64) ^ 12 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt (val5_lt fun i _ => dw_lt _ _ _)
      (val5_lt fun i _ => dw_lt _ _ _))
      (by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by decide))
  rw [h3.final (by rw [mulCols_sum]; exact hlt), mulCols_sum]

/-- The squares `a_i²` at `2¹²⁸ⁱ`. -/
def dsq (X : Nat → Nat) : Nat :=
  X 0 * X 0 + (2 ^ 64) ^ 2 * (X 1 * X 1) + (2 ^ 64) ^ 4 * (X 2 * X 2) + (2 ^ 64) ^ 6 * (X 3 * X 3) +
    (2 ^ 64) ^ 8 * (X 4 * X 4)

/-- Twice the cross products' columns, plus the squares, are the square. -/
theorem sqCols_sum (X : Nat → Nat) : 2 * colsV (sqCs X) 12 + dsq X = val5 X * val5 X := by
  simp only [colsV, val5, dsq]
  generalize 2 ^ 64 = B
  simp only [sqCs, sqPairs, colPairs, tsum, List.range_succ,
    List.range_zero, List.nil_append, List.cons_append, List.reverse_cons, List.reverse_nil,
    List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    sqF, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceLT, and_self, and_true, and_false, decide_true,
    decide_false, Bool.false_eq_true, ↓reduceIte]
  grind

/-- The words of the squares are the squares. -/
theorem colsV_dq (X : Nat → Nat) : colsV (dq X) 10 = dsq X := by
  simp only [colsV, dq, dsq]
  simp only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]
  have h0 := Nat.mod_add_div (X 0 * X 0) (2 ^ 64)
  have h1 := Nat.mod_add_div (X 1 * X 1) (2 ^ 64)
  have h2 := Nat.mod_add_div (X 2 * X 2) (2 ^ 64)
  have h3 := Nat.mod_add_div (X 3 * X 3) (2 ^ 64)
  have h4 := Nat.mod_add_div (X 4 * X 4) (2 ^ 64)
  generalize X 0 * X 0 % 2 ^ 64 = l0 at *
  generalize X 1 * X 1 % 2 ^ 64 = l1 at *
  generalize X 2 * X 2 % 2 ^ 64 = l2 at *
  generalize X 3 * X 3 % 2 ^ 64 = l3 at *
  generalize X 4 * X 4 % 2 ^ 64 = l4 at *
  generalize X 0 * X 0 / 2 ^ 64 = u0 at *
  generalize X 1 * X 1 / 2 ^ 64 = u1 at *
  generalize X 2 * X 2 / 2 ^ 64 = u2 at *
  generalize X 3 * X 3 / 2 ^ 64 = u3 at *
  generalize X 4 * X 4 / 2 ^ 64 = u4 at *
  rw [← h0, ← h1, ← h2, ← h3, ← h4]
  generalize 2 ^ 64 = B
  grind

theorem colsV_split (f : Nat → Nat) :
    colsV f 12 = colsV f 10 + (2 ^ 64) ^ 10 * (f 10 + 2 ^ 64 * f 11) := by
  simp only [colsV]; rw [Nat.pow_succ]; grind

theorem accW_split (m : Mem) :
    accW acc m b 12 = accW acc m b 10 + (2 ^ 64) ^ 10 * (dw m b (acc + 8 * 10) + 2 ^ 64 * dw m b (acc + 8 * 11)) := by
  rw [accW_eq, accW_eq, colsV_split]

/-- `square acc x`: the twelve words of `[x]²` at `acc`, the top two zero. -/
theorem square_ok {x : Nat} (hx : x + 48 ≤ acc) (hA : acc + 96 ≤ 2048) (hA8 : acc % 8 = 0)
    (hx8 : x % 8 = 0) {s0 : State} (hc : Ctx b s0) :
    WP isa (.block (square acc x)) s0 fun s' => Ctx b s' ∧ Rest clob64 s0 s' ∧
      Frame [AR acc b] s0.mem s'.mem ∧ accW acc s'.mem b 12 = E5 s0.mem b x * E5 s0.mem b x := by
  have hX : ∀ i, dw s0.mem b (x + 8 * i) < 2 ^ 64 := fun i => dw_lt _ _ _
  unfold square
  simp only [List.append_assoc]
  refine WP.append (pipe_ok hx hx8 hx hx8 hA hA8 tab_sq hc) fun s3 h3 => ?_
  rw [← sqCs_eq] at h3
  have hsum := sqCols_sum fun i => dw s0.mem b (x + 8 * i)
  have hlt : val5 (fun i => dw s0.mem b (x + 8 * i)) * val5 (fun i => dw s0.mem b (x + 8 * i)) <
      (2 ^ 64) ^ 10 := by
    rw [show (10 : Nat) = 5 + 5 from rfl, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (val5_lt fun i _ => hX i) (val5_lt fun i _ => hX i)
  have hfin := h3.final (by
    have : (2 ^ 64) ^ 10 ≤ (2 ^ 64) ^ 12 := Nat.pow_le_pow_right (by decide) (by decide)
    omega_using [hsum, hlt, this])
  -- The cross products' top two words are zero.
  obtain hS10 : colsV (sqCs fun i => dw s0.mem b (x + 8 * i)) 12 < (2 ^ 64) ^ 10 := by
    omega_using [hsum, hlt]
  obtain ⟨z10, z11⟩ : dw s3.mem b (acc + 8 * 10) = 0 ∧ dw s3.mem b (acc + 8 * 11) = 0 := by
    rw [accW_split] at hfin
    have : (2 ^ 64) ^ 10 ≤ (2 ^ 64) ^ 10 * (dw s3.mem b (acc + 8 * 10) + 2 ^ 64 * dw s3.mem b (acc + 8 * 11)) ∨
        dw s3.mem b (acc + 8 * 10) + 2 ^ 64 * dw s3.mem b (acc + 8 * 11) = 0 := by
      rcases Nat.eq_zero_or_pos (dw s3.mem b (acc + 8 * 10) + 2 ^ 64 * dw s3.mem b (acc + 8 * 11)) with h | h
      · exact .inr h
      · exact .inl (Nat.le_mul_of_pos_right _ h)
    rcases this with h | h
    · omega_using [hfin, hS10, h]
    · omega_using [h]
  refine wp_li (by decide) fun s4 u4 => wp_li (by decide) fun s5 u5 => ?_
  have hr5 : Rest clob64 s3 s5 := (u4.rest (by decide)).trans (u5.rest (by decide))
  have hm5 : s5.mem = s3.mem := by rw [u5.mem, u4.mem]
  have hd0 : DblInv acc b s0 x (fun i => dw s3.mem b (acc + 8 * i)) 0 s5 :=
    ⟨h3.ctx.of_rest hr5 (by decide), h3.rest.trans hr5, by rw [hm5]; exact h3.frame,
      fun i _ _ => by rw [hm5], by rw [u5.other _ (by decide), u4.gpr]; rfl, fun h' => absurd h' (by decide),
      by rw [u5.gpr]; decide, by rw [u5.gpr]; rfl⟩
  refine WP.mono (dbls_ok hx hA hA8 hx8 (fun i => dw_lt _ _ _) 10 (by decide) s5 hd0) fun s6 h6 =>
    ⟨h6.ctx, h6.rest, h6.frame, ?_⟩
  have hv := h6.val
  rw [colsV_add, colsV_dq] at hv
  have hd := colsV_dbw (C := fun i => dw s3.mem b (acc + 8 * i)) (fun i => dw_lt _ _ _) 9
  obtain hC10 : colsV (fun i => dw s3.mem b (acc + 8 * i)) 10 = colsV (sqCs fun i => dw s0.mem b (x + 8 * i)) 12 := by
    rw [← accW_eq, ← hfin, accW_split, z10, z11]; omega_using []
  rw [hC10] at hd
  obtain w10 : dw s6.mem b (acc + 8 * 10) = 0 := by rw [h6.hi 10 (by decide) (by decide)]; exact z10
  obtain w11 : dw s6.mem b (acc + 8 * 11) = 0 := by rw [h6.hi 11 (by decide) (by decide)]; exact z11
  rw [accW_split, w10, w11]; simp only [Nat.mul_zero, Nat.add_zero]
  have := accW_lt (acc := acc) s6.mem b 10
  generalize (2 ^ 64) ^ 10 = K at *
  generalize accW acc s6.mem b 10 = A at *
  generalize val5 (fun i => dw s0.mem b (x + 8 * i)) * val5 (fun i => dw s0.mem b (x + 8 * i)) = Q at *
  generalize colsV (dbw fun i => dw s3.mem b (acc + 8 * i)) 10 = D at *
  generalize colsV (sqCs fun i => dw s0.mem b (x + 8 * i)) 12 = S at *
  generalize dsq (fun i => dw s0.mem b (x + 8 * i)) = E at *
  generalize (s6.gpr .a4).toNat = c at *
  generalize dw s3.mem b (acc + 8 * 9) / 2 ^ 63 = t at *
  rcases Nat.eq_zero_or_pos (c + t) with h0 | hpos
  · have : c = 0 := by omega_using [h0]
    have : t = 0 := by omega_using [h0]
    subst_vars; omega_using []
  · have : K ≤ K * (c + t) := Nat.le_mul_of_pos_right _ hpos
    rw [Nat.mul_add] at this
    omega_using [hlt, hsum, hv, hd, this]

end

end VG.Proof.Weierstrass.RISCV64.Gen5

/-! ## Arithmetic modulo a five-word modulus on RISC-V: the final subtraction -/

namespace VG.Proof.Weierstrass.RISCV64.Gen5

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.Gen5
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt dw_write_self dw_write_other al8 colsV colsV_add)
open VG.Proof.Weierstrass.RISCV64.P256Field (adc_ok upd_keeps)
open VG.Impl.Weierstrass.RISCV64.P384Field (X XC XR sumWord selWord adcWord sbbWord addMWord movAB zext ptrs)
open VG.Proof.Weierstrass.RISCV64.P384Field (colsV_lt_of colsV_congr AR)

/-- A mask, zero or all ones. -/
def IsMask (m : BitVec 64) : Prop := m = 0 ∨ m = BitVec.allOnes 64

/-- `x ⊕ ((e ⊕ x) ∧ m)`: `e` under the mask all ones, `x` under zero. -/
theorem sel_mask {x e m : BitVec 64} (hm : IsMask m) :
    (e ^^^ x) &&& m ^^^ x = if m = BitVec.allOnes 64 then e else x := by
  rcases hm with rfl | rfl
  · have : (0 : BitVec 64) ≠ BitVec.allOnes 64 := by decide
    simp only [this, ↓reduceIte]
    ext i hi
    simp
  · simp only [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, ↓reduceIte]

/-- The mask of `a ∨ c`, for bits `a` and `c`. -/
theorem mask_of_bits {a c : BitVec 64} (ha : a.toNat ≤ 1) (hc : c.toNat ≤ 1) :
    IsMask (0 - (a ||| c)) ∧ (0 - (a ||| c) = BitVec.allOnes 64 ↔ a.toNat = 1 ∨ c.toNat = 1) := by
  obtain ha' : a = 0 ∨ a = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with h | h
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  obtain hc' : c = 0 ∨ c = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  rcases ha' with rfl | rfl <;> rcases hc' with rfl | rfl <;> (unfold IsMask; decide)

/-- The registers `csub` writes. -/
abbrev clobC : List Reg := [.t0, .a0, .a5, .a6, .a7]

/-- The five doublewords at `O`. -/
abbrev d5 (m : Mem) (O : Addr) : Nat := colsV (fun k => dw m O (8 * k)) 5

theorem out_contains (O : Addr) {j : Nat} (hj : j < 5) :
    (⟨O, 40⟩ : Region).Contains (O + BitVec.ofNat 64 (8 * j)) 8 := by
  have := Offset.contains O (d := 8 * j) (n := 8) (e := 0) (k := 40) (by omega_using []) (by omega_using [hj]) (by omega_using [])
  simpa using this

/-- A block that puts `N j` into `t0`, from `N (j - 1)` there for `j > 0`. -/
def KOk (k : List Instr) (j : Nat) (N : Nat → Nat) : Prop :=
  ∀ s : State, (j = 0 ∨ (s.gpr .t0).toNat = N (j - 1)) →
    WP isa (.block k) s fun s' => (s'.gpr .t0).toNat = N j ∧ Keeps [.t0, .a6] s s'

/-- After `j` words of `x + N` from `s0`, with `O` in `t2`. -/
structure SumInv (O : Addr) (N : Nat → Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobC → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨O, 40⟩] s0.mem s.mem
  t0 : 0 < j → (s.gpr .t0).toNat = N (j - 1)
  cy : (s.gpr .a7).toNat ≤ 1
  val : colsV (fun k => dw s.mem O (8 * k)) j + (2 ^ 64) ^ j * (s.gpr .a7).toNat =
    colsV (fun k => (s0.gpr (X k)).toNat + N k) j

theorem colsV_congr' {f g : Nat → Nat} : ∀ {n}, (∀ k < n, f k = g k) → colsV f n = colsV g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [colsV]; rw [colsV_congr' (fun k hk => h k (by omega_using [hk])), h n (by omega_using [])]

/-- Word `j` of `x + N`. -/
theorem sumStep_ok {O : Addr} {N : Nat → Nat} (hN : ∀ j, N j < 2 ^ 64) {k : List Instr} {j : Nat}
    (hj : j < 5) (hk : KOk k j N) (hal : O.toNat % 8 = 0) {s0 s : State} (h2 : s0.gpr .t2 = O)
    (hw : ∀ j < 5, InRegions s0.wr (O + BitVec.ofNat 64 (8 * j)) 8) (h : SumInv O N s0 j s) :
    WP isa (.block (k ++ sumWord j)) s (SumInv O N s0 (j + 1)) := by
  obtain ⟨-, x5, x6, x7, x0, xa, -, -, -, -, -⟩ := X_facts j hj
  obtain hpre : j = 0 ∨ (s.gpr .t0).toNat = N (j - 1) := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exact .inl h0
    · exact .inr (h.t0 h0)
  refine WP.block_append (WP.mono (hk s hpre) fun s1 ⟨e1, k1⟩ => ?_)
  unfold sumWord
  refine WP.block_append (WP.mono (adc_ok (d := .a5) (x := X j) (y := .t0) (c := .a7) (u := .a0))
    fun s2 ⟨e2, k2⟩ => ?_)
  obtain g2 : ∀ r, r ∉ clobC → s2.gpr r = s0.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r0, ra, r5, r6, r7⟩ := hr
    rw [k2.1 _ (by simp [ra, r5, r7]), k1.1 _ (by simp [r0, r6]), h.gpr r (by simp [r0, ra, r5, r6, r7])]
  obtain p2 : s2.gpr .t2 + BitVec.ofNat 64 (8 * j) = O + BitVec.ofNat 64 (8 * j) := by
    rw [g2 _ (by decide), h2]
  refine wp_sd (by omega_using [hj]) p2 (al8 hal (by omega_using [])) (by rw [k2.2.2.2.1, k1.2.2.2.1, h.wr]; exact hw j hj)
    fun s3 u3 => WP.block_nil ?_
  obtain ex : s1.gpr (X j) = s0.gpr (X j) := by rw [k1.1 _ (by simp [x0, x6]), h.gpr _ (by simp [x0, xa, x5, x6, x7])]
  obtain ec : s1.gpr .a7 = s.gpr .a7 := k1.1 _ (by decide)
  obtain e2' := e2 (by rw [ec]; exact h.cy)
  rw [ex, ec, e1] at e2'
  obtain hm3 : s3.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j)) (s2.gpr .a5) := by
    rw [u3.mem, k2.2.1, k1.2.1]
  refine ⟨fun r hr => by rw [u3.gpr]; exact g2 r hr, by rw [u3.rd, k2.2.2.1, k1.2.2.1, h.rd],
    by rw [u3.wr, k2.2.2.2.1, k1.2.2.2.1, h.wr], by rw [u3.sp, k2.2.2.2.2, k1.2.2.2.2, h.sp], ?_,
    fun _ => by rw [u3.gpr, k2.1 _ (by decide), e1]; rfl, ?_, ?_⟩
  · rw [hm3]; exact h.frame.writeW (List.mem_singleton_self _) _ (out_contains O hj)
  · rw [u3.gpr]
    have := (s2.gpr .a5).isLt; have := (s0.gpr (X j)).isLt; have := hN j; have := h.cy
    omega_using [e1, e2', this]
  · have hv := h.val
    obtain hc : colsV (fun k => dw s3.mem O (8 * k)) j = colsV (fun k => dw s.mem O (8 * k)) j :=
      colsV_congr' fun k hk => by rw [hm3, dw_write_other _ _ _ (by omega_using [hk]) (by omega_using [hj, hk]) (by omega_using [hj])]
    show colsV (fun k => dw s3.mem O (8 * k)) j + (2 ^ 64) ^ j * dw s3.mem O (8 * j) +
        (2 ^ 64) ^ (j + 1) * (s3.gpr .a7).toNat =
      colsV (fun k => (s0.gpr (X k)).toNat + N k) j + (2 ^ 64) ^ j * ((s0.gpr (X j)).toNat + N j)
    rw [hc, hm3, dw_write_self, u3.gpr, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..,
      ← hv]
    generalize (2 ^ 64) ^ j = E at *
    generalize colsV (fun k => dw s.mem O (8 * k)) j = C at *
    obtain key : E * (s2.gpr .a5).toNat + E * 2 ^ 64 * (s2.gpr .a7).toNat =
        E * (s.gpr .a7).toNat + E * ((s0.gpr (X j)).toNat + N j) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, e2']; congr 1; omega_using []
    omega_using [key]

/-- The words of `x + N`, by induction. -/
theorem sums_ok {O : Addr} {N : Nat → Nat} (hN : ∀ j, N j < 2 ^ 64) {ks : List (List Instr)}
    (hk : ∀ j < 5, KOk (ks.getD j []) j N) (hal : O.toNat % 8 = 0) {s0 : State} (h2 : s0.gpr .t2 = O)
    (hw : ∀ j < 5, InRegions s0.wr (O + BitVec.ofNat 64 (8 * j)) 8) :
    ∀ n ≤ 5, ∀ s, SumInv O N s0 0 s →
      WP isa (.block ((List.range n).flatMap fun j => ks.getD j [] ++ sumWord j)) s (SumInv O N s0 n) :=
  wp_range_flatMap (M := isa) (SumInv O N s0) fun j _ hj h => sumStep_ok hN hj (hk j hj) hal h2 hw h

/-- After `j` words of the selection from `s0`, by the mask `t0`. -/
structure SelInv (O : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .a5 → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨O, 40⟩] s0.mem s.mem
  lo : ∀ k < j, dw s.mem O (8 * k) =
    if s0.gpr .t0 = BitVec.allOnes 64 then dw s0.mem O (8 * k) else (s0.gpr (X k)).toNat
  hi : ∀ k, j ≤ k → k < 5 → dw s.mem O (8 * k) = dw s0.mem O (8 * k)

/-- Word `j` of the selection. -/
theorem selStep_ok {O : Addr} (hal : O.toNat % 8 = 0) {s0 s : State} (h2 : s0.gpr .t2 = O)
    (hw : ∀ j < 5, InRegions s0.wr (O + BitVec.ofNat 64 (8 * j)) 8) (hm : IsMask (s0.gpr .t0))
    {j : Nat} (hj : j < 5) (h : SelInv O s0 j s) :
    WP isa (.block (selWord j)) s (SelInv O s0 (j + 1)) := by
  obtain ⟨-, x5, -, -, x0, -, -, x2, -, -, -⟩ := X_facts j hj
  unfold selWord
  obtain p : s.gpr .t2 + BitVec.ofNat 64 (8 * j) = O + BitVec.ofNat 64 (8 * j) := by
    rw [h.gpr _ (by decide), h2]
  obtain hr : InRegions (s.rd ++ s.wr) (O + BitVec.ofNat 64 (8 * j)) 8 := by
    obtain ⟨r, hr, hc⟩ := hw j hj
    exact ⟨r, List.mem_append_right _ (by rw [h.wr]; exact hr), hc⟩
  refine wp_ld (by omega_using [hj]) p (al8 hal (by omega_using [])) hr fun s1 u1 => wp_xor fun s2 u2 =>
    VG.Proof.X25519.RISCV64.wp_and fun s3 u3 => wp_xor fun s4 u4 => ?_
  obtain g4 : ∀ r, r ≠ .a5 → s4.gpr r = s.gpr r := fun r hr => by
    rw [u4.other _ hr, u3.other _ hr, u2.other _ hr, u1.other _ hr]
  obtain v4 : s4.gpr .a5 = if s0.gpr .t0 = BitVec.allOnes 64 then s.mem.readW (O + BitVec.ofNat 64 (8 * j)) 64
      else s0.gpr (X j) := by
    rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr, u3.other _ x5, u2.other _ x5, u1.other _ x5,
      u2.other .t0 (by decide), u1.other .t0 (by decide), h.gpr _ x5, h.gpr .t0 (by decide)]
    exact sel_mask hm
  refine wp_sd (by omega_using [hj]) (by rw [g4 _ (by decide), p]) (al8 hal (by omega_using []))
    (by rw [u4.wr, u3.wr, u2.wr, u1.wr, h.wr]; exact hw j hj) fun s5 u5 => WP.block_nil ?_
  obtain hm5 : s5.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j)) (s4.gpr .a5) := by
    rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨fun r hr => by rw [u5.gpr, g4 r hr, h.gpr r hr], by rw [u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, h.rd],
    by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, h.wr], by rw [u5.sp, u4.sp, u3.sp, u2.sp, u1.sp, h.sp], ?_,
    fun k hk => ?_, fun k hk hk' => ?_⟩
  · rw [hm5]; exact h.frame.writeW (List.mem_singleton_self _) _ (out_contains O hj)
  · rw [hm5]
    rcases Nat.lt_or_ge k j with hkj | hkj
    · rw [dw_write_other _ _ _ (by omega_using [hkj]) (by omega_using [hj, hk]) (by omega_using [hj])]; exact h.lo k hkj
    · have : k = j := by omega_using [hk, hkj]
      subst this
      rw [dw_write_self, v4]
      split
      · exact h.hi k (Nat.le_refl _) hj
      · rfl
  · rw [hm5, dw_write_other _ _ _ (by omega_using [hk]) (by omega_using [hk']) (by omega_using [hj])]; exact h.hi k (by omega_using [hk]) hk'

theorem sels_ok {O : Addr} (hal : O.toNat % 8 = 0) {s0 : State} (h2 : s0.gpr .t2 = O)
    (hw : ∀ j < 5, InRegions s0.wr (O + BitVec.ofNat 64 (8 * j)) 8) (hm : IsMask (s0.gpr .t0)) :
    ∀ n ≤ 5, ∀ s, SelInv O s0 0 s →
      WP isa (.block ((List.range n).flatMap selWord)) s (SelInv O s0 n) :=
  wp_range_flatMap (M := isa) (SelInv O s0) fun _ _ hj h => selStep_ok hal h2 hw hm hj h

/-- `sumWith ks ++ csubTail`: `x mod m` at `[t2]`, for `x = X + 2³²⁰ XC` below
`2m`, where `ks[j]` puts the words `N j` of `2³²⁰ - m` into `t0`. -/
theorem csubWith_ok {ks : List (List Instr)} {N : Nat → Nat} {M : Nat} (hN : ∀ j, N j < 2 ^ 64)
    (hk : ∀ j < 5, KOk (ks.getD j []) j N) (hNv : colsV N 5 + M = 2 ^ 320) {s : State}
    {O : Addr} (ht2 : s.gpr .t2 = O) (hal : O.toNat % 8 = 0)
    (hw : ∀ j < 5, InRegions s.wr (O + BitVec.ofNat 64 (8 * j)) 8) (hc : (s.gpr XC).toNat ≤ 1)
    (hx : xv s + 2 ^ 320 * (s.gpr XC).toNat < 2 * M) :
    WP isa (.block (sumWith ks ++ csubTail)) s fun s' =>
      d5 s'.mem O = (xv s + 2 ^ 320 * (s.gpr XC).toNat) % M ∧
      Frame [⟨O, 40⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobC → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold sumWith csubTail
  rw [List.cons_append]
  refine wp_li (by decide) fun s1 u1 => ?_
  obtain h0 : SumInv O N s 0 s1 :=
    ⟨fun r hr => u1.other _ (fun h => hr (by simp [h])), u1.rd, u1.wr, u1.sp, by rw [u1.mem]; exact Frame.refl _ _,
      fun h => absurd h (Nat.lt_irrefl _), by rw [u1.gpr]; decide, by simp only [colsV, u1.gpr]; rfl⟩
  refine WP.block_append (WP.mono (sums_ok hN hk hal ht2 hw 5 (Nat.le_refl _) s1 h0) fun s2 h2 => ?_)
  rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_or fun s3 u3 => wp_li (imm := 0) (by decide) fun s4 u4 => wp_sub fun s5 u5 => ?_
  obtain hxc : s2.gpr XC = s.gpr XC := h2.gpr _ (by decide)
  obtain hm : IsMask (s5.gpr .t0) ∧ (s5.gpr .t0 = BitVec.allOnes 64 ↔
      (s2.gpr .a7).toNat = 1 ∨ (s.gpr XC).toNat = 1) := by
    rw [u5.gpr, u4.gpr, u4.other _ (by decide), u3.gpr, ← hxc]
    exact mask_of_bits h2.cy (by rw [hxc]; exact hc)
  obtain g5 : ∀ r, r ≠ .t0 → r ≠ .a7 → s5.gpr r = s2.gpr r := fun r h0 h7 => by
    rw [u5.other _ h0, u4.other _ h0, u3.other _ h7]
  obtain m5 : s5.mem = s2.mem := by rw [u5.mem, u4.mem, u3.mem]
  obtain p5 : s5.gpr .t2 = O := by rw [g5 _ (by decide) (by decide), h2.gpr _ (by decide), ht2]
  obtain w5 : s5.wr = s.wr := by rw [u5.wr, u4.wr, u3.wr, h2.wr]
  refine WP.mono (sels_ok hal p5 (by rw [w5]; exact hw) hm.1 5 (Nat.le_refl _) s5
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ => rfl⟩) fun s6 h6 => ?_
  obtain rt : ∀ r, r ∉ clobC → s6.gpr r = s.gpr r := fun r hr => by
    obtain h0 : r ≠ .t0 := fun h => hr (by simp [h])
    obtain h5 : r ≠ .a5 := fun h => hr (by simp [h])
    obtain h7 : r ≠ .a7 := fun h => hr (by simp [h])
    rw [h6.gpr r h5, g5 r h0 h7, h2.gpr r hr]
  obtain hxk : ∀ k < 5, (s5.gpr (X k)).toNat = (s.gpr (X k)).toNat := fun k hk => by
    obtain ⟨-, x5, x6, x7, x0, xa, -⟩ := X_facts k hk
    rw [g5 _ x0 x7, h2.gpr _ (by simp [x0, xa, x5, x6, x7])]
  obtain hd : d5 s6.mem O = if s5.gpr .t0 = BitVec.allOnes 64 then d5 s2.mem O else xv s := by
    split
    · exact colsV_congr' fun k hk => by rw [h6.lo k hk, ite_eq_left ‹_›, m5]
    · exact colsV_congr' fun k hk => by rw [h6.lo k hk, ite_eq_right ‹_›, hxk k hk]
  have hv := h2.val
  rw [colsV_add] at hv
  obtain hs : d5 s2.mem O + 2 ^ 320 * (s2.gpr .a7).toNat + M = xv s + 2 ^ 320 := by
    rw [two320]; simp only [d5, xv] at hv ⊢; omega_using [hNv, hv]
  obtain hd6 := colsV_lt_of (fun k => dw s2.mem O (8 * k)) (fun k => dw_lt _ _ _) 5
  rw [← two320] at hd6
  have hc7 := h2.cy
  refine ⟨?_, ?_, rt, ?_, ?_, ?_⟩
  · rw [hd]
    have hge := hm.2
    simp only [d5, xv] at hd6 hs hx ⊢
    generalize colsV (fun k => dw s2.mem O (8 * k)) 5 = D at *
    generalize colsV (fun k => (s.gpr (X k)).toNat) 5 = Y at *
    split
    · rename_i h
      obtain hg := hge.mp h
      rw [Nat.mod_eq_sub_mod (by omega_using [hNv, hv, hg]), Nat.mod_eq_of_lt (by omega_using [hx])]
      omega_using [hNv, hx, hv, hg]
    · rename_i h
      obtain hg : ¬ ((s2.gpr .a7).toNat = 1 ∨ (s.gpr XC).toNat = 1) := fun h' => h (hge.mpr h')
      rw [Nat.mod_eq_of_lt (by omega_using [hNv, hc, hc7, hd6, hv, hg])]
      omega_using [hc, hg]
  · exact h2.frame.trans (by rw [← m5]; exact h6.frame)
  · rw [h6.rd, u5.rd, u4.rd, u3.rd, h2.rd]
  · rw [h6.wr, w5]
  · rw [h6.sp, u5.sp, u4.sp, u3.sp, h2.sp]

end VG.Proof.Weierstrass.RISCV64.Gen5

namespace VG.Proof.Weierstrass.RISCV64.Gen5

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.Gen5
open VG.Proof.X25519.RISCV64 (Ctx Rest)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok clob64 dw_write_self dw_write_other al8 dw_frame colsV)
open VG.Proof.X25519.RISCV64.R64 (accW accW_eq)
open VG.Impl.Weierstrass.RISCV64.P384Field (X XC XR sumWord selWord adcWord sbbWord addMWord movAB zext ptrs)
open VG.Proof.Weierstrass.RISCV64.P384Field (colsV_lt_of colsV_congr AR)

/-- The registers the operations write. -/
abbrev clobM : List Reg := [.t0, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a4, .a5, .a6, .a7]

/-- The registers of the copies. -/
abbrev clobI : List Reg := [.t3, .t6, .a1, .a2, .a4, .a5]

/-- The five doublewords at `b + o`, as offsets from `b`. -/
theorem d5_add (m : Mem) (b : Addr) (o : Nat) : d5 m (b + BitVec.ofNat 64 o) = E5 m b o := by
  obtain e : ∀ k, (b + BitVec.ofNat 64 o) + BitVec.ofNat 64 k = b + BitVec.ofNat 64 (o + k) := fun k => by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  simp only [d5, E5, val5, colsV, dw, e, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul,
    Nat.pow_zero, Nat.zero_add, Nat.reducePow]
  omega_using []

theorem d5_lt (m : Mem) (O : Addr) : d5 m O < 2 ^ 320 := by
  rw [two320]; exact colsV_lt_of _ (fun _ => dw_lt _ _ _) 5

/-- The words of the operand at `p` copied to `b + o`. -/
theorem copyIn_ok {b A : Addr} {s : State} (hc : Ctx b s) {p : Reg} (hp : s.gpr p = A)
    (hpr : p ∉ clobI) (hal : A.toNat % 8 = 0)
    (hr : ∀ j < 5, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * j)) 8)
    {o : Nat} (ho : o + 40 ≤ 2048) (ho8 : o % 8 = 0) :
    WP isa (.block (copyIn p o)) s fun s' =>
      Ctx b s' ∧ Rest clobI s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 40⟩] s.mem s'.mem ∧
      d5 s'.mem (b + BitVec.ofNat 64 o) = d5 s.mem A := by
  unfold copyIn
  obtain hp' : ∀ r ∈ clobI, r ≠ p := fun r hr h => hpr (h ▸ hr)
  obtain h0 := hr 0 (by decide)
  obtain h1 := hr 1 (by decide)
  obtain h2 := hr 2 (by decide)
  obtain h3 := hr 3 (by decide)
  obtain h4 := hr 4 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at h0 h1 h2 h3 h4
  refine wp_ld (off := 0) (a := A + BitVec.ofNat 64 0) (by decide) (by rw [hp]) (al8 hal (by decide))
    (by exact h0) fun s1 u1 => ?_
  refine wp_ld (off := 8) (a := A + BitVec.ofNat 64 8) (by decide) (by rw [u1.other _ (hp' .t3 (by decide)).symm, hp]) (al8 hal (by decide))
    (by rw [u1.rd, u1.wr]; exact h1) fun s2 u2 => ?_
  refine wp_ld (off := 16) (a := A + BitVec.ofNat 64 16) (by decide) (by rw [u2.other _ (hp' .t6 (by decide)).symm, u1.other _ (hp' .t3 (by decide)).symm, hp]) (al8 hal (by decide))
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact h2) fun s3 u3 => ?_
  refine wp_ld (off := 24) (a := A + BitVec.ofNat 64 24) (by decide) (by rw [u3.other _ (hp' .a1 (by decide)).symm, u2.other _ (hp' .t6 (by decide)).symm, u1.other _ (hp' .t3 (by decide)).symm, hp]) (al8 hal (by decide))
    (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact h3) fun s4 u4 => ?_
  refine wp_ld (off := 32) (a := A + BitVec.ofNat 64 32) (by decide) (by rw [u4.other _ (hp' .a2 (by decide)).symm, u3.other _ (hp' .a1 (by decide)).symm, u2.other _ (hp' .t6 (by decide)).symm, u1.other _ (hp' .t3 (by decide)).symm, hp]) (al8 hal (by decide))
    (by rw [u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact h4) fun s5 u5 => ?_
  obtain r5 : Rest clobI s s5 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
    ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  obtain hc5 : Ctx b s5 := hc.of_rest r5 (by decide)
  obtain m5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain v0 : s5.gpr .t3 = s.mem.readW (A + BitVec.ofNat 64 0) 64 := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
  obtain v1 : s5.gpr .t6 = s.mem.readW (A + BitVec.ofNat 64 8) 64 := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.mem]
  obtain v2 : s5.gpr .a1 = s.mem.readW (A + BitVec.ofNat 64 16) 64 := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.mem, u1.mem]
  obtain v3 : s5.gpr .a2 = s.mem.readW (A + BitVec.ofNat 64 24) 64 := by
    rw [u5.other _ (by decide), u4.gpr, u3.mem, u2.mem, u1.mem]
  obtain v4 : s5.gpr .a4 = s.mem.readW (A + BitVec.ofNat 64 32) 64 := by
    rw [u5.gpr, u4.mem, u3.mem, u2.mem, u1.mem]
  refine sd_ok hc5 (d := o + 0) (by omega_using [ho]) (by omega_using [ho8]) fun s7 u7 => ?_
  obtain hc7 : Ctx b s7 := hc5.of_rest (u7.rest []) (by decide)
  refine sd_ok hc7 (d := o + 8) (by omega_using [ho]) (by omega_using [ho8]) fun s8 u8 => ?_
  obtain hc8 : Ctx b s8 := hc7.of_rest (u8.rest []) (by decide)
  refine sd_ok hc8 (d := o + 16) (by omega_using [ho]) (by omega_using [ho8]) fun s9 u9 => ?_
  obtain hc9 : Ctx b s9 := hc8.of_rest (u9.rest []) (by decide)
  refine sd_ok hc9 (d := o + 24) (by omega_using [ho]) (by omega_using [ho8]) fun s10 u10 => ?_
  obtain hc10 : Ctx b s10 := hc9.of_rest (u10.rest []) (by decide)
  refine sd_ok hc10 (d := o + 32) (by omega_using [ho]) (by omega_using [ho8]) fun s11 u11 => ?_
  refine WP.block_nil ?_
  obtain g11 : s11.gpr = s5.gpr := by rw [u11.gpr, u10.gpr, u9.gpr, u8.gpr, u7.gpr]
  obtain hm : s11.mem = (((((s.mem.writeW (b + BitVec.ofNat 64 (o + 0)) (s5.gpr .t3)).writeW
      (b + BitVec.ofNat 64 (o + 8)) (s5.gpr .t6)).writeW (b + BitVec.ofNat 64 (o + 16)) (s5.gpr .a1)).writeW
      (b + BitVec.ofNat 64 (o + 24)) (s5.gpr .a2)).writeW (b + BitVec.ofNat 64 (o + 32)) (s5.gpr .a4)) := by
    rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, m5, u10.gpr, u9.gpr, u8.gpr, u7.gpr]
  obtain r511 : Rest [] s5 s11 := ⟨fun r _ => by rw [g11], by rw [u11.rd, u10.rd, u9.rd, u8.rd, u7.rd],
    by rw [u11.wr, u10.wr, u9.wr, u8.wr, u7.wr], by rw [u11.sp, u10.sp, u9.sp, u8.sp, u7.sp]⟩
  refine ⟨hc5.of_rest r511 (by decide), r5.trans (r511.mono (by decide)), ?_, ?_⟩
  · rw [hm]
    obtain c : ∀ k < 5, (⟨b + BitVec.ofNat 64 o, 40⟩ : Region).Contains (b + BitVec.ofNat 64 (o + 8 * k)) 8 :=
      fun k hk => Offset.contains b (by omega_using []) (by omega_using [hk]) (by omega_using [ho])
    obtain c0 := c 0 (by decide)
    obtain c1 := c 1 (by decide)
    obtain c2 := c 2 (by decide)
    obtain c3 := c 3 (by decide)
    obtain c4 := c 4 (by decide)
    simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at c0 c1 c2 c3 c4
    exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW
      (List.mem_singleton_self _) _ c1).writeW (List.mem_singleton_self _) _ c2).writeW
      (List.mem_singleton_self _) _ c3).writeW (List.mem_singleton_self _) _ c4
  · rw [d5_add]
    obtain w : ∀ k < 5, dw s11.mem b (o + 8 * k) = dw s.mem A (8 * k) := by
      intro k hk
      rw [hm]
      obtain rfl | rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega_using [hk]
      all_goals simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul]
      all_goals (repeat rw [dw_write_other _ _ _ (by omega) (by omega_using [ho]) (by omega_using [ho])])
      all_goals rw [dw_write_self]
      all_goals (try rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)])
      exacts [by rw [v0]; rfl, by rw [v1]; rfl, by rw [v2]; rfl, by rw [v3]; rfl, by rw [v4]; rfl]
    simp only [E5, d5, val5, colsV, w 0 (by decide), w 1 (by decide), w 2 (by decide), w 3 (by decide),
      w 4 (by decide)]
    omega_using []

/-- The product's words, as `reduce` reads them. -/
theorem accW_prodV (m : Mem) (b : Addr) : accW ACC m b 12 = prodV m b := by
  rw [accW_eq]
  simp only [colsV, prodV, upW, T, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.zero_add,
    Nat.reducePow, Nat.one_mul]
  omega_using []

/-- `b + o` from `W`, for `b = W + e`. -/
theorem off_add (W : Addr) (e o : Nat) :
    W + BitVec.ofNat 64 e + BitVec.ofNat 64 o = W + BitVec.ofNat 64 (e + o) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- The five doublewords at `W + x`, through a frame of a region apart from them. -/
theorem d5_frame {m m' : Mem} {W : Addr} {e k x : Nat} (hf : Frame [⟨W + BitVec.ofNat 64 e, k⟩] m m')
    (hd : x + 40 ≤ e ∨ e + k ≤ x) (hx : x + 40 ≤ 2 ^ 64) (he : e + k ≤ 2 ^ 64) :
    d5 m' (W + BitVec.ofNat 64 x) = d5 m (W + BitVec.ofNat 64 x) := by
  rw [d5_add, d5_add]
  exact val5_congr fun i hi => dw_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint W (by omega_using [hd, hi]) (by omega_using [hx, hi]) he

/-- The working space at `W`, its own area from `W + 2048`, and `a3` its base. -/
structure WsAt (W : Addr) (s : State) : Prop where
  al : W.toNat % 8 = 0
  wr : (⟨W, 8192⟩ : Region) ∈ s.wr
  fit : W.toNat + 8192 ≤ 2 ^ 64
  a3 : s.gpr .a3 = W + BitVec.ofNat 64 2048

theorem WsAt.ctx {W : Addr} {s : State} (h : WsAt W s) : Ctx (W + BitVec.ofNat 64 2048) s :=
  ⟨h.a3, al8 h.al (by decide), fun d n hd => by
    rw [off_add]; exact VG.Proof.X25519.RISCV64.in_base h.wr (by omega_using [hd]) (by omega_using [hd])⟩

theorem WsAt.of_rest {W : Addr} {s s' : State} {ws : List Reg} (h : WsAt W s) (hr : Rest ws s s')
    (h3 : Reg.a3 ∉ ws) : WsAt W s' :=
  ⟨h.al, by rw [hr.wr]; exact h.wr, h.fit, by rw [hr.gpr _ h3, h.a3]⟩

/-- A pointer to the `40` bytes at `W + x` of the working space. -/
theorem WsAt.inR {W : Addr} {s : State} (h : WsAt W s) {x : Nat} (hx : x + 40 ≤ 8192) :
    ∀ j < 5, InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 x + BitVec.ofNat 64 (8 * j)) 8 := fun j hj => by
  rw [off_add]
  obtain ⟨r, hr, hc⟩ := VG.Proof.X25519.RISCV64.in_base (n := 8) h.wr (d := x + 8 * j) (by omega_using [hx, hj]) (by omega_using [hx, hj])
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem WsAt.inW {W : Addr} {s : State} (h : WsAt W s) {x : Nat} (hx : x + 40 ≤ 8192) :
    ∀ j < 5, InRegions s.wr (W + BitVec.ofNat 64 x + BitVec.ofNat 64 (8 * j)) 8 := fun j hj => by
  rw [off_add]
  exact VG.Proof.X25519.RISCV64.in_base h.wr (by omega_using [hx, hj]) (by omega_using [hx, hj])

/-- The regions `mulCore` writes, from `W`: the copies, the product and the result. -/
abbrev mulW (W : Addr) (o : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 3776, 40⟩, ⟨W + BitVec.ofNat 64 3816, 40⟩, ⟨W + BitVec.ofNat 64 3864, 96⟩,
    ⟨W + BitVec.ofNat 64 o, 40⟩, ⟨W + BitVec.ofNat 64 3776, 48⟩]

/-- An operand apart from the copies and the product. -/
abbrev Apart (x : Nat) : Prop := x + 40 ≤ 3776 ∨ 3960 ≤ x

/-- `mulWith red (sumWith ks)`: `[t2] = [t4] [t5] 2⁻³⁸⁴ mod m`, for a reduction
`red` that may write the product and the copy `MA` (as Gen5's `reduceR`,
which keeps registers there) and the words of `2³²⁰ - m` put into `t0` by
`ks`. -/
theorem mulWithF_ok {red : List Instr} {ks : List (List Instr)} {N : Nat → Nat} {M : Nat} (hM0 : 0 < M)
    (hN : ∀ j, N j < 2 ^ 64) (hk : ∀ j < 5, KOk (ks.getD j []) j N) (hNv : colsV N 5 + M = 2 ^ 320)
    (hred : ∀ {b : Addr} {s : State}, Ctx b s → upW s.mem b 10 2 = 0 → WP isa (.block red) s fun s' =>
      Ctx b s' ∧ Rest clobM s s' ∧ Frame [AR ACC b, ⟨b + BitVec.ofNat 64 MA, 48⟩] s.mem s'.mem ∧
      (s'.gpr XC).toNat ≤ 1 ∧
      ∃ Q, Q < 2 ^ 320 ∧ (xv s' + 2 ^ 320 * (s'.gpr XC).toNat) * 2 ^ 320 = prodV s.mem b + Q * M)
    {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 40 ≤ 8192) (hb : bb + 40 ≤ 8192) (ho : o + 40 ≤ 8192) (hdb : Apart bb)
    (hB : d5 s.mem (W + BitVec.ofNat 64 bb) < M) :
    WP isa (mulWith red (sumWith ks)) s fun s' =>
      d5 s'.mem (W + BitVec.ofNat 64 o) < M ∧
      d5 s'.mem (W + BitVec.ofNat 64 o) * 2 ^ 320 % M =
        d5 s.mem (W + BitVec.ofNat 64 a) * d5 s.mem (W + BitVec.ofNat 64 bb) % M ∧
      Frame (mulW W o) s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hc := hw.ctx
  obtain alA : (W + BitVec.ofNat 64 a).toNat % 8 = 0 := al8 hw.al ha8
  obtain alB : (W + BitVec.ofNat 64 bb).toNat % 8 = 0 := al8 hw.al hb8
  obtain eMA : W + BitVec.ofNat 64 2048 + BitVec.ofNat 64 MA = W + BitVec.ofNat 64 3776 := off_add _ _ _
  obtain eMB : W + BitVec.ofNat 64 2048 + BitVec.ofNat 64 MB = W + BitVec.ofNat 64 3816 := off_add _ _ _
  obtain eAC : W + BitVec.ofNat 64 2048 + BitVec.ofNat 64 ACC = W + BitVec.ofNat 64 3864 := off_add _ _ _
  -- The product at `ACC`, by either branch.
  obtain hprod : WP isa prodCode s fun s' =>
      Ctx (W + BitVec.ofNat 64 2048) s' ∧ Rest clob64 s s' ∧ Frame (mulW W o) s.mem s'.mem ∧
      prodV s'.mem (W + BitVec.ofNat 64 2048) =
        d5 s.mem (W + BitVec.ofNat 64 a) * d5 s.mem (W + BitVec.ofNat 64 bb) := by
    refine WP.ite (s.gpr .t4 == s.gpr .t5) rfl (fun heq => ?_) (fun _ => ?_)
    · have hab : W + BitVec.ofNat 64 a = W + BitVec.ofNat 64 bb := by
        rw [← h4, ← h5]; exact beq_iff_eq.mp heq
      refine WP.block_append (WP.mono (copyIn_ok hc (p := .t4) h4 (by decide) alA (hw.inR ha)
        (o := MA) (by decide) (by decide)) fun s1 ⟨c1, r1, f1, v1⟩ => ?_)
      refine WP.mono (square_ok (acc := ACC) (x := MA) (by decide) (by decide) (by decide) (by decide) c1)
        fun s2 ⟨c2, r2, f2, v2⟩ => ⟨c2, (r1.mono (by decide)).trans r2, ?_, ?_⟩
      · rw [eMA] at f1
        simp only [AR, eAC] at f2
        exact (f1.mono (by simp)).trans (f2.mono (by simp))
      · rw [← accW_prodV, v2, ← d5_add, v1, ← hab]
    · refine WP.block_append (WP.block_append (WP.mono
        (copyIn_ok hc (p := .t4) h4 (by decide) alA (hw.inR ha) (o := MA) (by decide) (by decide))
        fun s1 ⟨c1, r1, f1, v1⟩ => WP.mono (copyIn_ok c1 (p := .t5) (by rw [r1.gpr _ (by decide), h5])
          (by decide) alB ((hw.of_rest r1 (by decide)).inR hb) (o := MB) (by decide) (by decide))
        fun s2 ⟨c2, r2, f2, v2⟩ => ?_))
      refine WP.mono (product_ok (acc := ACC) (x := MA) (y := MB) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) c2) fun s3 ⟨c3, r3, f3, v3⟩ => ⟨c3, ((r1.trans r2).mono (by decide)).trans r3, ?_, ?_⟩
      · rw [eMA] at f1
        rw [eMB] at f2
        simp only [AR, eAC] at f3
        exact ((f1.mono (by simp)).trans (f2.mono (by simp))).trans (f3.mono (by simp))
      · rw [eMA] at f1 v1
        rw [eMB] at f2 v2
        rw [← accW_prodV, v3, ← d5_add, ← d5_add, eMA, eMB, v2, d5_frame f1 (by unfold Apart at hdb; omega_using [hdb])
          (by omega_using [hb]) (by omega_using []), d5_frame f2 (x := 3776) (by omega_using []) (by omega_using []) (by omega_using []), v1]
  refine WP.seq (WP.mono hprod fun s1 ⟨c1, r1, f1, v1⟩ => ?_)
  obtain hz1 : upW s1.mem (W + BitVec.ofNat 64 2048) 10 2 = 0 := by
    refine upW_hi_zero ?_
    obtain hA : d5 s.mem (W + BitVec.ofNat 64 a) < (2 ^ 64) ^ 5 := two320 ▸ d5_lt _ _
    obtain hM : M ≤ (2 ^ 64) ^ 5 := two320 ▸ (hNv ▸ Nat.le_add_left M _)
    rw [v1, show ((2 : Nat) ^ 64) ^ 10 = (2 ^ 64) ^ 5 * (2 ^ 64) ^ 5 by rw [← Nat.pow_add]]
    exact Nat.mul_lt_mul_of_lt_of_le hA (Nat.le_trans (Nat.le_of_lt hB) hM) (Nat.pos_of_ne_zero (by decide))
  refine WP.block_append (WP.mono (hred c1 hz1) fun s2 ⟨c2, r2, f2, x2, Q, hQ, hv2⟩ => ?_)
  obtain r12 : Rest clobM s s2 := (r1.mono (by decide) : Rest clobM _ _).trans r2
  obtain hw2 : WsAt W s2 := hw.of_rest r12 (by decide)
  obtain hlt : prodV s1.mem (W + BitVec.ofNat 64 2048) < 2 ^ 320 * M := by
    rw [v1]
    exact @Nat.mul_lt_mul_of_lt_of_le (d5 s.mem (W + BitVec.ofNat 64 a)) (2 ^ 320)
      (d5 s.mem (W + BitVec.ofNat 64 bb)) M (d5_lt _ _) (Nat.le_of_lt hB) hM0
  obtain hx : xv s2 + 2 ^ 320 * (s2.gpr XC).toNat < 2 * M := by
    generalize xv s2 + 2 ^ 320 * (s2.gpr XC).toNat = x at hv2 ⊢
    generalize (2 : Nat) ^ 320 = R at hQ hv2 hlt ⊢
    obtain h1 : Q * M < R * M := Nat.mul_lt_mul_of_pos_right hQ hM0
    obtain h2 : x * R < 2 * M * R := by
      rw [hv2]
      calc _ < R * M + R * M := Nat.add_lt_add hlt h1
        _ = 2 * M * R := by rw [← Nat.two_mul, Nat.mul_comm R M, Nat.mul_assoc]
    exact Nat.lt_of_mul_lt_mul_right h2
  refine WP.mono (csubWith_ok hN hk hNv (O := W + BitVec.ofNat 64 o) (by rw [r12.gpr _ (by decide), h2])
    (al8 hw.al ho8) (hw2.inW ho) x2 hx) fun s3 ⟨v3, f3, g3, rd3, wr3, sp3⟩ => ?_
  refine ⟨by rw [v3]; exact Nat.mod_lt _ hM0, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [v3, Nat.mod_mul_mod, hv2, Nat.add_mul_mod_self_right, v1]
  · simp only [AR, eAC, eMA] at f2
    exact f1.trans ((f2.mono (by simp)).trans (f3.mono (by simp)))
  · have sC : ∀ x ∈ clobC, x ∈ clobM := by decide
    rw [g3 r (fun h => hr (sC r h)), r12.gpr r hr]
  · rw [rd3, r2.rd, r1.rd]
  · rw [wr3, r2.wr, r1.wr]
  · rw [sp3, r2.sp, r1.sp]

/-- `mulWith red (sumWith ks)` for a reduction `red` as `reduce_ok`'s, which
writes only the product. -/
theorem mulWith_ok {red : List Instr} {ks : List (List Instr)} {N : Nat → Nat} {M : Nat} (hM0 : 0 < M)
    (hN : ∀ j, N j < 2 ^ 64) (hk : ∀ j < 5, KOk (ks.getD j []) j N) (hNv : colsV N 5 + M = 2 ^ 320)
    (hred : ∀ {b : Addr} {s : State}, Ctx b s → upW s.mem b 10 2 = 0 → WP isa (.block red) s fun s' =>
      Ctx b s' ∧ Rest clobM s s' ∧ Frame [AR ACC b] s.mem s'.mem ∧ (s'.gpr XC).toNat ≤ 1 ∧
      ∃ Q, Q < 2 ^ 320 ∧ (xv s' + 2 ^ 320 * (s'.gpr XC).toNat) * 2 ^ 320 = prodV s.mem b + Q * M)
    {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 40 ≤ 8192) (hb : bb + 40 ≤ 8192) (ho : o + 40 ≤ 8192) (hdb : Apart bb)
    (hB : d5 s.mem (W + BitVec.ofNat 64 bb) < M) :
    WP isa (mulWith red (sumWith ks)) s fun s' =>
      d5 s'.mem (W + BitVec.ofNat 64 o) < M ∧
      d5 s'.mem (W + BitVec.ofNat 64 o) * 2 ^ 320 % M =
        d5 s.mem (W + BitVec.ofNat 64 a) * d5 s.mem (W + BitVec.ofNat 64 bb) % M ∧
      Frame (mulW W o) s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  mulWithF_ok hM0 hN hk hNv (fun hc hz => WP.mono (hred hc hz) fun _ ⟨c, r, f, x, v⟩ =>
    ⟨c, r, f.mono (by simp), x, v⟩) hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB

end VG.Proof.Weierstrass.RISCV64.Gen5

namespace VG.Proof.Weierstrass.RISCV64.Gen5

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.Gen5
open VG.Proof.X25519.RISCV64 (Ctx Rest)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt clob64 al8 colsV dw_write_self dw_write_other)
open VG.Proof.Weierstrass.RISCV64.P256Field (adc_ok sbb_ok upd_keeps)
open VG.Impl.Weierstrass.RISCV64.P384Field (X XC XR sumWord selWord adcWord sbbWord addMWord movAB zext ptrs)
open VG.Proof.Weierstrass.RISCV64.P384Field (colsV_lt_of colsV_congr AR)

/-- The registers of a sum or a difference. -/
abbrev clobS : List Reg := [.t5, .t6, .t3, .t4, .a1, .a4, .a2, .a5, .a6, .t0]

/-- Word `j` of both operands, at `a0` and `a7`, into `X j` and `a5`. -/
theorem ld2_ok {A B : Addr} {s : State} (hA : s.gpr .a0 = A) (hB : s.gpr .a7 = B) {j : Nat} (hj : j < 5)
    (halA : A.toNat % 8 = 0) (halB : B.toNat % 8 = 0)
    (hrA : ∀ j < 5, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * j)) 8)
    (hrB : ∀ j < 5, InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (8 * j)) 8)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', (s'.gpr (X j)).toNat = dw s.mem A (8 * j) → (s'.gpr .a5).toNat = dw s.mem B (8 * j) →
      Keeps [X j, .a5] s s' → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d (X j) .a0 (8 * j) :: .load .d .a5 .a7 (8 * j) :: is)) s Q := by
  obtain ⟨-, x5, -, x7, -, xa, -⟩ := X_facts j hj
  refine wp_ld (by omega_using [hj]) (by rw [hA]) (al8 halA (by omega_using [])) (hrA j hj) fun s1 u1 => ?_
  refine wp_ld (by omega_using [hj]) (by rw [u1.other _ (Ne.symm x7), hB]) (al8 halB (by omega_using []))
    (by rw [u1.rd, u1.wr]; exact hrB j hj) fun s2 u2 => ?_
  exact k s2 (by rw [u2.other _ x5, u1.gpr]; rfl) (by rw [u2.gpr, u1.mem]; rfl)
    ((upd_keeps u1).trans (upd_keeps u2))

/-- After `j` words of the sum of `[A]` and `[B]`, from `s0`. -/
structure AddInv (A B : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobS → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  cy : (s.gpr .a2).toNat ≤ 1
  val : colsV (fun k => (s.gpr (X k)).toNat) j + (2 ^ 64) ^ j * (s.gpr .a2).toNat =
    colsV (fun k => dw s0.mem A (8 * k) + dw s0.mem B (8 * k)) j

theorem X_clobS : ∀ j < 5, X j ∈ clobS := by decide

/-- Word `j` of the sum. -/
theorem addStep_ok {A B : Addr} {s0 : State} (hA : s0.gpr .a0 = A) (hB : s0.gpr .a7 = B)
    (halA : A.toNat % 8 = 0) (halB : B.toNat % 8 = 0)
    (hrA : ∀ j < 5, InRegions (s0.rd ++ s0.wr) (A + BitVec.ofNat 64 (8 * j)) 8)
    (hrB : ∀ j < 5, InRegions (s0.rd ++ s0.wr) (B + BitVec.ofNat 64 (8 * j)) 8)
    {j : Nat} (hj : j < 5) {s : State} (h : AddInv A B s0 j s) :
    WP isa (.block (([.load .d (X j) .a0 (8 * j), .load .d .a5 .a7 (8 * j)] : List Instr) ++ adcWord (X j) .a5)) s
      (AddInv A B s0 (j + 1)) := by
  obtain ⟨x2, x5, x6, -, -, -, -, -, -, -, xne⟩ := X_facts j hj
  obtain rd : s.rd ++ s.wr = s0.rd ++ s0.wr := by rw [h.rd, h.wr]
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine ld2_ok (by rw [h.gpr _ (by decide), hA]) (by rw [h.gpr _ (by decide), hB]) hj halA halB
    (by rw [rd]; exact hrA) (by rw [rd]; exact hrB) fun s1 ex ey k1 => ?_
  refine WP.mono (adc_ok (d := X j) (x := X j) (y := .a5) (c := .a2) (u := .a6) x5 x2 (Ne.symm x6) (by decide))
    fun s2 ⟨e2, k2⟩ => ?_
  obtain ec : s1.gpr .a2 = s.gpr .a2 := k1.1 _ (by simp [Ne.symm x2])
  obtain e2' := e2 (by rw [ec]; exact h.cy)
  rw [ex, ey, ec, h.mem] at e2'
  obtain g : ∀ k < 5, k ≠ j → s2.gpr (X k) = s.gpr (X k) := fun k hk hkj => by
    obtain ⟨y2, y5, y6, -⟩ := X_facts k hk
    rw [k2.1 _ (by simp [xne k hk hkj, y6, y2]), k1.1 _ (by simp [xne k hk hkj, y5])]
  obtain kk := k1.trans k2
  refine ⟨fun r hr => ?_, by rw [kk.2.1, h.mem], by rw [kk.2.2.1, h.rd], by rw [kk.2.2.2.1, h.wr],
    by rw [kk.2.2.2.2, h.sp], ?_, ?_⟩
  · have n1 : r ≠ X j := fun e => hr (e ▸ X_clobS j hj)
    obtain n5 : r ≠ .a5 := fun e => hr (by rw [e]; decide)
    obtain n6 : r ≠ .a6 := fun e => hr (by rw [e]; decide)
    obtain n2 : r ≠ .a2 := fun e => hr (by rw [e]; decide)
    rw [k2.1 r (by simp [n1, n6, n2]), k1.1 r (by simp [n1, n5]), h.gpr r hr]
  · have := (s2.gpr (X j)).isLt
    have := dw_lt s0.mem A (8 * j); have := dw_lt s0.mem B (8 * j); have := h.cy
    omega_arith
  · have hv := h.val
    obtain hc : colsV (fun k => (s2.gpr (X k)).toNat) j = colsV (fun k => (s.gpr (X k)).toNat) j :=
      colsV_congr' fun k hk => by rw [g k (by omega_using [hj, hk]) (by omega_using [hk])]
    show colsV (fun k => (s2.gpr (X k)).toNat) j + (2 ^ 64) ^ j * (s2.gpr (X j)).toNat +
        (2 ^ 64) ^ (j + 1) * (s2.gpr .a2).toNat =
      colsV (fun k => dw s0.mem A (8 * k) + dw s0.mem B (8 * k)) j +
        (2 ^ 64) ^ j * (dw s0.mem A (8 * j) + dw s0.mem B (8 * j))
    rw [hc, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ .., ← hv]
    generalize (2 ^ 64) ^ j = E at *
    generalize colsV (fun k => (s.gpr (X k)).toNat) j = C at *
    obtain key : E * (s2.gpr (X j)).toNat + E * 2 ^ 64 * (s2.gpr .a2).toNat =
        E * (s.gpr .a2).toNat + E * (dw s0.mem A (8 * j) + dw s0.mem B (8 * j)) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, e2']; congr 1; omega_using []
    omega_using [key]

/-- `movAB` and the carry or borrow zeroed: from `s`, with `a0 = [t4]`, `a7 = [t5]`. -/
theorem movAB_ok {s : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .a0 = s.gpr .t4 → s'.gpr .a7 = s.gpr .t5 → (s'.gpr .a2).toNat = 0 →
      Rest [.a0, .a7, .a2] s s' → s'.mem = s.mem → WP isa (.block is) s' Q) :
    WP isa (.block (movAB ++ .li .a2 0 :: is)) s Q := by
  unfold movAB
  refine wp_addi (imm := 0) (by decide) fun s1 u1 => wp_addi (imm := 0) (by decide) fun s2 u2 =>
    wp_li (imm := 0) (by decide) fun s3 u3 => k s3 ?_ ?_ (by rw [u3.gpr]; rfl)
      ((u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))))
      (by rw [u3.mem, u2.mem, u1.mem])
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; simp
  · rw [u3.other _ (by decide), u2.gpr, u1.other _ (by decide)]; simp

/-- The sum of `[t4]` and `[t5]` into `X` and `XC`. -/
theorem addSum_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ha : a + 40 ≤ 8192) (hb : bb + 40 ≤ 8192) :
    WP isa (.block addSum) s fun s' =>
      xv s' + 2 ^ 320 * (s'.gpr XC).toNat = d5 s.mem (W + BitVec.ofNat 64 a) + d5 s.mem (W + BitVec.ofNat 64 bb) ∧
      (s'.gpr XC).toNat ≤ 1 ∧ Rest clobM s s' ∧ s'.mem = s.mem := by
  unfold addSum
  refine movAB_ok fun s1 e0 e7 e2 r1 m1 => ?_
  obtain hw1 : WsAt W s1 := hw.of_rest r1 (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (AddInv (W + BitVec.ofNat 64 a) (W + BitVec.ofNat 64 bb) s1)
    (fun j s hj h => addStep_ok (by rw [e0, h4]) (by rw [e7, h5]) (al8 hw.al ha8) (al8 hw.al hb8)
      (hw1.inR ha) (hw1.inR hb) hj h) 5 (Nat.le_refl _) s1
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, by rw [e2]; omega_using [], by simp only [colsV, e2]⟩) fun s2 h2 => ?_
  have hv := h2.val
  rw [VG.Proof.X448.RISCV64.R64.colsV_add, m1] at hv
  refine ⟨by rw [two320]; exact hv, h2.cy, r1.mono (by decide) |>.trans ⟨fun r hr => h2.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h | h | h | h | h | h | h | h | h <;> simp [h])), h2.rd, h2.wr, h2.sp⟩,
    by rw [h2.mem, m1]⟩

/-- After `j` words of the difference of `[A]` and `[B]`, from `s0`. -/
structure SubInv (A B : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobS → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  cy : (s.gpr .a2).toNat ≤ 1
  val : colsV (fun k => (s.gpr (X k)).toNat) j + colsV (fun k => dw s0.mem B (8 * k)) j =
    colsV (fun k => dw s0.mem A (8 * k)) j + (2 ^ 64) ^ j * (s.gpr .a2).toNat

/-- Word `j` of the difference. -/
theorem subStep_ok {A B : Addr} {s0 : State} (hA : s0.gpr .a0 = A) (hB : s0.gpr .a7 = B)
    (halA : A.toNat % 8 = 0) (halB : B.toNat % 8 = 0)
    (hrA : ∀ j < 5, InRegions (s0.rd ++ s0.wr) (A + BitVec.ofNat 64 (8 * j)) 8)
    (hrB : ∀ j < 5, InRegions (s0.rd ++ s0.wr) (B + BitVec.ofNat 64 (8 * j)) 8)
    {j : Nat} (hj : j < 5) {s : State} (h : SubInv A B s0 j s) :
    WP isa (.block (([.load .d (X j) .a0 (8 * j), .load .d .a5 .a7 (8 * j)] : List Instr) ++ sbbWord (X j) .a5)) s
      (SubInv A B s0 (j + 1)) := by
  obtain ⟨x2, x5, x6, -, x0, -, -, -, -, -, xne⟩ := X_facts j hj
  obtain rd : s.rd ++ s.wr = s0.rd ++ s0.wr := by rw [h.rd, h.wr]
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine ld2_ok (by rw [h.gpr _ (by decide), hA]) (by rw [h.gpr _ (by decide), hB]) hj halA halB
    (by rw [rd]; exact hrA) (by rw [rd]; exact hrB) fun s1 ex ey k1 => ?_
  refine WP.mono (sbb_ok (d := X j) (x := X j) (y := .a5) (c := .a2) (u := .a6) (v := .t0) x2 (Ne.symm x6)
    (by decide) (Ne.symm x0) (by decide) (by decide) (Ne.symm x6) (by decide)) fun s2 ⟨e2, k2⟩ => ?_
  obtain ec : s1.gpr .a2 = s.gpr .a2 := k1.1 _ (by simp [Ne.symm x2])
  obtain e2' := e2 (by rw [ec]; exact h.cy)
  rw [ex, ey, ec, h.mem] at e2'
  obtain g : ∀ k < 5, k ≠ j → s2.gpr (X k) = s.gpr (X k) := fun k hk hkj => by
    obtain ⟨y2, y5, y6, -, y0, -⟩ := X_facts k hk
    rw [k2.1 _ (by simp [xne k hk hkj, y6, y2, y0]), k1.1 _ (by simp [xne k hk hkj, y5])]
  obtain kk := k1.trans k2
  refine ⟨fun r hr => ?_, by rw [kk.2.1, h.mem], by rw [kk.2.2.1, h.rd], by rw [kk.2.2.2.1, h.wr],
    by rw [kk.2.2.2.2, h.sp], e2'.2, ?_⟩
  · have n1 : r ≠ X j := fun e => hr (e ▸ X_clobS j hj)
    obtain n5 : r ≠ .a5 := fun e => hr (by rw [e]; decide)
    obtain n6 : r ≠ .a6 := fun e => hr (by rw [e]; decide)
    obtain n2 : r ≠ .a2 := fun e => hr (by rw [e]; decide)
    obtain n0 : r ≠ .t0 := fun e => hr (by rw [e]; decide)
    rw [k2.1 r (by simp [n1, n6, n2, n0]), k1.1 r (by simp [n1, n5]), h.gpr r hr]
  · have hv := h.val
    obtain hc : colsV (fun k => (s2.gpr (X k)).toNat) j = colsV (fun k => (s.gpr (X k)).toNat) j :=
      colsV_congr' fun k hk => by rw [g k (by omega_using [hj, hk]) (by omega_using [hk])]
    show colsV (fun k => (s2.gpr (X k)).toNat) j + (2 ^ 64) ^ j * (s2.gpr (X j)).toNat +
        (colsV (fun k => dw s0.mem B (8 * k)) j + (2 ^ 64) ^ j * dw s0.mem B (8 * j)) =
      colsV (fun k => dw s0.mem A (8 * k)) j + (2 ^ 64) ^ j * dw s0.mem A (8 * j) +
        (2 ^ 64) ^ (j + 1) * (s2.gpr .a2).toNat
    rw [hc, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..]
    generalize (2 ^ 64) ^ j = E at *
    generalize colsV (fun k => (s.gpr (X k)).toNat) j = C at *
    obtain key : E * (s2.gpr (X j)).toNat + E * dw s0.mem B (8 * j) + E * (s.gpr .a2).toNat =
        E * dw s0.mem A (8 * j) + E * 2 ^ 64 * (s2.gpr .a2).toNat := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add, e2'.1]
    omega_using [hv, key]

/-- The difference of `[t4]` and `[t5]` into `X`, with its borrow in `a2`. -/
theorem subDiff_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ha : a + 40 ≤ 8192) (hb : bb + 40 ≤ 8192) :
    WP isa (.block subDiff) s fun s' =>
      xv s' + d5 s.mem (W + BitVec.ofNat 64 bb) = d5 s.mem (W + BitVec.ofNat 64 a) + 2 ^ 320 * (s'.gpr .a2).toNat ∧
      (s'.gpr .a2).toNat ≤ 1 ∧ Rest clobM s s' ∧ s'.mem = s.mem := by
  unfold subDiff
  refine movAB_ok fun s1 e0 e7 e2 r1 m1 => ?_
  obtain hw1 : WsAt W s1 := hw.of_rest r1 (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (SubInv (W + BitVec.ofNat 64 a) (W + BitVec.ofNat 64 bb) s1)
    (fun j s hj h => subStep_ok (by rw [e0, h4]) (by rw [e7, h5]) (al8 hw.al ha8) (al8 hw.al hb8)
      (hw1.inR ha) (hw1.inR hb) hj h) 5 (Nat.le_refl _) s1
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, by rw [e2]; omega_using [], by simp only [colsV, e2]⟩) fun s2 h2 => ?_
  have hv := h2.val
  rw [m1] at hv
  refine ⟨by rw [two320]; exact hv, h2.cy, r1.mono (by decide) |>.trans ⟨fun r hr => h2.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h | h | h | h | h | h | h | h | h <;> simp [h])), h2.rd, h2.wr, h2.sp⟩,
    by rw [h2.mem, m1]⟩

/-- A block that puts word `j` of `m` under the mask `t0` into `a6`. -/
def KMOk (k : List Instr) (j : Nat) (PW : Nat → Nat) : Prop :=
  ∀ s : State, IsMask (s.gpr .t0) →
    WP isa (.block k) s fun s' =>
      (s'.gpr .a6).toNat = (if s.gpr .t0 = BitVec.allOnes 64 then PW j else 0) ∧ Keeps [.a6, .a0] s s'

/-- The registers of the sum of `m` under the mask. -/
abbrev clobA : List Reg := [.t5, .t6, .t3, .t4, .a1, .a4, .a0, .a6, .a7]

/-- After `j` words of `x + (m ∧ M)` from `s0`, stored at `O` (in `t2`). -/
structure AddMInv (O : Addr) (PW : Nat → Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobA → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨O, 40⟩] s0.mem s.mem
  hi : ∀ k, j ≤ k → k < 5 → s.gpr (X k) = s0.gpr (X k)
  cy : (s.gpr .a7).toNat ≤ 1
  val : colsV (fun k => dw s.mem O (8 * k)) j + (2 ^ 64) ^ j * (s.gpr .a7).toNat =
    colsV (fun k => (s0.gpr (X k)).toNat + if s0.gpr .t0 = BitVec.allOnes 64 then PW k else 0) j

theorem X_clobA : ∀ j < 5, X j ∈ clobA := by decide

/-- Word `j` of `x + (m ∧ M)`. -/
theorem addMStep_ok {O : Addr} {PW : Nat → Nat} (hP : ∀ j, PW j < 2 ^ 64) {k : List Instr} {j : Nat}
    (hj : j < 5) (hk : KMOk k j PW) (hal : O.toNat % 8 = 0) {s0 s : State} (h2 : s0.gpr .t2 = O)
    (hm : IsMask (s0.gpr .t0))
    (hw : ∀ j < 5, InRegions s0.wr (O + BitVec.ofNat 64 (8 * j)) 8) (h : AddMInv O PW s0 j s) :
    WP isa (.block (k ++ addMWord j)) s (AddMInv O PW s0 (j + 1)) := by
  obtain ⟨-, -, x6, x7, x0, xa, -, x2, -, -, xne⟩ := X_facts j hj
  have ht0 : s.gpr .t0 = s0.gpr .t0 := h.gpr _ (by decide)
  refine WP.block_append (WP.mono (hk s (by rw [ht0]; exact hm)) fun s1 ⟨e1, k1⟩ => ?_)
  rw [ht0] at e1
  unfold addMWord
  refine WP.block_append (WP.mono (adc_ok (d := X j) (x := X j) (y := .a6) (c := .a7) (u := .a0) x6 x7
    (Ne.symm xa) (by decide)) fun s2 ⟨e2, k2⟩ => ?_)
  have g2 : ∀ r, r ∉ clobA → s2.gpr r = s0.gpr r := fun r hr => by
    have n1 : r ≠ X j := fun e => hr (e ▸ X_clobA j hj)
    have n6 : r ≠ .a6 := fun e => hr (by rw [e]; decide)
    have n7 : r ≠ .a7 := fun e => hr (by rw [e]; decide)
    have n0 : r ≠ .a0 := fun e => hr (by rw [e]; decide)
    rw [k2.1 _ (by simp [n1, n0, n7]), k1.1 _ (by simp [n6, n0]), h.gpr r hr]
  have p2 : s2.gpr .t2 + BitVec.ofNat 64 (8 * j) = O + BitVec.ofNat 64 (8 * j) := by
    rw [g2 _ (by decide), h2]
  refine wp_sd (by omega_using [hj]) p2 (al8 hal (by omega_using [])) (by rw [k2.2.2.2.1, k1.2.2.2.1, h.wr]; exact hw j hj)
    fun s3 u3 => WP.block_nil ?_
  have ex : s1.gpr (X j) = s0.gpr (X j) := by
    rw [k1.1 _ (by simp [x6, xa]), h.hi j (Nat.le_refl _) hj]
  have ec : s1.gpr .a7 = s.gpr .a7 := k1.1 _ (by decide)
  have e2' := e2 (by rw [ec]; exact h.cy)
  rw [ex, ec, e1] at e2'
  have hm3 : s3.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j)) (s2.gpr (X j)) := by
    rw [u3.mem, k2.2.1, k1.2.1]
  have hPm : (if s0.gpr .t0 = BitVec.allOnes 64 then PW j else 0) < 2 ^ 64 := by
    split
    · exact hP j
    · omega_using []
  refine ⟨fun r hr => by rw [u3.gpr]; exact g2 r hr, by rw [u3.rd, k2.2.2.1, k1.2.2.1, h.rd],
    by rw [u3.wr, k2.2.2.2.1, k1.2.2.2.1, h.wr], by rw [u3.sp, k2.2.2.2.2, k1.2.2.2.2, h.sp], ?_,
    fun k hk hk' => ?_, ?_, ?_⟩
  · rw [hm3]; exact h.frame.writeW (List.mem_singleton_self _) _ (out_contains O hj)
  · obtain ⟨-, -, y6, y7, -, ya, -⟩ := X_facts k hk'
    rw [u3.gpr, k2.1 _ (by simp [xne k hk' (by omega_using [hk]), ya, y7]), k1.1 _ (by simp [y6, ya])]
    exact h.hi k (by omega_using [hk]) hk'
  · rw [u3.gpr]
    have := (s2.gpr (X j)).isLt; have := (s0.gpr (X j)).isLt; have := h.cy
    omega_using [e1, e2', this]
  · have hv := h.val
    have hc : colsV (fun k => dw s3.mem O (8 * k)) j = colsV (fun k => dw s.mem O (8 * k)) j :=
      colsV_congr' fun k hk => by rw [hm3, dw_write_other _ _ _ (by omega_using [hk]) (by omega_using [hj, hk]) (by omega_using [hj])]
    show colsV (fun k => dw s3.mem O (8 * k)) j + (2 ^ 64) ^ j * dw s3.mem O (8 * j) +
        (2 ^ 64) ^ (j + 1) * (s3.gpr .a7).toNat =
      colsV (fun k => (s0.gpr (X k)).toNat + if s0.gpr .t0 = BitVec.allOnes 64 then PW k else 0) j +
        (2 ^ 64) ^ j * ((s0.gpr (X j)).toNat + if s0.gpr .t0 = BitVec.allOnes 64 then PW j else 0)
    rw [hc, hm3, dw_write_self, u3.gpr, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..,
      ← hv]
    generalize (if s0.gpr .t0 = BitVec.allOnes 64 then PW j else 0) = y at *
    generalize (2 ^ 64) ^ j = E at *
    generalize colsV (fun k => dw s.mem O (8 * k)) j = C at *
    have key : E * (s2.gpr (X j)).toNat + E * 2 ^ 64 * (s2.gpr .a7).toNat =
        E * (s.gpr .a7).toNat + E * ((s0.gpr (X j)).toNat + y) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, e2']; congr 1; omega_using []
    omega_using [key]

/-- The mask of a borrow. -/
theorem neg_mask {c : BitVec 64} (hc : c.toNat ≤ 1) :
    IsMask (0 - c) ∧ (0 - c = BitVec.allOnes 64 ↔ c.toNat = 1) := by
  obtain hc' : c = 0 ∨ c = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  rcases hc' with rfl | rfl <;> (unfold IsMask; decide)

theorem colsV_ite (c : Prop) [Decidable c] (f : Nat → Nat) (n : Nat) :
    colsV (fun k => if c then f k else 0) n = if c then colsV f n else 0 := by
  split
  · rfl
  · induction n with
    | zero => rfl
    | succ n ih => simp only [colsV, ih]; simp [*]

/-- `subWith ks`: `[t2] = ([t4] - [t5]) mod m`, for operands below `m`, where
`ks[j]` puts word `j` of `m` under the mask `t0` into `a6`. -/
theorem subWith_ok {ks : List (List Instr)} {PW : Nat → Nat} {M : Nat} (hP : ∀ j, PW j < 2 ^ 64)
    (hk : ∀ j < 5, KMOk (ks.getD j []) j PW) (hPv : colsV PW 5 = M)
    {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha8 : a % 8 = 0) (hb8 : bb % 8 = 0) (ho8 : o % 8 = 0)
    (ha : a + 40 ≤ 8192) (hb : bb + 40 ≤ 8192) (ho : o + 40 ≤ 8192)
    (hA : d5 s.mem (W + BitVec.ofNat 64 a) < M) (hB : d5 s.mem (W + BitVec.ofNat 64 bb) < M) :
    WP isa (.block (subWith ks)) s fun s' =>
      d5 s'.mem (W + BitVec.ofNat 64 o) =
        (d5 s.mem (W + BitVec.ofNat 64 a) + M - d5 s.mem (W + BitVec.ofNat 64 bb)) % M ∧
      Frame [⟨W + BitVec.ofNat 64 o, 40⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold subWith
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (subDiff_ok hw h4 h5 ha8 hb8 ha hb) fun s1 ⟨v1, c1, r1, m1⟩ => ?_)
  rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_li (imm := 0) (by decide) fun s2 u2 => wp_sub fun s3 u3 => wp_li (imm := 0) (by decide)
    fun s4 u4 => ?_
  obtain hm : IsMask (s4.gpr .t0) ∧ (s4.gpr .t0 = BitVec.allOnes 64 ↔ (s1.gpr .a2).toNat = 1) := by
    rw [u4.other _ (by decide), u3.gpr, u2.gpr, u2.other _ (by decide)]
    exact neg_mask c1
  obtain r4 : Rest clobM s s4 := r1.trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
    (u4.rest (by decide))))
  obtain hw4 : WsAt W s4 := hw.of_rest r4 (by decide)
  obtain p4 : s4.gpr .t2 = W + BitVec.ofNat 64 o := by rw [r4.gpr _ (by decide), h2]
  refine WP.mono (wp_range_flatMap (M := isa) (AddMInv (W + BitVec.ofNat 64 o) PW s4)
    (fun j s hj h => addMStep_ok hP hj (hk j hj) (al8 hw.al ho8) p4 hm.1 (hw4.inW ho) h) 5 (Nat.le_refl _) s4
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl, by rw [u4.gpr]; decide,
      by simp only [colsV, u4.gpr]; rfl⟩) fun s5 h5 => ?_
  obtain hx4 : ∀ k < 5, s4.gpr (X k) = s1.gpr (X k) := fun k hk => by
    obtain ⟨-, -, -, x7, x0, -⟩ := X_facts k hk
    rw [u4.other _ x7, u3.other _ x0, u2.other _ x0]
  obtain hm4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, m1]
  have hv := h5.val
  rw [VG.Proof.X448.RISCV64.R64.colsV_add, colsV_ite, hPv] at hv
  obtain hxv : colsV (fun k => (s4.gpr (X k)).toNat) 5 = xv s1 := colsV_congr' fun k hk => by rw [hx4 k hk]
  rw [hxv] at hv
  obtain hd := d5_lt s5.mem (W + BitVec.ofNat 64 o)
  obtain hY : xv s1 < 2 ^ 320 := by rw [two320]; exact colsV_lt_of _ (fun _ => BitVec.isLt _) 5
  obtain hMl : M < 2 ^ 320 := by rw [two320, ← hPv]; exact colsV_lt_of PW hP 5
  have hc7 := h5.cy
  refine ⟨?_, by rw [← hm4]; exact h5.frame, fun r hr => ?_, by rw [h5.rd, r4.rd], by rw [h5.wr, r4.wr],
    by rw [h5.sp, r4.sp]⟩
  · have hge := hm.2
    replace hv : d5 s5.mem (W + BitVec.ofNat 64 o) + 2 ^ 320 * (s5.gpr .a7).toNat =
        xv s1 + if s4.gpr .t0 = BitVec.allOnes 64 then M else 0 := by
      rw [two320]; exact hv
    generalize d5 s5.mem (W + BitVec.ofNat 64 o) = D at *
    generalize xv s1 = Y at *
    generalize d5 s.mem (W + BitVec.ofNat 64 a) = A at *
    generalize d5 s.mem (W + BitVec.ofNat 64 bb) = B at *
    split at hv
    · rename_i h
      obtain h1 := hge.mp h
      rw [h1] at v1
      obtain hAB : A < B := by omega_using [hY, v1]
      obtain hlt : A + M - B < M := by omega_using [hA, hAB]
      rw [Nat.mod_eq_of_lt hlt]
      omega_using [hMl, hd, hB, v1, hv, hAB]
    · rename_i h
      obtain h0 : (s1.gpr .a2).toNat = 0 := by
        have := c1; have : ¬ (s1.gpr .a2).toNat = 1 := fun h' => h (hge.mpr h'); omega_using [c1, this]
      rw [h0] at v1
      obtain hBA : B ≤ A := by omega_using [v1]
      rw [show A + M - B = (A - B) + M by omega_using [v1], Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [hA])]
      omega_using [hY, v1, hv]
  · have hA' : r ∉ clobA := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h | h | h | h | h | h | h | h <;> simp [h])
    rw [h5.gpr r hA', r4.gpr r hr]

end VG.Proof.Weierstrass.RISCV64.Gen5

namespace VG.Proof.Weierstrass.RISCV64.Gen5

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Weierstrass.RISCV64.Gen5 VG.Proof.X25519.RISCV64
open VG.Proof.Ed25519.RISCV64 (not_a4_a5)
open VG.Impl.Weierstrass.RISCV64.P384Field (X XC XR sumWord selWord adcWord sbbWord addMWord movAB zext ptrs)
open VG.Proof.Weierstrass.RISCV64.P384Field (colsV_lt_of colsV_congr AR)

/-- After `k` words of `pack p a dst` from `s0`. -/
structure PackInv10 (b q : Addr) (a dst : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.a4, .a5] s0 s
  frame : Frame [⟨q + BitVec.ofNat 64 dst, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, wd s.mem q (dst + 4 * j) = limb s0.mem b a j

theorem pack10_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) {p : Reg}
    (hp : p ∉ [Reg.a4, .a5]) (h14 : s0.gpr p = q) {a dst : Nat}
    (ha : a + 40 ≤ 2048) (ha4 : a % 4 = 0) (hdst : dst + 40 < 2048)
    (hw : ∀ k < 10, InRegions s0.wr (q + BitVec.ofNat 64 (dst + 4 * k)) 4)
    (hd : (⟨q + BitVec.ofNat 64 dst, 40⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 a, 40⟩) :
    WP isa (.block (pack p a dst)) s0 (PackInv10 b q a dst s0 10) := by
  obtain hp' := not_a4_a5 hp
  refine wp_range_flatMap (M := isa) (PackInv10 b q a dst s0) (fun k s hk h => ?_)
    10 (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  obtain hcs : Ctx b s := hc.of_rest h.rest (by decide)
  refine lw0_ok hcs (d := a + 4 * k) (by omega_using [ha, hk]) (by omega_using [ha4]) fun t1 v1 => ?_
  obtain hq1 : t1.gpr p = q := by rw [v1.other _ hp'.1, h.rest.gpr _ hp, h14]
  refine WP.mono (ByteLoad.storeLE32_ok (v := .a4) (tmp := .a5) (n := p) (off := dst + 4 * k)
    (by decide) hp'.2.symm (by omega_using [hdst, hk]) (by rw [hq1, v1.wr, h.rest.wr]; exact hw k hk)) fun t2 e2 => ?_
  obtain em : t2.mem = s.mem.writeW (q + BitVec.ofNat 64 (dst + 4 * k)) ((t1.gpr .a4).setWidth 32) := by
    rw [e2, RegUpd.mem_write, hq1]
    show t1.mem.writeW _ _ = _
    rw [v1.mem]
  obtain hr2 : Rest [.a4, .a5] t1 t2 := by
    rw [e2]
    exact ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ (not_a4_a5 hr).2, rfl, rfl, rfl⟩
  obtain hsrc : wd s.mem b (a + 4 * k) = limb s0.mem b a k := by
    refine wd_frame h.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine fun x hx hx' => hd x ?_ ?_
    · exact Region.sub_prefix (by omega_using [hk]) x hx'
    · exact Offset.sub b (d := a + 4 * k) (n := 4) (e := a) (k := 40) (by omega_using []) (by omega_using [hk]) x hx
  refine ⟨h.rest.trans ((v1.rest (by decide)).trans hr2), ?_, fun j hj => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_add_right _ _) (by omega_using []) (by omega_using [hdst, hk]))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega_using [])
  · rw [em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega_using [hj]) (by omega_arith) (by omega_using [hdst, hk])]
      exact h.outs j hj
    · rw [wd_write_self, toNat_lo32, v1.gpr, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _)]
      exact hsrc

/-- After `k` words of `unpack p o src` from `s0`. -/
structure UnpackInv10 (b : Addr) (o : Nat) (s0 : State) (f : Nat → Nat) (k : Nat) (s : State) : Prop where
  rest : Rest [.a4, .a5] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, limb s.mem b o j = f j

/-- `unpack p o src`: the words at `src` from `p` into the element at `o`. -/
theorem unpack10_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) {p : Reg}
    (hp : p ∉ [Reg.a4, .a5]) (h14 : s0.gpr p = q) {o src : Nat}
    (ho : o + 40 ≤ 2048) (ho4 : o % 4 = 0) (hsrc : src + 40 < 2048)
    (hr : ∀ k < 10, InRegions (s0.rd ++ s0.wr) (q + BitVec.ofNat 64 (src + 4 * k)) 4)
    (hd : (⟨q + BitVec.ofNat 64 src, 40⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 o, 40⟩) :
    WP isa (.block (unpack p o src)) s0 fun t =>
      Rest [.a4, .a5] s0 t ∧ Frame [⟨b + BitVec.ofNat 64 o, 40⟩] s0.mem t.mem ∧
      ∀ j < 10, limb t.mem b o j = wd s0.mem q (src + 4 * j) := by
  obtain hp' := not_a4_a5 hp
  let f := fun k => wd s0.mem q (src + 4 * k)
  refine WP.mono (wp_range_flatMap (M := isa) (UnpackInv10 b o s0 f) (fun k s hk h => ?_)
    10 (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩)
    fun t ht => ⟨ht.rest, ht.frame, ht.outs⟩
  obtain hq : s.gpr p = q := by rw [h.rest.gpr _ hp, h14]
  refine WP.append (ByteLoad.loadLE32_ok (d := .a4) (tmp := .a5) (n := p) (off := src + 4 * k)
    hp'.1.symm hp'.2.symm (by decide) (by omega_using [hsrc, hk])
    (by rw [hq, h.rest.rd, h.rest.wr]; exact hr k hk)) fun t1 e1 => ?_
  obtain hr1 : Rest [.a4, .a5] s t1 := by
    rw [e1]
    refine ⟨fun r hr' => ?_, rfl, rfl, rfl⟩
    rw [RegUpd.gpr_write_of_ne _ _ (not_a4_a5 hr').1, RegUpd.gpr_write_of_ne _ _ (not_a4_a5 hr').2]
  obtain hm1 : t1.mem = s.mem := by rw [e1]; rfl
  obtain hv : (t1.gpr .a4).toNat % 2 ^ 32 = f k := by
    rw [e1, RegUpd.gpr_write_self, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _), hq]
    show wd s.mem q (src + 4 * k) = _
    refine wd_frame h.frame fun r hr' => ?_
    rw [List.mem_singleton.mp hr']
    refine fun x hx hx' => hd x ?_ ?_
    · exact Offset.sub q (d := src + 4 * k) (n := 4) (e := src) (k := 40) (by omega_using []) (by omega_using [hk]) x hx
    · exact Region.sub_prefix (by omega_using [hk]) x hx'
  refine sw0_ok ((hc.of_rest h.rest (by decide)).of_rest hr1 (by decide))
    (by omega_using [ho, hk]) (by omega_using [ho4]) fun u hu => WP.block_nil ?_
  obtain em : u.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 4 * k)) ((t1.gpr .a4).setWidth 32) := by
    rw [hu.mem, hm1]
  refine ⟨h.rest.trans (hr1.trans (hu.rest _)), ?_, fun j hj => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_add_right _ _) (by omega_using []) (by omega_using [ho, hk]))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega_using [])
  · rw [limb, em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega_using [hj]) (by omega_arith) (by omega_using [ho, hk])]
      exact h.outs j hj
    · rw [wd_write_self, toNat_lo32, hv]

end VG.Proof.Weierstrass.RISCV64.Gen5

namespace VG.Proof.Weierstrass.RISCV64.Gen5

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.Gen5
open VG.Proof.X25519.RISCV64 (Ctx Rest limb wd in_base)
open VG.Proof.X448.RISCV64.R64 (dw dw_split al8 colsV)
open VG.Impl.Weierstrass.RISCV64.P384Field (X XC XR sumWord selWord adcWord sbbWord addMWord movAB zext ptrs)
open VG.Proof.Weierstrass.RISCV64.P384Field (colsV_lt_of colsV_congr AR)

/-- Six doublewords are their twelve words. -/
theorem d5_congr_wd {m m' : Mem} {O O' : Addr} (h : ∀ j < 10, wd m' O' (4 * j) = wd m O (4 * j)) :
    d5 m' O' = d5 m O := by
  simp only [d5, colsV, dw_split, Nat.mul_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd]
  have e : ∀ j < 10, wd m' O' (4 * j) = wd m O (4 * j) := h
  rw [show (0 : Nat) = 4 * 0 from rfl, show (4 : Nat) = 4 * 1 from rfl, show (8 : Nat) = 4 * 2 from rfl,
    show (12 : Nat) = 4 * 3 from rfl, show (16 : Nat) = 4 * 4 from rfl, show (20 : Nat) = 4 * 5 from rfl,
    show (24 : Nat) = 4 * 6 from rfl, show (28 : Nat) = 4 * 7 from rfl, show (32 : Nat) = 4 * 8 from rfl,
    show (36 : Nat) = 4 * 9 from rfl]
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide), e 5 (by decide),
    e 6 (by decide), e 7 (by decide), e 8 (by decide), e 9 (by decide)]

theorem wd_off (m : Mem) (b : Addr) (o d : Nat) : wd m b (o + d) = wd m (b + BitVec.ofNat 64 o) d := by
  simp only [VG.Proof.X25519.RISCV64.wd, off_add]

/-- `unpack p o 0` of the operand at `W + x` into `W + 2048 + o`. -/
theorem unpack_ok {W : Addr} {s : State} (hw : WsAt W s) {p : Reg} (hp : p ∉ [Reg.a4, .a5]) {x : Nat}
    (h : s.gpr p = W + BitVec.ofNat 64 x) (hx : x + 40 ≤ 3776) {o : Nat} (ho : 1912 ≤ o) (ho' : o + 40 ≤ 2048)
    (ho4 : o % 4 = 0) :
    WP isa (.block (unpack p o 0)) s fun t =>
      Rest [.a4, .a5] s t ∧ Frame [⟨W + BitVec.ofNat 64 (2048 + o), 40⟩] s.mem t.mem ∧
      d5 t.mem (W + BitVec.ofNat 64 (2048 + o)) = d5 s.mem (W + BitVec.ofNat 64 x) := by
  refine WP.mono (unpack10_ok hw.ctx hp h (o := o) (src := 0) ho' ho4 (by decide)
    (fun k hk => by
      rw [Nat.zero_add, off_add]
      obtain ⟨r, hr, hc⟩ := in_base (n := 4) hw.wr (d := x + 4 * k) (by omega_using [hx, hk]) (by omega_using [hx, hk])
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [off_add, Nat.add_zero, off_add]; exact Offset.disjoint W (by omega_using [hx, ho]) (by omega_using [hx]) (by omega_using [ho'])))
    fun t ⟨r, f, v⟩ => ⟨r, by rw [off_add] at f; exact f, ?_⟩
  rw [← off_add]
  exact d5_congr_wd fun j hj => by rw [← wd_off, ← limb, v j hj, Nat.zero_add]

/-- The slow branch's copies in, and its pointers. -/
theorem slowIn_ok {W : Addr} {s : State} (hw : WsAt W s) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha : a + 40 ≤ 3776) (hb : bb + 40 ≤ 3776) :
    WP isa (.block (([.addi .t1 .t2 0] : List Instr) ++ unpack .t4 SA 0 ++
        unpack .t5 SB 0 ++ ([.addi .t4 .a3 SA, .addi .t5 .a3 SB, .addi .t2 .a3 SO] : List Instr))) s
      fun t => WsAt W t ∧ t.gpr .t1 = W + BitVec.ofNat 64 o ∧ t.gpr .t4 = W + BitVec.ofNat 64 3960 ∧
        t.gpr .t5 = W + BitVec.ofNat 64 4000 ∧ t.gpr .t2 = W + BitVec.ofNat 64 4040 ∧
        d5 t.mem (W + BitVec.ofNat 64 3960) = d5 s.mem (W + BitVec.ofNat 64 a) ∧
        d5 t.mem (W + BitVec.ofNat 64 4000) = d5 s.mem (W + BitVec.ofNat 64 bb) ∧
        Frame [⟨W + BitVec.ofNat 64 3960, 40⟩, ⟨W + BitVec.ofNat 64 4000, 40⟩] s.mem t.mem ∧
        Rest [.t1, .t2, .t4, .t5, .a4, .a5] s t := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mv fun s1 u1 => ?_
  obtain hw1 : WsAt W s1 := hw.of_rest (u1.rest (ws := [.t1]) (by decide)) (by decide)
  refine WP.block_append (WP.mono (unpack_ok hw1 (p := .t4) (by decide) (by rw [u1.other _ (by decide), h4]) ha
    (o := SA) (by decide) (by decide) (by decide)) fun s2 ⟨r2, f2, v2⟩ => ?_)
  obtain hw2 : WsAt W s2 := hw1.of_rest r2 (by decide)
  refine WP.block_append (WP.mono (unpack_ok hw2 (p := .t5) (by decide)
    (by rw [r2.gpr _ (by decide), u1.other _ (by decide), h5]) hb (o := SB) (by decide) (by decide) (by decide))
    fun s3 ⟨r3, f3, v3⟩ => ?_)
  obtain hw3 : WsAt W s3 := hw2.of_rest r3 (by decide)
  refine wp_addi (by decide) fun s4 u4 => wp_addi (by decide) fun s5 u5 => wp_addi (by decide) fun s6 u6 =>
    WP.block_nil ?_
  obtain a3 : ∀ t : State, WsAt W t → t.gpr .a3 = W + BitVec.ofNat 64 2048 := fun t h => h.a3
  obtain r6 : Rest [.t1, .t2, .t4, .t5, .a4, .a5] s s6 :=
    (u1.rest (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  obtain m6 : s6.mem = s3.mem := by rw [u6.mem, u5.mem, u4.mem]
  have f2' := f2
  rw [show 2048 + SA = 3960 from rfl] at f2' v2
  rw [show 2048 + SB = 4000 from rfl] at f3 v3
  refine ⟨hw.of_rest r6 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, r6⟩
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r3.gpr _ (by decide),
      r2.gpr _ (by decide), u1.gpr, h2]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, a3 s3 hw3, off_add]; rfl
  · rw [u6.other _ (by decide), u5.gpr, u4.other _ (by decide), a3 s3 hw3, off_add]; rfl
  · rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), a3 s3 hw3, off_add]; rfl
  · rw [m6, d5_frame f3 (by omega_using []) (by omega_using []) (by omega_using []), v2, u1.mem]
  · rw [m6, v3, d5_frame f2' (by omega_using [hb]) (by omega_using [hb]) (by omega_using []), u1.mem]
  · rw [m6, ← u1.mem]
    exact (f2'.mono (by simp)).trans (f3.mono (by simp))

/-- The slow branch's copy out: `[o]` from `SO`. -/
theorem slowOut_ok {W : Addr} {s : State} (hw : WsAt W s) {o : Nat}
    (h1 : s.gpr .t1 = W + BitVec.ofNat 64 o) (ho : o + 40 ≤ 3776) :
    WP isa (.block (pack .t1 SO 0)) s fun t =>
      Rest [.a4, .a5] s t ∧ Frame [⟨W + BitVec.ofNat 64 o, 40⟩] s.mem t.mem ∧
      d5 t.mem (W + BitVec.ofNat 64 o) = d5 s.mem (W + BitVec.ofNat 64 4040) := by
  refine WP.mono (pack10_ok hw.ctx (p := .t1) (by decide) h1 (a := SO) (dst := 0) (by decide) (by decide)
    (by decide) (fun k hk => by
      rw [Nat.zero_add, off_add]
      exact in_base (n := 4) hw.wr (by omega_using [ho, hk]) (by omega_using [ho, hk]))
    (by
      rw [off_add, Nat.add_zero, off_add]
      exact Offset.disjoint W (d := o) (n := 40) (e := 2048 + SO) (k := 40) (by unfold SO; omega_using [ho]) (by omega_using [ho])
        (by unfold SO; omega_using [])))
    fun t ht => ⟨ht.rest, ?_, ?_⟩
  · have f := ht.frame
    rw [off_add, Nat.add_zero] at f
    exact f
  · rw [show (4040 : Nat) = 2048 + SO from rfl, ← off_add]
    exact d5_congr_wd fun j hj => by
      have := ht.outs j hj
      rw [Nat.zero_add] at this
      rw [this, limb, wd_off]

end VG.Proof.Weierstrass.RISCV64.Gen5

namespace VG.Proof.Weierstrass.RISCV64.Gen5

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.Gen5
open VG.Proof.X25519.RISCV64 (Ctx Rest)
open VG.Proof.Weierstrass.RISCV64.P256Field (ptr_mod8 aligned_of ptrs_ok zext_ok)
open VG.Impl.Weierstrass.RISCV64.P384Field (X XC XR sumWord selWord adcWord sbbWord addMWord movAB zext ptrs)
open VG.Proof.Weierstrass.RISCV64.P384Field (colsV_lt_of colsV_congr AR)

/-- An offset argument: the low word of its register. -/
abbrev lo (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- What an operation on the pointers `t4`, `t5` and `t2` does, for operands
satisfying `pre`: its result `res` of the operands, written at `[t2]`. -/
def CoreOk (core : Prog isa) (pre : Nat → Nat → Prop) (res : Nat → Nat → Nat → Prop) : Prop :=
  ∀ {W : Addr} {s : State} {a bb o : Nat}, WsAt W s → s.gpr .t4 = W + BitVec.ofNat 64 a →
    s.gpr .t5 = W + BitVec.ofNat 64 bb → s.gpr .t2 = W + BitVec.ofNat 64 o → a % 8 = 0 → bb % 8 = 0 →
    o % 8 = 0 → a + 40 ≤ 8192 → bb + 40 ≤ 8192 → o + 40 ≤ 8192 → Apart bb →
    pre (d5 s.mem (W + BitVec.ofNat 64 a)) (d5 s.mem (W + BitVec.ofNat 64 bb)) →
    WP isa core s fun s' =>
      res (d5 s.mem (W + BitVec.ofNat 64 a)) (d5 s.mem (W + BitVec.ofNat 64 bb)) (d5 s'.mem (W + BitVec.ofNat 64 o)) ∧
      Frame (mulW W o) s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

/-- The registers the functions write. -/
abbrev clobF : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-- The regions the functions write: their own working space and the result. -/
abbrev fnW (W : Addr) (o : Nat) : List Region := [⟨W + BitVec.ofNat 64 3776, 320⟩, ⟨W + BitVec.ofNat 64 o, 40⟩]

theorem mulW_fnW (W : Addr) (o : Nat) {m m' : Mem} (h : Frame (mulW W o) m m') : Frame (fnW W o) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega_using []) (by omega_using [])⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega_using []) (by omega_using [])⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega_using []) (by omega_using [])⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega_using []) (by omega_using [])⟩

/-- `fnA core`, from the working space at `W` and offsets below its own
working space that are zero-extended multiples of 8 (P-256's `ptrsA`). -/
theorem fnA_ok {core : Prog isa} {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop}
    (hcore : CoreOk core pre res) {W : Addr} {s : State} (h0 : s.gpr .a0 = W) (hal : W.toNat % 8 = 0)
    (hwr : (⟨W, 8192⟩ : Region) ∈ s.wr) (hfit : W.toNat + 8192 ≤ 2 ^ 64)
    (ho : lo s .a1 + 40 ≤ 3776) (ha : lo s .a2 + 40 ≤ 3776) (hb : lo s .a3 + 40 ≤ 3776)
    (h1 : (s.gpr .a1).toNat < 2 ^ 32 ∧ (s.gpr .a1).toNat % 8 = 0)
    (h2 : (s.gpr .a2).toNat < 2 ^ 32 ∧ (s.gpr .a2).toNat % 8 = 0)
    (h3 : (s.gpr .a3).toNat < 2 ^ 32 ∧ (s.gpr .a3).toNat % 8 = 0)
    (hpre : pre (d5 s.mem (W + BitVec.ofNat 64 (lo s .a2))) (d5 s.mem (W + BitVec.ofNat 64 (lo s .a3)))) :
    WP isa (fnA core) s fun s' =>
      res (d5 s.mem (W + BitVec.ofNat 64 (lo s .a2))) (d5 s.mem (W + BitVec.ofNat 64 (lo s .a3)))
        (d5 s'.mem (W + BitVec.ofNat 64 (lo s .a1))) ∧
      Frame (fnW W (lo s .a1)) s.mem s'.mem ∧ (∀ r, r ∉ clobF → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold fnA
  refine WP.seq (WP.mono (VG.Proof.Weierstrass.RISCV64.P256Field.ptrsA_ok h0 h1.1 h2.1 h3.1)
    fun s1 ⟨p2, p4, p5, p3, r1, m1⟩ => ?_)
  obtain hlo : ∀ r, VG.Proof.Weierstrass.RISCV64.P256Field.lo s r = lo s r := fun _ => rfl
  rw [hlo] at p2 p4 p5
  obtain hw1 : WsAt W s1 := ⟨hal, by rw [r1.wr]; exact hwr, hfit, p3⟩
  obtain sub1 : ∀ x ∈ [Reg.a3, .t2, .t4, .t5], x ∈ clobF := by decide
  obtain subM : ∀ x ∈ clobM, x ∈ clobF := by decide
  obtain al : ∀ r, (s.gpr r).toNat < 2 ^ 32 ∧ (s.gpr r).toNat % 8 = 0 → lo s r % 8 = 0 := fun r hr => by
    rw [show lo s r = VG.Proof.Weierstrass.RISCV64.P256Field.lo s r from rfl,
      VG.Proof.Weierstrass.RISCV64.P256Field.lo_eq hr.1]; exact hr.2
  refine WP.mono (hcore hw1 p4 p5 p2 (al _ h2) (al _ h3) (al _ h1) (by omega_using [ha]) (by omega_using [hb]) (by omega_using [ho])
    (.inl (by omega_using [hb])) (by rw [m1]; exact hpre)) fun s2 ⟨v2, f2, g2, rd2, wr2, sp2⟩ =>
      ⟨by rw [← m1]; exact v2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← m1]; exact mulW_fnW W _ f2
  · intro r hr
    rw [g2 r (fun h => hr (subM r h)), r1.gpr r (fun h => hr (sub1 r h))]
  · rw [rd2, r1.rd]
  · rw [wr2, r1.wr]
  · rw [sp2, r1.sp]

/-- `fn core`, from the working space at `W` and offsets below its own working space. -/
theorem fn_ok {core : Prog isa} {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop}
    (hcore : CoreOk core pre res) {W : Addr} {s : State} (h0 : s.gpr .a0 = W) (hal : W.toNat % 8 = 0)
    (hwr : (⟨W, 8192⟩ : Region) ∈ s.wr) (hfit : W.toNat + 8192 ≤ 2 ^ 64)
    (ho : lo s .a1 + 40 ≤ 3776) (ha : lo s .a2 + 40 ≤ 3776) (hb : lo s .a3 + 40 ≤ 3776)
    (hpre : pre (d5 s.mem (W + BitVec.ofNat 64 (lo s .a2))) (d5 s.mem (W + BitVec.ofNat 64 (lo s .a3)))) :
    WP isa (fn core) s fun s' =>
      res (d5 s.mem (W + BitVec.ofNat 64 (lo s .a2))) (d5 s.mem (W + BitVec.ofNat 64 (lo s .a3)))
        (d5 s'.mem (W + BitVec.ofNat 64 (lo s .a1))) ∧
      Frame (fnW W (lo s .a1)) s.mem s'.mem ∧ (∀ r, r ∉ clobF → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold fn
  refine WP.seq (WP.mono (zext_ok s) fun s0 ⟨z0, r0, m0⟩ => ?_)
  refine WP.seq (WP.mono (ptrs_ok z0 h0) fun s1 ⟨p2, p4, p5, p3, p0, r1', m1'⟩ => ?_)
  obtain hlo : ∀ r, VG.Proof.Weierstrass.RISCV64.P256Field.lo s r = lo s r := fun _ => rfl
  rw [hlo] at p2 p4 p5 p0
  rw [hlo, hlo] at p0
  obtain r1 : Rest [.a1, .a2, .a3, .t0, .t2, .t4, .t5] s s1 := (r0.mono (by decide)).trans (r1'.mono (by decide))
  obtain m1 : s1.mem = s.mem := by rw [m1', m0]
  obtain hw1 : WsAt W s1 := ⟨hal, by rw [r1.wr]; exact hwr, hfit, p3⟩
  obtain sub1 : ∀ x ∈ [Reg.a1, .a2, .a3, .t0, .t2, .t4, .t5], x ∈ clobF := by decide
  obtain subM : ∀ x ∈ clobM, x ∈ clobF := by decide
  refine WP.ite (s1.gpr .t0 == 0) rfl (fun hz => ?_) (fun _ => ?_)
  · -- The offsets are multiples of 8.
    rw [p0] at hz
    obtain ⟨al1, al2, al3⟩ := aligned_of (beq_iff_eq.mp hz)
    rw [ptr_mod8 hal (by omega_arith)] at al1 al2 al3
    refine WP.mono (hcore hw1 p4 p5 p2 al2 al3 al1 (by omega_using [ha]) (by omega_using [hb]) (by omega_using [ho]) (.inl (by omega_using [hb]))
      (by rw [m1]; exact hpre)) fun s2 ⟨v2, f2, g2, rd2, wr2, sp2⟩ => ⟨by rw [← m1]; exact v2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← m1]; exact mulW_fnW W _ f2
    · intro r hr
      rw [g2 r (fun h => hr (subM r h)), r1.gpr r (fun h => hr (sub1 r h))]
    · rw [rd2, r1.rd]
    · rw [wr2, r1.wr]
    · rw [sp2, r1.sp]
  · -- The byte-wise copies.
    refine WP.seq (WP.mono (slowIn_ok hw1 p4 p5 p2 ha hb) fun s2 ⟨hw2, q1, q4, q5, q2, v4, v5, f2, r2⟩ => ?_)
    refine WP.seq (WP.mono (hcore hw2 q4 q5 q2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (.inr (by decide)) (by rw [v4, v5, m1]; exact hpre)) fun s3 ⟨v3, f3, g3, rd3, wr3, sp3⟩ => ?_)
    obtain hw3 : WsAt W s3 := ⟨hal, by rw [wr3]; exact hw2.wr, hfit, by rw [g3 _ (by decide), hw2.a3]⟩
    refine WP.mono (slowOut_ok hw3 (by rw [g3 _ (by decide), q1]) ho) fun s4 ⟨r4, f4, v4'⟩ =>
      ⟨by rw [v4']; rw [v4, v5, m1] at v3; exact v3, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← m1]
      refine (f2.sub fun r hr => ?_).trans ((f3.sub fun r hr => ?_).trans (f4.sub fun r hr => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega_using []) (by omega_using [])⟩
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega_using []) (by omega_using [])⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega_using []) (by omega_using [])⟩
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega_using []) (by omega_using [])⟩
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega_using []) (by omega_using [])⟩
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega_using []) (by omega_using [])⟩
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega_using []) (by omega_using [])⟩
      · rw [List.mem_singleton.mp hr]
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    · intro r hr
      obtain s2' : ∀ x ∈ [Reg.t1, .t2, .t4, .t5, .a4, .a5], x ∈ clobF := by decide
      obtain s4' : ∀ x ∈ [Reg.a4, .a5], x ∈ clobF := by decide
      rw [r4.gpr r (fun h => hr (s4' r h)), g3 r (fun h => hr (subM r h)), r2.gpr r (fun h => hr (s2' r h)),
        r1.gpr r (fun h => hr (sub1 r h))]
    · rw [r4.rd, rd3, r2.rd, r1.rd]
    · rw [r4.wr, wr3, r2.wr, r1.wr]
    · rw [r4.sp, sp3, r2.sp, r1.sp]

end VG.Proof.Weierstrass.RISCV64.Gen5
