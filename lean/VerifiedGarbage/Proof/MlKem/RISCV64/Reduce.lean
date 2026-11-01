module

public import VerifiedGarbage.Proof.MlKem.Ntt
public import VerifiedGarbage.Impl.MlKem.RISCV64.Ntt
public import VerifiedGarbage.Proof.MlKem.Arith
public import VerifiedGarbage.Proof.MlKem.RISCV64.Common
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# ML-KEM on RISC-V: Barrett reduction and the tables

`reduce` computes `x mod q` of any `x < 2²⁵` (`red_toNat`), through
`barrett32` (`Proof/MlKem/Arith.lean`), its product by `q` four subtractions
of shifts (`bar_eq`); `table` stores a table of 128 `u32`s (`table_ok`), and
the tables of the code are those of the standard (`zetaTable_eq`,
`gammaTable_eq`). As on PPC64LE (`Proof/MlKem/PPC64LE/Reduce.lean`), but the
functions save no registers: they write none that their caller keeps
(`kept`).
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem

/-! ## Barrett reduction -/

/-- The constant of `consts`. -/
def C : BitVec 64 := 161270

theorem consts_val : sext32 ((0x27 : BitVec 20) ++ (0 : BitVec 12)) + BitVec.ofInt 64 1526 = C := by
  decide

theorem q_val : sext32 ((1 : BitVec 20) ++ (0 : BitVec 12)) + BitVec.ofInt 64 (-767) = 3329 := by
  decide

/-- The quotient's estimate in `barrett d t u`. -/
def quot (x : BitVec 64) : BitVec 64 := (x >>> 11 * C) >>> 18

/-- What `barrett d t u` leaves in `d`. -/
def bar (x : BitVec 64) : BitVec 64 :=
  x - quot x - quot x <<< 8 - quot x <<< 10 - quot x <<< 11

theorem bar_eq (x : BitVec 64) : bar x = x - quot x * 3329 := by
  unfold bar
  generalize quot x = T
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow]
  bv_omega

/-- What `reduce d t u` leaves in `d`. -/
def red (x : BitVec 64) : BitVec 64 := fixq (bar x - 3329)

theorem bar_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 25) : (bar x).toNat = barrett32 x.toNat := by
  obtain ⟨b1, b2⟩ := barrett32_bounds hx
  have hT : (quot x).toNat = barrett32Quot x.toNat := by
    rw [quot, BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow, show C.toNat = 161270 from rfl, Nat.mod_eq_of_lt (by omega)]
    rfl
  rw [bar_eq]
  unfold barrett32
  generalize quot x = T at hT
  rw [q_eq] at b2 ⊢
  bv_omega

theorem red_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 25) : (red x).toNat = x.toNat % q := by
  have h1 := barrett32_lt hx
  unfold red
  rw [fixq_subq (by rw [bar_toNat hx]; exact h1), bar_toNat hx, ← reduce32 hx, condSub_eq h1]

theorem red_lt {x : BitVec 64} (hx : x.toNat < 2 ^ 25) : (red x).toNat < q := by
  rw [red_toNat hx]; exact Nat.mod_lt _ (by decide)

theorem toNat_val64 (x : Zq) : (BitVec.ofNat 64 x.val).toNat = x.val := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega)]

/-- A product of reduced values, reduced. -/
theorem red_mul {a b : Zq} :
    (red (BitVec.ofNat 64 a.val * BitVec.ofNat 64 b.val)).toNat = (a * b).val := by
  have ha := val_lt a
  have hb := val_lt b
  have hp : (BitVec.ofNat 64 a.val * BitVec.ofNat 64 b.val).toNat = a.val * b.val := by
    rw [BitVec.toNat_mul, toNat_val64, toNat_val64]
    exact Nat.mod_eq_of_lt (by have := mul_lt_q2 ha hb; omega)
  rw [red_toNat (by rw [hp]; have := mul_lt_q2 ha hb; omega), hp, val_mul]

/-! ## Tables -/

theorem zetaTable_eq : zetaTable = zetas := rfl

theorem gammaTable_eq : gammaTable = gammas := rfl

theorem zetaTable_lt : ∀ k < 128, zetaTable.getD k 0 < q := by decide +kernel

theorem gammaTable_lt : ∀ k < 128, gammaTable.getD k 0 < q := by decide +kernel

/-- `t0 = 2048`, as the start of `table` leaves it. -/
theorem t0_val : sext32 ((1 : BitVec 20) ++ (0 : BitVec 12)) + BitVec.ofInt 64 (-2048) = 2048 := by
  decide

/-- An entry of a table, as `addi` of `t0 = 2048` makes it. -/
theorem entry_val (v : Nat) :
    (2048 : BitVec 64) + BitVec.ofInt 64 ((v : Int) - 2048) = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  simp only [show (2048 : BitVec 64).toNat = 2048 from rfl]
  omega

/-- After the first `k` entries of a table at `B`. -/
structure TabInv (T : List Nat) (B : Addr) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .t0 → r ≠ .t2 → s.gpr r = s₀.gpr r
  t0 : s.gpr .t0 = 2048
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨B, 512⟩] s₀.mem s.mem
  tab : ∀ j < k, s.mem.readW (B + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (T.getD j 0)

/-- `table T b` stores the table `T` at `b`. -/
theorem table_ok (T : List Nat) (hT : ∀ k < 128, T.getD k 0 < 4096) {b : Reg} (hb : b ≠ .t2)
    (hb0 : b ≠ .t0) {s₀ : State} {B : Addr} (hB : s₀.gpr b = B) (hal : B.toNat % 4 = 0)
    (hwr : ∀ k < 128, InRegions s₀.wr (B + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (table T b)) s₀ (TabInv T B s₀ 128) := by
  rw [table, List.cons_append, List.cons_append, List.nil_append]
  refine Wp.WP.cons exec_lui (Wp.WP.cons (exec_addi (by decide)) ?_)
  generalize hs₁ : (s₀.write .t0 (sext32 ((1 : BitVec 20) ++ (0 : BitVec 12)))).write .t0
    ((s₀.write .t0 (sext32 ((1 : BitVec 20) ++ (0 : BitVec 12)))).gpr .t0 + BitVec.ofInt 64 (-2048)) = s₁
  have h₁ : TabInv T B s₀ 0 s₁ := by
    subst hs₁
    refine ⟨fun r h0 _ => by simp [State.write, h0], by simp only [State.write, ite_true]; exact t0_val,
      rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  refine wp_range_flatMap (M := isa) (TabInv T B s₀) (fun k s hk h => ?_) 128 (Nat.le_refl _) s₁ h₁
  have e : (s.write .t2 (s.gpr .t0 + BitVec.ofInt 64 ((T.getD k 0 : Int) - 2048))).gpr b +
      BitVec.ofNat 64 (4 * k) = B + BitVec.ofNat 64 (4 * k) := by
    simp only [State.write, hb, ite_false, h.gpr b hb0 hb, hB]
  refine Wp.WP.cons (exec_addi (by unfold imm12; have := hT k hk; omega))
    (Wp.WP.cons (exec_store_w (show 4 * k < 2048 by omega) (by rw [e]; exact align4_add hal k)
      (by rw [e]; simp only [State.write]; rw [h.wr]; exact hwr k hk)) (WP.block_nil ?_))
  rw [e]
  have hv : ((s.write .t2 (s.gpr .t0 + BitVec.ofInt 64 ((T.getD k 0 : Int) - 2048))).gpr .t2).setWidth 32 =
      BitVec.ofNat 32 (T.getD k 0) := by
    simp only [State.write, ite_true, h.t0]
    rw [entry_val]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := hT k hk
    omega
  refine ⟨fun r h0 h2 => ?_, ?_, h.rd, h.wr, h.sp, ?_, fun j hj => ?_⟩
  · simp only [State.write, h2, ite_false]; exact h.gpr r h0 h2
  · simp only [State.write, show Reg.t0 ≠ Reg.t2 by decide, ite_false]; exact h.t0
  · exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · simp only [State.write] at hv ⊢
    rw [hv]
    by_cases ej : j = k
    · subst ej; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.tab j (by omega)

/-! ## Kept registers -/

/-- The registers the functions never write that their caller keeps: the
return address and the preserved registers. -/
def kept : List Reg := [.ra, .s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

theorem preserved_sub : ∀ r ∈ preserved, r ∈ kept := by decide

theorem table_kept {T : List Nat} {B : Addr} {s₀ s : State} {k : Nat} (h : TabInv T B s₀ k s) :
    ∀ r ∈ kept, s.gpr r = s₀.gpr r := fun r hr => h.gpr r (by revert r hr; decide) (by revert r hr; decide)

end VG.Proof.MlKem.RISCV64
