module

public import VerifiedGarbage.Proof.MlKem.Ntt
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Ntt
public import VerifiedGarbage.Proof.MlKem.Arith
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import all Init.Data.Nat.Bitwise.Basic

/-!
# ML-KEM on PPC64LE: Barrett reduction, the tables and the saved registers

`reduce` computes `x mod q` of any `x < 2²⁵` (`red_toNat`), through
`barrett32` (`Proof/MlKem/Arith.lean`); `table` stores a table of 128 `u32`s
(`table_ok`), and the tables of the code are those of the standard
(`zetaTable_eq`, `gammaTable_eq`).
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem

/-! ## Barrett reduction -/

/-- The constant of `consts`. -/
def C : BitVec 64 := 161270

theorem consts_val : ((0x2 : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 ||| (0x75F6 : BitVec 16).setWidth 64 = C := by
  decide

/-- What `barrett d t` leaves in `d`. -/
def bar (x : BitVec 64) : BitVec 64 := x - (x >>> 11 * C) >>> 18 * 3329

/-- What `reduce d t` leaves in `d`. -/
def red (x : BitVec 64) : BitVec 64 := fixq (bar x - 3329)

theorem bar_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 25) : (bar x).toNat = barrett32 x.toNat := by
  obtain ⟨b1, b2⟩ := barrett32_bounds hx
  have hT : ((x >>> 11 * C) >>> 18).toNat = barrett32Quot x.toNat := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow, show C.toNat = 161270 from rfl, Nat.mod_eq_of_lt (by omega)]
    rfl
  unfold bar barrett32
  generalize (x >>> 11 * C) >>> 18 = T at hT
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

/-- After the first `k` entries of a table at `B`. -/
structure TabInv (T : List Nat) (B : Addr) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  frame : Frame [⟨B, 512⟩] s₀.mem s.mem
  tab : ∀ j < k, s.mem.readW (B + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (T.getD j 0)

/-- `table T b` stores the table `T` at `b`. -/
theorem table_ok (T : List Nat) (hT : ∀ k < 128, T.getD k 0 < 2 ^ 15) {b : Reg} (hb : b ≠ .r12)
    (hb0 : b ≠ .r0) {s₀ : State} {B : Addr} (hB : s₀.gpr b = B)
    (hwr : ∀ k < 128, InRegions s₀.wr (B + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (table T b)) s₀ (TabInv T B s₀ 128) := by
  refine wp_range_flatMap (M := isa) (TabInv T B s₀) (fun k s hk h => ?_) 128 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have e : (s.write .r12 (BitVec.ofNat 64 (T.getD k 0))).gpr b + BitVec.ofNat 64 (4 * k) =
      B + BitVec.ofNat 64 (4 * k) := by
    simp only [State.write, hb, ite_false, h.gpr b hb, hB]
  refine WP.cons (exec_li (hT k hk)) (WP.cons (exec_store_w hb0 (show 4 * k < 2 ^ 15 by omega)
    (by rw [e]; simp only [State.write]; rw [h.wr]; exact hwr k hk)) (wp_nil ?_))
  rw [e]
  have hv : ((s.write .r12 (BitVec.ofNat 64 (T.getD k 0))).gpr .r12).setWidth 32 =
      BitVec.ofNat 32 (T.getD k 0) :=
    setWidth32_ofNat (by simp only [State.write, ite_true, BitVec.toNat_ofNat]
                         exact Nat.mod_eq_of_lt (by have := hT k hk; omega)) (by have := hT k hk; omega)
  refine ⟨fun r hr => ?_, h.rd, h.wr, h.sp, h.lr, ?_, fun j hj => ?_⟩
  · simp only [State.write, hr, ite_false]; exact h.gpr r hr
  · exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · simp only [State.write] at hv ⊢
    rw [hv]
    by_cases ej : j = k
    · subst ej; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.tab j (by omega)

end VG.Proof.MlKem.PPC64LE
