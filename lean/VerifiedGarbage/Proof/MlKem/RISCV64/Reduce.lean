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
# ML-KEM on RISC-V: the tables

`liq` loads `q`; `table` stores a table of 128 `u32`s (`table_ok`), and
the tables of the code are those of the standard (`zetaTable_eq`,
`gammaTable_eq`). As on PPC64LE (`Proof/MlKem/PPC64LE/Reduce.lean`), but the
functions save no registers: they write none that their caller keeps
(`kept`).
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem

theorem toNat_val64 (x : Zq) : (BitVec.ofNat 64 x.val).toNat = x.val := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega)]

/-! ## Tables -/

theorem zetaTable_eq : zetaTable = zetas := rfl

theorem gammaTable_eq : gammaTable = gammas := rfl

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

end VG.Proof.MlKem.RISCV64
