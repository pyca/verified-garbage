module

public import VerifiedGarbage.Proof.MlKem.Ntt
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Ntt
public import VerifiedGarbage.Proof.MlKem.Arith
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
public import VerifiedGarbage.TCB.PPC64LE.Target
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

/-! ## Saved registers -/

/-- The preserved registers the functions never write. -/
def kept : List Reg := [.r2, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27,
  .r28, .r29, .r30, .r31]

theorem preserved_split : ∀ r ∈ preserved, r = .r14 ∨ r = .r15 ∨ r ∈ kept := by decide

/-- Our caller's `r14` and `r15`, from `g`, saved at `A`. -/
def Saved (m : Mem) (A : Addr) (g : Reg → BitVec 64) : Prop :=
  m.readW A 64 = g .r14 ∧ m.readW (A + BitVec.ofNat 64 8) 64 = g .r15

/-- Two doublewords at `A` and `A + 8` are separate. -/
theorem sep8 (A : Addr) : Mem.Sep A (64 / 8) (A + BitVec.ofNat 64 8) (64 / 8) := by
  have := Offset.sep A (d := 0) (n := 8) (e := 8) (k := 8) (by omega) (by omega) (by omega)
  rwa [BitVec.add_zero] at this

theorem saved_write (m : Mem) (A : Addr) (g : Reg → BitVec 64) :
    Saved ((m.writeW A (g .r14)).writeW (A + BitVec.ofNat 64 8) (g .r15)) A g :=
  ⟨by rw [Mem.readW_writeW_sep (sep8 A) (by decide), Mem.readW_writeW_self64],
    Mem.readW_writeW_self64 _ _ _⟩

/-- `saveRegs b off` stores `r14` and `r15` at `A = b + off`. -/
theorem save_ok {s : State} {b : Reg} (hb : b ≠ .r0) {off : Nat} (ho : off + 8 < 2 ^ 15) (ho4 : off % 4 = 0)
    {A : Addr} (hA : s.gpr b + BitVec.ofNat 64 off = A) (hw0 : InRegions s.wr A 8)
    (hw8 : InRegions s.wr (A + BitVec.ofNat 64 8) 8) :
    WP isa (.block (saveRegs b off)) s fun s' => s'.gpr = s.gpr ∧ s'.lr = s.lr ∧ s'.sp = s.sp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = (s.mem.writeW A (s.gpr .r14)).writeW (A + BitVec.ofNat 64 8) (s.gpr .r15) := by
  have e8 : s.gpr b + BitVec.ofNat 64 (off + 8) = A + BitVec.ofNat 64 8 := by
    rw [← hA, BitVec.add_assoc, ← BitVec.ofNat_add]
  refine WP.cons (exec_store_d hb ⟨by omega, ho4⟩ (by rw [hA]; exact hw0)) ?_
  refine WP.cons (exec_store_d hb ⟨ho, by omega⟩ (by show InRegions s.wr _ 8; rw [e8]; exact hw8)) (wp_nil ?_)
  show s.gpr = s.gpr ∧ s.lr = s.lr ∧ s.sp = s.sp ∧ s.rd = s.rd ∧ s.wr = s.wr ∧
    (s.mem.writeW (s.gpr b + BitVec.ofNat 64 off) (s.gpr .r14)).writeW (s.gpr b + BitVec.ofNat 64 (off + 8))
      (s.gpr .r15) = _
  rw [hA, e8]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `restoreRegs b off` loads `r14` and `r15` from `A = b + off`. -/
theorem restore_ok {s : State} {b : Reg} (hb : b ≠ .r0) (hb14 : b ≠ .r14) {off : Nat} (ho : off + 8 < 2 ^ 15)
    (ho4 : off % 4 = 0) {A : Addr} (hA : s.gpr b + BitVec.ofNat 64 off = A)
    (hr0 : InRegions (s.rd ++ s.wr) A 8) (hr8 : InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 8) 8) :
    WP isa (.block (restoreRegs b off)) s fun s' => s'.gpr .r14 = s.mem.readW A 64 ∧
      s'.gpr .r15 = s.mem.readW (A + BitVec.ofNat 64 8) 64 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      s'.lr = s.lr ∧ s'.sp = s.sp ∧ s'.mem = s.mem := by
  have e8 : s.gpr b + BitVec.ofNat 64 (off + 8) = A + BitVec.ofNat 64 8 := by
    rw [← hA, BitVec.add_assoc, ← BitVec.ofNat_add]
  refine WP.cons (exec_load_d hb ⟨by omega, ho4⟩ (by rw [hA]; exact hr0)) ?_
  have g : (s.write .r14 (s.mem.readW (s.gpr b + BitVec.ofNat 64 off) 64)).gpr b = s.gpr b := by
    simp only [State.write, hb14, ite_false]
  refine WP.cons (exec_load_d hb ⟨ho, by omega⟩ (by rw [g, e8]; exact hr8)) (wp_nil ?_)
  rw [g, e8, hA]
  refine ⟨by simp [State.write], by simp [State.write], fun r hr => ?_, rfl, rfl, rfl⟩
  have : r ≠ .r14 ∧ r ≠ .r15 := by revert r hr; decide
  simp [State.write, this.1, this.2]

/-- The preserved registers, with `r14` and `r15` restored. -/
theorem preserved_of {g : Reg → BitVec 64} {s : State} (h14 : s.gpr .r14 = g .r14) (h15 : s.gpr .r15 = g .r15)
    (hk : ∀ r ∈ kept, s.gpr r = g r) : ∀ r ∈ preserved, s.gpr r = g r := fun r hr => by
  rcases preserved_split r hr with rfl | rfl | h
  · exact h14
  · exact h15
  · exact hk r h

end VG.Proof.MlKem.PPC64LE
