module

public import VerifiedGarbage.Proof.MlKem.RISCV64.Reduce
public import VerifiedGarbage.Proof.MlKem.RISCV64.Lazy
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
import VerifiedGarbage.Proof.MlKem.RISCV64.Ntt
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Reduce
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Lazy
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Ntt
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Init.Data.Nat.Bitwise.Basic

/-!
# ML-KEM on RISC-V: `vg_mlkem_multiply_ntts`

As on PPC64LE (`Proof/MlKem/PPC64LE/Mul.lean`), with no registers to save:
the table of the `γᵢ` stored (`setup_ok`); then one pair of coefficients per
iteration (`multiplyNTTs_even`, `multiplyNTTs_odd`), whose body is
symbolically executed once for any (aligned) pointers (`body_ok`); the
invariant says which coefficients of `h` are written, and that `h` is the
only memory written since the setup (`Inv`).
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.Mul

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Proof.MlKem.RISCV64.Lazy (barM barQ redM redM_toNat barM_lt barM_mod)

/-! ## Values -/

theorem red_mac (x y z w : Zq) :
    (redM (BitVec.ofNat 64 x.val * BitVec.ofNat 64 y.val + BitVec.ofNat 64 z.val * BitVec.ofNat 64 w.val)).setWidth 32 =
      BitVec.ofNat 32 (x * y + z * w).val := by
  have hx := val_lt x
  have hy := val_lt y
  have hz := val_lt z
  have hw := val_lt w
  have p1 := mul_lt_q2 hx hy
  have p2 := mul_lt_q2 hz hw
  have hs : (BitVec.ofNat 64 x.val * BitVec.ofNat 64 y.val + BitVec.ofNat 64 z.val * BitVec.ofNat 64 w.val).toNat =
      x.val * y.val + z.val * w.val := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul, toNat_val64, toNat_val64, toNat_val64, toNat_val64,
      Nat.mod_eq_of_lt (a := x.val * y.val) (by omega_arith), Nat.mod_eq_of_lt (a := z.val * w.val) (by omega_arith)]
    exact Nat.mod_eq_of_lt (by omega_arith)
  refine setWidth32_ofNat ?_ (by have := val_lt (x * y + z * w); omega_arith)
  rw [redM_toNat, hs, val_add', val_mul, val_mul, ← Nat.add_mod]

/-- A residue that is congruent may replace another in a sum of products. -/
theorem mod_lazy {y B x g : Nat} (h : B % q = x % q) : (y + B * g) % q = (y + x * g) % q := by
  rw [Nat.add_mod, Nat.mul_mod, h, ← Nat.mul_mod, ← Nat.add_mod]

theorem even_eq (a b c d γ : Zq) :
    (redM (BitVec.ofNat 64 a.val * BitVec.ofNat 64 b.val +
      barM (BitVec.ofNat 64 c.val * BitVec.ofNat 64 d.val) * BitVec.ofNat 64 γ.val)).setWidth 32 =
      BitVec.ofNat 32 (a * b + c * d * γ).val := by
  have ha := val_lt a
  have hb := val_lt b
  have hg := val_lt γ
  have hcd : (BitVec.ofNat 64 c.val * BitVec.ofNat 64 d.val).toNat = c.val * d.val := by
    rw [BitVec.toNat_mul, toNat_val64, toNat_val64]
    exact Nat.mod_eq_of_lt (by have := mul_lt_q2 (val_lt c) (val_lt d); omega_arith)
  generalize hB : barM (BitVec.ofNat 64 c.val * BitVec.ofNat 64 d.val) = B
  have hBl : B.toNat < 2 * q := hB ▸ barM_lt _
  have hBm : B.toNat % q = (c * d).val % q := by
    rw [← hB, barM_mod, hcd, val_mul, Nat.mod_mod]
  have p1 := mul_lt_q2 ha hb
  have hBg : B.toNat * γ.val < 2 ^ 32 := by
    have := Nat.mul_le_mul (Nat.le_of_lt hBl) (Nat.le_of_lt hg)
    have := q_eq; omega
  have hs : (BitVec.ofNat 64 a.val * BitVec.ofNat 64 b.val + B * BitVec.ofNat 64 γ.val).toNat =
      a.val * b.val + B.toNat * γ.val := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul, toNat_val64, toNat_val64, toNat_val64,
      Nat.mod_eq_of_lt (a := a.val * b.val) (by omega_arith),
      Nat.mod_eq_of_lt (a := B.toNat * γ.val) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  refine setWidth32_ofNat ?_ (by have := val_lt (a * b + c * d * γ); omega_arith)
  rw [redM_toNat, hs, mod_lazy hBm, val_add', val_mul a b, val_mul (c * d) γ, ← Nat.add_mod]

/-! ## The loop body -/

section
variable {s : State} {is : List Instr} {Q : State → Prop}

open Steps (Upd)

private theorem wp_mul {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  Steps.WP.cons exec_mul (k _ (Upd.write _ _ _))

private theorem wp_mulhu {d n m : Reg}
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 ((s.gpr n).toNat * (s.gpr m).toNat / 2 ^ 64)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.mulhu d n m :: is)) s Q :=
  Steps.WP.cons exec_mulhu (k _ (Upd.write _ _ _))

private theorem wp_srai63 {d n : Reg} (k : ∀ s', Upd s s' d ((s.gpr n).sshiftRight 63) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .sra .d d n 63 :: is)) s Q :=
  Steps.WP.cons (exec_shift_d (by decide)) (k _ (Upd.write _ _ _))

private theorem wp_and {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  Steps.WP.cons exec_logic (k _ (Upd.write _ _ _))

/-- `barrettM .t0 .a7`: `t0 := barM t0`, through `a7`. -/
private theorem bar_ok (h5 : s.gpr .a5 = 5541226816974932) (h6 : s.gpr .a6 = 3329)
    (k : ∀ s', s'.gpr .t0 = barM (s.gpr .t0) → (∀ r, r ≠ .t0 → r ≠ .a7 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (barrettM .t0 .a7 ++ is)) s Q := by
  simp only [barrettM, List.cons_append, List.nil_append]
  refine wp_mulhu fun s₁ u₁ => wp_mul fun s₂ u₂ => Steps.wp_sub fun s₃ u₃ => k s₃ ?_ (fun r h0 h7 => ?_)
    (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.sp, u₂.sp, u₁.sp])
  · rw [u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), u₁.other _ (by decide),
      h5, h6]
    rfl
  · rw [u₃.other r h0, u₂.other r h7, u₁.other r h7]

/-- `reduceM .t0 .a7`: `t0 := redM t0`, through `a7`. -/
private theorem red_ok (h5 : s.gpr .a5 = 5541226816974932) (h6 : s.gpr .a6 = 3329)
    (k : ∀ s', s'.gpr .t0 = redM (s.gpr .t0) → (∀ r, r ≠ .t0 → r ≠ .a7 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (reduceM .t0 .a7 ++ is)) s Q := by
  simp only [reduceM, fixup, List.append_assoc, List.cons_append, List.nil_append]
  refine bar_ok h5 h6 fun s₁ b₁ o₁ m₁ rd₁ wr₁ sp₁ => Steps.wp_sub fun s₂ u₂ => wp_srai63 fun s₃ u₃ =>
    wp_and fun s₄ u₄ => Steps.wp_add fun s₅ u₅ => k s₅ ?_ (fun r h0 h7 => ?_)
    (by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]) (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]) (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁])
  · have e6 : s₁.gpr .a6 = 3329 := by rw [o₁ _ (by decide) (by decide), h6]
    have e2 : s₄.gpr .t0 = barM (s.gpr .t0) - 3329 := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, b₁, e6]
    rw [u₅.gpr, e2, u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₂.other _ (by decide), b₁, e6]
    rfl
  · rw [u₅.other r h0, u₄.other r h7, u₃.other r h7, u₂.other r h0, o₁ r h0 h7]

end

section
variable {s : State} {x3 x4 x5 x6 c : BitVec 64}

open Steps (Upd)

theorem body_ok (h3 : s.gpr .a0 = x3) (h4 : s.gpr .a1 = x4) (h5 : s.gpr .a2 = x5) (h6 : s.gpr .a3 = x6)
    (h8 : s.gpr .a5 = 5541226816974932) (h9 : s.gpr .a6 = 3329) (h11 : s.gpr .t1 = c)
    (if0 : InRegions (s.rd ++ s.wr) x4 4) (if1 : InRegions (s.rd ++ s.wr) (x4 + BitVec.ofNat 64 4) 4)
    (ig0 : InRegions (s.rd ++ s.wr) x5 4) (ig1 : InRegions (s.rd ++ s.wr) (x5 + BitVec.ofNat 64 4) 4)
    (iγ : InRegions (s.rd ++ s.wr) x6 4)
    (o0 : InRegions s.wr x3 4) (o1 : InRegions s.wr (x3 + BitVec.ofNat 64 4) 4)
    (a3 : x3.toNat % 4 = 0) (a3' : (x3 + BitVec.ofNat 64 4).toNat % 4 = 0) (a4 : x4.toNat % 4 = 0)
    (a4' : (x4 + BitVec.ofNat 64 4).toNat % 4 = 0) (a5 : x5.toNat % 4 = 0)
    (a5' : (x5 + BitVec.ofNat 64 4).toNat % 4 = 0) (a6 : x6.toNat % 4 = 0) :
    WP isa (.block mulBody) s fun s' =>
      s'.gpr .a0 = x3 + 8 ∧ s'.gpr .a1 = x4 + 8 ∧ s'.gpr .a2 = x5 + 8 ∧ s'.gpr .a3 = x6 + 4 ∧
      s'.gpr .a5 = 5541226816974932 ∧ s'.gpr .a6 = 3329 ∧ s'.gpr .t1 = c - 1 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW x3
          ((redM ((s.mem.readW x4 32).setWidth 64 * (s.mem.readW x5 32).setWidth 64 +
            barM ((s.mem.readW (x4 + BitVec.ofNat 64 4) 32).setWidth 64 *
              (s.mem.readW (x5 + BitVec.ofNat 64 4) 32).setWidth 64) *
            (s.mem.readW x6 32).setWidth 64)).setWidth 32)).writeW (x3 + BitVec.ofNat 64 4)
          ((redM ((s.mem.readW x4 32).setWidth 64 * (s.mem.readW (x5 + BitVec.ofNat 64 4) 32).setWidth 64 +
            (s.mem.readW (x4 + BitVec.ofNat 64 4) 32).setWidth 64 * (s.mem.readW x5 32).setWidth 64)).setWidth 32) := by
  generalize ef0 : (s.mem.readW x4 32).setWidth 64 = f0
  generalize ef1 : (s.mem.readW (x4 + BitVec.ofNat 64 4) 32).setWidth 64 = f1
  generalize eg0 : (s.mem.readW x5 32).setWidth 64 = g0
  generalize eg1 : (s.mem.readW (x5 + BitVec.ofNat 64 4) 32).setWidth 64 = g1
  generalize eγ : (s.mem.readW x6 32).setWidth 64 = γ
  simp only [mulBody, List.append_assoc, List.cons_append, List.nil_append]
  -- the loads and the first product
  refine Steps.wp_lwu (a := x4) (by decide) (by rw [h4]; simp) a4 if0 fun s₁ u₁ => ?_
  refine Steps.wp_lwu (a := x4 + BitVec.ofNat 64 4) (by decide)
    (by rw [u₁.other _ (by decide), h4]) a4' (by rw [u₁.rd, u₁.wr]; exact if1) fun s₂ u₂ => ?_
  refine Steps.wp_lwu (a := x5) (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h5]; simp) a5
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact ig0) fun s₃ u₃ => ?_
  refine Steps.wp_lwu (a := x5 + BitVec.ofNat 64 4) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h5]) a5'
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact ig1) fun s₄ u₄ => ?_
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have v4 : s₄.gpr .a4 = f0 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, ef0]
  have v2 : s₄.gpr .t2 = f1 := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, ef1]
  have v3 : s₄.gpr .t3 = g0 := by rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, eg0]
  have v5 : s₄.gpr .t4 = g1 := by rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem, eg1]
  have g4 : ∀ r, r ≠ .a4 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  refine wp_mul fun s₅ u₅ => ?_
  have k5 : ∀ r, r ≠ .t0 → r ≠ .a4 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s₅.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h4 => by rw [u₅.other r h0, g4 r h1 h2 h3 h4]
  refine bar_ok (by rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), h8])
    (by rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), h9])
    fun s₆ b₆ o₆ m₆ rd₆ wr₆ sp₆ => ?_
  have e6 : s₆.gpr .t0 = barM (f1 * g1) := by rw [b₆, u₅.gpr, v2, v5]
  have k6 : ∀ r, r ≠ .t0 → r ≠ .a7 → s₆.gpr r = s₅.gpr r := o₆
  -- γ, its product, and the even coefficient
  refine Steps.wp_lwu (a := x6) (by decide)
    (by rw [k6 _ (by decide) (by decide), k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), h6]; simp)
    a6 (by rw [rd₆, wr₆, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact iγ)
    fun s₇ u₇ => ?_
  have v7 : s₇.gpr .a7 = γ := by rw [u₇.gpr, m₆, u₅.mem, m₄, eγ]
  refine wp_mul fun s₈ u₈ => wp_mul fun s₉ u₉ => Steps.wp_add fun s₁₀ u₁₀ => ?_
  have k10 : ∀ r, r ≠ .t0 → r ≠ .a7 → s₁₀.gpr r = s₅.gpr r := fun r h0 h7 => by
    rw [u₁₀.other r h0, u₉.other r h7, u₈.other r h0, u₇.other r h7, k6 r h0 h7]
  have w4 : ∀ r, r = .a4 ∨ r = .t2 ∨ r = .t3 ∨ r = .t4 → s₁₀.gpr r = s₄.gpr r := fun r hr => by
    have := k10 r (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
    rw [this, u₅.other r (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
  have e10 : s₁₀.gpr .t0 = f0 * g0 + barM (f1 * g1) * γ := by
    rw [u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), u₈.gpr, u₈.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₇.other _ (by decide), u₇.other _ (by decide), e6, v7,
      o₆ _ (by decide) (by decide), o₆ _ (by decide) (by decide), u₅.other _ (by decide),
      u₅.other _ (by decide), v4, v3]
  refine red_ok (by rw [k10 _ (by decide) (by decide), k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), h8])
    (by rw [k10 _ (by decide) (by decide), k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), h9])
    fun s₁₁ r₁₁ o₁₁ m₁₁ rd₁₁ wr₁₁ sp₁₁ => ?_
  have k11 : ∀ r, r ≠ .t0 → r ≠ .a7 → s₁₁.gpr r = s₅.gpr r := fun r h0 h7 => by rw [o₁₁ r h0 h7, k10 r h0 h7]
  have hm11 : s₁₁.mem = s.mem := by rw [m₁₁, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, m₆, u₅.mem, m₄]
  have hw11 : s₁₁.wr = s.wr := by
    rw [wr₁₁, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine Steps.wp_sw (a := x3) (by decide)
    (by rw [k11 _ (by decide) (by decide), k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), h3]; simp)
    a3 (by rw [hw11]; exact o0) fun s₁₂ g₁₂ => ?_
  -- the odd coefficient
  refine wp_mul fun s₁₃ u₁₃ => wp_mul fun s₁₄ u₁₄ => Steps.wp_add fun s₁₅ u₁₅ => ?_
  have q12 : ∀ r, s₁₂.gpr r = s₁₁.gpr r := fun r => by rw [g₁₂.gpr]
  have e15 : s₁₅.gpr .t0 = f0 * g1 + f1 * g0 := by
    rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.gpr, u₁₄.gpr, u₁₃.other _ (by decide), u₁₃.other _ (by decide),
      q12, q12, q12, q12, k11 _ (by decide) (by decide), k11 _ (by decide) (by decide),
      k11 _ (by decide) (by decide), k11 _ (by decide) (by decide), u₅.other _ (by decide), u₅.other _ (by decide),
      u₅.other _ (by decide), u₅.other _ (by decide), v4, v5, v2, v3]
  have k15 : ∀ r, r ≠ .t0 → r ≠ .a7 → s₁₅.gpr r = s₅.gpr r := fun r h0 h7 => by
    rw [u₁₅.other r h0, u₁₄.other r h7, u₁₃.other r h0, q12, k11 r h0 h7]
  refine red_ok (by rw [k15 _ (by decide) (by decide), k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), h8])
    (by rw [k15 _ (by decide) (by decide), k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), h9])
    fun s₁₆ r₁₆ o₁₆ m₁₆ rd₁₆ wr₁₆ sp₁₆ => ?_
  have k16 : ∀ r, r ≠ .t0 → r ≠ .a7 → s₁₆.gpr r = s₅.gpr r := fun r h0 h7 => by rw [o₁₆ r h0 h7, k15 r h0 h7]
  refine Steps.wp_sw (a := x3 + BitVec.ofNat 64 4) (by decide)
    (by rw [k16 _ (by decide) (by decide), k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), h3])
    a3' (by rw [wr₁₆, u₁₅.wr, u₁₄.wr, u₁₃.wr, g₁₂.wr, hw11]; exact o1) fun s₁₇ g₁₇ => ?_
  refine Steps.wp_addi (by decide) fun s₁₈ u₁₈ => Steps.wp_addi (by decide) fun s₁₉ u₁₉ =>
    Steps.wp_addi (by decide) fun s₂₀ u₂₀ => Steps.wp_addi (by decide) fun s₂₁ u₂₁ =>
    Steps.wp_subi (imm := 1) (by decide) fun s₂₂ u₂₂ => WP.block_nil ?_
  have k17 : ∀ r, r ≠ .t0 → r ≠ .a7 → s₁₇.gpr r = s₅.gpr r := fun r h0 h7 => by rw [g₁₇.gpr, k16 r h0 h7]
  have kk : ∀ r, r ≠ .t0 → r ≠ .a7 → r ≠ .a4 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s₁₇.gpr r = s.gpr r :=
    fun r h0 h7 h1 h2 h3 h4 => by rw [k17 r h0 h7, k5 r h0 h1 h2 h3 h4]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂₂.other _ (by decide), u₂₁.other _ (by decide), u₂₀.other _ (by decide), u₁₉.other _ (by decide),
      u₁₈.gpr, kk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h3]; rfl
  · rw [u₂₂.other _ (by decide), u₂₁.other _ (by decide), u₂₀.other _ (by decide), u₁₉.gpr,
      u₁₈.other _ (by decide), kk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h4]; rfl
  · rw [u₂₂.other _ (by decide), u₂₁.other _ (by decide), u₂₀.gpr, u₁₉.other _ (by decide),
      u₁₈.other _ (by decide), kk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h5]; rfl
  · rw [u₂₂.other _ (by decide), u₂₁.gpr, u₂₀.other _ (by decide), u₁₉.other _ (by decide),
      u₁₈.other _ (by decide), kk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h6]; rfl
  · rw [u₂₂.other _ (by decide), u₂₁.other _ (by decide), u₂₀.other _ (by decide), u₁₉.other _ (by decide),
      u₁₈.other _ (by decide), kk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h8]
  · rw [u₂₂.other _ (by decide), u₂₁.other _ (by decide), u₂₀.other _ (by decide), u₁₉.other _ (by decide),
      u₁₈.other _ (by decide), kk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h9]
  · rw [u₂₂.gpr, u₂₁.other _ (by decide), u₂₀.other _ (by decide), u₁₉.other _ (by decide),
      u₁₈.other _ (by decide), kk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h11]; rfl
  · have : r ≠ .t0 ∧ r ≠ .a7 ∧ r ≠ .a4 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .t4 ∧ r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧
        r ≠ .a3 ∧ r ≠ .t1 := by revert r; decide
    rw [u₂₂.other r this.2.2.2.2.2.2.2.2.2.2, u₂₁.other r this.2.2.2.2.2.2.2.2.2.1,
      u₂₀.other r this.2.2.2.2.2.2.2.2.1, u₁₉.other r this.2.2.2.2.2.2.2.1, u₁₈.other r this.2.2.2.2.2.2.1,
      kk r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2.1 this.2.2.2.2.2.1]
  · rw [u₂₂.rd, u₂₁.rd, u₂₀.rd, u₁₉.rd, u₁₈.rd, g₁₇.rd, rd₁₆, u₁₅.rd, u₁₄.rd, u₁₃.rd, g₁₂.rd, rd₁₁, u₁₀.rd,
      u₉.rd, u₈.rd, u₇.rd, rd₆, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₂₂.wr, u₂₁.wr, u₂₀.wr, u₁₉.wr, u₁₈.wr, g₁₇.wr, wr₁₆, u₁₅.wr, u₁₄.wr, u₁₃.wr, g₁₂.wr, hw11]
  · rw [u₂₂.sp, u₂₁.sp, u₂₀.sp, u₁₉.sp, u₁₈.sp, g₁₇.sp, sp₁₆, u₁₅.sp, u₁₄.sp, u₁₃.sp, g₁₂.sp, sp₁₁, u₁₀.sp,
      u₉.sp, u₈.sp, u₇.sp, sp₆, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₂₂.mem, u₂₁.mem, u₂₀.mem, u₁₉.mem, u₁₈.mem, g₁₇.mem, m₁₆, u₁₅.mem, u₁₄.mem, u₁₃.mem, g₁₂.mem,
      hm11, r₁₆, e15, r₁₁, e10]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev H : Addr := s₀.gpr .a0
abbrev F : Addr := s₀.gpr .a1
abbrev G : Addr := s₀.gpr .a2
abbrev S : Addr := s₀.gpr .a3
abbrev fp : Poly := polyAt s₀.mem (F s₀)
abbrev gp : Poly := polyAt s₀.mem (G s₀)

/-- Coefficient `j` of the output. -/
def out (j : Nat) : BitVec 32 := BitVec.ofNat 32 ((multiplyNTTs (fp s₀) (gp s₀))[j]!).val

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (F s₀), polyRegion (G s₀)]
  wr : s₀.wr = [polyRegion (H s₀), polyRegion (S s₀)]
  hf : (polyRegion (H s₀)).Disjoint (polyRegion (F s₀))
  hg : (polyRegion (H s₀)).Disjoint (polyRegion (G s₀))
  hs : (polyRegion (H s₀)).Disjoint (polyRegion (S s₀))
  fs : (polyRegion (F s₀)).Disjoint (polyRegion (S s₀))
  gs : (polyRegion (G s₀)).Disjoint (polyRegion (S s₀))
  fitH : (H s₀).toNat + 1024 ≤ 2 ^ 64
  fitF : (F s₀).toNat + 1024 ≤ 2 ^ 64
  fitG : (G s₀).toNat + 1024 ≤ 2 ^ 64
  fitS : (S s₀).toNat + 1024 ≤ 2 ^ 64
  redF : Reduced s₀.mem (F s₀)
  redG : Reduced s₀.mem (G s₀)
  alH : (H s₀).toNat % 4 = 0
  alF : (F s₀).toNat % 4 = 0
  alG : (G s₀).toNat % 4 = 0
  alS : (S s₀).toNat % 8 = 0

/-- What the setup leaves in memory `m₁`. -/
structure Setup (s₀ : State) (m₁ : Mem) : Prop where
  tab : ∀ j < 128, m₁.readW (S s₀ + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (gammaTable.getD j 0)
  f : ∀ j < 256, coeffAt m₁ (F s₀) j = coeffAt s₀.mem (F s₀) j
  g : ∀ j < 256, coeffAt m₁ (G s₀) j = coeffAt s₀.mem (G s₀) j

/-- After `i` pairs, from the memory `m₁` the setup left. -/
structure Inv (s₀ : State) (m₁ : Mem) (i : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = H s₀ + BitVec.ofNat 64 (8 * i)
  a1 : s.gpr .a1 = F s₀ + BitVec.ofNat 64 (8 * i)
  a2 : s.gpr .a2 = G s₀ + BitVec.ofNat 64 (8 * i)
  a3 : s.gpr .a3 = S s₀ + BitVec.ofNat 64 (4 * i)
  a5 : s.gpr .a5 = 5541226816974932
  a6 : s.gpr .a6 = 3329
  t1 : s.gpr .t1 = BitVec.ofNat 64 (128 - i)
  kept : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [polyRegion (H s₀)] m₁ s.mem
  coeff : ∀ j < 256, coeffAt s.mem (H s₀) j = if j < 2 * i then out s₀ j else coeffAt m₁ (H s₀) j

theorem out_even (s₀ : State) {i : Nat} (hi : i < 128) :
    out s₀ (2 * i) = BitVec.ofNat 32 ((fp s₀)[2 * i]! * (gp s₀)[2 * i]! +
      (fp s₀)[2 * i + 1]! * (gp s₀)[2 * i + 1]! * gamma i).val := by
  rw [out, multiplyNTTs_even _ _ hi]

theorem out_odd (s₀ : State) {i : Nat} (hi : i < 128) :
    out s₀ (2 * i + 1) = BitVec.ofNat 32 ((fp s₀)[2 * i]! * (gp s₀)[2 * i + 1]! +
      (fp s₀)[2 * i + 1]! * (gp s₀)[2 * i]!).val := by
  rw [out, multiplyNTTs_odd _ _ hi]

/-- A coefficient, zero-extended, is the element of `ℤ_q` it represents. -/
theorem wide {m : Mem} {p : Addr} {f : Poly} {j : Nat}
    (h : coeffAt m p j = BitVec.ofNat 32 (f[j]!).val) :
    (coeffAt m p j).setWidth 64 = BitVec.ofNat 64 (f[j]!).val := by
  rw [h, setWidth64_ofNat (by have := val_lt f[j]!; omega_arith)]

theorem step {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {i : Nat} (hi : i < 128) {s : State}
    (h : Inv s₀ m₁ i s) :
    WP isa (.block mulBody) s fun s' => Inv s₀ m₁ (i + 1) s' ∧ (s'.gpr .t1 != 0) = decide (i + 1 ≠ 128) := by
  have e0 : ∀ p : Addr, p + BitVec.ofNat 64 (8 * i) = coeffAddr p (2 * i) := fun p => by
    rw [show 8 * i = 4 * (2 * i) by omega_arith]
  have e1 : ∀ p : Addr, p + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 4 = coeffAddr p (2 * i + 1) := fun p => by
    rw [ptr_add, show 8 * i + 4 = 4 * (2 * i + 1) by omega_arith]
  have fS := hp.fitS
  have cF0 := coeff_contains (F s₀) (i := 2 * i) (by rw [n_eq]; omega_arith)
  have cF1 := coeff_contains (F s₀) (i := 2 * i + 1) (by rw [n_eq]; omega_arith)
  have cG0 := coeff_contains (G s₀) (i := 2 * i) (by rw [n_eq]; omega_arith)
  have cG1 := coeff_contains (G s₀) (i := 2 * i + 1) (by rw [n_eq]; omega_arith)
  have cH0 := coeff_contains (H s₀) (i := 2 * i) (by rw [n_eq]; omega_arith)
  have cH1 := coeff_contains (H s₀) (i := 2 * i + 1) (by rw [n_eq]; omega_arith)
  have cS : (polyRegion (S s₀)).Contains (S s₀ + BitVec.ofNat 64 (4 * i)) 4 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have iR : ∀ {R : Region} {a : Addr} {n : Nat}, R ∈ s₀.rd ++ s₀.wr → R.Contains a n →
      InRegions (s.rd ++ s.wr) a n := fun hR hc => by rw [h.rd, h.wr]; exact ⟨_, hR, hc⟩
  have iW : ∀ {R : Region} {a : Addr} {n : Nat}, R ∈ s₀.wr → R.Contains a n → InRegions s.wr a n :=
    fun hR hc => by rw [h.wr]; exact ⟨_, hR, hc⟩
  -- The values read.
  have vF : ∀ j < 256, coeffAt s.mem (F s₀) j = BitVec.ofNat 32 ((fp s₀)[j]!).val := fun j hj => by
    rw [coeffAt_congr (bytes_frame h.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.hf.symm) (by decide)) (by rw [n_eq]; exact hj), hm.f j hj]
    exact ofNat_val_eq (polyAt_val hp.redF (by rw [n_eq]; exact hj)).symm
  have vG : ∀ j < 256, coeffAt s.mem (G s₀) j = BitVec.ofNat 32 ((gp s₀)[j]!).val := fun j hj => by
    rw [coeffAt_congr (bytes_frame h.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.hg.symm) (by decide)) (by rw [n_eq]; exact hj), hm.g j hj]
    exact ofNat_val_eq (polyAt_val hp.redG (by rw [n_eq]; exact hj)).symm
  have vS : (s.mem.readW (S s₀ + BitVec.ofNat 64 (4 * i)) 32).setWidth 64 = BitVec.ofNat 64 (gamma i).val := by
    rw [h.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hs.symm)
      (by decide), hm.tab i hi, gammaTable_eq, gammas_getD hi,
      setWidth64_ofNat (by have := val_lt (gamma i); omega_arith)]
  refine WP.mono (body_ok h.a0 h.a1 h.a2 h.a3 h.a5 h.a6 h.t1
    (by rw [e0]; exact iR (by simp [hp.rd]) cF0) (by rw [e1]; exact iR (by simp [hp.rd]) cF1)
    (by rw [e0]; exact iR (by simp [hp.rd]) cG0) (by rw [e1]; exact iR (by simp [hp.rd]) cG1)
    (iR (by simp [hp.wr]) cS) (by rw [e0]; exact iW (by simp [hp.wr]) cH0)
    (by rw [e1]; exact iW (by simp [hp.wr]) cH1)
    (by rw [e0]; exact align4_add hp.alH _) (by rw [e1]; exact align4_add hp.alH _)
    (by rw [e0]; exact align4_add hp.alF _) (by rw [e1]; exact align4_add hp.alF _)
    (by rw [e0]; exact align4_add hp.alG _) (by rw [e1]; exact align4_add hp.alG _)
    (align4_add (by have := hp.alS; omega) _))
    fun s' ⟨r3, r4, r5, r6, r8, r9, r11, kp, rd, wr, sp, m⟩ => ⟨⟨?_, ?_, ?_, ?_, r8, r9, ?_,
      fun r hr => (kp r hr).trans (h.kept r hr), rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
      ?_, ?_⟩, ?_⟩
  · rw [r3]; exact ptr_succ _ 8 i
  · rw [r4]; exact ptr_succ _ 8 i
  · rw [r5]; exact ptr_succ _ 8 i
  · rw [r6]; exact ptr_succ _ 4 i
  · rw [r11]; exact count_sub hi
  · rw [m, e1 (H s₀), e0 (H s₀)]
    exact (h.frame.writeW (List.mem_singleton_self _) _ cH0).writeW (List.mem_singleton_self _) _ cH1
  · rw [m, e1, e1, e1, e0, e0, e0, vS]
    show ∀ j < 256, coeffAt ((s.mem.writeW (coeffAddr (H s₀) (2 * i)) _).writeW _ _) _ j = _
    rw [← coeffAt_eq, ← coeffAt_eq, ← coeffAt_eq, ← coeffAt_eq, wide (vF _ (by omega_arith)), wide (vF _ (by omega_arith)),
      wide (vG _ (by omega_arith)), wide (vG _ (by omega_arith)), even_eq, red_mac, ← out_even s₀ hi, ← out_odd s₀ hi,
      show 2 * (i + 1) = 2 * i + 1 + 1 by omega_arith]
    exact coeff_one (a := 2 * i + 1) (by omega_arith) (coeff_one (a := 2 * i) (by omega_arith) h.coeff rfl) rfl
  · rw [r11, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
    exact count_nz hi (by decide)

/-! ## Setup and the end -/

/-- The table stored in `scratch`. -/
theorem setup_base {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (table gammaTable .a3)) s₀ fun s =>
      Setup s₀ s.mem ∧ (∀ r, r ≠ .t0 → r ≠ .t2 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
        s.sp = s₀.sp := by
  have fS := hp.fitS
  have wS : ∀ {o k : Nat}, o + k ≤ 1024 → InRegions s₀.wr (S s₀ + BitVec.ofNat 64 o) k := fun h => by
    rw [hp.wr]; exact ⟨_, by simp, Offset.contains_base _ h (by omega_arith)⟩
  have a8 : (s₀.gpr .a3).toNat % 8 = 0 := hp.alS
  refine WP.mono (table_ok gammaTable (by decide) (b := .a3) (by decide) (by decide) rfl (by omega)
    fun k hk => wS (by omega_arith)) fun s₂ h₂ => ?_
  have fr : Frame [polyRegion (S s₀)] s₀.mem s₂.mem := by
    refine h₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    rw [List.mem_singleton] at hr; subst hr
    exact Ntt.sub_low _ (by omega_arith)
  refine ⟨⟨fun j hj => h₂.tab j hj, fun j hj => ?_, fun j hj => ?_⟩, h₂.gpr, h₂.rd, h₂.wr, h₂.sp⟩
  · exact coeffAt_congr (bytes_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.fs) (by decide)) (by rw [n_eq]; exact hj)
  · exact coeffAt_congr (bytes_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.gs) (by decide)) (by rw [n_eq]; exact hj)

theorem tail_ok {s : State} :
    WP isa (.block (constsM ++ ([.li .t1 128] : List Instr))) s
      fun s' => s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a2 = s.gpr .a2 ∧
        s'.gpr .a3 = s.gpr .a3 ∧ s'.gpr .a5 = 5541226816974932 ∧ s'.gpr .a6 = 3329 ∧ s'.gpr .t1 = 128 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  simp only [constsM, loadM, liq, Nat.reduceLT, ite_false, List.cons_append, List.nil_append,
    Int.reduceSub, Int.reduceNeg, Int.cast_ofNat_Int]
  crun [kept, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  all_goals decide

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (table gammaTable .a3 ++ constsM ++ ([.li .t1 128] : List Instr))) s₀
      fun s => Setup s₀ s.mem ∧ Inv s₀ s.mem 0 s := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp⟩ => ?_
  refine WP.mono tail_ok fun s ⟨r3, r4, r5, r6, r8, r9, r11, kp, m, rd', wr', sp'⟩ => ?_
  rw [m]
  refine ⟨hm, ⟨by rw [r3, e .a0 (by decide) (by decide)]; simp, by rw [r4, e .a1 (by decide) (by decide)]; simp,
    by rw [r5, e .a2 (by decide) (by decide)]; simp, by rw [r6, e .a3 (by decide) (by decide)]; simp, r8, r9, r11,
    fun r hr => ?_, rd'.trans rd, wr'.trans wr, sp'.trans sp, by rw [m]; exact Frame.refl _ _,
    fun j _ => by rw [m]; rfl⟩⟩
  rw [kp r hr, e r (by revert r hr; decide) (by revert r hr; decide)]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa multiplyNTTs s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      s.gpr .ra = s₀.gpr .ra ∧ PolyIs s.mem (H s₀) (Spec.MlKem.multiplyNTTs (fp s₀) (gp s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, h₁⟩ => ?_)
  exact wp_loop_nz (Inv s₀ s₁.mem) (N := 128) (by decide) (fun i hi s h => step hp hm hi h)
    (fun s h => ⟨fun r hr => h.kept r (preserved_sub r hr), h.sp, h.kept .ra (by decide),
      polyIs_of_coeffAt fun j hj => by
        rw [h.coeff j (by rw [n_eq] at hj; exact hj), ite_eq_left (by rw [n_eq] at hj; omega_arith)]; rfl⟩) h₁

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlKem.mulContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Proof.MlKem.mulContract, Proof.MlKem.mulSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x4000, 1024⟩]

theorem verified : Verified RISCV64.target Impl.MlKem.RISCV64.multiplyNTTs (Proof.MlKem.mulContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.a0, .a1, .a2, .a3] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_)
    (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hra, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hra⟩, ?_⟩
    sig_post [Proof.MlKem.mulContract, Proof.MlKem.mulSig, RISCV64.abi, RISCV64.argRegs]
    exact h
  · sig_pub [Proof.MlKem.mulContract, Proof.MlKem.mulSig, RISCV64.abi, RISCV64.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2
  · sig_pub [Proof.MlKem.mulContract, Proof.MlKem.mulSig, RISCV64.abi, RISCV64.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.mulContract, Proof.MlKem.mulSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact Add.reduced_zero _
        | decide +kernel

end VG.Proof.MlKem.RISCV64.Mul
