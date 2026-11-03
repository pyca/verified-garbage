module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Cols
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Arithmetic modulo P-521's prime in 58-bit limbs, on RISC-V: the product

`core` (`Impl/Weierstrass/RISCV64/P521Unsat.lean`) meets GenWide's
specification of an operation (`GenWide.CoreSpecP`): tight operands to a
tight result, the product modulo `p` (`core_spec`). An operand's doubled
limbs at `Y` (`dbl_ok`), the columns (`pipe_ok`, with `tab_mul`, `tab_sq`)
and their values (`mulCol_eq`, `sqCol_eq`), and what is left past `2⁵²²`,
doubled, into limbs 0 and 1 (`fold_ok`).
-/

@[expose] public section

-- `2⁵²²` is a numeral.
set_option exponentiation.threshold 600

namespace VG.Proof.Weierstrass.RISCV64.P521Unsat

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P521Unsat
open VG.Proof.Weierstrass.RISCV64.GenWide (CoreOk CoreSpecP ownR clobW xv ov)
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8)

/-! ## The doubled limbs -/

/-- An operand of the kernel: `[t4]` or `[t5]`. -/
def IsOp (A B : Addr) (src : Reg) (P : Addr) : Prop := src = .t4 ∧ P = A ∨ src = .t5 ∧ P = B

theorem ldP_ok {b A B O : Addr} {s : State} (hC : CoreOk 9 b A B O s) {src : Reg} {P : Addr}
    (hP : IsOp A B src P) {is : List Instr} {Q : State → Prop} {t : Reg} {i : Nat} (hi : i < 9)
    (k : ∀ s', Upd s s' t (s.mem.readW (P + BitVec.ofNat 64 (8 * i)) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t src (8 * i) :: is)) s Q := by
  rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ldA_ok hC hi k
  · exact ldB_ok hC hi k

theorem dwP_kept {b A B O : Addr} {s0 : State} (hC : CoreOk 9 b A B O s0) {src : Reg} {P : Addr}
    (hP : IsOp A B src P) {m : Mem} (hf : Frame [ownR 9 b] s0.mem m) {i : Nat} (hi : i < 9) :
    dw m P (8 * i) = dw s0.mem P (8 * i) := by
  rcases hP with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact dwA_kept hC hf hi
  · exact dwB_kept hC hf hi

/-- After `j` words of `dbl src`. -/
structure DblInv (b P : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .a1 → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 Y, 72⟩] s0.mem s.mem
  outs : ∀ i < j, dw s.mem b (Y + 8 * i) = dw s0.mem P (8 * i) * 2 % 2 ^ 64

theorem Y_own {b : Addr} : Region.Sub ⟨b + BitVec.ofNat 64 Y, 72⟩ (ownR 9 b) := own_sub (by rw [Y_eq]; omega) (by rw [Y_eq]; omega)

/-- `dbl src`: `Y[j] = 2 [P + 8 j]` (modulo `2⁶⁴`). -/
theorem dbl_ok {b A B O : Addr} {s0 : State} (hC : CoreOk 9 b A B O s0) {src : Reg} {P : Addr}
    (hP : IsOp A B src P) :
    WP isa (.block (dbl src)) s0 (DblInv b P s0 9) := by
  have hb := hC.nowrap
  refine wp_range_flatMap (M := isa) (DblInv b P s0) (fun j s hj h => ?_) 9 (Nat.le_refl _) s0
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  have hCs : CoreOk 9 b A B O s := core_of hC (fun r hr => h.gpr r fun e => hr (by rw [e]; decide)) h.rd h.wr
  refine ldP_ok hCs hP hj fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => ?_
  have hc₂ : Ctx b s₂ := ⟨by rw [u₂.other _ (by decide), u₁.other _ (by decide), hCs.ctx.a3], hCs.ctx.al,
    by rw [u₂.wr, u₁.wr]; exact hCs.ctx.wr⟩
  refine sd_ok hc₂ (by rw [Y_eq]; omega) (by rw [Y_eq]; omega) fun s₃ u₃ => WP.block_nil ⟨fun r hr => ?_,
    by rw [u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₃.wr, u₂.wr, u₁.wr, h.wr], by rw [u₃.sp, u₂.sp, u₁.sp, h.sp], ?_,
    fun i hi => ?_⟩
  · rw [u₃.gpr, u₂.other r hr, u₁.other r hr, h.gpr r hr]
  · rw [u₃.mem, u₂.mem, u₁.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains b (by rw [Y_eq]; omega)
      (by rw [Y_eq]; omega) (by rw [Y_eq]; omega))
  · have hP0 : dw s.mem P (8 * j) = dw s0.mem P (8 * j) :=
      dwP_kept hC hP (h.frame.sub fun _ hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Y_own⟩) hj
    rw [u₃.mem, u₂.mem, u₁.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [dw_write_other _ _ _ (by omega) (by rw [Y_eq]; omega) (by rw [Y_eq]; omega)]
      exact h.outs i hi
    · rw [dw_write_self, u₂.gpr, u₁.gpr, shl_toNat, ← hP0]
      rfl

/-! ## The fold -/

theorem shl1_and (x : BitVec 64) : ((x <<< 1) &&& M58).toNat = 2 * x.toNat % 2 ^ 58 := by
  rw [and_M58, shl_toNat]
  have : (2 : Nat) ^ 64 = 2 ^ 58 * 2 ^ 6 := by decide
  rw [this, Nat.mod_mul_right_mod, Nat.pow_one, Nat.mul_comm]

set_option linter.unusedSimpArgs false in
/-- `fold`: twice what is left in the accumulator into limbs 0 and 1, then
the limbs to `[O]`. -/
theorem fold_ok {b A B O : Addr} {s : State} (hC : CoreOk 9 b A B O s) (h6 : s.gpr .a6 = M58)
    (hz : ∀ c < 9, dw s.mem b (Z + 8 * c) < 2 ^ 58) (ha : acc s < 2 ^ 70) :
    WP isa (.block fold) s fun s' => Kept b O s s' ∧
      lv (fun j => dw s'.mem O (8 * j)) 9 = lv (fun c => dw s.mem b (Z + 8 * c)) 9 + 2 * acc s ∧
      TightF (fun j => dw s'.mem O (8 * j)) := by
  have hb := hC.nowrap
  rw [show fold = [.load .d .a1 .a3 Z, .load .d .a2 .a3 (Z + 8), .shift .sll .d .t3 .a4 1, .logic .and .t3 .t3 .a6,
    .add .a1 .a1 .t3, .shift .srl .d .t3 .a4 57, .shift .sll .d .t6 .a5 7, .add .t3 .t3 .t6, .add .a2 .a2 .t3,
    .shift .srl .d .t3 .a1 58, .logic .and .a1 .a1 .a6, .add .a2 .a2 .t3, .store .d .a1 .t2 (8 * 0),
    .store .d .a2 .t2 (8 * 1)] ++ copyZ 2 from rfl]
  have z0 := hz 0 (by decide)
  have z1 := hz 1 (by decide)
  have hL := (s.gpr .a4).isLt
  have hH : (s.gpr .a5).toNat < 2 ^ 6 := by simp only [acc] at ha; omega
  refine WP.block_append ?_
  refine ld_ok hC.ctx (by rw [Z_eq]; omega) (by rw [Z_eq]) fun s₁ u₁ => ?_
  refine ld_ok (b := b) ⟨by rw [u₁.other _ (by decide), hC.ctx.a3], hC.ctx.al, by rw [u₁.wr]; exact hC.ctx.wr⟩
    (by rw [Z_eq]; omega) (by rw [Z_eq]) fun s₂ u₂ => ?_
  refine wp_sll (by decide) fun s₃ u₃ => wp_and fun s₄ u₄ => wp_add fun s₅ u₅ => wp_srl (by decide) fun s₆ u₆ =>
    wp_sll (by decide) fun s₇ u₇ => wp_add fun s₈ u₈ => wp_add fun s₉ u₉ => wp_srl (by decide) fun s₁₀ u₁₀ =>
    wp_and fun s₁₁ u₁₁ => wp_add fun s₁₂ u₁₂ => ?_
  -- The registers' values.
  have ra1 : s₁₂.gpr .a1 = (s.mem.readW (b + BitVec.ofNat 64 Z) 64 + ((s.gpr .a4 <<< 1) &&& M58)) &&& M58 := by
    simp only [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, ne_eq, reduceCtorEq, not_false_eq_true, h6]
  have ra2 : s₁₂.gpr .a2 = s.mem.readW (b + BitVec.ofNat 64 (Z + 8)) 64 + (s.gpr .a4 >>> 57 + s.gpr .a5 <<< 7) +
      (s.mem.readW (b + BitVec.ofNat 64 Z) 64 + ((s.gpr .a4 <<< 1) &&& M58)) >>> 58 := by
    simp only [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, ne_eq, reduceCtorEq, not_false_eq_true, h6]
  have hK12 : Kept b O s s₁₂ := ⟨fun r hr => by
      have : r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .t3 ∧ r ≠ .t6 := ⟨fun e => hr (by rw [e]; decide), fun e => hr (by rw [e]; decide),
        fun e => hr (by rw [e]; decide), fun e => hr (by rw [e]; decide)⟩
      simp only [u₁₂.other, u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, ne_eq, this.1, this.2.1, this.2.2.1,
        this.2.2.2, not_false_eq_true],
    by simp only [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by simp only [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    by simp only [u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp],
    by simp only [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _⟩
  have hm12 : s₁₂.mem = s.mem := by simp only [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  -- The numbers.
  have hZ0 : (s.mem.readW (b + BitVec.ofNat 64 Z) 64).toNat = dw s.mem b (Z + 8 * 0) := rfl
  have hZ1 : (s.mem.readW (b + BitVec.ofNat 64 (Z + 8)) 64).toNat = dw s.mem b (Z + 8 * 1) := rfl
  generalize hz0 : dw s.mem b (Z + 8 * 0) = Z0 at z0 hZ0
  generalize hz1 : dw s.mem b (Z + 8 * 1) = Z1 at z1 hZ1
  generalize hLv : (s.gpr .a4).toNat = L at hL
  generalize hHv : (s.gpr .a5).toNat = H at hH
  have hm : 2 * L % 2 ^ 58 < 2 ^ 58 := Nat.mod_lt _ (by decide)
  have e11' : (s₁₂.gpr .a1).toNat = (Z0 + 2 * L % 2 ^ 58) % 2 ^ 58 := by
    rw [ra1, and_M58, BitVec.toNat_add, shl1_and, hZ0, hLv, Nat.mod_eq_of_lt (a := Z0 + _) (by omega)]
  have e12 : (s₁₂.gpr .a2).toNat = Z1 + (L / 2 ^ 57 + H * 2 ^ 7) + (Z0 + 2 * L % 2 ^ 58) / 2 ^ 58 := by
    rw [ra2, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, shr_toNat, shl_toNat, shr_toNat, BitVec.toNat_add,
      shl1_and, hZ0, hZ1, hLv, hHv, Nat.mod_eq_of_lt (a := Z0 + _) (by omega), Nat.mod_eq_of_lt (a := H * _) (by omega)]
    have : (Z0 + 2 * L % 2 ^ 58) / 2 ^ 58 ≤ 1 := by omega
    have : L / 2 ^ 57 < 2 ^ 7 := by omega
    rw [Nat.mod_eq_of_lt (a := L / 2 ^ 57 + _) (by omega), Nat.mod_eq_of_lt (a := Z1 + _) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hC12 : CoreOk 9 b A B O s₁₂ := hK12.core hC
  refine sdO_ok hC12 (by decide) fun s₁₃ u₁₃ => ?_
  have hC13 : CoreOk 9 b A B O s₁₃ := core_of hC12 (fun r _ => by rw [u₁₃.gpr]) u₁₃.rd u₁₃.wr
  refine sdO_ok hC13 (by decide) fun s₁₄ u₁₄ => WP.block_nil ?_
  have hK14 : Kept b O s s₁₄ := (hK12.sdO (by decide) u₁₃).sdO (by decide) u₁₄
  have hC14 : CoreOk 9 b A B O s₁₄ := hK14.core hC
  refine WP.mono (copyZ_ok hC14 (j₀ := 2) (by decide)) fun s' ⟨hK, _, hout⟩ => ?_
  have hm14 : ∀ d, 1472 ≤ d → d + 8 ≤ 1632 → dw s₁₄.mem b d = dw s.mem b d := fun d hd hd' => by
    rw [u₁₄.mem, dw_own_sdO hC (by decide) hd hd', u₁₃.mem, dw_own_sdO hC (by decide) hd hd', hm12]
  have o0 : dw s'.mem O (8 * 0) = (Z0 + 2 * L % 2 ^ 58) % 2 ^ 58 := by
    rw [hout 0 (by decide), ite_eq_right (by decide), u₁₄.mem,
      dw_write_other _ _ _ (by decide) (by decide) (by decide), u₁₃.mem, dw_write_self, e11']
  have o1 : dw s'.mem O (8 * 1) = Z1 + (L / 2 ^ 57 + H * 2 ^ 7) + (Z0 + 2 * L % 2 ^ 58) / 2 ^ 58 := by
    rw [hout 1 (by decide), ite_eq_right (by decide), u₁₄.mem, dw_write_self, u₁₃.gpr, e12]
  have oj : ∀ j, 2 ≤ j → j < 9 → dw s'.mem O (8 * j) = dw s.mem b (Z + 8 * j) := fun j hj hj' => by
    rw [hout j hj', ite_eq_left hj, hm14 _ (by rw [Z_eq]; omega) (by rw [Z_eq]; omega)]
  refine ⟨hK14.trans hK, ?_, ⟨fun i hi => ?_, ?_⟩⟩
  · refine lv_fold _ _ ?_ fun j hj hj' => oj j hj hj'
    show dw s'.mem O (8 * 0) + 2 ^ 58 * dw s'.mem O (8 * 1) =
      dw s.mem b (Z + 8 * 0) + 2 ^ 58 * dw s.mem b (Z + 8 * 1) + 2 * acc s
    rw [o0, o1, hz0, hz1]
    simp only [acc, hLv, hHv]
    have := Nat.div_add_mod (Z0 + 2 * L % 2 ^ 58) (2 ^ 58)
    have := Nat.div_add_mod (2 * L) (2 ^ 58)
    omega
  · show dw s'.mem O (8 * i) < 2 ^ 59
    rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | h2
    · rw [o0]; exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    · rw [o1]; omega
    · rw [oj i h2 (by omega)]; exact Nat.lt_trans (hz i (by omega)) (by decide)
  · show dw s'.mem O (8 * 8) < 2 ^ 58
    rw [oj 8 (by decide) (by decide)]; exact hz 8 (by decide)

/-! ## The product and the square -/

theorem tab_mul : Tab (terms mulPairs) mulPairs := ⟨by decide, by decide, by decide, by decide⟩

theorem tab_sq : Tab (terms sqPairs) sqPairs := ⟨by decide, by decide, by decide, by decide⟩

/-- After the doubled limbs of `[P]`. -/
structure Dbl (b A B O P : Addr) (s0 s : State) : Prop where
  kept : Kept b O s0 s
  core : CoreOk 9 b A B O s
  a6 : s.gpr .a6 = M58
  ys : ∀ j < 9, dw s.mem b (Y + 8 * j) = 2 * dw s0.mem P (8 * j)
  as : ∀ i < 9, dw s.mem A (8 * i) = dw s0.mem A (8 * i)
  bs : ∀ i < 9, dw s.mem B (8 * i) = dw s0.mem B (8 * i)

/-- `mask` and `dbl src`. -/
theorem maskDbl_ok {b A B O : Addr} {s0 : State} (hC : CoreOk 9 b A B O s0) {src : Reg} {P : Addr}
    (hP : IsOp A B src P) (hPt : TightF (fun i => dw s0.mem P (8 * i))) {is : List Instr} {Q : State → Prop}
    (k : ∀ s, Dbl b A B O P s0 s → WP isa (.block is) s Q) :
    WP isa (.block (mask ++ dbl src ++ is)) s0 Q := by
  rw [List.append_assoc]
  refine mask_ok fun s₁ k₁ h6 => ?_
  have K₁ : Kept b O s0 s₁ := (Kept.refl b O s0).keeps k₁
  have hC₁ := K₁.core hC
  refine WP.block_append (WP.mono (dbl_ok hC₁ hP) fun s₂ h₂ => k s₂ ?_)
  have hf : Frame [ownR 9 b] s₁.mem s₂.mem := h₂.frame.sub fun _ hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Y_own⟩
  have K₂ : Kept b O s0 s₂ := K₁.trans ⟨fun r hr => h₂.gpr r fun e => hr (by rw [e]; decide), h₂.rd, h₂.wr, h₂.sp,
    hf.mono fun _ hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..⟩
  have hm₁ : s₁.mem = s0.mem := k₁.2.1
  refine ⟨K₂, K₂.core hC, by rw [h₂.gpr _ (by decide), h6], fun j hj => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [h₂.outs j hj, hm₁]
    have := hPt.lt hj
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [dwA_kept hC₁ hf hi, hm₁]
  · rw [dwB_kept hC₁ hf hi, hm₁]

/-- The operands' words below `2⁶⁰`. -/
theorem srcsLt {b A B O P : Addr} {s0 s : State} (h : Dbl b A B O P s0 s) (hA : TightF (fun i => dw s0.mem A (8 * i)))
    (hB : TightF (fun i => dw s0.mem B (8 * i))) (hPt : TightF (fun i => dw s0.mem P (8 * i))) {ts : List Tm}
    (hsrc : SrcsOk ts) : SrcsLt s ts := by
  have key : ∀ x, srcOk x = true → sv s x < 2 ^ 60 := fun x hx => by
    unfold sv
    rcases srcOk_cases hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · dsimp only; rw [h.core.a, h.as i hi]; exact Nat.lt_trans (hA.lt hi) (by decide)
    · dsimp only; rw [h.core.b', h.bs i hi]; exact Nat.lt_trans (hB.lt hi) (by decide)
    · dsimp only; rw [h.core.ctx.a3, h.ys j hj]; have := hPt.lt hj; omega
  exact fun n hn => ⟨key _ (hsrc n hn).1, key _ (hsrc n hn).2⟩

/-- The kernel's result: tight, and its number modulo `p`. -/
def MulPost (b O : Addr) (V : Nat) (s0 s : State) : Prop :=
  Kept b O s0 s ∧ TightF (fun j => dw s.mem O (8 * j)) ∧ lv (fun j => dw s.mem O (8 * j)) 9 % p = V % p

/-- The columns, then the fold. -/
theorem colsFold_ok {b A B O P : Addr} {s0 s : State} (hC : CoreOk 9 b A B O s0) (h : Dbl b A B O P s0 s)
    {ts : List Tm} {ps : Nat → List (Src × Src)} (ht : Tab ts ps) (hlt : SrcsLt s ts) {V H : Nat}
    (hV : lv (col s ps) 9 + 2 ^ 522 * H = V + 2 * H) :
    WP isa (.block (pipe ts (fun c => (ps c).length) ++ fold)) s (MulPost b O V s0) := by
  refine WP.block_append (WP.mono (pipe_ok h.core h.a6 ht hlt) fun s₃ h₃ => ?_)
  have K₃ : Kept b O s0 s₃ := h.kept.trans ⟨h₃.inv.gpr, h₃.inv.rd, h₃.inv.wr, h₃.inv.sp,
    h₃.inv.frame.sub fun _ hr => ⟨_, List.mem_cons_self .., by
      rw [List.mem_singleton.mp hr]; exact own_sub (by rw [Z_eq]) (by rw [Z_eq]; omega)⟩⟩
  refine WP.mono (fold_ok (K₃.core hC) (h₃.inv.a6.trans h.a6) h₃.lt h₃.accLt) fun s₄ ⟨K₄, e₄, t₄⟩ =>
    ⟨K₃.trans K₄, t₄, mod_cancel (K := acc s₃ + H) ?_⟩
  have hv := h₃.val
  rw [show 58 * 9 = 522 from rfl] at hv
  rw [e₄]
  have : lv (fun c => dw s₃.mem b (Z + 8 * c)) 9 + 2 * acc s₃ + 2 ^ 522 * (acc s₃ + H) =
      (lv (fun c => dw s₃.mem b (Z + 8 * c)) 9 + 2 ^ 522 * acc s₃) + 2 ^ 522 * H + 2 * acc s₃ := by
    rw [Nat.mul_add]; omega
  rw [this, hv, hV]
  omega

/-- `mulC`: `[O] ≡ [A] [B]`. -/
theorem mulC_ok {b A B O : Addr} {s : State} (hC : CoreOk 9 b A B O s) (hA : TightF (fun i => dw s.mem A (8 * i)))
    (hB : TightF (fun i => dw s.mem B (8 * i))) :
    WP isa (.block mulC) s (MulPost b O (lv (fun i => dw s.mem A (8 * i)) 9 * lv (fun j => dw s.mem B (8 * j)) 9) s) := by
  unfold mulC
  rw [List.append_assoc (mask ++ dbl .t5)]
  refine maskDbl_ok hC (P := B) (.inr ⟨rfl, rfl⟩) hB fun s₂ h₂ => ?_
  refine colsFold_ok hC h₂ tab_mul (srcsLt h₂ hA hB hB tab_mul.src)
    (H := lv (mhi (fun i => dw s.mem A (8 * i)) (fun j => dw s.mem B (8 * j))) 9) ?_
  have e : lv (col s₂ mulPairs) 9 = lv (fun c => mlo (fun i => dw s.mem A (8 * i)) (fun j => dw s.mem B (8 * j)) c +
      2 * mhi (fun i => dw s.mem A (8 * i)) (fun j => dw s.mem B (8 * j)) c) 9 :=
    lv_congr fun c hc => mulCol_eq _ _ _ (fun i hi => ?_) (fun j hj => ?_) (fun j hj => ?_) hc
  · rw [e]; exact mulCols_sum _ _
  · show dw s₂.mem (s₂.gpr .t4) (8 * i) = _; rw [h₂.core.a, h₂.as i hi]
  · show dw s₂.mem (s₂.gpr .t5) (8 * j) = _; rw [h₂.core.b', h₂.bs j hj]
  · show dw s₂.mem (s₂.gpr .a3) (Y + 8 * j) = _; rw [h₂.core.ctx.a3, h₂.ys j hj]

/-- `sqC`: `[O] ≡ [A]²`. -/
theorem sqC_ok {b A O : Addr} {s : State} (hC : CoreOk 9 b A A O s) (hA : TightF (fun i => dw s.mem A (8 * i))) :
    WP isa (.block sqC) s (MulPost b O (lv (fun i => dw s.mem A (8 * i)) 9 * lv (fun j => dw s.mem A (8 * j)) 9) s) := by
  unfold sqC
  rw [List.append_assoc (mask ++ dbl .t4)]
  refine maskDbl_ok hC (P := A) (.inl ⟨rfl, rfl⟩) hA fun s₂ h₂ => ?_
  refine colsFold_ok hC h₂ tab_sq (srcsLt h₂ hA hA hA tab_sq.src) (H := lv (shi (fun i => dw s.mem A (8 * i))) 9) ?_
  have e : lv (col s₂ sqPairs) 9 = lv (fun c => 2 * scr (fun i => dw s.mem A (8 * i)) c +
      sdg (fun i => dw s.mem A (8 * i)) c + 2 * shi (fun i => dw s.mem A (8 * i)) c) 9 :=
    lv_congr fun c hc => sqCol_eq _ _ (fun i hi => ?_) (fun j hj => ?_) hc
  · rw [e]; exact sqCols_sum _
  · show dw s₂.mem (s₂.gpr .t4) (8 * i) = _; rw [h₂.core.a, h₂.as i hi]
  · show dw s₂.mem (s₂.gpr .a3) (Y + 8 * j) = _; rw [h₂.core.ctx.a3, h₂.ys j hj]

/-- `core`: the square if the pointers are equal, else the product. -/
theorem core_spec :
    CoreSpecP 9 core (fun A B => Tight A ∧ Tight B) (fun A B r => Tight r ∧ uv r % p = uv A * uv B % p) := by
  intro b A B O s hC ⟨hA, hB⟩
  rw [tight_xv] at hA hB
  have post : ∀ s', MulPost b O (lv (fun i => dw s.mem A (8 * i)) 9 * lv (fun j => dw s.mem B (8 * j)) 9) s s' →
      (Tight (ov s'.mem O 9) ∧ uv (ov s'.mem O 9) % p = uv (xv s.mem A 9) * uv (xv s.mem B 9) % p) ∧
      Frame [ownR 9 b, ⟨O, 8 * 9⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobW → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := fun s' ⟨K, t, v⟩ =>
    ⟨⟨tight_xv.mpr t, by rw [uv_xv, uv_xv, uv_xv]; exact v⟩, K.frame, K.gpr, K.rd, K.wr, K.sp⟩
  unfold core
  refine WP.ite (s.gpr .t4 == s.gpr .t5) rfl (fun he => ?_) (fun _ => ?_)
  · have hAB : A = B := by rw [← hC.a, ← hC.b']; exact beq_iff_eq.mp he
    subst hAB
    exact WP.mono (sqC_ok hC hA) post
  · exact WP.mono (mulC_ok hC hA hB) post

end VG.Proof.Weierstrass.RISCV64.P521Unsat
