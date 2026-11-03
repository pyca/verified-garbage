module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Cols
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Arithmetic modulo P-521's prime in 58-bit limbs, on RISC-V: sums and differences

`addC false` and `addC true` (`Impl/Weierstrass/RISCV64/P521Unsat.lean`)
meet GenWide's specification of an operation (`GenWide.CoreSpecP`): tight
operands to a tight result, `[a] + [b]` and `[a] + 4p - [b]` modulo `p`
(`add_spec`, `sub_spec`). Limb by limb with the carries (`addStep_ok`),
`4p`'s limbs in `a7` and `t6` for the difference, then the last carry,
doubled, into limb 0.
-/

@[expose] public section

-- `2⁵²²` and `p` are numerals.
set_option exponentiation.threshold 600

namespace VG.Proof.Weierstrass.RISCV64.P521Unsat

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P521Unsat
open VG.Proof.Weierstrass.RISCV64.GenWide (CoreOk CoreSpecP ownR clobW xv ov)
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8)

/-- Limb `j` of `4p`. -/
def p4 (j : Nat) : Nat := if j < 8 then 2 ^ 60 - 4 else 2 ^ 59 - 4

/-- Limb `j` of the sum or the difference, before the carries. -/
def addT (sub : Bool) (a b : Nat → Nat) (j : Nat) : Nat := if sub then a j + p4 j - b j else a j + b j

theorem lv_p4 : lv p4 9 = 4 * p := by
  simp only [lv, p4, Nat.reduceMul, Nat.reduceLT, ↓reduceIte, Nat.lt_irrefl]
  decide

theorem lv_add (f g : Nat → Nat) : ∀ n, lv (fun j => f j + g j) n = lv f n + lv g n
  | 0 => rfl
  | n + 1 => by rw [lv, lv, lv, lv_add f g n, Nat.mul_add]; omega

/-- The limbs of the sum or the difference: `[a] + [b]`, or `[a] + 4p - [b]`. -/
theorem lv_addT (sub : Bool) {a b : Nat → Nat} (hb : TightF b) :
    lv (addT sub a b) 9 = if sub then lv a 9 + 4 * p - lv b 9 else lv a 9 + lv b 9 := by
  cases sub
  · exact lv_add a b 9
  · have e : lv (addT true a b) 9 + lv b 9 = lv a 9 + lv p4 9 := by
      rw [← lv_add, ← lv_add]
      refine lv_congr fun j hj => ?_
      simp only [addT, ↓reduceIte, p4]
      have := hb.lt hj
      have h8 := hb.2
      split <;> rename_i h
      · omega
      · have : j = 8 := by omega
        subst this; omega
    rw [lv_p4] at e
    simp only [↓reduceIte]
    omega

/-- The constants of the difference: `4p`'s limbs. -/
def Consts (sub : Bool) (s : State) : Prop :=
  sub = true → (s.gpr .a7).toNat = 2 ^ 60 - 4 ∧ (s.gpr .t6).toNat = 2 ^ 59 - 4

/-- After `i` limbs of `addC sub`. -/
structure AddInv (sub : Bool) (b A B O : Addr) (s0 : State) (i : Nat) (s : State) : Prop where
  kept : Kept b O s0 s
  a6 : s.gpr .a6 = M58
  consts : Consts sub s
  fz : Frame [Zr b] s0.mem s.mem
  lt : ∀ j < i, dw s.mem b (Z + 8 * j) < 2 ^ 58
  carry : (s.gpr .a4).toNat < 8
  val : lv (fun j => dw s.mem b (Z + 8 * j)) i + 2 ^ (58 * i) * (s.gpr .a4).toNat =
    lv (addT sub (fun j => dw s0.mem A (8 * j)) (fun j => dw s0.mem B (8 * j))) i

/-- The limb's sum or difference, from `a1` and `a2`. -/
theorem mid_ok (sub : Bool) {i : Nat} (hi : i < 9) {s : State} (hc : Consts sub s) (hx : (s.gpr .a1).toNat < 2 ^ 59)
    (hy : (s.gpr .a2).toNat < 2 ^ 59) (hy8 : i = 8 → (s.gpr .a2).toNat < 2 ^ 58) :
    WP isa (.block (if sub then [.add .a1 .a1 (if i < 8 then .a7 else .t6), .sub .a1 .a1 .a2]
        else [.add .a1 .a1 .a2])) s fun s' =>
      (s'.gpr .a1).toNat = (if sub then (s.gpr .a1).toNat + p4 i - (s.gpr .a2).toNat
        else (s.gpr .a1).toNat + (s.gpr .a2).toNat) ∧ Keeps [.a1] s s' := by
  have keep1 : ∀ {s' : State} {v : BitVec 64}, Upd s s' .a1 v → Keeps [.a1] s s' := fun u =>
    ⟨fun r hr => u.other r (by simpa using hr), u.mem, u.rd, u.wr, u.sp⟩
  cases sub
  · refine wp_add fun s₁ u₁ => WP.block_nil ⟨?_, keep1 u₁⟩
    rw [u₁.gpr, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; rfl
  · obtain ⟨h7, h6⟩ := hc rfl
    simp only [↓reduceIte]
    refine wp_add fun s₁ u₁ => wp_sub fun s₂ u₂ => WP.block_nil ⟨?_, ?_⟩
    · have hc : (s.gpr (if i < 8 then .a7 else .t6)).toNat = p4 i := by
        unfold p4; split <;> assumption
      rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), BitVec.toNat_sub_of_le, BitVec.toNat_add, hc,
        Nat.mod_eq_of_lt (by unfold p4; split <;> omega)]
      · rw [BitVec.le_def, BitVec.toNat_add, hc, Nat.mod_eq_of_lt (by unfold p4; split <;> omega)]
        unfold p4; split
        · omega
        · rename_i h; have := hy8 (by omega); omega
    · exact ⟨fun r hr => by rw [u₂.other r (by simpa using hr), u₁.other r (by simpa using hr)],
        by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩

theorem step_arith {L Lt K c t : Nat} (hv : L + K * c = Lt) :
    L + K * ((t + c) % 2 ^ 58) + K * 2 ^ 58 * ((t + c) / 2 ^ 58) = Lt + K * t := by
  have h : K * ((t + c) % 2 ^ 58) + K * 2 ^ 58 * ((t + c) / 2 ^ 58) = K * t + K * c := by
    rw [Nat.mul_assoc, ← Nat.mul_add, Nat.add_comm, Nat.div_add_mod, Nat.mul_add]
  omega

/-- Limb `i`. -/
theorem addStep_ok (sub : Bool) {b A B O : Addr} {s0 : State} (hC : CoreOk 9 b A B O s0)
    (hA : TightF (fun i => dw s0.mem A (8 * i))) (hB : TightF (fun i => dw s0.mem B (8 * i))) {i : Nat} (hi : i < 9)
    {s : State} (h : AddInv sub b A B O s0 i s) :
    WP isa (.block (addStep sub i)) s (AddInv sub b A B O s0 (i + 1)) := by
  have hb := hC.nowrap
  have hCs := h.kept.core hC
  have hfo : Frame [ownR 9 b] s0.mem s.mem := h.fz.sub fun _ hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact own_sub (by rw [Z_eq]) (by rw [Z_eq]; omega)⟩
  unfold addStep
  simp only [List.cons_append, List.nil_append]
  refine ldA_ok hCs hi fun s₁ u₁ => ?_
  have hC₁ := core_of hCs (fun r hr => u₁.other r fun e => hr (by rw [e]; decide)) u₁.rd u₁.wr
  refine ldB_ok hC₁ hi fun s₂ u₂ => ?_
  have ex : (s₂.gpr .a1).toNat = dw s0.mem A (8 * i) := by
    rw [u₂.other _ (by decide), u₁.gpr, ← dwA_kept hC hfo hi]; rfl
  have ey : (s₂.gpr .a2).toNat = dw s0.mem B (8 * i) := by
    rw [u₂.gpr, u₁.mem, ← dwB_kept hC hfo hi]; rfl
  have hc₂ : Consts sub s₂ := fun e => by
    rw [u₂.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide)]
    exact h.consts e
  refine WP.block_append (WP.mono (mid_ok sub hi hc₂ (by rw [ex]; exact hA.lt hi) (by rw [ey]; exact hB.lt hi)
    (fun e => by subst e; rw [ey]; exact hB.2)) fun s₃ ⟨e₃, k₃⟩ => ?_)
  refine wp_add fun s₄ u₄ => wp_srl (by decide) fun s₅ u₅ => wp_and fun s₆ u₆ => ?_
  have hc₆ : Ctx b s₆ := ⟨by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), k₃.1 _ (by decide),
        u₂.other _ (by decide), hC₁.ctx.a3],
    hC.ctx.al, by rw [u₆.wr, u₅.wr, u₄.wr, k₃.2.2.2.1, u₂.wr]; exact hC₁.ctx.wr⟩
  refine sd_ok hc₆ (by rw [Z_eq]; omega) (by rw [Z_eq]; omega) fun s₇ u₇ => WP.block_nil ?_
  -- The numbers.
  have hT : (s₃.gpr .a1).toNat = addT sub (fun j => dw s0.mem A (8 * j)) (fun j => dw s0.mem B (8 * j)) i := by
    rw [e₃, ex, ey]; rfl
  have hTl : addT sub (fun j => dw s0.mem A (8 * j)) (fun j => dw s0.mem B (8 * j)) i < 2 ^ 60 + 2 ^ 59 := by
    have h1 : dw s0.mem A (8 * i) < 2 ^ 59 := hA.lt hi
    have h2 : dw s0.mem B (8 * i) < 2 ^ 59 := hB.lt hi
    unfold addT p4
    dsimp only
    split <;> (try split) <;> omega
  have hc4 : (s₃.gpr .a4).toNat = (s.gpr .a4).toNat := by
    rw [k₃.1 _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have ha4 : (s₄.gpr .a1).toNat = addT sub (fun j => dw s0.mem A (8 * j)) (fun j => dw s0.mem B (8 * j)) i +
      (s.gpr .a4).toNat := by
    rw [u₄.gpr, BitVec.toNat_add, hT, hc4]
    exact Nat.mod_eq_of_lt (by have := h.carry; omega)
  generalize ht : addT sub (fun j => dw s0.mem A (8 * j)) (fun j => dw s0.mem B (8 * j)) i = t at hTl ha4
  have hm6 : s₆.gpr .a6 = M58 := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), k₃.1 _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.a6]
  have hz : (s₆.gpr .a1).toNat = (t + (s.gpr .a4).toNat) % 2 ^ 58 := by
    rw [u₆.gpr, u₅.other .a1 (by decide), u₅.other .a6 (by decide), u₄.other .a6 (by decide), k₃.1 .a6 (by decide),
      u₂.other .a6 (by decide), u₁.other .a6 (by decide), h.a6, and_M58, ha4]
  have hcar : (s₇.gpr .a4).toNat = (t + (s.gpr .a4).toNat) / 2 ^ 58 := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.gpr, shr_toNat, ha4]
  have hK₇ : Kept b O s0 s₇ := by
    have K₃ : Kept b O s0 s₃ := ((h.kept.upd u₁).upd u₂).keeps k₃
    exact (((K₃.upd u₄).upd u₅).upd u₆).sd (by rw [Z_eq]; omega) (by rw [Z_eq]; omega) u₇
  have hm₇ : s₇.mem = s.mem.writeW (b + BitVec.ofNat 64 (Z + 8 * i)) (s₆.gpr .a1) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, k₃.2.1, u₂.mem, u₁.mem]
  have hold : ∀ j < i, dw s₇.mem b (Z + 8 * j) = dw s.mem b (Z + 8 * j) := fun j hj => by
    rw [hm₇, dw_write_other _ _ _ (by omega) (by rw [Z_eq]; omega) (by rw [Z_eq]; omega)]
  refine ⟨hK₇, ?_, fun e => ?_, ?_, fun j hj => ?_, ?_, ?_⟩
  · rw [u₇.gpr, hm6]
  · rw [u₇.gpr, u₆.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₄.other _ (by decide), k₃.1 _ (by decide), k₃.1 _ (by decide)]
    exact hc₂ e
  · rw [hm₇]
    exact h.fz.writeW (List.mem_singleton_self _) _ (Offset.contains b (by rw [Z_eq]; omega) (by rw [Z_eq]; omega)
      (by rw [Z_eq]; omega))
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [hold j hj]; exact h.lt j hj
    · rw [hm₇, dw_write_self, hz]; exact Nat.mod_lt _ (by decide)
  · rw [hcar]; have := h.carry; omega
  · have e₁ : lv (fun j => dw s₇.mem b (Z + 8 * j)) i = lv (fun j => dw s.mem b (Z + 8 * j)) i := lv_congr hold
    have e₂ : dw s₇.mem b (Z + 8 * i) = (t + (s.gpr .a4).toNat) % 2 ^ 58 := by rw [hm₇, dw_write_self, hz]
    simp only [lv]
    rw [e₁, e₂, hcar, ht, show 58 * (i + 1) = 58 * i + 58 by omega, Nat.pow_add]
    exact step_arith h.val

/-- The constants of the difference. -/
theorem consts_ok (sub : Bool) {s : State} :
    WP isa (.block (if sub then [.li .a7 1, .shift .sll .d .a7 .a7 60, .addi .a7 .a7 (-4), .li .t6 1,
        .shift .sll .d .t6 .t6 59, .addi .t6 .t6 (-4)] else [])) s fun s' =>
      Consts sub s' ∧ Keeps [.a7, .t6] s s' := by
  cases sub
  · exact WP.block_nil ⟨fun h => absurd h (by decide), Keeps.refl _ _⟩
  · simp only [↓reduceIte]
    refine wp_li (imm := 1) (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_subi (imm := 4) (by decide)
      fun s₃ u₃ => wp_li (imm := 1) (by decide) fun s₄ u₄ => wp_sll (by decide) fun s₅ u₅ =>
      wp_subi (imm := 4) (by decide) fun s₆ u₆ => WP.block_nil ⟨fun _ => ⟨?_, ?_⟩, ?_⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr]; decide
    · rw [u₆.gpr, u₅.gpr, u₄.gpr]; decide
    · refine ⟨fun r hr => ?_, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
        by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
        by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₆.other _ hr.2, u₅.other _ hr.2, u₄.other _ hr.2, u₃.other _ hr.1, u₂.other _ hr.1, u₁.other _ hr.1]

/-- `addC sub`: `[O] ≡ [A] + [B]`, or `[A] + 4p - [B]`. -/
theorem addC_ok (sub : Bool) {b A B O : Addr} {s : State} (hC : CoreOk 9 b A B O s)
    (hA : TightF (fun i => dw s.mem A (8 * i))) (hB : TightF (fun i => dw s.mem B (8 * i))) :
    WP isa (.block (addC sub)) s fun s' => Kept b O s s' ∧ TightF (fun j => dw s'.mem O (8 * j)) ∧
      lv (fun j => dw s'.mem O (8 * j)) 9 % p =
        lv (addT sub (fun j => dw s.mem A (8 * j)) (fun j => dw s.mem B (8 * j))) 9 % p := by
  have hb := hC.nowrap
  unfold addC
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine mask_ok fun s₁ k₁ h6 => wp_li (imm := 0) (by decide) fun s₂ u₂ => ?_
  refine WP.block_append (WP.mono (consts_ok sub) fun s₃ ⟨c₃, k₃⟩ => ?_)
  have K₃ : Kept b O s s₃ := (((Kept.refl b O s).keeps k₁).upd u₂).keeps k₃
  have hm₃ : s₃.mem = s.mem := by rw [k₃.2.1, u₂.mem, k₁.2.1]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (AddInv sub b A B O s)
    (fun i s' hi h => addStep_ok sub hC hA hB hi h) 9 (Nat.le_refl _) s₃
    ⟨K₃, by rw [k₃.1 _ (by decide), u₂.other _ (by decide), h6], c₃, by rw [hm₃]; exact Frame.refl _ _,
      fun _ h => absurd h (Nat.not_lt_zero _), by rw [k₃.1 _ (by decide), u₂.gpr]; decide,
      by rw [k₃.1 _ (by decide), u₂.gpr]; rfl⟩) fun s₄ h₄ => ?_)
  have hC₄ := h₄.kept.core hC
  refine ld_ok hC₄.ctx (by rw [Z_eq]; omega) (by rw [Z_eq]) fun s₅ u₅ => wp_sll (by decide) fun s₆ u₆ =>
    wp_add fun s₇ u₇ => ?_
  have K₇ : Kept b O s s₇ := ((h₄.kept.upd u₅).upd u₆).upd u₇
  have hC₇ := K₇.core hC
  rw [show (0 : Nat) = 8 * 0 from rfl]
  refine sdO_ok hC₇ (by decide) fun s₈ u₈ => ?_
  have K₈ : Kept b O s s₈ := K₇.sdO (by decide) u₈
  refine WP.mono (copyZ_ok (K₈.core hC) (j₀ := 1) (by decide)) fun s' ⟨K', _, hout⟩ => ?_
  -- The numbers.
  have hc := h₄.carry
  have hz := h₄.lt
  have hv := h₄.val
  rw [show 58 * 9 = 522 from rfl] at hv
  have hm₇ : s₇.mem = s₄.mem := by rw [u₇.mem, u₆.mem, u₅.mem]
  have hm8 : ∀ d, 1472 ≤ d → d + 8 ≤ 1632 → dw s₈.mem b d = dw s₄.mem b d := fun d hd hd' => by
    rw [u₈.mem, dw_own_sdO hC (by decide) hd hd', hm₇]
  have e₇ : (s₇.gpr .a1).toNat = dw s₄.mem b (Z + 8 * 0) + 2 * (s₄.gpr .a4).toNat := by
    have hZ0 : (s₄.mem.readW (b + BitVec.ofNat 64 Z) 64).toNat = dw s₄.mem b (Z + 8 * 0) := rfl
    have := hz 0 (by decide)
    rw [u₇.gpr, u₆.other _ (by decide), u₆.gpr, u₅.gpr, u₅.other _ (by decide), BitVec.toNat_add, shl_toNat, hZ0,
      Nat.mod_eq_of_lt (by omega : (s₄.gpr .a4).toNat * 2 ^ 1 < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    omega
  have o0 : dw s'.mem O (8 * 0) = dw s₄.mem b (Z + 8 * 0) + 2 * (s₄.gpr .a4).toNat := by
    rw [hout 0 (by decide), ite_eq_right (by decide), u₈.mem, dw_write_self, e₇]
  have oj : ∀ j, 1 ≤ j → j < 9 → dw s'.mem O (8 * j) = dw s₄.mem b (Z + 8 * j) := fun j hj hj' => by
    rw [hout j hj', ite_eq_left hj, hm8 _ (by rw [Z_eq]; omega) (by rw [Z_eq]; omega)]
  refine ⟨K₈.trans K', ⟨fun i hi => ?_, ?_⟩, mod_cancel (K := (s₄.gpr .a4).toNat) ?_⟩
  · show dw s'.mem O (8 * i) < 2 ^ 59
    rcases Nat.eq_zero_or_pos i with rfl | h1
    · rw [o0]; have := hz 0 (by decide); simp only [Nat.mul_zero, Nat.add_zero] at this ⊢; omega
    · rw [oj i h1 (by omega)]; exact Nat.lt_trans (hz i (by omega)) (by decide)
  · show dw s'.mem O (8 * 8) < 2 ^ 58
    rw [oj 8 (by decide) (by decide)]; exact hz 8 (by decide)
  · rw [lv_fold (fun j => dw s'.mem O (8 * j)) (fun j => dw s₄.mem b (Z + 8 * j)) (C := (s₄.gpr .a4).toNat)
      (by show dw s'.mem O (8 * 0) + 2 ^ 58 * dw s'.mem O (8 * 1) = _; rw [o0, oj 1 (by decide) (by decide)]; omega)
      fun j hj hj' => oj j (by omega) hj', ← hv]
    omega

/-- The sum, as a specification. -/
theorem add_spec :
    CoreSpecP 9 (.block (addC false)) (fun A B => Tight A ∧ Tight B)
      (fun A B r => Tight r ∧ uv r % p = (uv A + uv B) % p) := by
  intro b A B O s hC ⟨hA, hB⟩
  rw [tight_xv] at hA hB
  refine WP.mono (addC_ok false hC hA hB) fun s' ⟨K, t, v⟩ =>
    ⟨⟨tight_xv.mpr t, ?_⟩, K.frame, K.gpr, K.rd, K.wr, K.sp⟩
  rw [uv_xv, uv_xv, uv_xv, v, lv_addT false hB]
  rfl

/-- The difference, as a specification. -/
theorem sub_spec :
    CoreSpecP 9 (.block (addC true)) (fun A B => Tight A ∧ Tight B)
      (fun A B r => Tight r ∧ uv r % p = (uv A + 4 * p - uv B) % p) := by
  intro b A B O s hC ⟨hA, hB⟩
  rw [tight_xv] at hA hB
  refine WP.mono (addC_ok true hC hA hB) fun s' ⟨K, t, v⟩ =>
    ⟨⟨tight_xv.mpr t, ?_⟩, K.frame, K.gpr, K.rd, K.wr, K.sp⟩
  rw [uv_xv, uv_xv, uv_xv, v, lv_addT true hB]
  rfl

end VG.Proof.Weierstrass.RISCV64.P521Unsat
