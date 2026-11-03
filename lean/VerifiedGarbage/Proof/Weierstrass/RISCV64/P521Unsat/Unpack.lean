module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Cols
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Arithmetic modulo P-521's prime in 58-bit limbs, on RISC-V: words to limbs

`unpackC` (`Impl/Weierstrass/RISCV64/P521Unsat.lean`) meets GenWide's
specification of an operation (`GenWide.CoreSpecP`): a number below
`2⁵²²` as nine words to its limbs, tight, of the same number
(`unpack_spec`). Limb `k` from the words it has bits of (`ulimb`, by
`unpackStep_ok`), which are the number's bits `58 k …` (`ulimb_eq`).
-/

@[expose] public section

-- The limbs' positions are numerals.
set_option exponentiation.threshold 600

namespace VG.Proof.Weierstrass.RISCV64.P521Unsat

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P521Unsat
open VG.Proof.Weierstrass.RISCV64.GenWide (CoreOk CoreSpecP ownR clobW xv ov)
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8)

/-- Limb `k` of the number `X`, as `unpackStep k` computes it from its words. -/
def ulimb (X k : Nat) : Nat :=
  if 64 - 58 * k % 64 < 58 ∧ 58 * k / 64 + 1 < 9 then
    (lw X (58 * k / 64) / 2 ^ (58 * k % 64) + lw X (58 * k / 64 + 1) * 2 ^ (64 - 58 * k % 64) % 2 ^ 64) % 2 ^ 64 %
      2 ^ 58
  else lw X (58 * k / 64) / 2 ^ (58 * k % 64) % 2 ^ 58

set_option linter.unusedSimpArgs false in
theorem ulimb_eq (X : Nat) : ∀ k < 9, ulimb X k = X / 2 ^ (58 * k) % 2 ^ 58 := by
  intro k hk
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals simp only [ulimb, lw, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd,
    Nat.reduceLT, Nat.lt_irrefl, and_true, and_false, true_and, false_and, ↓reduceIte, Nat.pow_zero, Nat.div_one,
    Nat.zero_add, Nat.mul_zero]
  all_goals omega

theorem lv_digits (X : Nat) : ∀ n, lv (fun k => X / 2 ^ (58 * k) % 2 ^ 58) n = X % 2 ^ (58 * n)
  | 0 => by rw [lv, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | n + 1 => by
    rw [lv, lv_digits X n, show 58 * (n + 1) = 58 * n + 58 by omega, Nat.pow_add, Nat.mod_mul]

/-- After `k` limbs of the unpacking of `X`. -/
structure UInv (b O : Addr) (X : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  kept : Kept b O s0 s
  a6 : s.gpr .a6 = M58
  fz : Frame [Zr b] s0.mem s.mem
  outs : ∀ j < k, dw s.mem b (Z + 8 * j) = ulimb X j

theorem unpackStep_ok {b A B O : Addr} {s0 : State} (hC : CoreOk 9 b A B O s0) {k : Nat} (hk : k < 9) {s : State}
    (h : UInv b O (xv s0.mem A 9) s0 k s) :
    WP isa (.block (unpackStep k)) s (UInv b O (xv s0.mem A 9) s0 (k + 1)) := by
  have hb := hC.nowrap
  have hCs := h.kept.core hC
  have hfo : Frame [ownR 9 b] s0.mem s.mem := h.fz.sub fun _ hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact own_sub (by rw [Z_eq]) (by rw [Z_eq]; omega)⟩
  have hw : ∀ i < 9, (s.mem.readW (A + BitVec.ofNat 64 (8 * i)) 64).toNat = lw (xv s0.mem A 9) i := fun i hi => by
    rw [lw_xv _ _ hi, ← dwA_kept hC hfo hi]; rfl
  have hw8 : 58 * k / 64 < 8 := by omega
  -- The limb into `a1`, through `a2`.
  have mid : WP isa (.block ([.load .d .a1 .t4 (8 * (58 * k / 64)), .shift .srl .d .a1 .a1 (58 * k % 64)] ++
      (if 64 - 58 * k % 64 < 58 ∧ 58 * k / 64 + 1 < 9 then
        [.load .d .a2 .t4 (8 * (58 * k / 64 + 1)), .shift .sll .d .a2 .a2 (64 - 58 * k % 64), .add .a1 .a1 .a2]
       else []) ++ [.logic .and .a1 .a1 .a6])) s fun s' =>
        (s'.gpr .a1).toNat = ulimb (xv s0.mem A 9) k ∧ Keeps [.a1, .a2] s s' := by
    simp only [List.cons_append, List.nil_append]
    refine ldA_ok hCs (by omega) fun s₁ u₁ => wp_srl (by omega) fun s₂ u₂ => ?_
    have e₂ : (s₂.gpr .a1).toNat = lw (xv s0.mem A 9) (58 * k / 64) / 2 ^ (58 * k % 64) := by
      rw [u₂.gpr, u₁.gpr, shr_toNat, hw _ (by omega)]
    have k2 : Keeps [.a1, .a2] s s₂ := ⟨fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; rw [u₂.other r hr.1, u₁.other r hr.1],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩
    have hm6 : s₂.gpr .a6 = M58 := by rw [k2.1 _ (by decide), h.a6]
    split
    · rename_i hc
      have hC₂ := core_of hCs (fun r hr => k2.1 r fun e => hr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at e; rcases e with rfl | rfl <;> decide)) k2.2.2.1
        k2.2.2.2.1
      refine ldA_ok hC₂ (by omega) fun s₃ u₃ => wp_sll (by omega) fun s₄ u₄ => wp_add fun s₅ u₅ =>
        wp_and fun s₆ u₆ => WP.block_nil ⟨?_, ?_⟩
      · simp only [u₆.gpr, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, ne_eq, reduceCtorEq,
          not_false_eq_true, hm6]
        rw [and_M58, BitVec.toNat_add, e₂, shl_toNat, u₂.mem, u₁.mem, hw _ (by omega), ulimb, ite_eq_left hc]
      · exact (k2.trans (rs' := [.a1, .a2]) ⟨fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          rw [u₆.other _ hr.1, u₅.other _ hr.1, u₄.other _ hr.2, u₃.other _ hr.2],
          by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem], by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd],
          by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr], by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp]⟩).mono (by decide)
    · rename_i hc
      refine wp_and fun s₃ u₃ => WP.block_nil ⟨?_, ?_⟩
      · rw [u₃.gpr, hm6, and_M58, e₂, ulimb, ite_eq_right hc]
      · exact (k2.trans (rs' := [.a1]) ⟨fun r hr => u₃.other r (by simpa using hr), u₃.mem, u₃.rd, u₃.wr,
          u₃.sp⟩).mono (by decide)
  have e : unpackStep k = ([.load .d .a1 .t4 (8 * (58 * k / 64)), .shift .srl .d .a1 .a1 (58 * k % 64)] ++
      (if 64 - 58 * k % 64 < 58 ∧ 58 * k / 64 + 1 < 9 then
        [.load .d .a2 .t4 (8 * (58 * k / 64 + 1)), .shift .sll .d .a2 .a2 (64 - 58 * k % 64), .add .a1 .a1 .a2]
       else []) ++ [.logic .and .a1 .a1 .a6]) ++ [.store .d .a1 .a3 (Z + 8 * k)] := by
    simp only [unpackStep, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  refine WP.block_append (WP.mono mid fun s₁ ⟨e₁, k₁⟩ => ?_)
  have hc₁ : Ctx b s₁ := ⟨by rw [k₁.1 _ (by decide), hCs.ctx.a3], hCs.ctx.al, by rw [k₁.2.2.2.1]; exact hCs.ctx.wr⟩
  refine sd_ok hc₁ (by rw [Z_eq]; omega) (by rw [Z_eq]; omega) fun s₂ u₂ => WP.block_nil ?_
  have hm₂ : s₂.mem = s.mem.writeW (b + BitVec.ofNat 64 (Z + 8 * k)) (s₁.gpr .a1) := by rw [u₂.mem, k₁.2.1]
  refine ⟨(h.kept.keeps k₁).sd (by rw [Z_eq]; omega) (by rw [Z_eq]; omega) u₂, by rw [u₂.gpr, k₁.1 _ (by decide), h.a6],
    by rw [hm₂]; exact h.fz.writeW (List.mem_singleton_self _) _ (Offset.contains b (by rw [Z_eq]; omega)
      (by rw [Z_eq]; omega) (by rw [Z_eq]; omega)), fun j hj => ?_⟩
  rw [hm₂]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · rw [dw_write_other _ _ _ (by omega) (by rw [Z_eq]; omega) (by rw [Z_eq]; omega)]; exact h.outs j hj
  · rw [dw_write_self, e₁]

/-- `unpackC`: the limbs of a number below `2⁵²²`. -/
theorem unpack_spec :
    CoreSpecP 9 (.block unpackC) (fun A _ => A < 2 ^ 522) (fun A _ r => Tight r ∧ uv r = A) := by
  intro b A B O s hC hA
  unfold unpackC
  rw [List.append_assoc]
  refine mask_ok fun s₁ k₁ h6 => ?_
  have K₁ : Kept b O s s₁ := (Kept.refl b O s).keeps k₁
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (UInv b O (xv s.mem A 9) s)
    (fun k s' hk h => unpackStep_ok hC hk h) 9 (Nat.le_refl _) s₁
    ⟨K₁, h6, by rw [k₁.2.1]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s₂ h₂ => ?_)
  refine WP.mono (copyZ_ok (h₂.kept.core hC) (j₀ := 0) (by decide)) fun s' ⟨K', _, hout⟩ => ?_
  have hb := hC.nowrap
  have hm : ∀ j < 9, dw s'.mem O (8 * j) = ulimb (xv s.mem A 9) j := fun j hj => by
    rw [hout j hj, ite_eq_left (Nat.zero_le _)]; exact h₂.outs j hj
  have hlt : ∀ j < 9, dw s'.mem O (8 * j) < 2 ^ 58 := fun j hj => by
    rw [hm j hj, ulimb_eq _ j hj]; exact Nat.mod_lt _ (by decide)
  refine ⟨⟨tight_xv.mpr ⟨fun i hi => Nat.lt_trans (hlt i (by omega)) (by decide), hlt 8 (by decide)⟩, ?_⟩,
    (h₂.kept.trans K').frame, (h₂.kept.trans K').gpr, (h₂.kept.trans K').rd, (h₂.kept.trans K').wr,
    (h₂.kept.trans K').sp⟩
  rw [uv_xv, lv_congr (g := fun k => xv s.mem A 9 / 2 ^ (58 * k) % 2 ^ 58) fun j hj => by
    rw [hm j hj, ulimb_eq _ j hj], lv_digits, Nat.mod_eq_of_lt hA]

end VG.Proof.Weierstrass.RISCV64.P521Unsat
