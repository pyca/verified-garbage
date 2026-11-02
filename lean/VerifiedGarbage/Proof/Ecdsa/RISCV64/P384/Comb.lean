module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Main
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Joint.Table
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulFn
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes

/-!
# The comb on RISC-V over P-384: the body

`vg_p384_mul_g`'s body, as `Proof/Ecdsa/RISCV64/Comb/Main.lean` proves
P-256's, from its lemmas that do not depend on the curve (the selections,
`tree_ok`, the window's bits, the digit's facts and the masks). What differs:

* The scan: a table's 64 entries of 96 bytes pass offset 2047, so quadword `q`
  of the entry is selected among four groups of 16 (`tree_ok` over bits 0 to
  3, at `a0` and at `a7` set to `a0` plus 16, 32 and 48 entries), the pairs
  by bit 4 and the two by bit 5 (`scanWord_ok`).
* The window reads the copy of `k` at `KC`, past 2047, by `ldAt`.
* The rows are `6144` bytes, `4096 j + 2048 j` (`row_ok`).
* The 55 steps, the six-word slots and the table of 55 rows.
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.Ecdsa.RISCV64.P384.Comb

open VG.Proof.Ecdsa.RISCV64.Comb (upd_keep wp_and wp_sra pick_mask wp_pick mod_two_pow_succ' tree_ok wp_sllReg
  wp_xori funnel_bit window_bits digit_facts mask_bit maskOfBit_ok masks_ok)

/-! ## The scan of a table's entries -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont
open VG.Proof.Weierstrass.RISCV64 (maskOf WsReg sd_ws)
open VG.Impl.Ecdsa.RISCV64 (DX)
open VG.Proof.Ecdsa.RISCV64.Joint (wp_addAt)

/-- The address of quadword `q` of entry `e` of the row at `T`. -/
abbrev entAddr (T : Addr) (q e : Nat) : Addr := T + BitVec.ofNat 64 (8 * q + 96 * e)

/-- What the scan needs of the row at `a0`: each quadword `q` of its 64
entries aligned and readable. -/
structure RowOk (s : State) (q : Nat) : Prop where
  ent : ∀ e < 64, (entAddr (s.gpr .a0) q e).toNat % 8 = 0 ∧ InRegions (s.rd ++ s.wr) (entAddr (s.gpr .a0) q e) 8

/-- The registers apart from those of the masks and the bases. -/
theorem treeRegs_ne : ∀ (b : Reg), b = .a0 ∨ b = .a7 → ∀ r ∈ treeRegs, r ≠ b ∧ ∀ c < 4, r ≠ maskReg c := by
  intro b hb r hr
  simp only [treeRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  refine ⟨?_, fun c hc => ?_⟩
  · rcases hb with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Quadword `q` of entry `t % 64` of the row at `a0`, by the masks of
`t`'s bits, to `D`'s word `q`. -/
theorem scanWord_ok {s : State} {base : Addr} (hw : WsReg s base) {q t : Nat} (hq : q < 12)
    (hm : ∀ c < 6, s.gpr (maskReg c) = maskOf (t.testBit c)) (hr : RowOk s q) :
    WP isa (.block (Impl.Ecdsa.RISCV64.Comb.Cfg.scanWord Impl.Ecdsa.RISCV64.p384 q)) s fun s' =>
      s'.mem = s.mem.writeW (off base (Impl.Ecdsa.RISCV64.p384.sl DX + 8 * q))
        (s.mem.readW (entAddr (s.gpr .a0) q (t % 64)) 64) ∧
      Keep (treeRegs ++ [.a7]) s s' := by
  have heb : Impl.Ecdsa.RISCV64.Comb.Cfg.eb Impl.Ecdsa.RISCV64.p384 = 96 := rfl
  have hDX : Impl.Ecdsa.RISCV64.p384.sl DX = 880 := rfl
  unfold Impl.Ecdsa.RISCV64.Comb.Cfg.scanWord
  simp only [show ¬ (Impl.Ecdsa.RISCV64.p384.n = 4) from by decide, ↓reduceIte]
  rw [heb, hDX, VG.Proof.Weierstrass.RISCV64.sdAt_lo (by omega)]
  simp only [List.append_assoc, show 16 * 96 = 1536 from rfl, show 32 * 96 = 3072 from rfl,
    show 48 * 96 = 4608 from rfl]
  have hne := treeRegs_ne
  have hmk : ∀ {s₁ : State} {rs : List Reg}, Keep rs s s₁ → (∀ c < 6, maskReg c ∉ rs) →
      ∀ c < 6, s₁.gpr (maskReg c) = maskOf (t.testBit c) := fun k h c hc => by rw [k.gpr (h c hc)]; exact hm c hc
  have mr : ∀ c < 6, maskReg c ∉ treeRegs ++ [.a7] := by
    intro c hc
    have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have mr' : ∀ {rs : List Reg}, (∀ r ∈ rs, r ∈ treeRegs ++ [.a7]) → ∀ c < 6, maskReg c ∉ rs :=
    fun h c hc hm' => mr c hc (h _ hm')
  have hgrp : ∀ {s₁ : State} (g : Nat), g < 4 → s₁.gpr .a0 = s.gpr .a0 → s₁.rd = s.rd → s₁.wr = s.wr →
      (g = 0 ∨ s₁.gpr .a7 = s.gpr .a0 + BitVec.ofNat 64 (1536 * g)) →
      ∀ e < 16, ((if g = 0 then s₁.gpr .a0 else s₁.gpr .a7) + BitVec.ofNat 64 (8 * q + 96 * e)).toNat % 8 = 0 ∧
        InRegions (s₁.rd ++ s₁.wr) ((if g = 0 then s₁.gpr .a0 else s₁.gpr .a7) + BitVec.ofNat 64 (8 * q + 96 * e)) 8 ∧
        (if g = 0 then s₁.gpr .a0 else s₁.gpr .a7) + BitVec.ofNat 64 (8 * q + 96 * e) =
          entAddr (s.gpr .a0) q (16 * g + e) := by
    intro s₁ g hg h0 hrd hwr h7 e he
    have hx : (if g = 0 then s₁.gpr .a0 else s₁.gpr .a7) + BitVec.ofNat 64 (8 * q + 96 * e) =
        entAddr (s.gpr .a0) q (16 * g + e) := by
      by_cases hg0 : g = 0
      · subst hg0; simp only [↓reduceIte, h0, entAddr, Nat.mul_zero, Nat.zero_add]
      · simp only [hg0, ↓reduceIte]
        rcases h7 with h7 | h7
        · exact absurd h7 hg0
        · rw [h7, BitVec.add_assoc, BitVec.ofNat_add_ofNat, entAddr]; congr 2; omega
    rw [hx, hrd, hwr]
    exact ⟨(hr.ent _ (by omega)).1, (hr.ent _ (by omega)).2, rfl⟩
  -- Group 0, at `a0`.
  refine WP.block_append (WP.mono (tree_ok .a0 96 t 4 (8 * q) .t0 [.t1, .t2, .t3, .t4, .t5, .t6] s (by decide)
    (by decide) (hne .a0 (.inl rfl)) (fun c hc => hm c (by omega)) (by omega)
    (fun e he => by
      have := hgrp (s₁ := s) 0 (by decide) rfl rfl rfl (.inl rfl) e he
      simp only [↓reduceIte] at this
      exact ⟨this.1, this.2.1⟩)) fun s₁ ⟨v₁, k₁, m₁⟩ => ?_)
  have e0₁ : s₁.gpr .a0 = s.gpr .a0 := by exact k₁.gpr (by decide)
  have v₁' : s₁.gpr .t0 = s.mem.readW (entAddr (s.gpr .a0) q (t % 16)) 64 := v₁
  -- Group 1, at `a0 + 1536`.
  refine wp_addAt (v := 1536) (by decide) fun s₂ u₂ => ?_
  have k₂ := upd_keep u₂
  have a7₂ : s₂.gpr .a7 = s.gpr .a0 + BitVec.ofNat 64 (1536 * 1) := by rw [u₂.gpr, e0₁]
  have e0₂ : s₂.gpr .a0 = s.gpr .a0 := by rw [u₂.other .a0 (by decide), e0₁]
  have rd₂ : s₂.rd = s.rd := by rw [k₂.2.1, k₁.2.1]
  have wr₂ : s₂.wr = s.wr := by rw [k₂.2.2, k₁.2.2]
  have hm₂ := hmk (k₁.trans k₂) (mr' (by simp [treeRegs]))
  refine WP.block_append (WP.mono (tree_ok .a7 96 t 4 (8 * q) .t1 [.t2, .t3, .t4, .t5, .t6] s₂ (by decide)
    (by decide) (fun r hr => hne .a7 (.inr rfl) r (by simp only [treeRegs]; exact List.mem_cons_of_mem _ hr))
    (fun c hc => hm₂ c (by omega)) (by omega)
    (fun e he => by
      have := hgrp 1 (by decide) e0₂ rd₂ wr₂ (.inr a7₂) e he
      simp only [show (1 : Nat) ≠ 0 from by decide, ↓reduceIte] at this
      exact ⟨this.1, this.2.1⟩)) fun s₃ ⟨v₃, k₃, m₃⟩ => ?_)
  have g1 := hgrp 1 (by decide) e0₂ rd₂ wr₂ (.inr a7₂) (t % 16) (Nat.mod_lt _ (by decide))
  simp only [show (1 : Nat) ≠ 0 from by decide, ↓reduceIte] at g1
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, m₁]
  rw [g1.2.2, m₂] at v₃
  -- Entries `0 … 31`, by bit 4.
  have a5₃ : s₃.gpr (maskReg 4) = maskOf (t.testBit 4) := by rw [k₃.gpr (by decide)]; exact hm₂ 4 (by decide)
  have t0₃ : s₃.gpr .t0 = s.mem.readW (entAddr (s.gpr .a0) q (t % 16)) 64 := by
    rw [k₃.gpr (by decide), u₂.other .t0 (by decide), v₁']
  refine wp_pick (by decide) (by decide) a5₃ fun s₄ v₄ k₄ m₄ => ?_
  rw [t0₃, v₃] at v₄
  have e0₄ : s₄.gpr .a0 = s.gpr .a0 := by rw [k₄.gpr (by decide), k₃.gpr (by decide), e0₂]
  -- Group 2, at `a0 + 3072`.
  refine wp_addAt (v := 3072) (by decide) fun s₅ u₅ => ?_
  have a7₅ : s₅.gpr .a7 = s.gpr .a0 + BitVec.ofNat 64 (1536 * 2) := by rw [u₅.gpr, e0₄]
  have e0₅ : s₅.gpr .a0 = s.gpr .a0 := by rw [u₅.other .a0 (by decide), e0₄]
  have rd₅ : s₅.rd = s.rd := by rw [u₅.rd, k₄.2.1, k₃.2.1, rd₂]
  have wr₅ : s₅.wr = s.wr := by rw [u₅.wr, k₄.2.2, k₃.2.2, wr₂]
  have K₅ : Keep (treeRegs ++ [.a7]) s s₅ :=
    (((k₁.trans k₂).trans k₃).trans (k₄.trans (upd_keep u₅))).mono (by simp [treeRegs])
  have hm₅ := hmk K₅ mr
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, m₄, m₃, m₂]
  refine WP.block_append (WP.mono (tree_ok .a7 96 t 4 (8 * q) .t1 [.t2, .t3, .t4, .t5, .t6] s₅ (by decide)
    (by decide) (fun r hr => hne .a7 (.inr rfl) r (by simp only [treeRegs]; exact List.mem_cons_of_mem _ hr))
    (fun c hc => hm₅ c (by omega)) (by omega)
    (fun e he => by
      have := hgrp 2 (by decide) e0₅ rd₅ wr₅ (.inr a7₅) e he
      simp only [show (2 : Nat) ≠ 0 from by decide, ↓reduceIte] at this
      exact ⟨this.1, this.2.1⟩)) fun s₆ ⟨v₆, k₆, m₆⟩ => ?_)
  have g2 := hgrp 2 (by decide) e0₅ rd₅ wr₅ (.inr a7₅) (t % 16) (Nat.mod_lt _ (by decide))
  simp only [show (2 : Nat) ≠ 0 from by decide, ↓reduceIte] at g2
  rw [g2.2.2, m₅] at v₆
  -- Group 3, at `a0 + 4608`.
  have e0₆ : s₆.gpr .a0 = s.gpr .a0 := by rw [k₆.gpr (by decide), e0₅]
  refine wp_addAt (v := 4608) (by decide) fun s₇ u₇ => ?_
  have a7₇ : s₇.gpr .a7 = s.gpr .a0 + BitVec.ofNat 64 (1536 * 3) := by rw [u₇.gpr, e0₆]
  have e0₇ : s₇.gpr .a0 = s.gpr .a0 := by rw [u₇.other .a0 (by decide), e0₆]
  have rd₇ : s₇.rd = s.rd := by rw [u₇.rd, k₆.2.1, rd₅]
  have wr₇ : s₇.wr = s.wr := by rw [u₇.wr, k₆.2.2, wr₅]
  have K₇ : Keep (treeRegs ++ [.a7]) s s₇ := ((K₅.trans k₆).trans (upd_keep u₇)).mono (by simp [treeRegs])
  have hm₇ := hmk K₇ mr
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, m₆, m₅]
  refine WP.block_append (WP.mono (tree_ok .a7 96 t 4 (8 * q) .t2 [.t3, .t4, .t5, .t6] s₇ (by decide)
    (by decide) (fun r hr => hne .a7 (.inr rfl) r (by
      simp only [treeRegs]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
    (fun c hc => hm₇ c (by omega)) (by omega)
    (fun e he => by
      have := hgrp 3 (by decide) e0₇ rd₇ wr₇ (.inr a7₇) e he
      simp only [show (3 : Nat) ≠ 0 from by decide, ↓reduceIte] at this
      exact ⟨this.1, this.2.1⟩)) fun s₈ ⟨v₈, k₈, m₈⟩ => ?_)
  have g3 := hgrp 3 (by decide) e0₇ rd₇ wr₇ (.inr a7₇) (t % 16) (Nat.mod_lt _ (by decide))
  simp only [show (3 : Nat) ≠ 0 from by decide, ↓reduceIte] at g3
  rw [g3.2.2, m₇] at v₈
  -- Entries `32 … 63`, by bit 4, then all by bit 5.
  have a5₈ : s₈.gpr (maskReg 4) = maskOf (t.testBit 4) := by rw [k₈.gpr (by decide)]; exact hm₇ 4 (by decide)
  have t1₈ : s₈.gpr .t1 = s₆.gpr .t1 := by rw [k₈.1 .t1 (by decide), u₇.other .t1 (by decide)]
  refine wp_pick (by decide) (by decide) a5₈ fun s₉ v₉ k₉ m₉ => ?_
  rw [t1₈, v₆, v₈] at v₉
  have a6₉ : s₉.gpr (maskReg 5) = maskOf (t.testBit 5) := by
    rw [k₉.gpr (by decide), k₈.gpr (by decide)]; exact hm₇ 5 (by decide)
  refine wp_pick (by decide) (by decide) a6₉ fun s₁₀ v₁₀ k₁₀ m₁₀ => ?_
  have t0₉ : s₉.gpr .t0 = s₆.gpr .t0 := by
    rw [k₉.1 .t0 (by decide), k₈.1 .t0 (by decide), u₇.other .t0 (by decide)]
  have t0₆ : s₆.gpr .t0 = s₄.gpr .t0 := by rw [k₆.gpr (by decide), u₅.other .t0 (by decide)]
  rw [t0₉, t0₆, v₄, v₉] at v₁₀
  -- The store.
  have K₁₀ : Keep (treeRegs ++ [.a7]) s s₁₀ :=
    ((((K₇.trans k₈).trans k₉).trans k₁₀)).mono (by simp [treeRegs])
  have hw₁₀ : WsReg s₁₀ base := ⟨by rw [K₁₀.gpr (by decide), hw.s0], by rw [K₁₀.2.2]; exact hw.wr, hw.nowrap, hw.al⟩
  refine sd_ws hw₁₀ (by omega) (by omega) fun s₁₁ u₁₁ => WP.block_nil ⟨?_, ?_⟩
  · have hE : ∀ x y, x = y → s.mem.readW (entAddr (s.gpr .a0) q x) 64 = s.mem.readW (entAddr (s.gpr .a0) q y) 64 :=
      fun x y h => by rw [h]
    rw [u₁₁.mem, m₁₀, m₉, m₈, m₇, v₁₀]
    congr 1
    rw [show 64 = 2 ^ (5 + 1) from rfl, mod_two_pow_succ' t 5, show 2 ^ 5 = 2 ^ (4 + 1) from rfl,
      mod_two_pow_succ' t 4]
    by_cases h5 : t.testBit 5 <;> by_cases h4 : t.testBit 4 <;>
      simp only [h5, h4, ↓reduceIte, Bool.false_eq_true] <;> exact hE _ _ (by simp only [Nat.reducePow]; omega)
  · exact ⟨fun r hr => by rw [u₁₁.gpr, K₁₀.gpr hr], by rw [u₁₁.rd, K₁₀.2.1], by rw [u₁₁.wr, K₁₀.2.2]⟩

end

/-! ## The window, the digit and the masks -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Proof.Weierstrass.RISCV64 (maskOf WsReg sd_ws ld_ws testBit_wordsVal wp_srlReg)
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Proof.Weierstrass (combWin magH)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

end

/-- The shift of the high word. -/
theorem shamt_eq : ∀ j < 55, (BitVec.ofNat 64 (7 * j) ^^^ BitVec.ofInt 64 63).toNat % 64 = 63 - 7 * j % 64 := by
  decide

/-- `8 j - j`. -/
theorem seven_mul {j : Nat} (hj : j < 55) :
    BitVec.ofNat 64 j <<< 3 - BitVec.ofNat 64 j = BitVec.ofNat 64 (7 * j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have := hj
  omega

/-- The slot of the copy of `k`. -/
theorem kc_eq : p384.sl KC = 2272 := rfl

/-- `t2 = k_j`, for `j` in `s1`, from the copy of `k` at `KC` and its zero word. -/
theorem window_ok {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 55)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) (hz : word s.mem base (p384.sl KC + 48) = 0) :
    WP isa (.block (Cfg.window p384)) s fun s' =>
      s'.gpr .t2 = BitVec.ofNat 64 (combWin 7 (wordsVal s.mem base (p384.sl KC) 6) j) ∧
        Rest [.t0, .t1, .t2, .t3, .t4] s s' ∧ s'.mem = s.mem := by
  have hn := hw.nowrap
  have hal := hw.al
  have hq : 7 * j / 64 ≤ 5 := by omega
  rw [Cfg.window, kc_eq] at *
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_sll (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => ?_
  have e₂ : s₂.gpr .t0 = BitVec.ofNat 64 (7 * j) := by
    rw [u₂.gpr, u₁.gpr, u₁.other .s1 (by decide), h1, seven_mul hj]
  refine wp_srl (by decide) fun s₃ u₃ => wp_sll (by decide) fun s₄ u₄ => wp_add fun s₅ u₅ => ?_
  have e₅' : s₅.gpr .t1 = base + BitVec.ofNat 64 (8 * (7 * j / 64)) := by
    rw [u₅.gpr, u₄.gpr, u₄.other .s0 (by decide), u₃.gpr, u₃.other .s0 (by decide),
      u₂.other .s0 (by decide), u₁.other .s0 (by decide), hw.s0, e₂]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega : 7 * j < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega : 7 * j / 64 * 8 < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega : 8 * (7 * j / 64) < 18446744073709551616)]
    omega
  have e₅ : ∀ d, s₅.gpr .t1 + BitVec.ofNat 64 d = off base (d + 8 * (7 * j / 64)) := by
    intro d
    rw [e₅', BitVec.add_assoc, BitVec.ofNat_add_ofNat, off, Nat.add_comm]
  have r₅ : Rest [.t0, .t1] s s₅ :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
      ((u₄.rest (by decide)).trans (u₅.rest (by decide)))))
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have inr : ∀ d, d + 8 ≤ 8192 → InRegions (s₅.rd ++ s₅.wr) (off base d) 8 := fun d hd =>
    ⟨_, List.mem_append_right _ (r₅.wr ▸ hw.wr), Offset.contains_base base hd (by omega)⟩
  have alg : ∀ d, d % 8 = 0 → d < 8192 → (off base d).toNat % 8 = 0 := fun d h8 hd => by
    simp only [off]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine VG.Proof.Weierstrass.RISCV64.wp_ldAt (by omega) (e₅ 2272) (alg _ (by omega) (by omega)) (inr _ (by omega))
    fun s₆ u₆ => ?_
  refine VG.Proof.Weierstrass.RISCV64.wp_ldAt (by omega) (by rw [u₆.other .t1 (by decide)]; exact e₅ 2280)
    (alg _ (by omega) (by omega))
    (by rw [u₆.rd, u₆.wr]; exact inr _ (by omega)) fun s₇ u₇ => ?_
  refine wp_srlReg fun s₈ u₈ => wp_xori (by decide) fun s₉ u₉ => wp_sll (by decide) fun s₁₀ u₁₀ => ?_
  refine wp_sllReg fun s₁₁ u₁₁ => wp_or fun s₁₂ u₁₂ => wp_andi (by decide) fun s₁₃ u₁₃ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have t0₈ : s₈.gpr .t0 = BitVec.ofNat 64 (7 * j) := by
      rw [u₈.other .t0 (by decide), u₇.other .t0 (by decide), u₆.other .t0 (by decide), u₅.other .t0 (by decide),
        u₄.other .t0 (by decide), u₃.other .t0 (by decide)]
      exact e₂
    have sh : (s₉.gpr .t4).toNat % 64 = 63 - 7 * j % 64 := by
      rw [u₉.gpr, t0₈]; exact shamt_eq j hj
    have sh7 : (s₇.gpr .t0).toNat % 64 = 7 * j % 64 := by
      rw [u₇.other .t0 (by decide), u₆.other .t0 (by decide), u₅.other .t0 (by decide), u₄.other .t0 (by decide),
        u₃.other .t0 (by decide), e₂, BitVec.toNat_ofNat]
      omega
    rw [u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, u₁₁.other .t2 (by decide), u₁₀.gpr, u₁₀.other .t2 (by decide),
      u₁₀.other .t4 (by decide), sh, u₉.other .t2 (by decide), u₉.other .t3 (by decide), u₈.gpr,
      u₈.other .t3 (by decide), sh7, u₇.gpr, u₇.other .t2 (by decide), u₆.gpr, u₆.mem, m₅]
    refine window_bits fun i hi => ?_
    have e5 : wordsVal s.mem base 2272 7 = wordsVal s.mem base 2272 6 := by
      rw [wordsVal_succ_top s.mem base 2272 6, show 2272 + 8 * 6 = 2272 + 48 from rfl, hz]; simp
    rw [← e5, ← testBit_wordsVal s.mem base 7 2272 (7 * j + i) (by omega)]
    by_cases h : 7 * j % 64 + i < 64
    · simp only [h, ↓reduceIte]
      rw [show (7 * j + i) / 64 = 7 * j / 64 by omega, show (7 * j + i) % 64 = 7 * j % 64 + i by omega,
        ← BitVec.testBit_toNat, show 2272 + 8 * (7 * j / 64) = 2272 + 8 * (7 * j / 64) from rfl]
    · simp only [h, ↓reduceIte]
      rw [show (7 * j + i) / 64 = 7 * j / 64 + 1 by omega,
        show (7 * j + i) % 64 = 7 * j % 64 + i - 64 by omega, ← BitVec.testBit_toNat,
        show 2272 + 8 * (7 * j / 64 + 1) = 2280 + 8 * (7 * j / 64) by omega]
  · exact (r₅.mono (by decide)).trans ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans
      ((u₈.rest (by decide)).trans ((u₉.rest (by decide)).trans ((u₁₀.rest (by decide)).trans
        ((u₁₁.rest (by decide)).trans ((u₁₂.rest (by decide)).trans (u₁₃.rest (by decide)))))))))
  · rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]


/-! ## The digit and the masks -/

theorem pt_eq : p384.sl PT = 1504 := rfl

/-- The digit of the window `v` in `t2`: the masks to `PT`'s slot, the
entry's number in `t2`. -/
theorem digit_ok {s : State} {base : Addr} (hw : WsReg s base) {v : Nat} (hv : v < 128)
    (h2 : s.gpr .t2 = BitVec.ofNat 64 v) :
    WP isa (.block (Cfg.digit p384)) s fun s' =>
      (magH 64 v ≠ 0 → (s'.gpr .t2).toNat = magH 64 v - 1) ∧
      word s'.mem base (p384.sl PT) = maskOf (decide (v < 64)) ∧
      word s'.mem base (p384.sl PT + 8) = maskOf (decide (magH 64 v = 0)) ∧
      Outside base (p384.sl PT) 16 s.mem s'.mem ∧ Rest [.t2, .t3, .t4] s s' := by
  have hn := hw.nowrap
  obtain ⟨f1, f2, f3⟩ := digit_facts v hv
  rw [Cfg.digit, pt_eq]
  refine wp_subi (imm := 64) (by decide) fun s₁ u₁ => wp_sra (by decide) fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
  refine wp_sub fun s₄ u₄ => wp_subi (imm := 1) (by decide) fun s₅ u₅ => wp_sra (by decide) fun s₆ u₆ => ?_
  have r₆ : Rest [.t2, .t3, .t4] s s₆ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans
    ((u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans (u₆.rest (by decide))))))
  have e3 : s₆.gpr .t3 = (BitVec.ofNat 64 v - BitVec.ofNat 64 64).sshiftRight 63 := by
    rw [u₆.other .t3 (by decide), u₅.other .t3 (by decide), u₄.other .t3 (by decide), u₃.other .t3 (by decide),
      u₂.gpr, u₁.gpr, h2]
  have e5 : s₅.gpr .t2 = (((BitVec.ofNat 64 v - BitVec.ofNat 64 64) ^^^
      (BitVec.ofNat 64 v - BitVec.ofNat 64 64).sshiftRight 63) -
      (BitVec.ofNat 64 v - BitVec.ofNat 64 64).sshiftRight 63) - BitVec.ofNat 64 1 := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other .t3 (by decide), u₂.gpr, u₂.other .t2 (by decide), u₁.gpr, h2]
  have e2 : s₆.gpr .t2 = s₅.gpr .t2 := u₆.other .t2 (by decide)
  have e4 : s₆.gpr .t4 = maskOf (decide (magH 64 v = 0)) := by rw [u₆.gpr, e5]; exact f2
  have hw₆ : WsReg s₆ base := hw.of_rest r₆
  refine sd_ws hw₆ (by decide) (by decide) fun s₇ u₇ => ?_
  refine sd_ws (hw₆.of_rest (u₇.rest [])) (by decide) (by decide) fun s₈ u₈ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hz; rw [u₈.gpr, u₇.gpr, e2, e5]; exact f3 hz
  · rw [u₈.mem, (writeW_outside s₇.mem base (d := 1512) (s₇.gpr .t4) (by omega)).word (d := 1504) (by omega)
      (by omega), u₇.mem, word_writeW_self, e3, f1]
  · rw [u₈.mem, word_writeW_self, u₇.gpr, e4]
  · intro x hx
    rw [u₈.mem, writeW_outside s₇.mem base (d := 1512) (s₇.gpr .t4) (by omega) x (by omega), u₇.mem,
      writeW_outside s₆.mem base (d := 1504) (s₆.gpr .t3) (by omega) x (by omega)]
    rw [show s₆.mem = s.mem by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]]
  · exact r₆.trans ((u₇.rest _).trans (u₈.rest _))

/-- The row: `a0 = s4 + 6144 j`, `a7 = a0 + 2048`. -/
theorem row_ok {s : State} {j : Nat} (hj : j < 55) (h1 : s.gpr .s1 = BitVec.ofNat 64 j) :
    WP isa (.block (Cfg.row p384)) s fun s' =>
      s'.gpr .a0 = s.gpr .s4 + BitVec.ofNat 64 (6144 * j) ∧ Rest [.t0, .t1, .a0] s s' ∧ s'.mem = s.mem := by
  simp only [Cfg.row, show ¬ (p384.n = 4) from by decide, ↓reduceIte]
  refine wp_sll (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  refine wp_add fun s₄ u₄ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [u₄.gpr, u₃.other .s4 (by decide), u₂.other .s4 (by decide), u₁.other .s4 (by decide), u₃.gpr,
      u₂.other .t0 (by decide), u₁.gpr, u₂.gpr, u₁.other .s1 (by decide), h1]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    have := hj
    omega
  · exact (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
      (u₄.rest (by decide))))
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]

end

/-! ## The entry -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Proof.Weierstrass.RISCV64 (maskOf WsReg copy_ok sel_ok ld_ws)
open VG.Proof.Weierstrass (Unch combWin magH)
open VG.Proof.X25519.RISCV64 (Rest)

/-- The words of P-384's tables. -/
abbrev tabWords : List (BitVec 64) := Impl.Weierstrass.tcombWords 6 (2 ^ 384) Spec.P384.curve.p Impl.P384.p384Comb7

/-- What the comb needs of the table at `T`, for the working space at `base`. -/
structure TabOk (s : State) (base T : Addr) : Prop where
  held : ∀ i < 42240, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = tabWords.getD i 0
  al : T.toNat % 64 = 0
  rd : (⟨T, 337920⟩ : Region) ∈ s.rd
  fit : T.toNat + 337920 ≤ 2 ^ 64
  far : ∀ d < 337920, 8192 ≤ ofs base (T + BitVec.ofNat 64 d)

/-- Memory changed only in the working space keeps the table. -/
theorem TabOk.of_mem {s s' : State} {base T : Addr} (h : TabOk s base T) (hrd : s'.rd = s.rd)
    (hm : ∀ x, 8192 ≤ ofs base x → s'.mem x = s.mem x) : TabOk s' base T where
  held i hi := by
    rw [← h.held i hi]
    refine Mem.readW_congr fun b hb => hm _ ?_
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact h.far _ (by omega)
  al := h.al
  rd := hrd ▸ h.rd
  fit := h.fit
  far := h.far

theorem TabOk.of_outside {s s' : State} {base T : Addr} (h : TabOk s base T) (hrd : s'.rd = s.rd) {o n : Nat}
    (hon : o + n ≤ 8192) (ho : Outside base o n s.mem s'.mem) : TabOk s' base T :=
  h.of_mem hrd fun x hx => ho x (.inr (by omega))

/-- The address of quadword `q` of entry `e` of row `j`. -/
theorem entAddr_row (T : Addr) (j q e : Nat) :
    entAddr (T + BitVec.ofNat 64 (6144 * j)) q e = T + BitVec.ofNat 64 (8 * (j * (64 * (2 * 6)) + e * (2 * 6) + q)) := by
  rw [entAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2
  omega

/-- What the scan of row `j` needs. -/
theorem rowOk_of_tab {s : State} {base T : Addr} (h : TabOk s base T) {j q : Nat} (hj : j < 55) (hq : q < 12)
    (h0 : s.gpr .a0 = T + BitVec.ofNat 64 (6144 * j)) :
    RowOk s q where
  ent e he := by
    rw [h0, entAddr_row]
    have hd : 8 * (j * (64 * (2 * 6)) + e * (2 * 6) + q) + 8 ≤ 337920 := by omega
    refine ⟨?_, ⟨_, List.mem_append_left _ h.rd, Offset.contains_base T hd (by omega)⟩⟩
    have hf := h.fit
    have e : (T + BitVec.ofNat 64 (8 * (j * (64 * (2 * 6)) + e * (2 * 6) + q))).toNat =
        T.toNat + 8 * (j * (64 * (2 * 6)) + e * (2 * 6) + q) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 8 * (j * (64 * (2 * 6)) + e * (2 * 6) + q) <
        2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
    have := h.al
    rw [e]
    omega

theorem dx_eq : p384.sl DX = 880 := rfl

/-- The `2 n` quadwords of entry `t % 64` of row `j` to `D`. -/
theorem scans_ok {base T : Addr} {j t : Nat} (hj : j < 55) : ∀ n ≤ 12, ∀ {s : State}, WsReg s base → TabOk s base T →
    s.gpr .a0 = T + BitVec.ofNat 64 (6144 * j) →
    (∀ c < 6, s.gpr (maskReg c) = maskOf (t.testBit c)) →
    WP isa (.block ((List.range n).flatMap (Cfg.scanWord p384))) s fun s' =>
      (∀ q < n, word s'.mem base (880 + 8 * q) = s.mem.readW (entAddr (s.gpr .a0) q (t % 64)) 64) ∧
      Outside base 880 (8 * n) s.mem s'.mem ∧ Keep (treeRegs ++ [.a7]) s s'
  | 0, _, s, _, _, _, _ => WP.block_nil ⟨fun q hq => absurd hq (by omega), Outside.refl _ _ _ _, Keep.refl _ _⟩
  | n + 1, hn, s, hw, hT, h0, hm => by
    have hnw := hw.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (scans_ok hj n (by omega) hw hT h0 hm) fun s₁ ⟨v₁, O₁, k₁⟩ => ?_)
    have ne : ∀ r ∈ [Reg.s0, .a0, .a1, .a2, .a3, .a4, .a5, .a6], r ∉ treeRegs ++ [.a7] := by decide
    have e0 : s₁.gpr .a0 = s.gpr .a0 := k₁.gpr (ne _ (by simp))
    have hw₁ : WsReg s₁ base := ⟨by rw [k₁.gpr (ne _ (by simp)), hw.s0], by rw [k₁.2.2]; exact hw.wr, hw.nowrap, hw.al⟩
    have hT₁ : TabOk s₁ base T := hT.of_outside k₁.2.1 (by omega) O₁
    have hm₁ : ∀ c < 6, s₁.gpr (maskReg c) = maskOf (t.testBit c) := fun c hc => by
      rw [k₁.gpr (by
        have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
      exact hm c hc
    refine WP.mono (scanWord_ok hw₁ (q := n) (by omega) hm₁
      (rowOk_of_tab hT₁ hj (by omega) (by rw [e0, h0]))) fun s₂ ⟨m₂, k₂⟩ => ?_
    rw [dx_eq, e0] at m₂
    -- The entry's quadword, as the table held it.
    have hr : s₁.mem.readW (entAddr (s.gpr .a0) n (t % 64)) 64 = s.mem.readW (entAddr (s.gpr .a0) n (t % 64)) 64 := by
      refine Mem.readW_congr fun b hb => O₁ _ (.inr ?_)
      rw [h0, entAddr_row, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      have := hT.far (8 * (j * (64 * (2 * 6)) + t % 64 * (2 * 6) + n) + b) (by
        have := Nat.mod_lt t (show 64 > 0 by decide); omega)
      omega
    have O₂ : Outside base (880 + 8 * n) 8 s₁.mem s₂.mem := by rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun q hq => ?_, ?_, k₁.trans k₂ |>.mono (fun r hr => (List.mem_append.mp hr).elim id id)⟩
    · by_cases hqn : q < n
      · rw [O₂.word (by omega) (by omega), v₁ q hqn]
      · obtain rfl : q = n := by omega
        rw [m₂, word_writeW_self, hr]
    · exact (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))


/-! ## The entry's words -/

theorem comb7_len : Impl.P384.p384Comb7.length = 55 := by decide

theorem comb7_lenH : ∀ j < 55, (Impl.P384.p384Comb7.getD j []).length = 64 := by decide

/-- `x R mod p`. -/
abbrev montP (x : Nat) : Nat := x * 2 ^ 384 % Spec.P384.curve.p

/-- Entry `e` of row `j`. -/
abbrev entOf (j e : Nat) : Nat × Nat := Proof.Weierstrass.combAt Impl.P384.p384Comb7 j e

/-- Quadword `q` of entry `e` of row `j`: the words of `x`, then of `y`, in
Montgomery's form. -/
theorem entry_word {s : State} {base T : Addr} (hT : TabOk s base T) {j e q : Nat} (hj : j < 55) (he : e < 64)
    (hq : q < 12) :
    s.mem.readW (entAddr (T + BitVec.ofNat 64 (6144 * j)) q e) 64 =
      if q < 6 then Impl.Weierstrass.wordOf (montP (entOf j e).1) q
      else Impl.Weierstrass.wordOf (montP (entOf j e).2) (q - 6) := by
  rw [entAddr_row, hT.held _ (by omega)]
  exact Proof.Weierstrass.tcombWords_getD comb7_len comb7_lenH hj he hq


/-- The scalar: the copy of `k`. -/
abbrev kOf (m : Mem) (base : Addr) : Nat := wordsVal m base 2272 6

/-- The registers the entry's selection writes. -/
abbrev selRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-- Memory but the working space keeps the table. -/
theorem TabOk.of_unch {s s' : State} {base T : Addr} (h : TabOk s base T) (hrd : s'.rd = s.rd)
    {W : List (Nat × Nat)} (hW : ∀ w ∈ W, w.1 + w.2 ≤ 8192) (hu : Unch base W s.mem s'.mem) : TabOk s' base T :=
  h.of_mem hrd fun x hx => hu.far fun w hw => by have := hW w hw; omega

/-- The entry of digit `j` in `D`: `(x R, y R, R)` for the magnitude `m ≠ 0`
of the digit, `(0, R, 0)` for `m = 0`, and the mask of the digit's sign in
`PT`'s first word. -/
theorem select_ok {s : State} {base T : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 55)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) (h2 : s.gpr .s4 = T) (hT : TabOk s base T)
    (hz : word s.mem base (2272 + 48) = 0) (hZ : wordsVal s.mem base 208 6 = 0) :
    WP isa (.block (Cfg.select p384)) s fun s' =>
      wordsVal s'.mem base 880 6 = (if magH 64 (combWin 7 (kOf s.mem base) j) = 0 then 0
        else montP (entOf j (magH 64 (combWin 7 (kOf s.mem base) j) - 1)).1) ∧
      wordsVal s'.mem base 928 6 = (if magH 64 (combWin 7 (kOf s.mem base) j) = 0 then wordsVal s.mem base 304 6
        else montP (entOf j (magH 64 (combWin 7 (kOf s.mem base) j) - 1)).2) ∧
      wordsVal s'.mem base 976 6 = (if magH 64 (combWin 7 (kOf s.mem base) j) = 0 then 0
        else wordsVal s.mem base 304 6) ∧
      word s'.mem base 1504 = maskOf (decide (combWin 7 (kOf s.mem base) j < 64)) ∧
      Unch base [(880, 144), (1504, 16)] s.mem s'.mem ∧ Rest selRegs s s' := by
  have hn := hw.nowrap
  generalize hv : combWin 7 (kOf s.mem base) j = v
  have hv128 : v < 128 := hv ▸ Proof.Weierstrass.combWin_lt 7 _ j
  generalize hg : magH 64 v = mg
  have hmg : mg ≤ 64 := hg ▸ Proof.Weierstrass.magH_le (by omega)
  rw [Cfg.select]
  simp only [List.append_assoc]
  -- The window.
  refine WP.block_append (WP.mono (window_ok hw hj h1 (by rw [kc_eq]; exact hz)) fun s₁ ⟨t₁, r₁, m₁⟩ => ?_)
  rw [kc_eq, show wordsVal s.mem base 2272 6 = kOf s.mem base from rfl, hv] at t₁
  have hw₁ := hw.of_rest r₁
  -- The digit.
  refine WP.block_append (WP.mono (digit_ok hw₁ hv128 t₁) fun s₂ ⟨t₂, pt₂, pz₂, O₂, r₂⟩ => ?_)
  rw [hg] at t₂ pz₂
  rw [pt_eq] at pt₂ pz₂ O₂
  have hw₂ := hw₁.of_rest r₂
  -- The masks.
  refine WP.block_append (WP.mono masks_ok fun s₃ ⟨v₃, r₃, m₃⟩ => ?_)
  -- The row.
  have e1 : s₃.gpr .s1 = BitVec.ofNat 64 j := by
    rw [r₃.gpr _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide), h1]
  have e2 : s₃.gpr .s4 = T := by rw [r₃.gpr _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide), h2]
  refine WP.block_append (WP.mono (row_ok hj e1) fun s₄ ⟨a₄, r₄, m₄⟩ => ?_)
  rw [e2] at a₄
  have hw₄ := (hw₂.of_rest r₃).of_rest r₄
  have U₄ : Unch base [(1504, 16)] s.mem s₄.mem := by
    rw [m₄, m₃]; rw [m₁] at O₂; exact O₂.unch
  have hT₄ : TabOk s₄ base T :=
    hT.of_unch (by rw [r₄.rd, r₃.rd, r₂.rd, r₁.rd]) (by simp) U₄
  have hm₄ : ∀ c < 6, s₄.gpr (maskReg c) = maskOf ((s₂.gpr .t2).toNat.testBit c) := fun c hc => by
    rw [r₄.gpr _ (by
      have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), v₃ c hc, BitVec.testBit_toNat]
  -- The scans.
  refine WP.block_append (WP.mono (WP.rdwr (scans_ok hj 12 (Nat.le_refl _) hw₄ hT₄ a₄ hm₄))
    fun s₅ ⟨⟨v₅, O₅, k₅⟩, rd₅, wr₅, sp₅⟩ => ?_)
  have r₅ : Rest (treeRegs ++ [.a7]) s₄ s₅ := ⟨k₅.1, rd₅, wr₅, sp₅⟩
  have hw₅ := hw₄.of_rest r₅
  -- `Z = 1`.
  refine WP.block_append (WP.mono (copy_ok 6 hw₅ (o := 976) (a := 304) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₆ ⟨e₆, r₆, O₆⟩ => ?_)
  have hw₆ := hw₅.of_rest r₆
  -- The mask of `m = 0`.
  rw [List.cons_append, List.nil_append]
  refine ld_ws hw₆ (d := 1512) (by decide) (by decide) fun s₇ u₇ => ?_
  have a7₇ : s₇.gpr .a7 = maskOf (decide (mg = 0)) := by
    rw [u₇.gpr, O₆.word (by omega) (by omega), O₅.word (by omega) (by omega), m₄, m₃]; exact pz₂
  have hw₇ := hw₆.of_rest (u₇.rest (ws := [.a7]) (by decide))
  -- The point at infinity for `m = 0`.
  refine WP.block_append (WP.mono (sel_ok (decide (mg = 0)) 6 hw₇ a7₇ (o := 880) (a := 880) (b := 208)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₈ ⟨e₈, r₈, O₈⟩ => ?_)
  have hw₈ := hw₇.of_rest r₈
  refine WP.block_append (WP.mono (sel_ok (decide (mg = 0)) 6 hw₈ (by rw [r₈.gpr _ (by decide)]; exact a7₇)
    (o := 928) (a := 928) (b := 304)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₉ ⟨e₉, r₉, O₉⟩ => ?_)
  have hw₉ := hw₈.of_rest r₉
  refine WP.mono (sel_ok (decide (mg = 0)) 6 hw₉ (by rw [r₉.gpr _ (by decide), r₈.gpr _ (by decide)]; exact a7₇)
    (o := 976) (a := 976) (b := 208)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₁₀ ⟨e₁₀, r₁₀, O₁₀⟩ => ?_
  -- What the slots hold.
  have U₇ : Unch base [(1504, 16), (880, 96), (976, 48)] s.mem s₇.mem := by
    rw [u₇.mem]; exact (U₄.trans O₅.unch).trans O₆.unch
  have hZ₇ : wordsVal s₇.mem base 208 6 = 0 := by rw [U₇.wordsVal (by simp) (by omega), hZ]
  have hO₇ : wordsVal s₇.mem base 304 6 = wordsVal s.mem base 304 6 := U₇.wordsVal (by simp) (by omega)
  have hD : mg ≠ 0 → ∀ q < 12, word s₇.mem base (880 + 8 * q) =
      if q < 6 then Impl.Weierstrass.wordOf (montP (entOf j (mg - 1)).1) q
      else Impl.Weierstrass.wordOf (montP (entOf j (mg - 1)).2) (q - 6) := by
    intro h0 q hq
    have ht : (s₂.gpr .t2).toNat % 64 = mg - 1 := by rw [t₂ h0]; omega
    rw [u₇.mem, O₆.word (by omega) (by omega), v₅ q hq, a₄, ht, entry_word hT₄ hj (by omega) hq]
  have hpx : mg ≠ 0 → montP (entOf j (mg - 1)).1 < 2 ^ 384 := fun _ => by
    have := Nat.mod_lt ((entOf j (mg - 1)).1 * 2 ^ 384) (show 0 < Spec.P384.curve.p by decide)
    exact Nat.lt_trans this (by decide)
  have hpy : mg ≠ 0 → montP (entOf j (mg - 1)).2 < 2 ^ 384 := fun _ => by
    have := Nat.mod_lt ((entOf j (mg - 1)).2 * 2 ^ 384) (show 0 < Spec.P384.curve.p by decide)
    exact Nat.lt_trans this (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [O₁₀.wordsVal (by omega) (by omega), O₉.wordsVal (by omega) (by omega), e₈]
    by_cases h0 : mg = 0
    · simp only [h0, decide_true, ↓reduceIte]; exact hZ₇
    · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine Proof.Weierstrass.wordsVal_of_shifts _ _ _ _ _ (hpx h0) fun i hi => ?_
      rw [hD h0 i (by omega)]; simp only [show i < 6 from hi, ↓reduceIte]; rfl
  · rw [O₁₀.wordsVal (by omega) (by omega), e₉, O₈.wordsVal (by omega) (by omega),
      O₈.wordsVal (by omega) (by omega)]
    by_cases h0 : mg = 0
    · simp only [h0, decide_true, ↓reduceIte]; exact hO₇
    · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine Proof.Weierstrass.wordsVal_of_shifts _ _ _ _ _ (hpy h0) fun i hi => ?_
      rw [show 928 + 8 * i = 880 + 8 * (i + 6) by omega, hD h0 (i + 6) (by omega)]
      simp only [show ¬ i + 6 < 6 by omega, ↓reduceIte, Nat.add_sub_cancel]; rfl
  · have e224 : wordsVal s₅.mem base 304 6 = wordsVal s.mem base 304 6 := by
      rw [← O₆.wordsVal (d := 304) (by omega) (by omega), ← u₇.mem]; exact hO₇
    rw [e₁₀, O₉.wordsVal (by omega) (by omega), O₈.wordsVal (by omega) (by omega),
      O₉.wordsVal (by omega) (by omega), O₈.wordsVal (by omega) (by omega)]
    by_cases h0 : mg = 0
    · simp only [h0, decide_true, ↓reduceIte]; exact hZ₇
    · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]; rw [u₇.mem, e₆, e224]
  · rw [O₁₀.word (by omega) (by omega), O₉.word (by omega) (by omega), O₈.word (by omega) (by omega), u₇.mem,
      O₆.word (by omega) (by omega), O₅.word (by omega) (by omega), m₄, m₃, pt₂]
  · exact ((((U₄.trans O₅.unch).trans O₆.unch).trans (by rw [← u₇.mem]; exact O₈.unch)).trans
      (O₉.unch.trans O₁₀.unch)).cover (by decide)
  · exact (r₁.mono (by decide)).trans ((r₂.mono (by decide)).trans ((r₃.mono (by decide)).trans
      ((r₄.mono (by decide)).trans ((r₅.mono (by decide)).trans ((r₆.mono (by decide)).trans
      (((u₇.rest (ws := [.a7]) (by decide)).mono (by decide)).trans ((r₈.mono (by decide)).trans ((r₉.mono (by decide)).trans
      (r₁₀.mono (by decide))))))))))

end

/-! ## A step -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P384 (W field_ok unit mul_zero_pt)
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point)

/-- `R mod p`, one in Montgomery's form. -/
abbrev oneM : Nat := 2 ^ 384 % W.p

/-- The value in `D.y` before the negation. -/
abbrev yDig (i v : Nat) : Nat := if magH 64 v = 0 then oneM else montP (entOf i (magH 64 v - 1)).2

theorem toM_montP (x : Nat) : toM W.p (2 ^ 384) (montP x) = Fin.ofNat W.p x := toM_mont unit

/-- The entry of digit `i`, `y` negated for a negative digit, represents the
digit's signed point. -/
theorem entry_rep (hL : Law W) {k i : Nat} (hi : i < 55) :
    Rep W (toM W.p (2 ^ 384) (if magH 64 (combWin 7 k i) = 0 then 0
        else montP (entOf i (magH 64 (combWin 7 k i) - 1)).1))
      (toM W.p (2 ^ 384) (if combWin 7 k i < 64 then (0 + W.p - yDig i (combWin 7 k i)) % W.p
        else yDig i (combWin 7 k i)))
      (toM W.p (2 ^ 384) (if magH 64 (combWin 7 k i) = 0 then 0 else oneM))
      (signedPtW W 7 k i) := by
  have hC := P384.combOk7 hL
  have hv := combWin_lt 7 k i
  unfold signedPtW yDig
  generalize combWin 7 k i = v at hv ⊢
  simp only [show 2 ^ (7 - 1) = 64 from rfl]
  by_cases h64 : 64 ≤ v
  · have hmg : magH 64 v = v - 64 := by unfold magH; simp [h64]
    simp only [h64, ↓reduceIte, show ¬ v < 64 by omega, hmg]
    by_cases h0 : v - 64 = 0
    · simp only [h0, ↓reduceIte, toM_zero, combPtW, Nat.zero_mul, mul_zero_pt]
      rw [toM_one unit]; exact rep_infinity' hL
    · obtain ⟨m, hm⟩ : ∃ m, v - 64 = m + 1 := ⟨v - 64 - 1, by omega⟩
      simp only [hm, Nat.add_one_ne_zero, ↓reduceIte, combPtW, Nat.add_sub_cancel]
      rw [hC.entry i hi m (by simp; omega), toM_montP, toM_montP, toM_one unit]
      exact rep_affine' hL _ _
  · have hmg : magH 64 v = 64 - v := by unfold magH; simp [h64]
    obtain ⟨m, hm⟩ : ∃ m, 64 - v = m + 1 := ⟨64 - v - 1, by omega⟩
    simp only [h64, ↓reduceIte, show v < 64 by omega, hmg, hm, Nat.add_one_ne_zero, combPtW, Nat.add_sub_cancel]
    rw [hC.entry i hi m (by simp; omega), toM_montP, toM_one unit,
      toM_sub (A := 0) (B := montP (entOf i m).2) (Nat.le_of_lt (Nat.lt_of_lt_of_le
        (Nat.mod_lt _ (by decide)) (Nat.le_of_eq (Nat.zero_add _).symm))),
      toM_zero, toM_montP]
    have := rep_affine' hL (Fin.ofNat W.p (entOf i m).1) (-Fin.ofNat W.p (entOf i m).2)
    simp only [negPt]
    rwa [show (0 : Fe W) - Fin.ofNat W.p (entOf i m).2 = -Fin.ofNat W.p (entOf i m).2 by grind]


/-! ## The negation and the addition -/

/-- `y = -y` by the sign's mask in `PT`. -/
theorem negate_ok {s : State} {base : Addr} (hw : WsReg s base) (hZ : wordsVal s.mem base 208 6 = 0)
    (hY : wordsVal s.mem base 928 6 < W.p) {c : Bool} (hPT : word s.mem base 1504 = maskOf c) :
    WP isa (Cfg.negate p384) s fun s' =>
      wordsVal s'.mem base 928 6 = (if c then (0 + W.p - wordsVal s.mem base 928 6) % W.p
        else wordsVal s.mem base 928 6) ∧
      Unch base [(1456, 48), (3712, 384), (928, 48)] s.mem s'.mem ∧ Kp s s' := by
  have hn := hw.nowrap
  rw [Cfg.negate]
  refine WP.seq (WP.mono (subCall_ok field_ok hw (o := p384.sl ACC) (a := p384.sl ZERO) (b := p384.sl DY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by show wordsVal s.mem base 208 6 < _; rw [hZ]; decide) hY) fun s₁ ⟨K₁, v₁⟩ => ?_)
  have hw₁ := hw.of_kp K₁.kp
  have U₁ : Unch base [(1456, 48), (3712, 384)] s.mem s₁.mem := fun x hx => K₁.mem x hx
  rw [List.cons_append, List.nil_append]
  refine ld_ws hw₁ (d := 1504) (by decide) (by decide) fun s₂ u₂ => ?_
  have a7 : s₂.gpr .a7 = maskOf c := by
    rw [u₂.gpr, U₁.word (by simp) (by omega), hPT]
  have hw₂ := hw₁.of_rest (u₂.rest (ws := [.a7]) (by decide))
  refine WP.mono (sel_ok c 6 hw₂ a7 (o := 928) (a := 928) (b := 1456) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨e₃, r₃, O₃⟩ => ⟨?_, ?_, ?_⟩
  · have hacc : wordsVal s₂.mem base 1456 6 = (0 + W.p - wordsVal s.mem base 928 6) % W.p := by
      rw [u₂.mem]
      have : wordsVal s₁.mem base 1456 6 =
          (wordsVal s.mem base 208 6 + W.p - wordsVal s.mem base 928 6) % W.p := v₁
      rw [hZ] at this
      exact this
    have hy : wordsVal s₂.mem base 928 6 = wordsVal s.mem base 928 6 := by
      rw [u₂.mem]; exact U₁.wordsVal (by simp) (by omega)
    rw [e₃, hacc, hy]
  · have O₃' := O₃; rw [u₂.mem] at O₃'; exact U₁.trans O₃'.unch
  · exact K₁.kp.trans (Kp.of_rest ((u₂.rest (ws := [.a7]) (by decide)).mono (by decide) |>.trans
      (r₃.mono (by decide))) (ws := [.a7, .t0, .t1]) (by decide))

/-- The slots of the addition. -/
abbrev combSl : List Nat :=
  [352, 1984, 736, 784, 832, 880, 928, 976, 1024, 1072, 1120, 1168, 1216, 1264, 1312, 1360, 1408]

theorem combLay : Lay p384.MP' (own 6) (· ∈ combSl) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ combSl, ∀ y ∈ combSl, x ≠ y → x + 8 * 6 ≤ y ∨ y + 8 * 6 ≤ x)
    x hx y hy, by decide, by decide⟩

/-- The slots the addition reads. -/
abbrev addV : List Nat := [352, 1984, 736, 784, 832, 880, 928, 976]

/-- P-384's `a` is `-3`. -/
theorem am3 : AM3 W := by unfold AM3; decide

/-- `T = R + D` by the complete addition for `a = -3`, then `R = T`. -/
theorem addR_ok {s : State} {base : Addr} (hw : WsReg s base) (hlt : ∀ x ∈ addV, wordsVal s.mem base x 6 < W.p) :
    WP isa (.seq (fprog p384.FP (rcb3 p384.rcb3Slots (p384.pt RX RY RZ) (p384.pt DX DY DZ) (p384.pt TX TY TZ)))
      (.block (copy 6 (p384.sl RX) (p384.sl TX) ++ copy 6 (p384.sl RY) (p384.sl TY) ++
        copy 6 (p384.sl RZ) (p384.sl TZ)))) s fun s' =>
      Kp s s' ∧ Unch base [(736, 768), (3712, 384)] s.mem s'.mem ∧
      (∀ x ∈ [736, 784, 832], wordsVal s'.mem base x 6 < W.p) ∧
      (tmv W 6 base s' 736, tmv W 6 base s' 784, tmv W 6 base s' 832) =
        rcbAdd3 (tmv W 6 base s 1984) (tmv W 6 base s 736) (tmv W 6 base s 784)
          (tmv W 6 base s 832) (tmv W 6 base s 880) (tmv W 6 base s 928) (tmv W 6 base s 976) := by
  have hn := hw.nowrap
  have hI : Inv 6 base W.p (· ∈ combSl) addV (fun x => tmv W 6 base s x) s :=
    ⟨hw, by decide, hlt, fun _ _ => rfl⟩
  refine WP.seq (WP.mono (rcb3_ok (M := p384.MP') (F := p384Field) field_ok rfl combLay
    (fun x hx => by have := (by decide : ∀ x ∈ combSl, x < 4095) x hx; exact this) unit
    (S := p384.rcb3Slots) (p := p384.pt RX RY RZ) (q := p384.pt DX DY DZ) (o := p384.pt TX TY TZ)
    ⟨by decide, by decide⟩ (by decide) hI (by decide)) fun s₁ ⟨K₁, I₁, v₁⟩ => ?_)
  have hw₁ := hw.of_kp K₁.kp
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok 6 hw₁ (o := 736) (a := 1024) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₂ ⟨e₂, r₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (copy_ok 6 hw₂ (o := 784) (a := 1072) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₃ ⟨e₃, r₃, O₃⟩ => ?_)
  have hw₃ := hw₂.of_rest r₃
  refine WP.mono (copy_ok 6 hw₃ (o := 832) (a := 1120) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₄ ⟨e₄, r₄, O₄⟩ => ?_
  have tx : wordsVal s₄.mem base 736 6 = wordsVal s₁.mem base 1024 6 := by
    rw [O₄.wordsVal (by omega) (by omega), O₃.wordsVal (by omega) (by omega), e₂]
  have ty : wordsVal s₄.mem base 784 6 = wordsVal s₁.mem base 1072 6 := by
    rw [O₄.wordsVal (by omega) (by omega), e₃, O₂.wordsVal (by omega) (by omega)]
  have tz : wordsVal s₄.mem base 832 6 = wordsVal s₁.mem base 1120 6 := by
    rw [e₄, O₃.wordsVal (by omega) (by omega), O₂.wordsVal (by omega) (by omega)]
  have hT : ∀ x ∈ [1024, 1072, 1120], x ∈ [(p384.pt TX TY TZ).x, (p384.pt TX TY TZ).y, (p384.pt TX TY TZ).z] ++ addV := by
    decide
  refine ⟨K₁.kp.trans (Kp.of_rest ((r₂.trans r₃).trans r₄)), ?_, ?_, ?_⟩
  · have U₁ : Unch base ((rcbW p384.rcb3Slots (p384.pt TX TY TZ)).map (fun w => (w, 8 * 6)) ++ [(own 6, 64 * 6)])
        s.mem s₁.mem := fun x hx => K₁.mem x hx
    exact (((U₁.trans O₂.unch).trans O₃.unch).trans O₄.unch).cover (by decide)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [tx]; exact I₁.lt 1024 (hT 1024 (by simp))
    · rw [ty]; exact I₁.lt 1072 (hT 1072 (by simp))
    · rw [tz]; exact I₁.lt 1120 (hT 1120 (by simp))
  · simp only [tmv]
    have h704 : toM W.p (2 ^ (64 * 6)) (wordsVal s₁.mem base 1024 6) = _ := I₁.val 1024 (hT 1024 (by simp))
    have h736 : toM W.p (2 ^ (64 * 6)) (wordsVal s₁.mem base 1072 6) = _ := I₁.val 1072 (hT 1072 (by simp))
    have h768 : toM W.p (2 ^ (64 * 6)) (wordsVal s₁.mem base 1120 6) = _ := I₁.val 1120 (hT 1120 (by simp))
    rw [tx, ty, tz, h704, h736, h768]
    exact v₁


/-! ## A step -/

/-- What the steps read, as the loop's start `s₀` holds it. -/
structure CombPre (base T : Addr) (s₀ : State) : Prop where
  s4 : s₀.gpr .s4 = T
  kz : word s₀.mem base (2272 + 48) = 0
  zero : wordsVal s₀.mem base 208 6 = 0
  one : wordsVal s₀.mem base 304 6 = oneM
  a : tmv W 6 base s₀ 352 = Fin.ofNat W.p W.a
  b : tmv W 6 base s₀ 1984 = Fin.ofNat W.p W.b
  alt : wordsVal s₀.mem base 352 6 < W.p
  blt : wordsVal s₀.mem base 1984 6 < W.p

/-- What the steps write. -/
abbrev stepW : List (Nat × Nat) := [(736, 816), (3712, 384)]

/-- The loop's invariant at `s1 = j`: `R` represents `[combEW j]G`, for the
scalar the start holds. -/
structure CombInv (base T : Addr) (s₀ s : State) (j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .s1 = BitVec.ofNat 64 j
  keep : Kc s₀ s
  unch : Unch base stepW s₀.mem s.mem
  tab : TabOk s base T
  lt : ∀ x ∈ [736, 784, 832], wordsVal s.mem base x 6 < W.p
  rep : Rep W (tmv W 6 base s 736) (tmv W 6 base s 784) (tmv W 6 base s 832)
    (Spec.Weierstrass.mul (combEW 7 (kOf s₀.mem base) 55 j) (Spec.Weierstrass.G W))

theorem signed_onCurve (hL : Law W) (k i : Nat) : Spec.Weierstrass.onCurve W (signedPtW W 7 k i) = true := by
  unfold signedPtW combPtW
  split
  · exact hL.onCurve_mul P384.onCurve_G _
  · exact onCurve_negPt (hL.onCurve_mul P384.onCurve_G _)

/-- A step: from `[combEW j]G` to `[combEW (j - 1)]G`. -/
theorem step_ok (hL : Law W) {base T : Addr} {s₀ : State} (hP : CombPre base T s₀) {j : Nat} (hj1 : 1 ≤ j)
    (hj : j ≤ 55) {s : State} (hI : CombInv base T s₀ s j) :
    WP isa (Cfg.step p384) s fun s' => CombInv base T s₀ s' (j - 1) := by
  have hn := hI.ws.nowrap
  have uS : ∀ d, d + 48 ≤ 736 ∨ 1552 ≤ d → d + 48 ≤ 3712 →
      wordsVal s.mem base d 6 = wordsVal s₀.mem base d 6 := fun d h h' =>
    hI.unch.wordsVal (by simp; omega) (by omega)
  have hk : kOf s.mem base = kOf s₀.mem base := uS 2272 (by omega) (by omega)
  rw [Cfg.step]
  -- `s1 -= 1` and the entry.
  refine WP.seq (wp_decCounter hj1 hI.ctr fun s₁ u₁ => ?_)
  have hw₁ := hI.ws.of_kc (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))
  refine WP.mono (select_ok hw₁ (j := j - 1) (by omega) u₁.gpr
    (by rw [u₁.other _ (by decide), hI.keep.gpr _ (by decide) (by decide), hP.s4])
    (hI.tab.of_mem u₁.rd fun x _ => by rw [u₁.mem])
    (by rw [u₁.mem, hI.unch.word (by simp) (by omega), hP.kz])
    (by rw [u₁.mem, uS 208 (by omega) (by omega), hP.zero])) fun s₂ ⟨dx₂, dy₂, dz₂, pt₂, U₂, r₂⟩ => ?_
  rw [u₁.mem, hk] at dx₂ dy₂ dz₂ pt₂
  rw [u₁.mem] at U₂
  rw [uS 304 (by omega) (by omega), hP.one] at dy₂ dz₂
  have hw₂ := hw₁.of_rest r₂
  generalize hv : combWin 7 (kOf s₀.mem base) (j - 1) = v at dx₂ dy₂ dz₂ pt₂
  have hv128 : v < 128 := hv ▸ combWin_lt 7 _ _
  -- What the slots hold so far.
  have uS₂ : ∀ d, d + 48 ≤ 736 ∨ 1552 ≤ d → d + 48 ≤ 3712 →
      wordsVal s₂.mem base d 6 = wordsVal s₀.mem base d 6 := fun d h h' => by
    rw [U₂.wordsVal (by simp; omega) (by omega), uS d h h']
  have hR₂ : ∀ d ∈ [736, 784, 832], wordsVal s₂.mem base d 6 = wordsVal s.mem base d 6 := by
    intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> exact U₂.wordsVal (by simp) (by omega)
  have hlt1 : oneM < W.p := Nat.mod_lt _ (by decide)
  have hlty : yDig (j - 1) v < W.p := by
    unfold yDig; split
    · exact hlt1
    · exact Nat.mod_lt _ (by decide)
  -- The negation.
  refine WP.seq (WP.mono (negate_ok hw₂ (by rw [uS₂ 208 (by omega) (by omega), hP.zero])
    (by rw [dy₂]; exact hlty) pt₂) fun s₃ ⟨dy₃, U₃, K₃⟩ => ?_)
  rw [dy₂] at dy₃
  have hw₃ := hw₂.of_kp K₃
  have e₃ : ∀ d, (d + 48 ≤ 928 ∨ 976 ≤ d) → (d + 48 ≤ 1456 ∨ 1504 ≤ d) → d + 48 ≤ 3712 →
      wordsVal s₃.mem base d 6 = wordsVal s₂.mem base d 6 := fun d h1 h2 h3 =>
    U₃.wordsVal (by simp; omega) (by omega)
  -- The addition.
  have hlt₃ : ∀ x ∈ addV, wordsVal s₃.mem base x 6 < W.p := by
    intro x hx
    simp only [addV, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [e₃ _ (by omega) (by omega) (by omega), uS₂ _ (by omega) (by omega)]; exact hP.alt
    · rw [e₃ _ (by omega) (by omega) (by omega), uS₂ _ (by omega) (by omega)]; exact hP.blt
    · rw [e₃ _ (by omega) (by omega) (by omega), hR₂ 736 (by simp)]; exact hI.lt 736 (by simp)
    · rw [e₃ _ (by omega) (by omega) (by omega), hR₂ 784 (by simp)]; exact hI.lt 784 (by simp)
    · rw [e₃ _ (by omega) (by omega) (by omega), hR₂ 832 (by simp)]; exact hI.lt 832 (by simp)
    · rw [e₃ _ (by omega) (by omega) (by omega), dx₂]; split
      · decide
      · exact Nat.mod_lt _ (by decide)
    · rw [dy₃]; split
      · exact Nat.mod_lt _ (by decide)
      · exact hlty
    · rw [e₃ _ (by omega) (by omega) (by omega), dz₂]; split
      · decide
      · exact hlt1
  refine WP.mono (addR_ok hw₃ hlt₃) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => ?_
  -- The invariant.
  have hU : Unch base stepW s₀.mem s₄.mem :=
    (((hI.unch.trans U₂).trans U₃).trans U₄).cover (by decide)
  refine ⟨hw₃.of_kp K₄, ?_, ?_, hU, ?_, lt₄, ?_⟩
  · rw [K₄.gpr _ (by decide), K₃.gpr _ (by decide), r₂.gpr _ (by decide), u₁.gpr]
  · exact ((hI.keep.trans (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))).trans
      (Kc.of_rest r₂)).trans (K₃.kc.trans K₄.kc)
  · exact (hI.tab.of_unch (by rw [K₄.rd, K₃.rd, r₂.rd, u₁.rd]) (W := [(880, 144), (1504, 16)] ++
      [(1456, 48), (3712, 384), (928, 48)] ++ [(736, 768), (3712, 384)]) (by decide)
      ((U₂.trans U₃).trans U₄))
  · -- `T = R + D`, with `D` the signed entry.
    have eb : tmv W 6 base s₃ 1984 = Fin.ofNat W.p W.b := by
      simp only [tmv]; rw [e₃ _ (by omega) (by omega) (by omega), uS₂ _ (by omega) (by omega)]; exact hP.b
    have eR : ∀ d ∈ [736, 784, 832], tmv W 6 base s₃ d = tmv W 6 base s d := by
      intro d hd
      simp only [tmv]
      have := hR₂ d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rw [e₃ d (by omega) (by omega) (by omega), this]
    have hD := entry_rep hL (k := kOf s₀.mem base) (i := j - 1) (by omega)
    rw [hv] at hD
    have ex : tmv W 6 base s₃ 880 = toM W.p (2 ^ 384) (if magH 64 v = 0 then 0
        else montP (entOf (j - 1) (magH 64 v - 1)).1) := by
      simp only [tmv]; rw [e₃ _ (by omega) (by omega) (by omega), dx₂]
    have ey : tmv W 6 base s₃ 928 = toM W.p (2 ^ 384) (if v < 64 then (0 + W.p - yDig (j - 1) v) % W.p
        else yDig (j - 1) v) := by
      simp only [tmv]; rw [dy₃]; simp only [decide_eq_true_eq, yDig]
    have ez : tmv W 6 base s₃ 976 = toM W.p (2 ^ 384) (if magH 64 v = 0 then 0 else oneM) := by
      simp only [tmv]; rw [e₃ _ (by omega) (by omega) (by omega), dz₂]
    rw [eb, eR 736 (by simp), eR 784 (by simp), eR 832 (by simp), ex, ey, ez] at v₄
    have hS := hL.add3 am3 (hL.onCurve_mul P384.onCurve_G _) (signed_onCurve hL (kOf s₀.mem base) (j - 1))
      hI.rep hD v₄.symm
    have hadd := combW_add hL P384.onCurve_G (w := 7) (k := kOf s₀.mem base) (J := 55) (j := j - 1) (by omega)
    rw [Nat.sub_add_cancel hj1] at hadd
    unfold signedPtW at hS
    rw [hadd] at hS
    exact hS

end

/-! ## The body -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P384 (W field_ok unit mul_zero_pt)
open VG.Proof.X25519.RISCV64 (Rest)


/-- What the body writes. -/
abbrev bodyW : List (Nat × Nat) := [(2272, 56), (736, 816), (3712, 384)]

/-- The body: `R = [k]G`, for the number `k` at `K`'s slot. -/
theorem body_ok (hL : Law W) {s : State} {base T : Addr} (hw : WsReg s base) (h2 : s.gpr .s4 = T)
    (hT : TabOk s base T) (hz : wordsVal s.mem base 208 6 = 0) (hone : wordsVal s.mem base 304 6 = oneM)
    (ha : tmv W 6 base s 352 = Fin.ofNat W.p W.a) (hb : tmv W 6 base s 1984 = Fin.ofNat W.p W.b)
    (hap : wordsVal s.mem base 352 6 < W.p) (hbp : wordsVal s.mem base 1984 6 < W.p) :
    WP isa (Cfg.body p384 Impl.P384.p384Comb7Start) s fun s' =>
      Kc s s' ∧ Unch base bodyW s.mem s'.mem ∧ TabOk s' base T ∧
      (∀ x ∈ [736, 784, 832], wordsVal s'.mem base x 6 < W.p) ∧
      Rep W (tmv W 6 base s' 736) (tmv W 6 base s' 784) (tmv W 6 base s' 832)
        (Spec.Weierstrass.mul (wordsVal s.mem base 1552 6) (Spec.Weierstrass.G W)) := by
  have hn := hw.nowrap
  have hC := P384.combOk7 hL
  rw [Cfg.body]
  simp only [List.append_assoc]
  -- The copy of `k`, and its zero word.
  refine WP.seq ?_
  refine WP.block_append (WP.mono (copy_ok 6 hw (o := 2272) (a := 1552) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  simp only [List.cons_append, List.nil_append]
  refine wp_li (imm := 0) (by decide) fun s₂ u₂ => ?_
  have hw₂ := hw₁.of_rest (u₂.rest (ws := [.t0]) (by decide))
  refine VG.Proof.Weierstrass.RISCV64.sdAt_ws hw₂ (by decide) (d := 2320) (by decide) (by decide) fun s₃ u₃ => ?_
  have hw₃ := hw₂.of_rest (u₃.rest [])
  have O₃ : Outside base 2320 8 s₂.mem s₃.mem := by rw [u₃.mem]; exact writeW_outside _ _ _ (by omega)
  -- `R = S`.
  refine WP.block_append (WP.mono (setConst_ok 6 hw₃ (o := 736) (x := VG.Impl.Ecdh.RISCV64.Cfg.mont p384
    Impl.P384.p384Comb7Start.1) (by decide) (by decide)) fun s₄ ⟨r₄, O₄, e₄⟩ => ?_)
  have hw₄ := hw₃.of_rest r₄
  refine WP.block_append (WP.mono (setConst_ok 6 hw₄ (o := 784) (x := VG.Impl.Ecdh.RISCV64.Cfg.mont p384
    Impl.P384.p384Comb7Start.2) (by decide) (by decide)) fun s₅ ⟨r₅, O₅, e₅⟩ => ?_)
  have hw₅ := hw₄.of_rest r₅
  refine WP.block_append (WP.mono (copy_ok 6 hw₅ (o := 832) (a := 304) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₆ ⟨e₆, r₆, O₆⟩ => ?_)
  have hw₆ := hw₅.of_rest r₆
  refine wp_li (imm := 55) (by decide) fun s₇ u₇ => WP.block_nil ?_
  have r₇ : Rest [.t0, .t1] s s₆ :=
    ((r₁.mono (by decide)).trans ((u₂.rest (ws := [.t0, .t1]) (by decide)).trans (u₃.rest _))).trans
      ((r₄.trans r₅).trans (r₆.mono (by decide)))
  have hw₇ : WsReg s₇ base := hw₆.of_kc (Kc.of_rest (u₇.rest (ws := [.s1]) (by decide)))
  have U₆ : Unch base [(2272, 48), (2320, 8), (736, 48), (784, 48), (832, 48)] s.mem s₆.mem := by
    have O₃' : Outside base 2320 8 s₁.mem s₃.mem := by rw [← u₂.mem]; exact O₃
    exact (((O₁.unch.trans O₃'.unch).trans O₄.unch).trans O₅.unch).trans O₆.unch
  have U₇ : Unch base [(2272, 48), (2320, 8), (736, 48), (784, 48), (832, 48)] s.mem s₇.mem := by
    rw [u₇.mem]; exact U₆
  have e7 : ∀ d, (d + 48 ≤ 736 ∨ 880 ≤ d) → (d + 48 ≤ 2272 ∨ 2328 ≤ d) → d + 48 ≤ 3712 →
      wordsVal s₇.mem base d 6 = wordsVal s.mem base d 6 := fun d h1 h2 h3 =>
    U₇.wordsVal (by simp; omega) (by omega)
  -- The loop's start.
  have hP : CombPre base T s₇ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₇.other _ (by decide), r₇.gpr _ (by decide), h2]
    · show word s₇.mem base 2320 = 0
      rw [u₇.mem, O₆.word (by omega) (by omega), O₅.word (by omega) (by omega), O₄.word (by omega) (by omega),
        u₃.mem, word_writeW_self, u₂.gpr]; rfl
    · rw [e7 208 (by omega) (by omega) (by omega)]; exact hz
    · rw [e7 304 (by omega) (by omega) (by omega)]; exact hone
    · simp only [tmv]; rw [e7 352 (by omega) (by omega) (by omega)]; exact ha
    · simp only [tmv]; rw [e7 1984 (by omega) (by omega) (by omega)]; exact hb
    · rw [e7 352 (by omega) (by omega) (by omega)]; exact hap
    · rw [e7 1984 (by omega) (by omega) (by omega)]; exact hbp
  have hk : kOf s₇.mem base = wordsVal s.mem base 1552 6 := by
    show wordsVal s₇.mem base 2272 6 = _
    rw [u₇.mem, O₆.wordsVal (by omega) (by omega), O₅.wordsVal (by omega) (by omega),
      O₄.wordsVal (by omega) (by omega), O₃.wordsVal (by omega) (by omega), u₂.mem, e₁]
  have hT₇ : TabOk s₇ base T := hT.of_unch (by rw [u₇.rd, r₆.rd, r₅.rd, r₄.rd, u₃.rd, u₂.rd, r₁.rd])
    (by decide) U₇
  have ex : wordsVal s₇.mem base 736 6 = montP Impl.P384.p384Comb7Start.1 := by
    rw [u₇.mem, O₆.wordsVal (by omega) (by omega), O₅.wordsVal (by omega) (by omega), e₄]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
  have ey : wordsVal s₇.mem base 784 6 = montP Impl.P384.p384Comb7Start.2 := by
    rw [u₇.mem, O₆.wordsVal (by omega) (by omega), e₅]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
  have ez : wordsVal s₇.mem base 832 6 = oneM := by
    rw [u₇.mem, e₆, O₅.wordsVal (by omega) (by omega), O₄.wordsVal (by omega) (by omega),
      O₃.wordsVal (by omega) (by omega), u₂.mem, O₁.wordsVal (by omega) (by omega)]; exact hone
  have hI : CombInv base T s₇ s₇ 55 := by
    refine ⟨hw₇, u₇.gpr, Kc.refl _, Unch.refl _ _ _, hT₇, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rw [ex]; exact Nat.mod_lt _ (by decide)
      · rw [ey]; exact Nat.mod_lt _ (by decide)
      · rw [ez]; exact Nat.mod_lt _ (by decide)
    · simp only [tmv]
      rw [ex, ey, ez, toM_montP, toM_montP, show 2 ^ (64 * 6) = 2 ^ 384 from rfl, toM_one unit,
        combEW_top, show 7 - 1 = 6 from rfl, show 2 ^ 6 = 2 ^ (7 - 1) from rfl, hC.start]
      exact rep_affine' hL _ _
  -- The steps.
  refine countLoop_ok (Inv := fun j s' => CombInv base T s₇ s' j) (n := 55) (fun j s' hi => hi.ctr)
    (fun j s' h1 h2 hi => step_ok hL hP h1 h2 hi) (fun s' hi => ?_) (by decide) (by decide) hI
  refine ⟨(Kc.of_rest r₇).trans ((Kc.of_rest (u₇.rest (ws := [.s1]) (by decide))).trans hi.keep),
    ((U₇.trans hi.unch).cover (by decide)), hi.tab, hi.lt, ?_⟩
  have hr := hi.rep
  rw [hk, combEW_zero (by have := wordsVal_lt s.mem base 1552 6; omega)] at hr
  exact hr

end

end VG.Proof.Ecdsa.RISCV64.P384.Comb
