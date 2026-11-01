module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
public import VerifiedGarbage.Impl.Sm4Gcm.RISCV64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SM4-GCM on RISC-V: the entry of `vg_sm4_gcm_seal` and `vg_sm4_gcm_open`

Untrusted: everything here is checked by Lean. AES-GCM's entry
(`Proof/AesGcm/RISCV64/OneEntry.lean`) with the arguments one register
earlier, and `tag` in `a7`: it loads `W` from the stack argument at
`sp + off`, saves our caller's registers there, keeps the arguments in
registers and the addresses of the additional data and the data in `W`
(`one1_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov aadO dataO save saved)
open VG.Proof.AesGcm.RISCV64 hiding SO1 one1_wp

/-- After the entry of `seal` or `open`, from `s₀`. -/
structure SO1 (W : Addr) (s₀ s₁ : State) : Prop where
  keeps : Keeps' s₀ s₁
  saved : SavedAt s₁.mem W s₀
  frame : Frame [oneR W] s₀.mem s₁.mem
  aad : s₁.mem.readW (W + BitVec.ofNat 64 aadO) 64 = s₀.gpr .a3
  dat : s₁.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a5
  s0 : s₁.gpr .s0 = W
  s1 : s₁.gpr .s1 = W + BitVec.ofNat 64 16
  s2 : s₁.gpr .s2 = s₀.gpr .a0
  s4 : s₁.gpr .s4 = s₀.gpr .a1
  s5 : s₁.gpr .s5 = s₀.gpr .a2
  s7 : s₁.gpr .s7 = s₀.gpr .a2
  s10 : s₁.gpr .s10 = s₀.gpr .a4
  s11 : s₁.gpr .s11 = s₀.gpr .a6
  s9 : s₁.gpr .s9 = s₀.gpr .a7

theorem one1_wp {s₀ : State} {off : Nat} {W : Addr} (hoff : off = 0 ∨ off = 8)
    (hW : Covers [⟨W, 2560⟩] s₀.wr) (hWa : W.toNat % 8 = 0) (hsa : s₀.sp.toNat % 16 = 0)
    (hWi : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 off) 8)
    (hWv : s₀.mem.readW (s₀.sp + BitVec.ofNat 64 off) 64 = W) :
    WP isa (.block (oneEntry off)) s₀ (SO1 W s₀) := by
  simp only [oneEntry, List.cons_append, List.nil_append]
  refine Steps.wp_addSp (imm := 0) (by decide) fun sA uA => ?_
  refine Steps.wp_ld (off := off) (a := s₀.sp + BitVec.ofNat 64 off) (by omega) (by rw [uA.gpr, add_ofNat_zero])
    (Spill.al8 (by omega) (by omega)) (by rw [uA.rd, uA.wr]; exact hWi) fun sB uB => ?_
  have b12 : sB.gpr .t1 = W := by rw [uB.gpr, uA.mem, hWv]
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (b := .t1) (by rw [b12, uB.wr, uA.wr]; exact hW) (by rw [b12]; exact hWa))
    fun s₂ ⟨hg, h31, hk, hsv, hf⟩ => ?_
  rw [b12] at h31 hsv hf
  have e : ∀ r, r ≠ .t1 → r ≠ .s0 → s₂.gpr r = s₀.gpr r := fun r a c => by
    rw [hg r c, uB.other r a, uA.other r a]
  have sv₂ : SavedAt s₂.mem W s₀ := hsv.congr fun p hp => by
    rw [uB.other _ (by revert hp; revert p; decide), uA.other _ (by revert hp; revert p; decide)]
  rw [uB.mem, uA.mem] at hf
  have kB : s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr ∧ s₂.sp = s₀.sp :=
    ⟨by rw [hk.rd, uB.rd, uA.rd], by rw [hk.wr, uB.wr, uA.wr], by rw [hk.sp, uB.sp, uA.sp]⟩
  refine Steps.wp_mv fun s₄ u₄ =>
    Steps.wp_addi (imm := 16) (by decide) fun s₅ u₅ => Steps.wp_mv fun s₆ u₆ => Steps.wp_mv fun s₇ u₇ =>
    Steps.wp_mv fun s₈ u₈ => ?_
  have g₈ : s₈.gpr .s0 = W := by simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄,
    reduceCtorEq, ite_false, h31]
  have k₈ : s₈.rd = s₀.rd ∧ s₈.wr = s₀.wr ∧ s₈.sp = s₀.sp ∧ s₈.mem = s₂.mem :=
    ⟨by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, kB.1], by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, kB.2.1],
      by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, kB.2.2], by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]⟩
  refine Steps.wp_sd (off := aadO) (a := W + BitVec.ofNat 64 aadO) (by decide) (by rw [g₈])
    (Spill.al8 hWa (by decide)) (by rw [k₈.2.1]; exact in_off hW (by decide) (by decide)) fun s₉ m₉ => ?_
  refine Steps.wp_mv fun s₁₀ u₁₀ => ?_
  refine Steps.wp_sd (off := dataO) (a := W + BitVec.ofNat 64 dataO) (by decide)
    (by rw [u₁₀.other _ (by decide), m₉.gpr, g₈]) (Spill.al8 hWa (by decide))
    (by rw [u₁₀.wr, m₉.wr, k₈.2.1]; exact in_off hW (by decide) (by decide)) fun s₁₁ m₁₁ => ?_
  refine Steps.wp_mv fun s₁₂ u₁₂ => Steps.wp_mv fun s₁₃ u₁₃ => WP.block_nil ?_
  have sp₁₃ : s₁₃.sp = s₀.sp := by rw [u₁₃.sp, u₁₂.sp, m₁₁.sp, u₁₀.sp, m₉.sp, k₈.2.2.1]
  have rd₁₃ : s₁₃.rd = s₀.rd := by rw [u₁₃.rd, u₁₂.rd, m₁₁.rd, u₁₀.rd, m₉.rd, k₈.1]
  have wr₁₃ : s₁₃.wr = s₀.wr := by rw [u₁₃.wr, u₁₂.wr, m₁₁.wr, u₁₀.wr, m₉.wr, k₈.2.1]
  -- The memory: the two addresses stored after the saved registers.
  have v₄ : s₈.gpr .a3 = s₀.gpr .a3 := by
    simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, reduceCtorEq, ite_false]
    exact e _ (by decide) (by decide)
  have v₆ : s₁₀.gpr .a5 = s₀.gpr .a5 := by
    rw [u₁₀.other _ (by decide), m₉.gpr]
    simp only [upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, reduceCtorEq, ite_false]
    exact e _ (by decide) (by decide)
  generalize hM : (s₂.mem.writeW (W + BitVec.ofNat 64 aadO) (s₀.gpr .a3)).writeW (W + BitVec.ofNat 64 dataO)
    (s₀.gpr .a5) = M
  have m₁₃ : s₁₃.mem = M := by
    rw [u₁₃.mem, u₁₂.mem, m₁₁.mem, u₁₀.mem, v₆, m₉.mem, v₄, k₈.2.2.2, hM]
  have fM : Frame [oneR W] s₀.mem M := by
    rw [← hM]
    exact ((hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))
  have dS : ∀ {d : Nat}, 232 ≤ d → d + 8 ≤ 248 → (savedR W).Disjoint ⟨W + BitVec.ofNat 64 d, 8⟩ :=
    fun h₁ h₂ => Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  refine ⟨⟨by rw [rd₁₃], by rw [wr₁₃], by rw [sp₁₃]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₁₃, ← hM]
    exact (sv₂.frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dS (by decide) (by decide))).frame
      ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dS (by decide) (by decide))
  · rw [m₁₃]; exact fM
  · rw [m₁₃, ← hM, Mem.readW_writeW_sep (Region.Disjoint.sep
      (Offset.disjoint W (d := aadO) (n := 8) (e := dataO) (k := 8) (.inl (by decide)) (by decide) (by decide))
      (Region.contains_self _ _) (Region.contains_self _ _)) (by decide), Mem.readW_writeW_self64]
  · rw [m₁₃, ← hM, Mem.readW_writeW_self64]
  all_goals simp only [upd_gpr u₁₃, upd_gpr u₁₂, upd_gpr u₁₀, m₁₁.gpr, m₉.gpr, upd_gpr u₈,
    upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, reduceCtorEq, ite_false, ite_true]
  all_goals first
    | exact h31
    | (rw [h31])
    | exact e _ (by decide) (by decide)

end VG.Proof.Sm4Gcm.RISCV64
