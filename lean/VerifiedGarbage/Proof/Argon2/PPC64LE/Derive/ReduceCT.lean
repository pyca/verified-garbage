module

public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.CTCall
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Reduce
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillCT1
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Locals
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.CTCall
meta import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Reduce
meta import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillCT1
meta import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Locals
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.MemoryInit
meta import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.MemoryInit
public import VerifiedGarbage.Proof.Argon2.Matrix
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Parameters

/-!
# Argon2 on PPC64LE: the final block and the tag, in two runs

`reduce_rel`: the reduction's loop runs the same number of times in both runs
and each lane's XOR addresses the same blocks; `finalOutput_rel`: H′ is
called with the same arguments.
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd wp_addi wp_li)
open VG.Spec.Argon2 (Block zeroBlock)
open VG.Impl.Argon2.PPC64LE.Derive (laneOff laneLenOff lda)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The instructions before `finalOutput`'s call of H′. -/
theorem foBlk_ok {s : State} (h : Inv s₀ s) :
    WP isa (.block [lda .r3 Impl.Argon2.PPC64LE.Derive.memoryArg, .li .r4 1024,
      lda .r5 Impl.Argon2.PPC64LE.Derive.outArg, lda .r6 Impl.Argon2.PPC64LE.Derive.outLenArg,
      Impl.Argon2.PPC64LE.HPrime.mov .r7 .r31]) s fun t => Two.HArgs s₀ t ∧
      t.gpr .r3 = memP s₀ ∧ t.gpr .r4 = BitVec.ofNat 64 1024 ∧ t.gpr .r5 = outP s₀ ∧
      t.gpr .r6 = arg s₀ 17 := by
  have b1 := blocks_pos hp
  have tg := hp.tag_ge
  have tl := hp.tag_lt
  have b1k : 1024 ≤ blocksN s₀ * 1024 := Nat.le_mul_of_pos_left _ b1
  unfold Impl.Argon2.PPC64LE.HPrime.mov
  refine wp_lda hp h (i := 13) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁
  refine wp_li (by decide) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂
  refine wp_lda hp i₂ (i := 16) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃
  refine wp_lda hp i₃ (i := 17) (by decide) fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄
  refine wp_addi (by decide) fun s₅ u₅ => WP.block_nil ?_
  have i₅ := i₄.upd u₅
  have si : s₅.gpr .r3 = memP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ax : s₅.gpr .r4 = BitVec.ofNat 64 1024 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  have di : s₅.gpr .r5 = outP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  have cx : s₅.gpr .r6 = arg s₀ 17 := by
    rw [u₅.other _ (by decide), u₄.gpr]
  have r7 : s₅.gpr .r7 = scrP s₀ := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h.r31]; simp
  refine ⟨⟨i₅, r7, ⟨memR s₀, by simp, 0, by rw [si]; simp, by rw [ax]; show 0 + 1024 ≤ blocksN s₀ * 1024; omega⟩,
    ⟨outR s₀, by simp, 0, by rw [di]; simp, by rw [cx]; show 0 + outL s₀ ≤ outL s₀; omega⟩,
    by rw [ax]; decide, by rw [cx]; exact ⟨by show 1 ≤ outL s₀; omega, tl⟩⟩, si, ax, di, cx⟩

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `reduce` leaks the same trace in two runs. -/
theorem reduce_rel {M₁ M₂ : Array Block} :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁ ∧ Represents s₁.mem (memP s₀₁) (prm s₀₁).blocks M₁) ∧
      (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂ ∧ Represents s₂.mem (memP s₀₂) (prm s₀₂).blocks M₂))
      Impl.Argon2.PPC64LE.Derive.reduce fun _ _ => True := by
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  unfold Impl.Argon2.PPC64LE.Derive.reduce
  refine RelCT.seqW (T.leaf [] [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => reduceStart_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => reduceStart_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  generalize hN : lanesN s₀₁ = N at hl1
  have hN₂ : lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      RI s₀₁ M₁ l s₁ ∧ RI s₀₂ M₂ l s₂) ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega, hl1, h.1, h.2⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, g₁, g₂⟩ e₁ e₂
  have body : RelCT isa (fun s₁ s₂ => RI s₀₁ M₁ l s₁ ∧ RI s₀₂ M₂ l s₂)
      (.block (Impl.Argon2.PPC64LE.Derive.reduceLane ++ Impl.Argon2.PPC64LE.Derive.advanceBy laneOff
        (Impl.Argon2.PPC64LE.Derive.ldw .r4 Impl.Argon2.PPC64LE.Derive.lanesArg))) fun _ _ => True :=
    T.leaf [laneOff, laneLenOff] [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [h.1.lane, h.2.lane], (T.prm_lw h.1.pr h.2.pr).1⟩, by simp⟩) ⟨_, by taint_decide⟩
  obtain ⟨ht, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩ := rel_wp body
    (fun s h => reduceLane_ok T.hp₁ h (by rw [hN]; exact hl))
    (fun s h => reduceLane_ok T.hp₂ h (by rw [hN₂]; exact hl)) s₁ s₂ t₁ t₂ s₁' s₂' ⟨g₁, g₂⟩ e₁ e₂
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, c₁.trans c₂.symm, fun _ => trivial, fun hc => ?_⟩
  have e₀ : some (!decide (l + 1 = N)) = some true := c₁.symm.trans hc
  have e : l + 1 ≠ N := by simpa using e₀
  exact ⟨N - (l + 1), by omega, l + 1, rfl, by omega, k₁, k₂⟩

/-- `finalOutput` leaks the same trace in two runs. -/
theorem finalOutput_rel :
    RelCT isa (fun s₁ s₂ => Inv s₀₁ s₁ ∧ Inv s₀₂ s₂) Impl.Argon2.PPC64LE.Derive.finalOutput
      fun _ _ => True := by
  unfold Impl.Argon2.PPC64LE.Derive.finalOutput
  refine RelCT.seqW (T.leaf [] [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => foBlk_ok T.hp₁ h) (fun s h => foBlk_ok T.hp₂ h) ?_
  refine T.hcall_rel fun s₁ s₂ ⟨k₁, k₂⟩ => ⟨k₁.1, k₂.1, ?_, ?_, ?_, ?_⟩
  · rw [k₁.2.1, k₂.2.1, T.pb.memP_eq]
  · rw [k₁.2.2.1, k₂.2.2.1]
  · rw [k₁.2.2.2.1, k₂.2.2.2.1, T.pb.outP_eq]
  · rw [k₁.2.2.2.2, k₂.2.2.2.2, T.pb.arg_eq (by decide)]

end Two

end VG.Proof.Argon2.PPC64LE.Derive
