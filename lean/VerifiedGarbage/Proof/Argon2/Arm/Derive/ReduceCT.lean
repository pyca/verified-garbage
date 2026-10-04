import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCT1

/-!
# Argon2 on ARMv7: the final block and the tag, in two runs

`reduce_rel`: XORing every lane's last block into the first leaks the same
trace in two runs (the lane's last block's address is related by
correctness); `finalOutput_rel`: so does the call of H′ that writes the tag.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd wp_mov wp_sub op2_imm op2_reg)
open VG.Proof.Sha512.Arm (Only)
open VG.Spec.Argon2 (Block zeroBlock)
open VG.Impl.Argon2.Arm.Derive (argOff laneOff laneLenOff ld st)

theorem RI.of_only {s₀ s t : State} {M : Array Block} {l : Nat} (h : RI s₀ M l s) {ds : List Reg}
    (k : Only ds s t) (h11 : Reg.r11 ∉ ds) : RI s₀ M l t :=
  ⟨h.inv.only k h11, h.pr.of_mem k.mem, by rw [lw_mem k.mem]; exact h.lane, by rw [k.mem]; exact h.first,
    fun j hj j0 => by rw [k.mem]; exact h.rest j hj j0⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The first part of a lane's reduction: `r0 :=` the address of its last block. -/
theorem redPart1_ok {s : State} {M : Array Block} {l : Nat} (h : RI s₀ M l s) (hl : l < lanesN s₀) :
    WP isa (.block (([ld .r0 laneOff, ld .r1 laneLenOff, .dp .sub .r1 .r1 (.imm 1)] : List Instr) ++
      Impl.Argon2.Arm.Derive.blockAddr)) s fun t => RI s₀ M l t ∧
      t.gpr .r0 = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + ((prm s₀).laneLen - 1)) * 1024) := by
  have L8 := laneLen_ge hp
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc hp h.inv (d := laneOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁ (by decide)
  refine wp_ldloc hp i₁ (d := laneLenOff) (by decide) fun s₂ u₂ => wp_sub (op2_imm (by decide)) fun s₃ u₃ => ?_
  have o₃ := ((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)
  have i₃ := h.inv.only o₃ (by decide)
  rw [← List.append_nil Impl.Argon2.Arm.Derive.blockAddr]
  refine blockAddr_ok hp i₃ (h.pr.of_mem o₃.mem) hl (col := (prm s₀).laneLen - 1) (by omega)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.lane])
    (by rw [u₃.gpr, u₂.gpr, lw_mem u₁.mem, h.pr.laneLen, ofNat_pred (by omega) rfl]) fun s₄ a₄ k₄ =>
      WP.block_nil ⟨h.of_only (o₃.trans k₄) (by decide), a₄⟩

/-- The instructions before `finalOutput`'s call of H′. -/
theorem foBlk_ok {s : State} (h : Inv s₀ s) :
    WP isa (.block [ld .r0 (argOff 13), .mov .r1 (.imm 1024), ld .r2 (argOff 16), ld .r3 (argOff 17),
      ld .r12 (argOff 15)]) s fun t => Inv s₀ t ∧ t.gpr .r12 = scrP s₀ ∧
      t.gpr .r0 = memP s₀ ∧ t.gpr .r1 = 1024 ∧ t.gpr .r2 = outP s₀ ∧ t.gpr .r3 = arg s₀ 17 := by
  refine wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide)
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide)
  refine wp_ldarg hp i₂ (i := 16) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide)
  refine wp_ldarg hp i₃ (i := 17) (by decide) fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄ (by decide)
  refine wp_ldarg hp i₄ (i := 15) (by decide) fun s₅ u₅ => WP.block_nil ⟨i₄.upd u₅ (by decide),
    u₅.gpr, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₅.other _ (by decide), u₄.gpr]

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `reduce` leaks the same trace in two runs. -/
theorem reduce_rel {M₁ M₂ : Array Block} :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁ ∧ Represents s₁.mem (memB s₀₁) (prm s₀₁).blocks M₁) ∧
      (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂ ∧ Represents s₂.mem (memB s₀₂) (prm s₀₂).blocks M₂))
      Impl.Argon2.Arm.Derive.reduce fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  unfold Impl.Argon2.Arm.Derive.reduce
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => reduceStart_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => reduceStart_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  generalize hN : lanesN s₀₁ = N at hl1
  have hN₂ : lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      RI s₀₁ M₁ l s₁ ∧ RI s₀₂ M₂ l s₂) ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega, hl1, h.1, h.2⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, g₁, g₂⟩ e₁ e₂
  have body : RelCT isa (fun s₁ s₂ => RI s₀₁ M₁ l s₁ ∧ RI s₀₂ M₂ l s₂)
      (.block (Impl.Argon2.Arm.Derive.reduceLane ++ Impl.Argon2.Arm.Derive.advance laneOff
        (argOff Impl.Argon2.Arm.Derive.lanesArg))) fun _ _ => True := by
    rw [show Impl.Argon2.Arm.Derive.reduceLane ++ Impl.Argon2.Arm.Derive.advance laneOff
        (argOff Impl.Argon2.Arm.Derive.lanesArg) =
      (([ld .r0 laneOff, ld .r1 laneLenOff, .dp .sub .r1 .r1 (.imm 1)] : List Instr) ++
        Impl.Argon2.Arm.Derive.blockAddr) ++
      (([.mov .r1 (.reg .r0), ld .r3 (argOff Impl.Argon2.Arm.Derive.memoryArg)] : List Instr) ++
        (Impl.Argon2.Arm.Derive.writeBlock true ++ Impl.Argon2.Arm.Derive.advance laneOff
          (argOff Impl.Argon2.Arm.Derive.lanesArg))) by
      simp only [Impl.Argon2.Arm.Derive.reduceLane, List.append_assoc]]
    refine RelCT.block_split (RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩)
        ⟨_, by taint_decide⟩)
      (fun s h => redPart1_ok T.hp₁ h (by rw [hN]; exact hl))
      (fun s h => redPart1_ok T.hp₂ h (by rw [hN₂]; exact hl)) ?_)
    exact T.leafI [.r0] (fun s₁ s₂ h => ⟨h.1.1.inv, h.2.1.inv, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2, h.2.2, pe, T.pb.memP_eq]⟩) ⟨_, by taint_decide⟩
  obtain ⟨ht, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩ := rel_wp body
    (fun s h => reduceLane_ok T.hp₁ h (by rw [hN]; exact hl))
    (fun s h => reduceLane_ok T.hp₂ h (by rw [hN₂]; exact hl)) s₁ s₂ t₁ t₂ s₁' s₂' ⟨g₁, g₂⟩ e₁ e₂
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show VG.Arm.eval .ne s₁' = VG.Arm.eval .ne s₂'; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : l + 1 ≠ N := by
    rw [show isa.eval .ne s₁' = VG.Arm.eval .ne s₁' from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (l + 1), by omega, l + 1, rfl, by omega, k₁, k₂⟩

/-- `finalOutput` leaks the same trace in two runs. -/
theorem finalOutput_rel :
    RelCT isa (fun s₁ s₂ => Inv s₀₁ s₁ ∧ Inv s₀₂ s₂) Impl.Argon2.Arm.Derive.finalOutput fun _ _ => True := by
  have pre : ∀ {s₀ : State}, DPre s₀ → ∀ {t : State}, Inv s₀ t ∧ t.gpr .r12 = scrP s₀ ∧
      t.gpr .r0 = memP s₀ ∧ t.gpr .r1 = 1024 ∧ t.gpr .r2 = outP s₀ ∧ t.gpr .r3 = arg s₀ 17 →
      Inv s₀ t ∧ t.gpr .r12 = scrP s₀ ∧
        (∃ R ∈ [memR s₀, locR s₀], ∃ off, State.addr (t.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .r1).toNat ≤ R.len) ∧ (t.gpr .r0).toNat + (t.gpr .r1).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀, outR s₀], ∃ off, State.addr (t.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .r3).toNat ≤ R.len) ∧ (t.gpr .r2).toNat + (t.gpr .r3).toNat ≤ 2 ^ 32 ∧
        1 ≤ (t.gpr .r3).toNat := fun {s₀} hp {t} ⟨i, d, si, ax, di, cx⟩ => by
    have b1 := blocks_pos hp
    have hm := hp.mem_fits
    have ho := hp.out_fits
    have tg := hp.tag_ge
    refine ⟨i, d, ⟨memR s₀, by simp, 0, by rw [si]; simp, by rw [ax]; show 0 + 1024 ≤ blocksN s₀ * 1024; omega⟩,
      by rw [si, ax]; show _ + 1024 ≤ 2 ^ 32; omega,
      ⟨outR s₀, by simp, 0, by rw [di]; simp, by rw [cx]; show 0 + outL s₀ ≤ outL s₀; omega⟩,
      by rw [di, cx]; exact ho, by rw [cx]; show 1 ≤ outL s₀; omega⟩
  unfold Impl.Argon2.Arm.Derive.finalOutput
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => foBlk_ok T.hp₁ h) (fun s h => foBlk_ok T.hp₂ h) ?_
  refine T.hcall_rel fun s₁ s₂ ⟨k₁, k₂⟩ => ⟨pre T.hp₁ k₁, pre T.hp₂ k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.2.2.1, k₂.2.2.1, T.pb.memP_eq]
  · rw [k₁.2.2.2.1, k₂.2.2.2.1]
  · rw [k₁.2.2.2.2.1, k₂.2.2.2.2.1, T.pb.outP_eq]
  · rw [k₁.2.2.2.2.2, k₂.2.2.2.2.2, T.pb.arg_eq (by decide)]

end Two

end VG.Proof.Argon2.Arm.Derive
