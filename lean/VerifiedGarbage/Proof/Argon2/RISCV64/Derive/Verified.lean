module

public import VerifiedGarbage.Impl.Argon2.RISCV64.Derive
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Correct
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.InitialCT
import VerifiedGarbage.Proof.Argon2.References
import VerifiedGarbage.Proof.Argon2.Iterations
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.CTCall
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillCT1
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.InitialCT
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Correct
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Scratch
meta import VerifiedGarbage.Proof.Argon2.References
meta import VerifiedGarbage.Proof.Argon2.Iterations
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.CTCall
import VerifiedGarbage.Proof.Argon2.FinalReduction
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Reduce
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Reduce
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillLoops
public import VerifiedGarbage.Proof.Argon2.FillStep
public import VerifiedGarbage.Proof.Argon2.Slices
import VerifiedGarbage.Proof.Argon2.IterationsIndices
import VerifiedGarbage.Proof.Argon2.SegmentIndices
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillBlock
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillLoops
meta import VerifiedGarbage.Proof.Argon2.FillStep
meta import VerifiedGarbage.Proof.Argon2.Slices
meta import VerifiedGarbage.Proof.Argon2.IterationsIndices
meta import VerifiedGarbage.Proof.Argon2.SegmentIndices
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillBlock
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillCT1
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillCall
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillCache
meta import VerifiedGarbage.Proof.Argon2.FillPositions
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillCache
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillCall
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.MemoryInit
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.MemoryInit
public import VerifiedGarbage.Proof.Argon2.Matrix
meta import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Argon2.RISCV64.Derive.BodyCT`, which only this module used -/

section

/-! ### `Argon2.RISCV64.Derive.MemCT`, which only this module used -/

section

/-!
# Argon2 on RISC-V: the memory's initialization, in two runs

`memoryInit_rel`: clearing the memory and the first two blocks of each lane
leak the same trace in two runs. The lanes' loop runs the same number of
times in both (`lane_ok`'s condition), and each call of H′ has the same
arguments: H₀'s place, the cell, and the lengths.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd wp_addi wp_li wp_mv)
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (matrixCell)

/-- The arguments of H′ for block `c` of a lane. -/
def initArgs (c : Nat) : List Instr :=
  [.li .a0 c, .store .w .a0 .s3 Impl.Argon2.RISCV64.Derive.columnOff,
    .store .w .s1 .s3 Impl.Argon2.RISCV64.Derive.laneWordOff, .addi .a0 .s3 Impl.Argon2.RISCV64.Derive.h0Off,
    .li .a1 72, Impl.Argon2.RISCV64.HPrime.mov .a2 .s2, .li .a3 1024, Impl.Argon2.RISCV64.HPrime.mov .a4 .s4]

theorem initBlock_eq (c : Nat) :
    Impl.Argon2.RISCV64.Derive.initBlock c = .seq (.block (initArgs c)) Impl.Argon2.RISCV64.Derive.hPrimeCall :=
  rfl

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- H′'s arguments for block `c` of lane `l`. -/
theorem initArgs_ok {s : State} (h : Inv s₀ s) {l c : Nat} (hl : l < lanesN s₀) (hc : c < 2)
    (r29 : s.gpr .s2 = memP s₀ + BitVec.ofNat 64 ((l * (prm s₀).laneLen + c) * 1024)) :
    WP isa (.block (initArgs c)) s fun t => Two.HArgs s₀ t ∧ t.gpr .a0 = E s₀ + BitVec.ofNat 64 0 ∧
      t.gpr .a1 = BitVec.ofNat 64 72 ∧
      t.gpr .a2 = memP s₀ + BitVec.ofNat 64 ((l * (prm s₀).laneLen + c) * 1024) ∧
      t.gpr .a3 = BitVec.ofNat 64 1024 := by
  have hlt := hp.lanes_lt
  have L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega_using [this]
  have hcell : l * (prm s₀).laneLen + c < blocksN s₀ := by
    rw [hp.blocks_eq]
    have := Nat.mul_le_mul_right (prm s₀).laneLen (show l + 1 ≤ lanesN s₀ by omega_using [hl])
    rw [Nat.succ_mul] at this
    omega_using [hc, L2, this]
  unfold initArgs Impl.Argon2.RISCV64.HPrime.mov
  refine wp_li (by omega_using [hc]) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁
  refine wp_stlocw i₁ (d := 64) (by decide) fun s₂ i₂ _ g₂ => ?_
  refine wp_stlocw i₂ (d := 68) (by decide) fun s₃ i₃ _ g₃ => ?_
  refine wp_addi (by decide) fun s₄ u₄ => wp_li (by decide) fun s₅ u₅ =>
    wp_addi (by decide) fun s₆ u₆ => wp_li (by decide) fun s₇ u₇ => wp_addi (by decide) fun s₈ u₈ =>
    WP.block_nil ?_
  have i₈ := ((((i₃.upd u₄).upd u₅).upd u₆).upd u₇).upd u₈
  have r3₈ : s₈.gpr .a0 = E s₀ + BitVec.ofNat 64 0 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.gpr, g₃, g₂, i₁.s3]
    rfl
  have r4₈ : s₈.gpr .a1 = BitVec.ofNat 64 72 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  have r6₈ : s₈.gpr .a3 = BitVec.ofNat 64 1024 := by rw [u₈.other _ (by decide), u₇.gpr]
  have r5₈ : s₈.gpr .a2 = memP s₀ + BitVec.ofNat 64 ((l * (prm s₀).laneLen + c) * 1024) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), g₃, g₂, u₁.other _ (by decide), r29]
    simp
  have r7₈ : s₈.gpr .a4 = scrP s₀ := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), g₃, g₂, i₁.s4]
    simp
  have hcell' : (l * (prm s₀).laneLen + c) * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega_using [hcell]
  refine ⟨⟨i₈, r7₈, ⟨inR s₀, by simp, 0, by rw [r3₈]; simp, by rw [r4₈]; show 0 + 72 ≤ 72; omega_using []⟩,
    ⟨memR s₀, by simp, (l * (prm s₀).laneLen + c) * 1024, by rw [r5₈], by rw [r6₈]; exact hcell'⟩,
    by rw [r4₈]; decide, by rw [r6₈]; decide⟩, r3₈, r4₈, r5₈, r6₈⟩

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `clear` leaks the same trace in two runs. -/
theorem clear_rel {F₁ F₂ : State → Prop} (hF₁ : ∀ s, F₁ s → Inv s₀₁ s) (hF₂ : ∀ s, F₂ s → Inv s₀₂ s) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) Impl.Argon2.RISCV64.Derive.clear fun _ _ => True :=
  T.leaf [] [] (fun s₁ s₂ h => ⟨hF₁ _ h.1, hF₂ _ h.2, by simp, by simp⟩) ⟨_, by taint_decide⟩

/-- Block `c` of lane `l` leaks the same trace in two runs. -/
theorem initBlock_rel {l c : Nat} (hl : l < lanesN s₀₁) (hc : c < 2)
    (hcA : ∃ hc, (VG.Taint.check frameTaint (τF [] [.s1, .s2]) (.block (initArgs c)) hc).isSome = true)
    {F₁ F₂ : State → Prop}
    (hF₁ : ∀ s, F₁ s → Inv s₀₁ s ∧ s.gpr .s1 = BitVec.ofNat 64 l ∧
      s.gpr .s2 = memP s₀₁ + BitVec.ofNat 64 ((l * (prm s₀₁).laneLen + c) * 1024))
    (hF₂ : ∀ s, F₂ s → Inv s₀₂ s ∧ s.gpr .s1 = BitVec.ofNat 64 l ∧
      s.gpr .s2 = memP s₀₂ + BitVec.ofNat 64 ((l * (prm s₀₂).laneLen + c) * 1024)) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (Impl.Argon2.RISCV64.Derive.initBlock c) fun _ _ => True := by
  have hl₂ : l < lanesN s₀₂ := by rw [← T.pb.lanesN_eq]; exact hl
  rw [initBlock_eq]
  refine RelCT.seqW (T.leaf [] [.s1, .s2] (fun s₁ s₂ h => ⟨(hF₁ _ h.1).1, (hF₂ _ h.2).1, by simp, by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [(hF₁ _ h.1).2.1, (hF₂ _ h.2).2.1], by
        rw [(hF₁ _ h.1).2.2, (hF₂ _ h.2).2.2, T.pb.memP_eq, T.pb.prm_eq]⟩⟩) hcA)
    (fun s h => initArgs_ok T.hp₁ (hF₁ s h).1 hl hc (hF₁ s h).2.2)
    (fun s h => initArgs_ok T.hp₂ (hF₂ s h).1 hl₂ hc (hF₂ s h).2.2) ?_
  exact T.hcall_rel fun s₁ s₂ ⟨h₁, h₂⟩ => ⟨h₁.1, h₂.1, by rw [h₁.2.1, h₂.2.1, T.pb.E_eq],
    by rw [h₁.2.2.1, h₂.2.2.1], by rw [h₁.2.2.2.1, h₂.2.2.2.1, T.pb.memP_eq, T.pb.prm_eq],
    by rw [h₁.2.2.2.2, h₂.2.2.2.2]⟩

/-- One lane's first two blocks leak the same trace in two runs. -/
theorem initLane_rel {l : Nat} (hl : l < lanesN s₀₁) {h0₁ h0₂ : List Byte} :
    RelCT isa (fun s₁ s₂ => LI s₀₁ h0₁ l s₁ ∧ LI s₀₂ h0₂ l s₂) Impl.Argon2.RISCV64.Derive.initLane
      fun _ _ => True := by
  have hl₂ : l < lanesN s₀₂ := by rw [← T.pb.lanesN_eq]; exact hl
  let G (s₀ : State) (h0 : List Byte) (c : Nat) (t : State) : Prop :=
    Inv s₀ t ∧ Prm s₀ t ∧ bytesAt t.mem (E s₀ + BitVec.ofNat 64 0) 64 = h0 ∧
      t.gpr .s1 = BitVec.ofNat 64 l ∧
      t.gpr .s2 = memP s₀ + BitVec.ofNat 64 ((l * (prm s₀).laneLen + c) * 1024)
  have w0 : ∀ {s₀ : State} {h0 : List Byte}, DPre s₀ → l < lanesN s₀ → ∀ s, LI s₀ h0 l s →
      WP isa (Impl.Argon2.RISCV64.Derive.initBlock 0) s (G s₀ h0 0) := fun {s₀ h0} hp hl s h =>
    (initBlock_ok hp h.inv h.pr h.b0 hl (c := 0) (by decide) h.s1 (by rw [h.s2, Nat.add_zero])).mono
      fun t ⟨i, p, b, e, d, _⟩ => ⟨i, p, b, by rw [e, h.s1], by rw [d, h.s2, Nat.add_zero]⟩
  have wA : ∀ {s₀ : State} {h0 : List Byte} (s : State), G s₀ h0 0 s →
      WP isa (.block [.addi .s2 .s2 1024]) s (G s₀ h0 1) := fun {s₀ h0} s h =>
    wp_addi (by decide) fun t u => WP.block_nil ⟨h.1.upd u, h.2.1.of_mem u.mem,
      by rw [u.mem]; exact h.2.2.1, by rw [u.other _ (by decide), h.2.2.2.1],
      by rw [u.gpr, h.2.2.2.2, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_mul, Nat.add_mul,
        Nat.zero_mul, Nat.add_zero]⟩
  have w1 : ∀ {s₀ : State} {h0 : List Byte}, DPre s₀ → l < lanesN s₀ → ∀ s, G s₀ h0 1 s →
      WP isa (Impl.Argon2.RISCV64.Derive.initBlock 1) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
        t.gpr .s1 = BitVec.ofNat 64 l ∧
        t.gpr .s2 = memP s₀ + BitVec.ofNat 64 ((l * (prm s₀).laneLen + 1) * 1024) :=
    fun {s₀ h0} hp hl s h =>
      (initBlock_ok hp h.1 h.2.1 h.2.2.1 hl (c := 1) (by decide) h.2.2.2.1 h.2.2.2.2).mono
        fun t ⟨i, p, _, e, d, _⟩ => ⟨i, p, by rw [e, h.2.2.2.1], by rw [d, h.2.2.2.2]⟩
  unfold Impl.Argon2.RISCV64.Derive.initLane
  refine RelCT.seqW (T.initBlock_rel (c := 0) (F₁ := LI s₀₁ h0₁ l) (F₂ := LI s₀₂ h0₂ l) hl (by decide)
      ⟨_, by taint_decide⟩ (fun s h => ⟨h.inv, h.s1, by rw [h.s2, Nat.add_zero]⟩)
      (fun s h => ⟨h.inv, h.s1, by rw [h.s2, Nat.add_zero]⟩))
    (w0 T.hp₁ hl) (w0 T.hp₂ hl₂) ?_
  refine RelCT.seqW (T.leaf [] [.s2] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp, by
      simp only [List.mem_singleton, forall_eq]
      rw [h.1.2.2.2.2, h.2.2.2.2.2, T.pb.memP_eq, T.pb.prm_eq]⟩) ⟨_, by taint_decide⟩)
    wA wA ?_
  refine RelCT.seqW (T.initBlock_rel (c := 1) hl (by decide) ⟨_, by taint_decide⟩
      (fun s h => ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩) (fun s h => ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩))
    (w1 T.hp₁ hl) (w1 T.hp₂ hl₂) ?_
  exact T.leaf [Impl.Argon2.RISCV64.Derive.strideOff] [.s1, .s2] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by
      simp only [List.mem_singleton, forall_eq]
      rw [h.1.2.1.stride, h.2.2.1.stride, T.pb.prm_eq], by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [h.1.2.2.1, h.2.2.2.1], by rw [h.1.2.2.2, h.2.2.2.2, T.pb.memP_eq, T.pb.prm_eq]⟩⟩)
    ⟨_, by taint_decide⟩

/-- The lanes' loop leaks the same trace in two runs. -/
theorem initLanes_rel {h0₁ h0₂ : List Byte} :
    RelCT isa (fun s₁ s₂ => LI s₀₁ h0₁ 0 s₁ ∧ LI s₀₂ h0₂ 0 s₂)
      (.loop Impl.Argon2.RISCV64.Derive.initLane (.nonzero .a0)) fun _ _ => True := by
  have hl1 := T.hp₁.lanes_pos
  refine (RelCT.loop (Q := fun _ _ => True)
    (fun n s₁ s₂ => ∃ l, n = lanesN s₀₁ - l ∧ l < lanesN s₀₁ ∧ LI s₀₁ h0₁ l s₁ ∧ LI s₀₂ h0₂ l s₂)
    (fun n => RelCT.exists_ fun l => ?_) (lanesN s₀₁)).mono
    (fun s₁ s₂ h => ⟨0, by omega_using [], hl1, h.1, h.2⟩) fun _ _ h => h
  by_cases hn : l < lanesN s₀₁ ∧ n = lanesN s₀₁ - l
  · obtain ⟨hl, rfl⟩ := hn
    have hl₂ : l < lanesN s₀₂ := by rw [← T.pb.lanesN_eq]; exact hl
    refine ((T.initLane_rel hl (h0₁ := h0₁) (h0₂ := h0₂)).wp
      (F₁ := fun t => LI s₀₁ h0₁ (l + 1) t ∧
        VG.RISCV64.eval (.nonzero .a0) t = some (!decide (l + 1 = lanesN s₀₁)))
      (F₂ := fun t => LI s₀₂ h0₂ (l + 1) t ∧
        VG.RISCV64.eval (.nonzero .a0) t = some (!decide (l + 1 = lanesN s₀₂)))
      fun s₁ s₂ h => ⟨lane_ok T.hp₁ hl h.1, lane_ok T.hp₂ hl₂ h.2⟩).mono
      (fun s₁ s₂ h => ⟨h.2.2.1, h.2.2.2⟩) fun s₁ s₂ ⟨_, ⟨li₁, c₁⟩, ⟨li₂, c₂⟩⟩ => ⟨?_, fun _ => trivial, fun hc => ?_⟩
    · exact c₁.trans (c₂.trans (by rw [T.pb.lanesN_eq])).symm
    · have e₀ : some (!decide (l + 1 = lanesN s₀₁)) = some true := c₁.symm.trans hc
      have e : ¬(l + 1 = lanesN s₀₁) := by simpa using e₀
      exact ⟨lanesN s₀₁ - (l + 1), by omega_using [hl], l + 1, rfl, by omega_using [hl, e], li₁, li₂⟩
  · exact RelCT.of_false fun s₁ s₂ h => hn ⟨h.2.1, h.1⟩

/-- The memory's initialization leaks the same trace in two runs. -/
theorem memoryInit_rel {h0₁ h0₂ : List Byte} :
    RelCT isa (fun s₁ s₂ =>
      (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁ ∧ bytesAt s₁.mem (E s₀₁ + BitVec.ofNat 64 0) 64 = h0₁) ∧
      (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂ ∧ bytesAt s₂.mem (E s₀₂ + BitVec.ofNat 64 0) 64 = h0₂))
      Impl.Argon2.RISCV64.Derive.memoryInit fun _ _ => True := by
  unfold Impl.Argon2.RISCV64.Derive.memoryInit
  refine RelCT.seqW (T.clear_rel (fun s h => h.1) (fun s h => h.1))
    (fun s h => clearW_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => clearW_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine RelCT.seqW (T.leaf [] [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => laneStart_ok T.hp₁ h) (fun s h => laneStart_ok T.hp₂ h) ?_
  exact T.initLanes_rel

end Two

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-! ### `Argon2.RISCV64.Derive.ReduceCT`, which only this module used -/

section

/-!
# Argon2 on RISC-V: the final block and the tag, in two runs

`reduce_rel`: the reduction's loop runs the same number of times in both runs
and each lane's XOR addresses the same blocks; `finalOutput_rel`: H′ is
called with the same arguments.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd wp_addi wp_li)
open VG.Spec.Argon2 (Block zeroBlock)
open VG.Impl.Argon2.RISCV64.Derive (laneOff laneLenOff lda)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The instructions before `finalOutput`'s call of H′. -/
theorem foBlk_ok {s : State} (h : Inv s₀ s) :
    WP isa (.block [lda .a0 Impl.Argon2.RISCV64.Derive.memoryArg, .li .a1 1024,
      lda .a2 Impl.Argon2.RISCV64.Derive.outArg, lda .a3 Impl.Argon2.RISCV64.Derive.outLenArg,
      Impl.Argon2.RISCV64.HPrime.mov .a4 .s4]) s fun t => Two.HArgs s₀ t ∧
      t.gpr .a0 = memP s₀ ∧ t.gpr .a1 = BitVec.ofNat 64 1024 ∧ t.gpr .a2 = outP s₀ ∧
      t.gpr .a3 = arg s₀ 17 := by
  have b1 := blocks_pos hp
  have tg := hp.tag_ge
  have tl := hp.tag_lt
  have b1k : 1024 ≤ blocksN s₀ * 1024 := Nat.le_mul_of_pos_left _ b1
  unfold Impl.Argon2.RISCV64.HPrime.mov
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
  have si : s₅.gpr .a0 = memP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ax : s₅.gpr .a1 = BitVec.ofNat 64 1024 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  have di : s₅.gpr .a2 = outP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  have cx : s₅.gpr .a3 = arg s₀ 17 := by
    rw [u₅.other _ (by decide), u₄.gpr]
  have r7 : s₅.gpr .a4 = scrP s₀ := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h.s4]; simp
  refine ⟨⟨i₅, r7, ⟨memR s₀, by simp, 0, by rw [si]; simp, by rw [ax]; show 0 + 1024 ≤ blocksN s₀ * 1024; omega_using [b1]⟩,
    ⟨outR s₀, by simp, 0, by rw [di]; simp, by rw [cx]; show 0 + outL s₀ ≤ outL s₀; omega_using []⟩,
    by rw [ax]; decide, by rw [cx]; exact ⟨by show 1 ≤ outL s₀; omega_using [tg], tl⟩⟩, si, ax, di, cx⟩

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `reduce` leaks the same trace in two runs. -/
theorem reduce_rel {M₁ M₂ : Array Block} :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁ ∧ Represents s₁.mem (memP s₀₁) (prm s₀₁).blocks M₁) ∧
      (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂ ∧ Represents s₂.mem (memP s₀₂) (prm s₀₂).blocks M₂))
      Impl.Argon2.RISCV64.Derive.reduce fun _ _ => True := by
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  unfold Impl.Argon2.RISCV64.Derive.reduce
  refine RelCT.seqW (T.leaf [] [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => reduceStart_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => reduceStart_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  generalize hN : lanesN s₀₁ = N at hl1
  have hN₂ : lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      RI s₀₁ M₁ l s₁ ∧ RI s₀₂ M₂ l s₂) ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega_using [], hl1, h.1, h.2⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, g₁, g₂⟩ e₁ e₂
  have body : RelCT isa (fun s₁ s₂ => RI s₀₁ M₁ l s₁ ∧ RI s₀₂ M₂ l s₂)
      (.block (Impl.Argon2.RISCV64.Derive.reduceLane ++ Impl.Argon2.RISCV64.Derive.advanceBy laneOff
        (Impl.Argon2.RISCV64.Derive.ldw .a1 Impl.Argon2.RISCV64.Derive.lanesArg))) fun _ _ => True :=
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
  exact ⟨N - (l + 1), by omega_using [hn, hl], l + 1, rfl, by omega_using [hl, e], k₁, k₂⟩

/-- `finalOutput` leaks the same trace in two runs. -/
theorem finalOutput_rel :
    RelCT isa (fun s₁ s₂ => Inv s₀₁ s₁ ∧ Inv s₀₂ s₂) Impl.Argon2.RISCV64.Derive.finalOutput
      fun _ _ => True := by
  unfold Impl.Argon2.RISCV64.Derive.finalOutput
  refine RelCT.seqW (T.leaf [] [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => foBlk_ok T.hp₁ h) (fun s h => foBlk_ok T.hp₂ h) ?_
  refine T.hcall_rel fun s₁ s₂ ⟨k₁, k₂⟩ => ⟨k₁.1, k₂.1, ?_, ?_, ?_, ?_⟩
  · rw [k₁.2.1, k₂.2.1, T.pb.memP_eq]
  · rw [k₁.2.2.1, k₂.2.2.1]
  · rw [k₁.2.2.2.1, k₂.2.2.2.1, T.pb.outP_eq]
  · rw [k₁.2.2.2.2, k₂.2.2.2.2, T.pb.arg_eq (by decide)]

end Two

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-! ### `Argon2.RISCV64.Derive.FillCT3`, which only this module used -/

section

/-! ### `Argon2.RISCV64.Derive.FillCT2`, which only this module used -/

section

/-!
# Argon2 on RISC-V: a block of the filling loops, in two runs

`fillBlock_rel`: one block's trace depends only on its position and on the
reference block's index, which the leakage permits (`Spec.Argon2.references`):
the reference is computed from the random word in the frame, with no address
or branch depending on it (`reference_rel`), G is called on the previous and
the reference blocks (`fillCompress_rel`), and its output is written to the
current block (`fillWrite_rel`), whose address the runs agree on.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd wp_addi)
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.RISCV64.Derive (tmpOff curOff ld)

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `reference` leaks the same trace in two runs at the same position: it
reads the random word, but neither branches on it nor addresses memory with it. -/
theorem reference_rel {pass slice lane index ctr : Nat} :
    RelCT isa (fun s₁ s₂ => W s₀₁ pass slice lane index ctr s₁ ∧ W s₀₂ pass slice lane index ctr s₂)
      Impl.Argon2.RISCV64.Derive.reference fun _ _ => True :=
  T.leafF [] [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp, by simp⟩) ⟨_, by taint_decide⟩

end Two

/-! ## G and the new block -/

/-- The instructions before `fillCompress`'s call of G. -/
theorem fcBlk_ok {s₀ s : State} (h : Inv s₀ s) {P R : Nat} (ha : s.gpr .a0 = memP s₀ + BitVec.ofNat 64 (P * 1024))
    (htmp : lw s₀ s tmpOff = memP s₀ + BitVec.ofNat 64 (R * 1024)) :
    WP isa (.block ([ld .a1 tmpOff, Impl.Argon2.RISCV64.HPrime.mov .a2 .s4] ++
      Impl.Argon2.RISCV64.Derive.gScratch)) s fun t =>
      Inv s₀ t ∧ t.gpr .a3 = gwP s₀ ∧ t.gpr .a2 = scrP s₀ + BitVec.ofNat 64 0 ∧
      t.gpr .a0 = memP s₀ + BitVec.ofNat 64 (P * 1024) ∧ t.gpr .a1 = memP s₀ + BitVec.ofNat 64 (R * 1024) := by
  unfold Impl.Argon2.RISCV64.HPrime.mov Impl.Argon2.RISCV64.Derive.gScratch
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc h (d := tmpOff) (by decide) fun s₂ u₂ => wp_addi (by decide) fun s₃ u₃ =>
    wp_addi (imm := 1024) (by decide) fun s₄ u₄ => wp_addi (imm := 1024) (by decide) fun s₅ u₅ =>
    WP.block_nil ⟨(((h.upd u₂).upd u₃).upd u₄).upd u₅, ?_, ?_, ?_, ?_⟩
  · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), h.s0, BitVec.add_assoc,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), h.s4]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), ha]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, htmp]

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `fillCompress` leaks the same trace in two runs at the same position and
with the same reference block. -/
theorem fillCompress_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hl : lane < lanesN s₀₁)
    (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen) {R : Nat} (hR : R < blocksN s₀₁) :
    RelCT isa (fun s₁ s₂ => (FS s₀₁ pass slice lane index ctr st₁ s₁ ∧
        lw s₀₁ s₁ tmpOff = memP s₀₁ + BitVec.ofNat 64 (R * 1024)) ∧
      (FS s₀₂ pass slice lane index ctr st₂ s₂ ∧ lw s₀₂ s₂ tmpOff = memP s₀₂ + BitVec.ofNat 64 (R * 1024)))
      Impl.Argon2.RISCV64.Derive.fillCompress fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have hR₂ : R < blocksN s₀₂ := T.pb.blocksN_eq ▸ hR
  have L8 := laneLen_ge T.hp₁
  obtain ⟨cl, _⟩ := cell_fits T.hp₁ hl (col := (slice * (prm s₀₁).segmentLen + index + (prm s₀₁).laneLen - 1) %
    (prm s₀₁).laneLen) (Nat.mod_lt _ (by omega_using [L8]))
  have L8₂ := laneLen_ge T.hp₂
  obtain ⟨cl₂, _⟩ := cell_fits T.hp₂ hl₂ (col := (slice * (prm s₀₂).segmentLen + index + (prm s₀₂).laneLen - 1) %
    (prm s₀₂).laneLen) (Nat.mod_lt _ (by omega_using [L8₂]))
  unfold Impl.Argon2.RISCV64.Derive.fillCompress
  refine RelCT.seqW (T.leafF [] [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.2.1.w⟩, by simp, by simp⟩)
      ⟨_, by taint_decide⟩)
    (G₁ := fun t => W s₀₁ pass slice lane index ctr t ∧ t.gpr .a0 = memP s₀₁ + BitVec.ofNat 64
      ((lane * (prm s₀₁).laneLen + (slice * (prm s₀₁).segmentLen + index + (prm s₀₁).laneLen - 1) %
        (prm s₀₁).laneLen) * 1024) ∧ lw s₀₁ t tmpOff = memP s₀₁ + BitVec.ofNat 64 (R * 1024))
    (G₂ := fun t => W s₀₂ pass slice lane index ctr t ∧ t.gpr .a0 = memP s₀₂ + BitVec.ofNat 64
      ((lane * (prm s₀₂).laneLen + (slice * (prm s₀₂).segmentLen + index + (prm s₀₂).laneLen - 1) %
        (prm s₀₂).laneLen) * 1024) ∧ lw s₀₂ t tmpOff = memP s₀₂ + BitVec.ofNat 64 (R * 1024))
    (fun s h => (prevPointer_ok T.hp₁ h.1.inv h.1.pr h.1.pos hl hs hi).mono fun t ⟨a, k⟩ =>
      ⟨h.1.w.of_only k, a, by rw [lw_mem k.mem]; exact h.2⟩)
    (fun s h => (prevPointer_ok T.hp₂ h.1.inv h.1.pr h.1.pos hl₂ hs hi₂).mono fun t ⟨a, k⟩ =>
      ⟨h.1.w.of_only k, a, by rw [lw_mem k.mem]; exact h.2⟩) ?_
  refine RelCT.seqW (T.leafF [] [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1, h.2.1⟩, by simp, by simp⟩)
      ⟨_, by taint_decide⟩)
    (fun s h => fcBlk_ok h.1.inv h.2.1 h.2.2) (fun s h => fcBlk_ok h.1.inv h.2.1 h.2.2) ?_
  refine T.ccall_rel (o := 0) (by decide) (by decide) fun s₁ s₂ ⟨⟨i₁, d₁, c₁, a₁, e₁⟩, ⟨i₂, d₂, c₂, a₂, e₂⟩⟩ =>
    ⟨⟨i₁, d₁, c₁, by rw [a₁]; exact .inl ⟨_, cl, rfl⟩, by rw [e₁]; exact .inl ⟨R, hR, rfl⟩⟩,
     ⟨i₂, d₂, c₂, by rw [a₂]; exact .inl ⟨_, cl₂, rfl⟩, by rw [e₂]; exact .inl ⟨R, hR₂, rfl⟩⟩,
     by rw [a₁, a₂, pe, T.pb.memP_eq], by rw [e₁, e₂, T.pb.memP_eq]⟩

/-- `fillWrite` leaks the same trace in two runs at the same position. -/
theorem fillWrite_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} :
    RelCT isa (fun s₁ s₂ => (FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ FS s₀₂ pass slice lane index ctr st₂ s₂) ∧
      lw s₀₁ s₁ curOff = lw s₀₂ s₂ curOff) Impl.Argon2.RISCV64.Derive.fillWrite fun _ _ => True :=
  T.leafF [] [curOff] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.1.2.w⟩, by simp, by
    simp only [List.mem_singleton, forall_eq]; exact h.2⟩) ⟨_, by taint_decide⟩

/-- `fillBlock` leaks the same trace in two runs at the same position whose
reference blocks agree. -/
theorem fillBlock_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index)
    (href : Spec.Argon2.reference (prm s₀₁) pass lane slice index
        (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory) =
      Spec.Argon2.reference (prm s₀₂) pass lane slice index
        (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice index st₂.memory)) :
    RelCT isa (fun s₁ s₂ => FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.RISCV64.Derive.fillBlock fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have hb₁ : blocksN s₀₁ = (prm s₀₁).blocks := T.hp₁.blocks
  have refLt := Proof.Argon2.reference_cell_lt (prm s₀₁) T.hp₁.lanes_pos T.hp₁.memory_ge pass lane slice index
    (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory) hl
  simp only at refLt
  generalize hR : (Spec.Argon2.reference (prm s₀₁) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory)).1 * (prm s₀₁).laneLen +
    (Spec.Argon2.reference (prm s₀₁) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory)).2 = R at refLt
  have hR₂ : (Spec.Argon2.reference (prm s₀₂) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice index st₂.memory)).1 * (prm s₀₂).laneLen +
    (Spec.Argon2.reference (prm s₀₂) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice index st₂.memory)).2 = R := by
    rw [← href, ← pe]; exact hR
  generalize hC : lane * (prm s₀₁).laneLen + (slice * (prm s₀₁).segmentLen + index) = C
  have hC₂ : lane * (prm s₀₂).laneLen + (slice * (prm s₀₂).segmentLen + index) = C := by rw [← pe]; exact hC
  have ec : ctrNext (prm s₀₂) pass slice index ctr = ctrNext (prm s₀₁) pass slice index ctr := by rw [pe]
  unfold Impl.Argon2.RISCV64.Derive.fillBlock
  refine RelCT.seqW (T.randomSource_rel hpass hs hi)
    (fun s h => randomSource_ok T.hp₁ h hpass hl hs hi) (fun s h => randomSource_ok T.hp₂ h hpass hl₂ hs hi₂) ?_
  refine RelCT.seqW (G₁ := fun t =>
      FS s₀₁ pass slice lane index (ctrNext (prm s₀₁) pass slice index ctr) st₁ t ∧
      lw s₀₁ t tmpOff = memP s₀₁ + BitVec.ofNat 64 (R * 1024) ∧
      lw s₀₁ t curOff = memP s₀₁ + BitVec.ofNat 64 (C * 1024))
    (G₂ := fun t => FS s₀₂ pass slice lane index (ctrNext (prm s₀₁) pass slice index ctr) st₂ t ∧
      lw s₀₂ t tmpOff = memP s₀₂ + BitVec.ofNat 64 (R * 1024) ∧
      lw s₀₂ t curOff = memP s₀₂ + BitVec.ofNat 64 (C * 1024))
    ((T.reference_rel (ctr := ctrNext (prm s₀₁) pass slice index ctr)).mono
      (fun s₁ s₂ h => ⟨h.1.1.w, by rw [← ec]; exact h.2.1.w⟩) fun _ _ h => h)
    (fun s g => (reference_ok T.hp₁ ⟨g.1, g.2.1, g.2.2⟩ hpass hl hs hi active).mono fun t ⟨r, tmp, cur⟩ =>
      ⟨r.fs, by rw [tmp, hR], by rw [cur, hC]⟩)
    (fun s g => (reference_ok T.hp₂ ⟨g.1, g.2.1, g.2.2⟩ hpass hl₂ hs hi₂ active).mono fun t ⟨r, tmp, cur⟩ =>
      ⟨by rw [← ec]; exact r.fs, by rw [tmp, hR₂], by rw [cur, hC₂]⟩) ?_
  refine RelCT.seqW (G₁ := fun t =>
      FS s₀₁ pass slice lane index (ctrNext (prm s₀₁) pass slice index ctr) st₁ t ∧
      lw s₀₁ t curOff = memP s₀₁ + BitVec.ofNat 64 (C * 1024))
    (G₂ := fun t => FS s₀₂ pass slice lane index (ctrNext (prm s₀₁) pass slice index ctr) st₂ t ∧
      lw s₀₂ t curOff = memP s₀₂ + BitVec.ofNat 64 (C * 1024))
    ((T.fillCompress_rel hl hs hi (by rw [hb₁]; exact refLt)).mono
      (fun _ _ h => ⟨⟨h.1.1, h.1.2.1⟩, ⟨h.2.1, h.2.2.1⟩⟩) fun _ _ h => h)
    (fun s g => (fillCompress_ok T.hp₁ g.1 hl hs hi (by rw [hb₁]; exact refLt) g.2.1).mono
      fun t ⟨f, l, _⟩ => ⟨f, by rw [l _ (by decide), g.2.2]⟩)
    (fun s g => (fillCompress_ok T.hp₂ g.1 hl₂ hs hi₂ (by rw [← T.pb.blocksN_eq, hb₁]; exact refLt) g.2.1).mono
      fun t ⟨f, l, _⟩ => ⟨f, by rw [l _ (by decide), g.2.2]⟩) ?_
  exact T.fillWrite_rel.mono (fun _ _ h => ⟨⟨h.1.1, h.2.1⟩, by rw [h.1.2, h.2.2, T.pb.memP_eq]⟩) fun _ _ h => h

end Two

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-!
# Argon2 on RISC-V: the filling loops, in two runs

The loops run in lockstep in two runs with the same public data: their
positions and counters agree, and so do the indices of the data-dependent
references still to be made (the rest of `Spec.Argon2.references`), from
which each block's reference agrees (`ref_same`). `passes_rel`: the filling
loops leak the same trace in two runs whose references agree.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.RISCV64.Derive (sliceOff segLenOff indexOff laneOff laneLenOff passOff counterOff
  strideOff ld st)

/-- A block's reference, in two runs whose references from it on agree. -/
theorem ref_same (p : Spec.Argon2.Params) (pass lane slice i count : Nat) (X₁ X₂ : FillState)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i)
    (h : (Proof.Argon2.segment p pass lane slice i (count + 1) X₁).indices =
      (Proof.Argon2.segment p pass lane slice i (count + 1) X₂).indices) :
    Spec.Argon2.reference p pass lane slice i (Proof.Argon2.FillStep.random p pass lane slice i X₁.memory) =
      Spec.Argon2.reference p pass lane slice i (Proof.Argon2.FillStep.random p pass lane slice i X₂.memory) := by
  cases hind : Spec.Argon2.independent p pass slice
  · exact Proof.Argon2.segment_first_reference p pass lane slice i count X₁ X₂ active h hind
  · unfold Proof.Argon2.FillStep.random
    rw [hind]
    rfl

/-- The doublewords of the frame a lane's state fixes. -/
abbrev wsL : List Nat := [passOff, laneOff, sliceOff, laneLenOff, strideOff, segLenOff]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `setLocal d v`, alone. -/
theorem setLocal_w {s : State} {st : FillState} (h : FB s₀ st s) {d : Nat} (hd : VarOff d)
    (hd₂ : d + 8 ≤ 224) {v : Nat} (hv : v < 2048) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.setLocal d v)) s fun t => FB s₀ st t ∧
      lw s₀ t d = BitVec.ofNat 64 v ∧
      ∀ e, e + 8 ≤ 320 → (d + 8 ≤ e ∨ e + 8 ≤ d) → lw s₀ t e = lw s₀ s e := by
  rw [← List.append_nil (Impl.Argon2.RISCV64.Derive.setLocal _ _)]
  exact setLocal_ok hp h hd hd₂ hv fun t f v o _ => WP.block_nil ⟨f, v, o⟩

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

theorem wordsL {st₁ st₂ : FillState} {pass slice lane : Nat} {s₁ s₂ : State}
    (h₁ : LS s₀₁ st₁ pass slice lane s₁) (h₂ : LS s₀₂ st₂ pass slice lane s₂) :
    ∀ d ∈ wsL, lw s₀₁ s₁ d = lw s₀₂ s₂ d := by
  obtain ⟨a, b, c⟩ := T.prm_lw h₁.fb.pr h₂.fb.pr
  intro d hd
  simp only [wsL, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁.pass.trans h₂.pass.symm
  · exact h₁.lane.trans h₂.lane.symm
  · exact h₁.slice.trans h₂.slice.symm
  · exact a
  · exact b
  · exact c

/-- A piece the taint analysis proves from the arguments alone. -/
theorem leafI {P : State → State → Prop} {c : Prog isa}
    (hag : ∀ s₁ s₂, P s₁ s₂ → Inv s₀₁ s₁ ∧ Inv s₀₂ s₂)
    (hc : ∃ hc, (VG.Taint.check frameTaint (τF [] []) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  T.leaf [] [] (fun s₁ s₂ h => ⟨(hag s₁ s₂ h).1, (hag s₁ s₂ h).2, by simp, by simp⟩) hc

/-- `segmentStart` leaks the same trace in two runs at the same lane. -/
theorem segmentStart_rel {pass slice lane : Nat} {st₁ st₂ : FillState} :
    RelCT isa (fun s₁ s₂ => LS s₀₁ st₁ pass slice lane s₁ ∧ LS s₀₂ st₂ pass slice lane s₂)
      Impl.Argon2.RISCV64.Derive.segmentStart fun _ _ => True :=
  T.leaf wsL [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, T.wordsL h.1 h.2, by simp⟩) ⟨_, by taint_decide⟩

/-- A block of a segment and the index advanced, in two runs at the same
position whose reference blocks agree. -/
theorem segBody_rel {pass slice lane i c : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : i < (prm s₀₁).segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i)
    (href : Spec.Argon2.reference (prm s₀₁) pass lane slice i
        (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice i X₁.memory) =
      Spec.Argon2.reference (prm s₀₂) pass lane slice i
        (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice i X₂.memory)) :
    RelCT isa (fun s₁ s₂ => FS s₀₁ pass slice lane i c X₁ s₁ ∧ FS s₀₂ pass slice lane i c X₂ s₂)
      (.seq Impl.Argon2.RISCV64.Derive.fillBlock
        (.block (Impl.Argon2.RISCV64.Derive.advanceBy indexOff (ld .a1 segLenOff))))
      fun v₁ v₂ => (FS s₀₁ pass slice lane (i + 1) (ctrNext (prm s₀₁) pass slice i c)
          (Spec.Argon2.fillBlock (prm s₀₁) pass slice lane i X₁) v₁ ∧
          VG.RISCV64.eval (.nonzero .a1) v₁ = some (!decide (i + 1 = (prm s₀₁).segmentLen))) ∧
        (FS s₀₂ pass slice lane (i + 1) (ctrNext (prm s₀₂) pass slice i c)
          (Spec.Argon2.fillBlock (prm s₀₂) pass slice lane i X₂) v₂ ∧
          VG.RISCV64.eval (.nonzero .a1) v₂ = some (!decide (i + 1 = (prm s₀₂).segmentLen))) := by
  have pe := T.pb.prm_eq
  have hi₂ : i < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  refine rel_wp (RelCT.seqW (T.fillBlock_rel hpass hl hs hi active href)
    (fun s h => fillBlock_ok T.hp₁ h hpass hl hs hi active)
    (fun s h => fillBlock_ok T.hp₂ h hpass hl₂ hs hi₂ active)
    (T.leafI (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv⟩) ⟨_, by taint_decide⟩))
    (fun s h => segStep_ok T.hp₁ h hpass hl hs hi active) (fun s h => segStep_ok T.hp₂ h hpass hl₂ hs hi₂ active)

/-- `segment` leaks the same trace in two runs at the same lane whose
references in it agree. -/
theorem segment_rel {pass slice lane : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hl : lane < lanesN s₀₁)
    (hind : (Proof.Argon2.segment (prm s₀₁) pass lane slice 0 (prm s₀₁).segmentLen st₁).indices =
      (Proof.Argon2.segment (prm s₀₁) pass lane slice 0 (prm s₀₁).segmentLen st₂).indices) :
    RelCT isa (fun s₁ s₂ => LS s₀₁ st₁ pass slice lane s₁ ∧ LS s₀₂ st₂ pass slice lane s₂)
      Impl.Argon2.RISCV64.Derive.segment fun _ _ => True := by
  have pe := T.pb.prm_eq
  have s2 := T.hp₁.segLen_two
  have hS : Proof.Argon2.segmentStart pass slice ≤ 2 := by unfold Proof.Argon2.segmentStart; split <;> omega_arith
  have hS2 : pass = 0 → slice = 0 → Proof.Argon2.segmentStart pass slice = 2 := fun a b => by
    unfold Proof.Argon2.segmentStart; rw [ite_eq_left ⟨a, b⟩]
  rw [Proof.Argon2.segment_start _ _ _ _ _ s2, Proof.Argon2.segment_start _ _ _ _ _ s2] at hind
  generalize hSd : Proof.Argon2.segmentStart pass slice = S at hS hS2 hind
  generalize hL : (prm s₀₁).segmentLen = L at hind s2
  have hL₂ : (prm s₀₂).segmentLen = L := by rw [← pe, hL]
  unfold Impl.Argon2.RISCV64.Derive.segment
  refine RelCT.seq (rel_wp T.segmentStart_rel
    (fun s h => segmentStart_ok T.hp₁ h hpass hs) (fun s h => segmentStart_ok T.hp₂ h hpass hs)) ?_
  rw [hSd]
  refine RelCT.seqW (T.leafF [] [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp, by simp⟩)
      ⟨_, by taint_decide⟩)
    (fun s h => segCmp_ok T.hp₁ h hS) (fun s h => segCmp_ok T.hp₂ h hS) ?_
  refine RelCT.ite (fun s₁ s₂ h => (h.1.2.trans (by rw [hL, hL₂])).trans h.2.2.symm)
    (RelCT.nil fun _ _ _ => trivial) ?_
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ i, n = L - i ∧ S ≤ i ∧ i < L ∧ ∃ c,
      FS s₀₁ pass slice lane i c (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₁) s₁ ∧
      FS s₀₂ pass slice lane i c (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₂) s₂ ∧
      (Proof.Argon2.segment (prm s₀₁) pass lane slice i (L - i)
          (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₁)).indices =
        (Proof.Argon2.segment (prm s₀₁) pass lane slice i (L - i)
          (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₂)).indices) ?step (L - S)).mono
    (fun s₁ s₂ ⟨⟨⟨h₁, c₁⟩, ⟨h₂, _⟩⟩, e⟩ => ?init) fun _ _ h => h
  case init =>
    have hb : S < L := by
      have e' : some (decide (S = L)) = some false := by
        rw [← hL]; exact c₁.symm.trans e
      have := of_decide_eq_false (Option.some.inj e')
      omega_arith
    exact ⟨S, rfl, Nat.le_refl _, hb, 0, by rw [Nat.sub_self]; exact h₁, by rw [Nat.sub_self]; exact h₂,
      by rw [Nat.sub_self]; exact hind⟩
  case step =>
    intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨i, hn, hSi, hi, c, h₁, h₂, hidx⟩ e₁ e₂
    have active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i := by
      by_cases a : pass = 0
      · by_cases b : slice = 0
        · have := hS2 a b; omega_arith
        · exact .inr (.inl b)
      · exact .inl a
    rw [show L - i = (L - (i + 1)) + 1 by omega_arith] at hidx
    have href := ref_same (prm s₀₁) pass lane slice i (L - (i + 1)) _ _ active hidx
    rw [Proof.Argon2.segment_succ, Proof.Argon2.segment_succ] at hidx
    obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.segBody_rel (c := c) hpass hl hs (by rw [hL]; exact hi) active
      (by rw [← pe]; exact href) s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
    rw [← pe] at g₂ c₂
    have eq₁ : ∀ X, Proof.Argon2.segment (prm s₀₁) pass lane slice S (i + 1 - S) X =
        Spec.Argon2.fillBlock (prm s₀₁) pass slice lane i
          (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) X) :=
      fun X => by rw [show i + 1 - S = (i - S) + 1 by omega_arith, segment_snoc, show S + (i - S) = i by omega_arith]
    rw [← eq₁] at g₁ g₂ hidx
    rw [← eq₁] at hidx
    rw [hL] at c₁ c₂
    refine ⟨ht, c₁.trans c₂.symm, fun _ => trivial, fun hc => ?_⟩
    have e₀ : some (!decide (i + 1 = L)) = some true := c₁.symm.trans hc
    have e : i + 1 ≠ L := by simpa using e₀
    exact ⟨L - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, by omega_arith, _, g₁, g₂, hidx⟩

/-- A lane's segment and the lane advanced, in two runs. -/
theorem laneBody_rel {pass slice l : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hl : l < lanesN s₀₁)
    (hind : (Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen X₁).indices =
      (Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen X₂).indices) :
    RelCT isa (fun s₁ s₂ => LS s₀₁ X₁ pass slice l s₁ ∧ LS s₀₂ X₂ pass slice l s₂)
      (.seq Impl.Argon2.RISCV64.Derive.segment
        (.block (Impl.Argon2.RISCV64.Derive.advanceBy laneOff
          (Impl.Argon2.RISCV64.Derive.ldw .a1 Impl.Argon2.RISCV64.Derive.lanesArg))))
      fun v₁ v₂ => (LS s₀₁ (Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen X₁) pass slice
          (l + 1) v₁ ∧ VG.RISCV64.eval (.nonzero .a1) v₁ = some (!decide (l + 1 = lanesN s₀₁))) ∧
        (LS s₀₂ (Proof.Argon2.segment (prm s₀₂) pass l slice 0 (prm s₀₂).segmentLen X₂) pass slice (l + 1) v₂ ∧
          VG.RISCV64.eval (.nonzero .a1) v₂ = some (!decide (l + 1 = lanesN s₀₂))) := by
  have hl₂ : l < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  exact rel_wp (RelCT.seqW (T.segment_rel hpass hs hl hind)
    (fun s h => segment_ok T.hp₁ h hpass hs hl) (fun s h => segment_ok T.hp₂ h hpass hs hl₂)
    (T.leafI (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv⟩) ⟨_, by taint_decide⟩))
    (fun s h => laneStep_ok T.hp₁ h hpass hs hl) (fun s h => laneStep_ok T.hp₂ h hpass hs hl₂)

/-- `lanesLoop` leaks the same trace in two runs at the same slice whose
references in it agree. -/
theorem lanes_rel {pass slice : Nat} {Y₁ Y₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hind : (Proof.Argon2.lanes (prm s₀₁) pass slice 0 (lanesN s₀₁) Y₁).indices =
      (Proof.Argon2.lanes (prm s₀₁) pass slice 0 (lanesN s₀₁) Y₂).indices) :
    RelCT isa (fun s₁ s₂ => SS s₀₁ Y₁ pass slice s₁ ∧ SS s₀₂ Y₂ pass slice s₂)
      Impl.Argon2.RISCV64.Derive.lanesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.RISCV64.Derive.lanesLoop
  refine RelCT.seqW (T.leafI (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv⟩) ⟨_, by taint_decide⟩)
    (fun s h => (setLocal_w T.hp₁ h.fb (d := laneOff) (by decide) (by decide) (by decide)).mono
      fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, by rw [o _ (by decide) (by decide)]; exact h.slice,
        v⟩ : LS s₀₁ Y₁ pass slice 0 t))
    (fun s h => (setLocal_w T.hp₂ h.fb (d := laneOff) (by decide) (by decide) (by decide)).mono
      fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, by rw [o _ (by decide) (by decide)]; exact h.slice,
        v⟩ : LS s₀₂ Y₂ pass slice 0 t)) ?_
  generalize hN : lanesN s₀₁ = N at hind hl1
  have hN₂ : lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      LS s₀₁ (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₁) pass slice l s₁ ∧
      LS s₀₂ (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₂) pass slice l s₂ ∧
      (Proof.Argon2.lanes (prm s₀₁) pass slice l (N - l) (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₁)).indices =
        (Proof.Argon2.lanes (prm s₀₁) pass slice l (N - l) (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₂)).indices)
    ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega_arith, hl1, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, h₁, h₂, hidx⟩ e₁ e₂
  rw [show N - l = (N - (l + 1)) + 1 by omega_arith] at hidx
  have hseg := Proof.Argon2.lanes_first_segment (prm s₀₁) pass slice l (N - (l + 1)) _ _ s2 hidx
  rw [Proof.Argon2.lanes_succ, Proof.Argon2.lanes_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.laneBody_rel hpass hs (by rw [hN]; exact hl) hseg
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe] at g₂
  have eq : ∀ X, Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen
      (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l X) = Proof.Argon2.lanes (prm s₀₁) pass slice 0 (l + 1) X :=
    fun X => by unfold Proof.Argon2.lanes; rw [foldl_range'_snoc, Nat.zero_add]
  rw [eq] at g₁ g₂ hidx
  rw [eq] at hidx
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, c₁.trans c₂.symm, fun _ => trivial, fun hc => ?_⟩
  have e₀ : some (!decide (l + 1 = N)) = some true := c₁.symm.trans hc
  have e : l + 1 ≠ N := by simpa using e₀
  exact ⟨N - (l + 1), by omega_arith, l + 1, rfl, by omega_arith, g₁, g₂, hidx⟩

/-- A slice's lanes and the slice advanced, in two runs. -/
theorem sliceBody_rel {pass j : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32) (hj : j < 4)
    (hind : (Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) X₁).indices =
      (Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) X₂).indices) :
    RelCT isa (fun s₁ s₂ => SS s₀₁ X₁ pass j s₁ ∧ SS s₀₂ X₂ pass j s₂)
      (.seq Impl.Argon2.RISCV64.Derive.lanesLoop (.block (Impl.Argon2.RISCV64.Derive.advanceImm sliceOff 4)))
      fun v₁ v₂ => (SS s₀₁ (Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) X₁) pass (j + 1) v₁ ∧
          VG.RISCV64.eval (.nonzero .a1) v₁ = some (!decide (j + 1 = 4))) ∧
        (SS s₀₂ (Proof.Argon2.lanes (prm s₀₂) pass j 0 (lanesN s₀₂) X₂) pass (j + 1) v₂ ∧
          VG.RISCV64.eval (.nonzero .a1) v₂ = some (!decide (j + 1 = 4))) :=
  rel_wp (RelCT.seqW (T.lanes_rel hpass hj hind)
    (fun s h => lanes_ok T.hp₁ h hpass hj) (fun s h => lanes_ok T.hp₂ h hpass hj)
    (T.leafI (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv⟩) ⟨_, by taint_decide⟩))
    (fun s h => sliceStep_ok T.hp₁ h hpass hj) (fun s h => sliceStep_ok T.hp₂ h hpass hj)

/-- `slicesLoop` leaks the same trace in two runs at the same pass whose
references in it agree. -/
theorem slices_rel {pass : Nat} {Z₁ Z₂ : FillState} (hpass : pass < 2 ^ 32)
    (hind : (Proof.Argon2.slices (prm s₀₁) pass 0 4 Z₁).indices =
      (Proof.Argon2.slices (prm s₀₁) pass 0 4 Z₂).indices) :
    RelCT isa (fun s₁ s₂ => PS s₀₁ Z₁ pass s₁ ∧ PS s₀₂ Z₂ pass s₂)
      Impl.Argon2.RISCV64.Derive.slicesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.RISCV64.Derive.slicesLoop
  refine RelCT.seqW (T.leafI (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv⟩) ⟨_, by taint_decide⟩)
    (fun s h => (setLocal_w T.hp₁ h.fb (d := sliceOff) (by decide) (by decide) (by decide)).mono
      fun t ⟨f, v, o⟩ => (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, v⟩ : SS s₀₁ Z₁ pass 0 t))
    (fun s h => (setLocal_w T.hp₂ h.fb (d := sliceOff) (by decide) (by decide) (by decide)).mono
      fun t ⟨f, v, o⟩ => (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, v⟩ : SS s₀₂ Z₂ pass 0 t)) ?_
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ j, n = 4 - j ∧ j < 4 ∧
      SS s₀₁ (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₁) pass j s₁ ∧
      SS s₀₂ (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₂) pass j s₂ ∧
      (Proof.Argon2.slices (prm s₀₁) pass j (4 - j) (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₁)).indices =
        (Proof.Argon2.slices (prm s₀₁) pass j (4 - j) (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₂)).indices)
    ?step 4).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, rfl, by decide, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, hn, hj, h₁, h₂, hidx⟩ e₁ e₂
  rw [show 4 - j = (3 - j) + 1 by omega_arith] at hidx
  have hl := Proof.Argon2.slices_first_lane_fold (prm s₀₁) pass j (3 - j) _ _ s2 hidx
  rw [Proof.Argon2.slices_succ, Proof.Argon2.slices_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.sliceBody_rel hpass hj hl s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe, ← le] at g₂
  have eq : ∀ X, Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) (Proof.Argon2.slices (prm s₀₁) pass 0 j X) =
      Proof.Argon2.slices (prm s₀₁) pass 0 (j + 1) X :=
    fun X => by unfold Proof.Argon2.slices; rw [foldl_range'_snoc, Nat.zero_add]; rfl
  rw [eq] at g₁ g₂
  rw [show 3 - j = 4 - (j + 1) by omega_arith] at hidx
  refine ⟨ht, c₁.trans c₂.symm, fun _ => trivial, fun hc => ?_⟩
  have e₀ : some (!decide (j + 1 = 4)) = some true := c₁.symm.trans hc
  have e : j + 1 ≠ 4 := by simpa using e₀
  refine ⟨4 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, g₁, g₂, ?_⟩
  rw [← eq, ← eq]
  exact hidx

/-- A pass and the pass advanced, in two runs. -/
theorem passBody_rel {k : Nat} {X₁ X₂ : FillState} (hk : k < itersN s₀₁)
    (hind : (Spec.Argon2.fillPass (prm s₀₁) X₁ k).indices = (Spec.Argon2.fillPass (prm s₀₁) X₂ k).indices) :
    RelCT isa (fun s₁ s₂ => PS s₀₁ X₁ k s₁ ∧ PS s₀₂ X₂ k s₂)
      (.seq Impl.Argon2.RISCV64.Derive.slicesLoop
        (.block (Impl.Argon2.RISCV64.Derive.advanceBy passOff
          (Impl.Argon2.RISCV64.Derive.ldw .a1 Impl.Argon2.RISCV64.Derive.iterationsArg))))
      fun v₁ v₂ => (PS s₀₁ (Spec.Argon2.fillPass (prm s₀₁) X₁ k) (k + 1) v₁ ∧
          VG.RISCV64.eval (.nonzero .a1) v₁ = some (!decide (k + 1 = itersN s₀₁))) ∧
        (PS s₀₂ (Spec.Argon2.fillPass (prm s₀₂) X₂ k) (k + 1) v₂ ∧
          VG.RISCV64.eval (.nonzero .a1) v₂ = some (!decide (k + 1 = itersN s₀₂))) := by
  have hk₂ : k < itersN s₀₂ := T.pb.itersN_eq ▸ hk
  have hpl : itersN s₀₁ < 2 ^ 32 := (arg32 s₀₁ 5).isLt
  rw [← Proof.Argon2.slices_pass, ← Proof.Argon2.slices_pass] at hind
  exact rel_wp (RelCT.seqW (T.slices_rel (by omega_arith) hind)
    (fun s h => slices_ok T.hp₁ h (by omega_arith)) (fun s h => slices_ok T.hp₂ h (by omega_arith))
    (T.leafI (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv⟩) ⟨_, by taint_decide⟩))
    (fun s h => passStep_ok T.hp₁ h hk) (fun s h => passStep_ok T.hp₂ h hk₂)

/-- `passesLoop` leaks the same trace in two runs whose references agree. -/
theorem passes_rel {W₁ W₂ : FillState}
    (hind : (Proof.Argon2.iterations (prm s₀₁) 0 (itersN s₀₁) W₁).indices =
      (Proof.Argon2.iterations (prm s₀₁) 0 (itersN s₀₁) W₂).indices) :
    RelCT isa (fun s₁ s₂ => FB s₀₁ W₁ s₁ ∧ FB s₀₂ W₂ s₂) Impl.Argon2.RISCV64.Derive.passesLoop
      fun _ _ => True := by
  have pe := T.pb.prm_eq
  have ie := T.pb.itersN_eq
  have hp1 := T.hp₁.passes_pos
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.RISCV64.Derive.passesLoop
  refine RelCT.seqW (T.leafI (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv⟩) ⟨_, by taint_decide⟩)
    (fun s h => (setLocal_w T.hp₁ h (d := passOff) (by decide) (by decide) (by decide)).mono
      fun t ⟨f, v, _⟩ => (⟨f, v⟩ : PS s₀₁ W₁ 0 t))
    (fun s h => (setLocal_w T.hp₂ h (d := passOff) (by decide) (by decide) (by decide)).mono
      fun t ⟨f, v, _⟩ => (⟨f, v⟩ : PS s₀₂ W₂ 0 t)) ?_
  generalize hN : itersN s₀₁ = N at hind hp1
  have hN₂ : itersN s₀₂ = N := by rw [← ie, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ k, n = N - k ∧ k < N ∧
      PS s₀₁ (Proof.Argon2.iterations (prm s₀₁) 0 k W₁) k s₁ ∧
      PS s₀₂ (Proof.Argon2.iterations (prm s₀₁) 0 k W₂) k s₂ ∧
      (Proof.Argon2.iterations (prm s₀₁) k (N - k) (Proof.Argon2.iterations (prm s₀₁) 0 k W₁)).indices =
        (Proof.Argon2.iterations (prm s₀₁) k (N - k) (Proof.Argon2.iterations (prm s₀₁) 0 k W₂)).indices)
    ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega_arith, by omega_arith, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨k, hn, hk, h₁, h₂, hidx⟩ e₁ e₂
  rw [show N - k = (N - (k + 1)) + 1 by omega_arith] at hidx
  have hpass := Proof.Argon2.iterations_first_pass (prm s₀₁) k (N - (k + 1)) _ _ s2 hidx
  rw [Proof.Argon2.iterations_succ, Proof.Argon2.iterations_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.passBody_rel (by rw [hN]; exact hk) hpass s₁ s₂ t₁ t₂ s₁' s₂'
    ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe] at g₂
  have eq : ∀ X, Spec.Argon2.fillPass (prm s₀₁) (Proof.Argon2.iterations (prm s₀₁) 0 k X) k =
      Proof.Argon2.iterations (prm s₀₁) 0 (k + 1) X :=
    fun X => by unfold Proof.Argon2.iterations; rw [foldl_range'_snoc, Nat.zero_add]
  rw [eq] at g₁ g₂ hidx
  rw [eq] at hidx
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, c₁.trans c₂.symm, fun _ => trivial, fun hc => ?_⟩
  have e₀ : some (!decide (k + 1 = N)) = some true := c₁.symm.trans hc
  have e : k + 1 ≠ N := by simpa using e₀
  exact ⟨N - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, g₁, g₂, hidx⟩

end Two

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-!
# Argon2 on RISC-V: the derivation is constant time

`body_rel`: the body leaks the same trace in two runs with the same public
data and the same data-dependent references (`deriveRV.pub`), piece by
piece; `derive_ct`: so does the whole function, in its frame.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Spec.Blake2 (bytesAt)

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- The setup and the parameters' block leak the same trace in two runs. -/
theorem parameters_rel :
    RelCT isa (fun s₁ s₂ => s₁ = entry s₀₁ ∧ s₂ = entry s₀₂)
      (.block (Impl.Argon2.RISCV64.Derive.setup ++ Impl.Argon2.RISCV64.Derive.parameters)) fun _ _ => True :=
  RelCT.taint (A := frameTaint) (⟨RegSet.ofList [], 0⟩ : FrameTaint.T) (fun s₁ s₂ ⟨h₁, h₂⟩ => by
      subst h₁ h₂
      exact ⟨⟨by rw [entry_sp, entry_sp, T.pb.E_eq], fun r hr => by simp [RegSet.mem_ofList] at hr⟩,
        fun k _ hb => by simp at hb⟩)
    (by taint_decide)

/-- The body leaks the same trace in two runs with the same data-dependent
references. -/
theorem body_rel
    (href : Spec.Argon2.references (prm s₀₁) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁) =
      Spec.Argon2.references (prm s₀₂) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂)) :
    RelCT isa (fun s₁ s₂ => s₁ = entry s₀₁ ∧ s₂ = entry s₀₂) Impl.Argon2.RISCV64.Derive.body
      fun _ _ => True := by
  have pe := T.pb.prm_eq
  have L8 := laneLen_ge T.hp₁
  have hind := Proof.Argon2.references_injective (prm s₀₁) (by omega_using [L8]) (pwB s₀₁) (saltB s₀₁) (secB s₀₁)
    (adB s₀₁) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂) (by rw [href, pe])
  rw [← Proof.Argon2.iterations_fill, ← Proof.Argon2.iterations_fill] at hind
  have par : ∀ {s₀ : State}, DPre s₀ → ∀ s, s = entry s₀ →
      WP isa (.block (Impl.Argon2.RISCV64.Derive.setup ++ Impl.Argon2.RISCV64.Derive.parameters)) s
        fun t => Inv s₀ t ∧ Prm s₀ t := fun {s₀} hp s h => by
    subst h
    rw [← List.append_nil Impl.Argon2.RISCV64.Derive.parameters, ← List.append_assoc]
    rw [List.append_assoc]
    exact setup_ok hp fun t i _ => parameters_ok hp i fun t' i' p' => WP.block_nil ⟨i', p'⟩
  unfold Impl.Argon2.RISCV64.Derive.body
  refine RelCT.seqW T.parameters_rel (par T.hp₁) (par T.hp₂) ?_
  refine RelCT.seqW T.code_rel (fun s h => code_ok T.hp₁ h.1 h.2) (fun s h => code_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW T.memoryInit_rel (fun s h => memoryInit_ok T.hp₁ h.1 h.2.1 h.2.2)
    (fun s h => memoryInit_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine RelCT.seqW ((T.passes_rel (W₁ := Spec.Argon2.initMemory (prm s₀₁)
      (Spec.Argon2.initialHash (prm s₀₁) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁)))
      (W₂ := Spec.Argon2.initMemory (prm s₀₂)
      (Spec.Argon2.initialHash (prm s₀₂) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂)))
      (by rw [← pe]; exact hind)).mono (fun _ _ h => ⟨⟨h.1.1, h.1.2.1, h.1.2.2⟩, ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩)
      fun _ _ h => h)
    (fun s h => passes_ok T.hp₁ ⟨h.1, h.2.1, h.2.2⟩) (fun s h => passes_ok T.hp₂ ⟨h.1, h.2.1, h.2.2⟩) ?_
  refine RelCT.seqW (T.reduce_rel.mono (fun _ _ h => ⟨⟨h.1.inv, h.1.pr, h.1.mem⟩, ⟨h.2.inv, h.2.pr, h.2.mem⟩⟩)
      fun _ _ h => h)
    (fun s h => reduce_ok T.hp₁ h.inv h.pr h.mem) (fun s h => reduce_ok T.hp₂ h.inv h.pr h.mem) ?_
  refine RelCT.seqW (T.finalOutput_rel.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
    (G₁ := fun t => Inv s₀₁ t) (G₂ := fun t => Inv s₀₂ t)
    (fun s h => (finalOutput_ok T.hp₁ h.1).mono fun _ h => h.1)
    (fun s h => (finalOutput_ok T.hp₂ h.1).mono fun _ h => h.1) ?_
  exact T.leaf [] [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp, by simp⟩) ⟨_, by taint_decide⟩

end Two

/-! ## The frame -/

theorem alloc_eq {n : Nat} {s a : State} (h : isa.push (.alloc n) s = some a) : a = allocd n s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

/-- Two runs of a frame that reserves stack leak the same trace if the runs of
its body do: reserving it accesses no memory. -/
theorem RelCT.allocFrame {n : Nat} {body : Prog isa} {P : State → State → Prop}
    (hb : RelCT isa (fun x y => ∃ a b, P a b ∧ isa.push (.alloc n) a = some x ∧ isa.push (.alloc n) b = some y)
      body fun _ _ => True) :
    RelCT isa P (.frame (.alloc n) body (.free n)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ _ =>
    cases e₂ with
    | frame p₂ b₂ _ =>
      obtain ⟨ht, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, p₁, p₂⟩ b₁ b₂
      refine ⟨?_, trivial⟩
      rw [ht]
      simp [addrs]

/-- The derivation leaks the same trace in two runs with the same public data. -/
theorem derive_rel :
    RelCT isa (fun s₁ s₂ => deriveRV.pre s₁ ∧ deriveRV.pre s₂ ∧ deriveRV.pub s₁ s₂)
      Impl.Argon2.RISCV64.Derive.derive fun _ _ => True := by
  unfold Impl.Argon2.RISCV64.Derive.derive
  refine RelCT.allocFrame ?_
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, pa, pb⟩ e₁ e₂
  have ea := alloc_eq pa
  have eb := alloc_eq pb
  subst ea eb
  exact Two.body_rel ⟨h₁, h₂, hpub.1⟩ hpub.2 _ _ t₁ t₂ a' b' ⟨rfl, rfl⟩ e₁ e₂

theorem derive_ct : ConstantTime isa deriveRV.pre deriveRV.pub Impl.Argon2.RISCV64.Derive.derive :=
  derive_rel.constantTime

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-!
# Argon2 on RISC-V: the derivation is verified

`derive_verified`: the derivation against `deriveRV` (correct, constant
time, and satisfiable: `satState`). `deriveShared_verified`: against the
shared contract `Spec.Argon2.deriveContract`, through `deriveFlat`, whose
precondition spells `DPre` out as `Sig.contract` lays the regions out, and
whose public data are the arguments one by one.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64

/-! ## A state satisfying the precondition -/

/-- The arguments on the stack: one thread, empty secret and associated data,
8 blocks at `0x10000`, scratch at `0x20000` and a 4-byte tag at `0x30000`
(the register arguments are Argon2d, an empty password and salt, one pass
over 8 KiB in one lane). -/
def satStack : List Nat := [1, 0, 0, 0, 0, 0x10000, 8, 0x20000, 0x30000, 4]

/-- Memory holding `satStack` at the stack pointer, `0x40000`, where the
first argument in memory is. -/
def satMem (a : Addr) : Byte :=
  if 0x40000 ≤ a.toNat ∧ a.toNat < 0x40050 then
    ((BitVec.ofNat 64 (satStack[(a.toNat - 0x40000) / 8]?.getD 0)) >>> (8 * ((a.toNat - 0x40000) % 8))).setWidth 8
  else 0

def satState : State where
  gpr r := match r with
    | .a5 => 1 | .a6 => 8 | .a7 => 1 | _ => 0
  sp := 0x40000
  mem := satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x40000, 80⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩]

/-- The arguments of `satState`. -/
def satArgs : List Nat := [0, 0, 0, 0, 0, 1, 8, 1] ++ satStack

theorem sat_args : ∀ i < 18, arg satState i = BitVec.ofNat 64 (satArgs[i]?.getD 0) := by decide

theorem sat_pre : DPre satState := by
  have a : ∀ i < 18, arg satState i = BitVec.ofNat 64 (satArgs[i]?.getD 0) := sat_args
  have e : stackArgAddr satState 0 = 0x40000 := by decide
  have sp : satState.sp = 0x40000 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [pwR, saltR, secR, adR, memR, scrR, outR, argR, stkR0, pwP, pwL, saltP, saltL, secP,
    secL, adP, adL, memP, blocksN, scrP, outP, outL, kindV, itersN, mcostN, lanesN, threadsN, prm, arg32,
    a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide), a 5 (by decide),
    a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide), a 11 (by decide),
    a 12 (by decide), a 13 (by decide), a 14 (by decide), a 15 (by decide), a 16 (by decide), a 17 (by decide),
    e, sp]
  all_goals first
    | rfl
    | decide
    | (intro r hr w hw
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hw
       rcases hr with rfl | rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
         exact Region.disjoint_of_sep (by decide))
    | (intro r hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))
    | exact Region.disjoint_of_sep (by decide)

theorem derive_verified : Verified RISCV64.target Impl.Argon2.RISCV64.Derive.derive deriveRV :=
  ⟨fun _ hs => correct hs, derive_ct, ⟨satState, sat_pre⟩⟩

/-! ## The shared contract -/

/-- `deriveRV`, its precondition spelt out as `Sig.contract` lays the
regions out, and its public data argument by argument. -/
def deriveFlat : Contract RISCV64.isa :=
  { deriveRV with
    pre := fun s =>
      let pw : Region := ⟨arg s 1, (arg s 2).toNat⟩
      let salt : Region := ⟨arg s 3, (arg s 4).toNat⟩
      let sec : Region := ⟨arg s 9, (arg s 10).toNat⟩
      let ad : Region := ⟨arg s 11, (arg s 12).toNat⟩
      let mem : Region := ⟨arg s 13, (arg s 14).toNat * 1024⟩
      let scr : Region := ⟨arg s 15, 16384⟩
      let out : Region := ⟨arg s 16, (arg s 17).toNat⟩
      let args : Region := ⟨stackArgAddr s 0, 80⟩
      let stack : Region := below s.sp 320
      s.rd = [pw, salt, sec, ad, args] ∧ s.wr = [mem, scr, out] ∧
      pw.Disjoint mem ∧ pw.Disjoint scr ∧ pw.Disjoint out ∧ salt.Disjoint mem ∧ salt.Disjoint scr ∧
      salt.Disjoint out ∧ sec.Disjoint mem ∧ sec.Disjoint scr ∧ sec.Disjoint out ∧ ad.Disjoint mem ∧
      ad.Disjoint scr ∧ ad.Disjoint out ∧ args.Disjoint mem ∧ args.Disjoint scr ∧ args.Disjoint out ∧
      mem.Disjoint scr ∧ mem.Disjoint out ∧ scr.Disjoint out ∧
      stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint sec ∧ stack.Disjoint ad ∧ stack.Disjoint mem ∧
      stack.Disjoint scr ∧ stack.Disjoint out ∧
      (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 64 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 64 ∧
      (arg s 9).toNat + (arg s 10).toNat ≤ 2 ^ 64 ∧ (arg s 11).toNat + (arg s 12).toNat ≤ 2 ^ 64 ∧
      (arg s 13).toNat + (arg s 14).toNat * 1024 ≤ 2 ^ 64 ∧ (arg s 15).toNat + 16384 ≤ 2 ^ 64 ∧
      (arg s 16).toNat + (arg s 17).toNat ≤ 2 ^ 64 ∧ 320 ≤ s.sp.toNat ∧ s.sp.toNat + 8 * 10 ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ (arg s 13).toNat % 8 = 0 ∧ (arg s 15).toNat % 8 = 0 ∧
      (arg32 s 0).toNat ≤ 2 ∧
      Spec.Argon2.valid (Spec.Argon2.params (arg32 s 0).toNat (arg32 s 5).toNat (arg32 s 6).toNat
        (arg32 s 7).toNat (arg s 17).toNat) (arg s 2).toNat (arg s 4).toNat (arg s 10).toNat (arg s 12).toNat ∧
      1 ≤ (arg32 s 8).toNat ∧ (arg32 s 8).toNat < 2 ^ 24 ∧
      (arg s 14).toNat = (Spec.Argon2.params (arg32 s 0).toNat (arg32 s 5).toNat (arg32 s 6).toNat
        (arg32 s 7).toNat (arg s 17).toNat).blocks
    pub := fun s₁ s₂ =>
      (s₁.sp = s₂.sp ∧ Spec.Argon2.references (prm s₁) (pwB s₁) (saltB s₁) (secB s₁) (adB s₁) =
        Spec.Argon2.references (prm s₂) (pwB s₂) (saltB s₂) (secB s₂) (adB s₂)) ∧
      arg32 s₁ 0 = arg32 s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3 ∧
      arg s₁ 4 = arg s₂ 4 ∧ arg32 s₁ 5 = arg32 s₂ 5 ∧ arg32 s₁ 6 = arg32 s₂ 6 ∧
      arg32 s₁ 7 = arg32 s₂ 7 ∧ arg32 s₁ 8 = arg32 s₂ 8 ∧ arg s₁ 9 = arg s₂ 9 ∧
      arg s₁ 10 = arg s₂ 10 ∧ arg s₁ 11 = arg s₂ 11 ∧ arg s₁ 12 = arg s₂ 12 ∧ arg s₁ 13 = arg s₂ 13 ∧
      arg s₁ 14 = arg s₂ 14 ∧ arg s₁ 15 = arg s₂ 15 ∧ arg s₁ 16 = arg s₂ 16 ∧ arg s₁ 17 = arg s₂ 17 }

theorem deriveFlat_pre {s : State} (h : deriveFlat.pre s) : DPre s := by
  obtain ⟨hrd, hwr, d₁, d₂, d₃, d₄, d₅, d₆, d₇, d₈, d₉, d₁₀, d₁₁, d₁₂, d₁₃, d₁₄, d₁₅, m₁, m₂, m₃,
    k₁, k₂, k₃, k₄, k₅, k₆, k₇, f₁, f₂, f₃, f₄, f₅, f₆, f₇, lo, hi, sa, ma, ca, kd, vd, t₁, t₂, bl⟩ := h
  refine
    { rd := hrd
      wr := hwr
      ro_w := ?_
      mem_scr := m₁
      mem_out := m₂
      scr_out := m₃
      stk_all := ?_
      pw_fits := f₁
      salt_fits := f₂
      sec_fits := f₃
      ad_fits := f₄
      mem_fits := f₅
      scr_fits := f₆
      out_fits := f₇
      sp_lo := lo
      sp_hi := hi
      sp_al := sa
      mem_al := ma
      scr_al := ca
      kind_le := kd
      valid := vd
      threads := ⟨t₁, t₂⟩
      blocks := bl }
  · intro r hr w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hw
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    exacts [d₁, d₂, d₃, d₄, d₅, d₆, d₇, d₈, d₉, d₁₀, d₁₁, d₁₂, d₁₃, d₁₄, d₁₅]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [k₁, k₂, k₃, k₄, k₅, k₆, k₇]

theorem argPub_int {s : State} {i : Nat} (h : i ∈ intArgs) : argPub s i = (arg32 s i).setWidth 64 :=
  ite_eq_left_iff.mpr fun n => absurd h n

theorem argPub_word {s : State} {i : Nat} (h : i ∉ intArgs) : argPub s i = arg s i :=
  ite_eq_right_iff.mpr fun n => absurd n h

theorem deriveFlat_pub {s₁ s₂ : State} (h : deriveFlat.pub s₁ s₂) : deriveRV.pub s₁ s₂ := by
  obtain ⟨⟨sp, refs⟩, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17⟩ := h
  refine ⟨⟨sp, fun i hi => ?_⟩, refs⟩
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
    i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first
    | rw [argPub_int (by decide), argPub_int (by decide)]; simp only [*]
    | rw [argPub_word (by decide), argPub_word (by decide)]; simp only [*]

theorem deriveFlat_implies : deriveRV.Implies deriveFlat :=
  ⟨fun _ h => deriveFlat_pre h, fun _ _ _ h => h, fun _ _ _ _ h => deriveFlat_pub h,
    ⟨satState, by
      have a : ∀ i < 18, arg satState i = BitVec.ofNat 64 (satArgs[i]?.getD 0) := sat_args
      have e : stackArgAddr satState 0 = 0x40000 := by decide
      simp only [deriveFlat, arg32, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide),
        a 4 (by decide), a 5 (by decide), a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide),
        a 10 (by decide), a 11 (by decide), a 12 (by decide), a 13 (by decide), a 14 (by decide),
        a 15 (by decide), a 16 (by decide), a 17 (by decide), e]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ <;>
      exact Region.disjoint_of_sep (by decide)⟩⟩

theorem flat_implies : deriveFlat.Implies (Spec.Argon2.deriveContract RISCV64.abi 320) := by
  sig_implies [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, deriveFlat, deriveRV, arg, arg32, prm, pwB,
    saltB, secB, adB, pwR, saltR, secR, adR, pwP, pwL, saltP, saltL, secP, secL, adP, adL, kindV, itersN, mcostN,
    lanesN, outL, outP, below, RISCV64.abi, RISCV64.argRegs, List.getD, List.range, List.range.loop]
    [satState, satMem, satStack, RISCV64.stackArg, RISCV64.stackArgAddr, Mem.readW, Mem.read,
      Spec.Argon2.params, Spec.Argon2.valid, Spec.Argon2.Params.blocks, Spec.Argon2.Params.segmentLen]
    using satState

/-- The emitted function, against the shared contract. -/
theorem deriveShared_verified :
    Verified RISCV64.target Impl.Argon2.RISCV64.Derive.derive (Spec.Argon2.deriveContract RISCV64.abi 320) :=
  (derive_verified.of_implies deriveFlat_implies).of_implies flat_implies

end VG.Proof.Argon2.RISCV64.Derive
