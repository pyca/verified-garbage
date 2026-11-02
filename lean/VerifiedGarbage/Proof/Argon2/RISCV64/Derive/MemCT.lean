module

public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.CTCall
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.MemoryInit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.CTCall
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.MemoryInit
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Parameters
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Parameters

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
  have L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega
  have hcell : l * (prm s₀).laneLen + c < blocksN s₀ := by
    rw [hp.blocks_eq]
    have := Nat.mul_le_mul_right (prm s₀).laneLen (show l + 1 ≤ lanesN s₀ by omega)
    rw [Nat.succ_mul] at this
    omega
  unfold initArgs Impl.Argon2.RISCV64.HPrime.mov
  refine wp_li (by omega) fun s₁ u₁ => ?_
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
  have hcell' : (l * (prm s₀).laneLen + c) * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
  refine ⟨⟨i₈, r7₈, ⟨inR s₀, by simp, 0, by rw [r3₈]; simp, by rw [r4₈]; show 0 + 72 ≤ 72; omega⟩,
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
    (fun s₁ s₂ h => ⟨0, by omega, hl1, h.1, h.2⟩) fun _ _ h => h
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
      exact ⟨lanesN s₀₁ - (l + 1), by omega, l + 1, rfl, by omega, li₁, li₂⟩
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
