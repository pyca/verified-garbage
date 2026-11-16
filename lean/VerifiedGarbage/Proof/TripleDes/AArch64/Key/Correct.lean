module

public import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Contract
public import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Composition
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey
import VerifiedGarbage.Proof.TripleDes.Bytes

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.TripleDes.AArch64.Key (tabName)

theorem cmpLength_ok (s : State) :
    ∃ s', runBlock isa [.subImm .x .x4 .x1 16] s = some s' ∧
      isa.eval (.zero .x .x4) s' = some (s.gpr .x1 == 16) ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.syms = s.syms := by
  refine ⟨s.write .x .x4 (s.gpr .x1 - 16), ?_, ?_, fun r hr => gpr_write_of_ne _ _ _ hr, rfl, rfl,
    rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show (16 : Nat) < 4096 from by decide, ite_true, State.read, BitVec.setWidth_eq]
    rfl
  · change VG.AArch64.eval (.zero .x .x4) _ = _
    simp only [VG.AArch64.eval, State.read, gpr_write_self, BitVec.setWidth_eq]
    exact congrArg some (by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      bv_omega)

theorem beq16_toNat (x : BitVec 64) : (x == 16) = decide (x.toNat = 16) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    apply BitVec.eq_of_toNat_eq
    exact h

theorem body_ok (origin s : State) (hp : Permissions origin) (hs : Components origin s 0)
    (h6 : s.gpr .x6 = s.syms tabName) :
    WP isa (.seq (Impl.TripleDes.AArch64.Key.component 0 0)
      (.seq (Impl.TripleDes.AArch64.Key.component 8 1)
        (.seq (.block [.subImm .x .x4 .x1 16])
          (.ite (.zero .x .x4) (.block Impl.TripleDes.AArch64.Key.copyThird)
            (Impl.TripleDes.AArch64.Key.component 16 2))))) s (Components origin · 3) := by
  apply WP.seq
  apply WP.mono (componentStep_ok origin s 0 (by decide) hp hs h6 (by rfl))
  intro s₁ ⟨hs₁, h₁⟩
  apply WP.seq
  apply WP.mono (componentStep_ok origin s₁ 1 (by decide) hp hs₁ h₁ (by rfl))
  intro s₂ ⟨hs₂, h₂⟩
  apply WP.seq
  obtain ⟨s₃, run₃, flag₃, reg₃, mem₃, rd₃, wr₃, syms₃⟩ := cmpLength_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have hs₃ : Components origin s₃ 2 :=
    ⟨fun c hc j hj => by rw [mem₃]; exact hs₂.keys c hc j hj, rd₃.trans hs₂.rd, wr₃.trans hs₂.wr,
      fun r h4 h5 h6 => (reg₃ r h4).trans (hs₂.reg r h4 h5 h6), by rw [mem₃]; exact hs₂.frame⟩
  have flag : isa.eval (.zero .x .x4) s₃ = some (decide ((origin.gpr .x1).toNat = 16)) := by
    rw [flag₃, hs₂.reg .x1 (by decide) (by decide) (by decide), beq16_toNat]
  by_cases h16 : (origin.gpr .x1).toNat = 16
  · apply WP.ite true (by simpa only [h16, decide_true] using flag)
    · intro _; exact copyThird_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simpa only [h16, decide_false] using flag)
    · simp
    · intro _
      exact WP.mono (componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by rw [reg₃ .x6 (by decide), syms₃]; exact h₂)
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false]))
        fun _ h => h.1

theorem expand_correct (s : State) (hs : contract.pre s) :
    WP isa Impl.TripleDes.AArch64.Key.expandKey s
      (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ contract.post s s') := by
  obtain ⟨hrd, hwr, keyOutput, valid⟩ := hs
  rw [Impl.TripleDes.AArch64.Key.expandKey]
  apply WP.seq
  refine WP.of_runBlock ⟨s.write .x .x6 (s.syms tabName), rfl, ?_⟩
  have g₁ (r : Reg) (hr : r ≠ .x6) : (s.write .x .x6 (s.syms tabName)).gpr r = s.gpr r :=
    gpr_write_of_ne _ _ _ hr
  have hp : Permissions s := by
    constructor
    · intro offset hoff
      rw [hrd, hwr]
      exact ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, by simp,
        Offset.contains_base _ hoff (by
          have bound := BitVec.isLt (s.gpr .x1)
          omega_using [hoff, bound])⟩
    · intro offset n hoff
      rw [hwr]
      exact ⟨⟨s.gpr .x2, 384⟩, by simp, Offset.contains_base _ hoff (by omega_using [hoff])⟩
    · exact keyOutput
    · exact valid
  refine WP.mono (body_ok s _ hp ⟨fun _ h => by omega, rfl, rfl, fun r _ _ h6 => g₁ r h6,
    Frame.refl _ _⟩ (gpr_write_self _ _ _ _)) fun s₂ h₂ => ⟨fun r hr => ?_, ?_⟩
  · have kept : ∀ r ∈ preserved, r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x6 := by decide
    exact h₂.reg r (kept r hr).1 (kept r hr).2.1 (kept r hr).2.2
  · have result := h₂.schedule
    rw [← VG.Proof.TripleDes.expandKey_memory s.mem (s.gpr .x0) (s.gpr .x1).toNat valid] at result
    exact result

end VG.Proof.TripleDes.AArch64.Key
