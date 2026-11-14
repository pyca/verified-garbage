module

public import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Contract
public import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Composition
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rc2.AArch64.Lookup
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Rotation
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.TripleDes.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit

/-! ### `TripleDes.AArch64.Key.Body`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.Rc2.AArch64 (Keep)

theorem cmpLength_ok (s : State) :
    ∃ s', runBlock isa [.subImm .x .x4 .x1 16] s = some s' ∧
      isa.eval (.zero .x .x4) s' = some (s.gpr .x1 == 16) ∧ Keep [.x4] s s' := by
  refine ⟨s.write .x .x4 (s.gpr .x1 - 16), ?_, ?_, write_keep _ _⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show (16 : Nat) < 4096 from by decide, ite_true, State.read, BitVec.setWidth_eq]
    rfl
  · change VG.AArch64.eval (.zero .x .x4) _ = _
    simp only [VG.AArch64.eval, State.read, gpr_write_self, BitVec.setWidth_eq]
    exact congrArg some (by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      bv_omega)

theorem Components.keep {origin s t : State} {n : Nat} (hs : Components origin s n)
    (ht : Keep [.x4] s t) : Components origin t n :=
  ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r hr => (ht.reg r (by revert hr; cases r <;> decide)).trans (hs.reg r hr), by rw [ht.mem]; exact hs.frame⟩

theorem beq16_toNat (x : BitVec 64) : (x == 16) = decide (x.toNat = 16) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    apply BitVec.eq_of_toNat_eq
    exact h

theorem body_ok (origin s : State) (hp : Permissions origin) (hs : Components origin s 0)
    (Q : State → Prop)
    (finish : ∀ t, Components origin t 3 → WP isa (.block Impl.TripleDes.AArch64.Key.restore) t Q) :
    WP isa (.seq (Impl.TripleDes.AArch64.Key.component 0 0)
      (.seq (Impl.TripleDes.AArch64.Key.component 8 1)
        (.seq (.block [.subImm .x .x4 .x1 16])
          (.seq (.ite (.zero .x .x4) (.block Impl.TripleDes.AArch64.Key.copyThird)
            (Impl.TripleDes.AArch64.Key.component 16 2)) (.block Impl.TripleDes.AArch64.Key.restore))))) s Q := by
  apply WP.seq
  apply WP.mono (componentStep_ok origin s 0 (by decide) hp hs (by rfl))
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (componentStep_ok origin s₁ 1 (by decide) hp hs₁ (by rfl))
  intro s₂ hs₂
  apply WP.seq
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := cmpLength_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have hs₃ := hs₂.keep keep₃
  apply WP.seq
  apply WP.mono (Q := (Components origin · 3)) ?_
  · intro t ht
    exact finish t ht
  have flag : isa.eval (.zero .x .x4) s₃ = some (decide ((origin.gpr .x1).toNat = 16)) := by
    rw [flag₃, hs₂.reg .x1 (by decide), beq16_toNat]
  by_cases h16 : (origin.gpr .x1).toNat = 16
  · apply WP.ite true (by simpa only [h16, decide_true] using flag)
    · intro _; exact copyThird_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simpa only [h16, decide_false] using flag)
    · simp
    · intro _
      exact componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

end VG.Proof.TripleDes.AArch64.Key

end

end

/-! ### `TripleDes.AArch64.Key.Save`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

/-- The four callee-saved registers, in slot order. -/
def savedReg (i : Nat) : Reg := (Impl.TripleDes.AArch64.Key.savedRegs).getD i .x19

theorem save_eq : Impl.TripleDes.AArch64.Key.save = Spill.saveCode .x3 (Spill.slots savedReg 4) := by
  decide +kernel

theorem restore_eq : Impl.TripleDes.AArch64.Key.restore = Spill.restoreCode .x3 (Spill.slots savedReg 4) := by
  decide +kernel

def Saved (original current : State) : Prop :=
  ∀ i < 4, current.mem.readW (current.gpr .x3 + BitVec.ofNat 64 (8 * i)) 64 =
    original.gpr (savedReg i)

theorem save_ok (s : State)
    (hw : ∀ i < 4, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block Impl.TripleDes.AArch64.Key.save) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Saved s s' ∧
      Frame [⟨s.gpr .x3, 32⟩] s.mem s'.mem) := by
  rw [save_eq]
  refine WP.mono (Spill.save_wp (by decide) (Spill.forall_slots hw)) fun s' h =>
    ⟨h.gpr, h.rd, h.wr, fun i hi => ?_, ?_⟩
  · rw [h.gpr, h.mem]
    exact Spill.saveMem_saved (l := Spill.slots savedReg 4) (by decide) s.mem (s.gpr .x3) s.gpr
      (savedReg i, 8 * i) (Spill.mem_slots hi)
  · rw [h.mem]; exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem restore_ok (original s : State) (hsaved : Saved original s)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block Impl.TripleDes.AArch64.Key.restore) s (fun s' =>
      (∀ r ∈ Impl.TripleDes.AArch64.Key.savedRegs, s'.gpr r = original.gpr r) ∧
      VG.Proof.Rc2.AArch64.Keep (Impl.TripleDes.AArch64.Key.savedRegs) s s') := by
  rw [restore_eq]
  have hregs : (Spill.slots savedReg 4).map Prod.fst = Impl.TripleDes.AArch64.Key.savedRegs := by
    decide +kernel
  exact WP.mono (Spill.restore_wp rfl (by decide) (by decide) (Spill.forall_slots hread)
    (Spill.forall_slots hsaved)) fun s' h =>
    ⟨fun r hr => h.gpr_of (.inl (hregs ▸ hr)), ⟨fun r hr => h.other r (hregs ▸ hr), h.mem, h.rd, h.wr⟩⟩

end VG.Proof.TripleDes.AArch64.Key

end

end


@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64

 theorem expand_correct (s : State) (hs : contract.pre s) :
    WP isa Impl.TripleDes.AArch64.Key.expandKey s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ contract.post s s') := by
  obtain ⟨hrd, hwr, keyOutput, keyScratch, outputScratch, valid⟩ := hs
  have scratchWrites : ∀ i < 4, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .x3, 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  rw [Impl.TripleDes.AArch64.Key.expandKey]
  apply WP.seq
  apply WP.mono (save_ok s scratchWrites)
  intro s₁ h₁
  have g₁ (r : Reg) : s₁.gpr r = s.gpr r := congrFun h₁.1 r
  have hp : Permissions s₁ := by
    constructor
    · intro offset hoff
      rw [h₁.2.1, h₁.2.2.1, g₁, hrd, hwr]
      exact ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, by simp,
        Offset.contains_base _ (by simpa only [g₁] using hoff) (by
          have bound := BitVec.isLt (s.gpr .x1)
          rw [g₁] at hoff
          omega_using [hoff, bound])⟩
    · intro offset hoff
      rw [h₁.2.2.1, g₁, hwr]
      exact ⟨⟨s.gpr .x2, 384⟩, by simp, Offset.contains_base _ hoff (by omega_using [hoff])⟩
    · simpa only [keyR, outputR, g₁] using keyOutput
    · simpa only [g₁] using valid
  apply body_ok s₁ s₁ hp ⟨fun _ h => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  intro s₂ h₂
  have g₂ (r : Reg) (hr : r ∈ keyKept) : s₂.gpr r = s.gpr r :=
    (h₂.reg r hr).trans (g₁ r)
  have frame₂ : Frame [⟨s.gpr .x2, 384⟩] s₁.mem s₂.mem := by
    have h := h₂.frame
    rw [outputR, g₁] at h
    exact h
  have saved₂ : Saved s s₂ := by
    intro i hi
    have sub : Region.Sub ⟨s.gpr .x3 + BitVec.ofNat 64 (8 * i), 8⟩ ⟨s.gpr .x3, 512⟩ :=
      Offset.sub_base _ (by omega_using [hi])
    have mem := frame₂.readW (a := s.gpr .x3 + BitVec.ofNat 64 (8 * i)) (w := 64)
      (r := ⟨s.gpr .x3 + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact (outputScratch.sub_right sub).symm)
      (by decide)
    rw [g₂ .x3 (by decide)]
    have saved₁ := h₁.2.2.2.1 i hi
    rw [g₁] at saved₁
    exact mem.trans saved₁
  have scratchReads : ∀ i < 4, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x3 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [h₂.rd, h₂.wr, h₁.2.1, h₁.2.2.1, g₂ .x3 (by decide)]
    obtain ⟨r, hr, hc⟩ := scratchWrites i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.mono (restore_ok s s₂ saved₂ scratchReads)
  intro s₃ h₃
  have scratchFrame : Frame [⟨s.gpr .x3, 512⟩] s.mem s₁.mem := h₁.2.2.2.2.sub (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨s.gpr .x3, 512⟩, by simp, Region.sub_prefix (by decide)⟩)
  have initialBytes := VG.Proof.TripleDes.bytesAt_eq_of_frame (s.gpr .x0) (s.gpr .x1).toNat
    scratchFrame (Nat.le_of_lt (BitVec.isLt _)) (by simpa using keyScratch)
  constructor
  · intro r hr
    have kept : ∀ r ∈ preserved, r ∈ Impl.TripleDes.AArch64.Key.savedRegs ∨ r ∈ keyKept := by decide
    rcases kept r hr with saved | other
    · exact h₃.1 r saved
    · exact (h₃.2.reg r (by revert other; cases r <;> decide)).trans (g₂ r other)
  · have result := h₂.schedule
    simp only [g₁] at result
    rw [← VG.Proof.TripleDes.expandKey_memory s₁.mem (s.gpr .x0) (s.gpr .x1).toNat valid,
      initialBytes] at result
    change Spec.TripleDes.scheduleAt s₃.mem (s.gpr .x2) = _
    rw [h₃.2.mem]
    exact result

end VG.Proof.TripleDes.AArch64.Key
