module

public import VerifiedGarbage.Proof.TripleDes.Scratch
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.Arm.FunctionsLit
public import VerifiedGarbage.Proof.TripleDes.Arm.Key.Body
public import VerifiedGarbage.Proof.TripleDes.Arm.ConstantTime
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rc2.Arm.Save
public import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `TripleDes.Arm.Key.Correct`, which only this module used -/

section

/-! ### `TripleDes.Arm.Key.Save`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (slotsOf)

theorem save_eq : Impl.TripleDes.Arm.Key.save =
    (slotsOf Impl.TripleDes.Arm.Key.savedRegs).map (fun p => Instr.str p.1 .r3 p.2) := by
  rw [Impl.TripleDes.Arm.Key.save, slotsOf, List.map_map]; rfl

theorem restore_eq : Impl.TripleDes.Arm.Key.restore =
    (slotsOf Impl.TripleDes.Arm.Key.savedRegs).map (fun p => Instr.ldr p.1 .r3 p.2) := by
  rw [Impl.TripleDes.Arm.Key.restore, slotsOf, List.map_map]; rfl

theorem slots_ok : Spill.Slots 0 36 (slotsOf Impl.TripleDes.Arm.Key.savedRegs) := by decide

theorem slot_index : ∀ p ∈ slotsOf Impl.TripleDes.Arm.Key.savedRegs, ∃ i < 9, p.2 = 4 * i := by decide

def Saved (original current : State) : Prop :=
  Spill.Saved current.mem (State.addr (current.gpr .r3)) original.gpr (slotsOf Impl.TripleDes.Arm.Key.savedRegs)

theorem save_ok (s : State)
    (fit : (s.gpr .r3).toNat + 256 ≤ 2 ^ 32)
    (hw : ∀ i < 9, InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block Impl.TripleDes.Arm.Key.save) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Saved s s' ∧
      Frame [⟨State.addr (s.gpr .r3), 36⟩] s.mem s'.mem) := by
  rw [save_eq, ← List.append_nil (List.map _ _)]
  refine Spill.save_ok _ s _ (fun p hp => ?_) (WP.block_nil ⟨rfl, rfl, rfl,
    Spill.saveMem_saved _ _ _ _ slots_ok, Spill.saveMem_frame _ _ _ (by decide) _ (by decide)⟩)
  obtain ⟨i, hi, he⟩ := slot_index p hp
  exact ⟨by omega_using [hi, he], by omega_using [fit, hi, he], he ▸ hw i hi⟩

theorem restore_ok (original s : State) (hsaved : Saved original s)
    (fit : (s.gpr .r3).toNat + 256 ≤ 2 ^ 32)
    (hread : ∀ i < 9, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r3) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block Impl.TripleDes.Arm.Key.restore) s (fun s' =>
      (∀ r ∈ Impl.TripleDes.Arm.Key.savedRegs, s'.gpr r = original.gpr r) ∧
      VG.Proof.Rc2.Arm.Keep (Impl.TripleDes.Arm.Key.savedRegs) s s') := by
  rw [restore_eq, ← List.append_nil (List.map _ _)]
  have hregs : (slotsOf Impl.TripleDes.Arm.Key.savedRegs).map Prod.fst = Impl.TripleDes.Arm.Key.savedRegs := by
    decide
  refine Spill.restoreList_ok _ s _ (by decide) (fun p hp => ?_)
    fun s' hl ho hm hrd hwr _ => WP.block_nil ⟨?_, ⟨fun r hr => ho r (hregs ▸ hr), hm, hrd, hwr⟩⟩
  · obtain ⟨i, hi, he⟩ := slot_index p hp
    have hne : ∀ p ∈ slotsOf Impl.TripleDes.Arm.Key.savedRegs, p.1 ≠ .r3 := by decide
    exact ⟨hne p hp, by omega_using [hi, he], by omega_using [fit, hi, he], he ▸ hread i hi⟩
  · exact Spill.restored_of (hsaved.restored hl) fun r hr => hregs ▸ hr

end VG.Proof.TripleDes.Arm.Key

end

end

/-! ## `Contract` -/

@[expose] public section

section

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm

def contract : Contract isa where
  pre s :=
    let key : Region := ⟨(State.addr (s.gpr .r0)), (s.gpr .r1).toNat⟩
    let output : Region := ⟨(State.addr (s.gpr .r2)), 384⟩
    let scratch : Region := ⟨(State.addr (s.gpr .r3)), 512⟩
    s.rd = [key] ∧ s.wr = [output, scratch] ∧ key.Disjoint output ∧ key.Disjoint scratch ∧
      output.Disjoint scratch ∧
      Spec.TripleDes.validKey (s.gpr .r1).toNat ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 384 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 512 ≤ 2 ^ 32
  post s s' := Spec.TripleDes.scheduleAt s'.mem ((State.addr (s.gpr .r2))) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem ((State.addr (s.gpr .r0))) (s.gpr .r1).toNat)
  pub := PublicRegs [.r0, .r1, .r2, .r3]

end VG.Proof.TripleDes.Arm.Key

end

/-! ## `Correct` -/

section

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm

 theorem expand_correct (s : State) (hs : contract.pre s) :
    WP isa Impl.TripleDes.Arm.Key.expandKey s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ contract.post s s') := by
  obtain ⟨hrd, hwr, keyOutput, keyScratch, outputScratch, valid, keyFit, outputFit, scratchFit⟩ := hs
  have scratchWrites : ∀ i < 9, InRegions s.wr ((State.addr (s.gpr .r3)) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨(State.addr (s.gpr .r3)), 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  rw [Impl.TripleDes.Arm.Key.expandKey]
  apply WP.seq
  apply WP.mono (save_ok s (by omega_using [scratchFit]) scratchWrites)
  intro s₁ h₁
  have g₁ (r : Reg) : s₁.gpr r = s.gpr r := congrFun h₁.1 r
  have hp : Permissions s₁ := by
    constructor
    · intro offset hoff
      rw [h₁.2.1, h₁.2.2.1, g₁, hrd, hwr]
      exact ⟨⟨(State.addr (s.gpr .r0)), (s.gpr .r1).toNat⟩, by simp,
        Offset.contains_base _ (by simpa only [g₁] using hoff) (by
          have bound := BitVec.isLt (s.gpr .r1)
          rw [g₁] at hoff
          omega_using [hoff, bound])⟩
    · intro offset hoff
      rw [h₁.2.2.1, g₁, hwr]
      exact ⟨⟨(State.addr (s.gpr .r2)), 384⟩, by simp, Offset.contains_base _ hoff (by omega_using [hoff])⟩
    · simpa only [keyR, outputR, g₁] using keyOutput
    · simpa only [g₁] using valid
    · simpa only [g₁] using keyFit
    · simpa only [g₁] using outputFit
  apply body_ok s₁ s₁ hp ⟨fun _ h => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  intro s₂ h₂
  have g₂ (r : Reg) (hr : r ∈ keyKept) : s₂.gpr r = s.gpr r :=
    (h₂.reg r hr).trans (g₁ r)
  have frame₂ : Frame [⟨(State.addr (s.gpr .r2)), 384⟩] s₁.mem s₂.mem := by
    have h := h₂.frame
    rw [outputR, g₁] at h
    exact h
  have saved₂ : Saved s s₂ := by
    have saved₁ := h₁.2.2.2.1
    unfold Saved at saved₁ ⊢; rw [g₁] at saved₁; rw [g₂ .r3 (by decide)]
    exact Spill.Saved.frame saved₁ slots_ok frame₂ fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (outputScratch.sub_right (Offset.sub_base _ (by decide))).symm
  have scratchReads : ∀ i < 9, InRegions (s₂.rd ++ s₂.wr) ((State.addr (s₂.gpr .r3)) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [h₂.rd, h₂.wr, h₁.2.1, h₁.2.2.1, g₂ .r3 (by decide)]
    obtain ⟨r, hr, hc⟩ := scratchWrites i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.mono (restore_ok s s₂ saved₂ (by rw [g₂ .r3 (by decide)]; omega_using [scratchFit]) scratchReads)
  intro s₃ h₃
  have scratchFrame : Frame [⟨(State.addr (s.gpr .r3)), 512⟩] s.mem s₁.mem := h₁.2.2.2.2.sub (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨(State.addr (s.gpr .r3)), 512⟩, by simp, Region.sub_prefix (by decide)⟩)
  have initialBytes := VG.Proof.TripleDes.bytesAt_eq_of_frame ((State.addr (s.gpr .r0))) (s.gpr .r1).toNat
    scratchFrame (by have bound := (s.gpr .r1).isLt; omega_using [bound]) (by simpa using keyScratch)
  constructor
  · intro r hr
    have kept : ∀ r ∈ preserved, r ∈ Impl.TripleDes.Arm.Key.savedRegs ∨ r ∈ keyKept := by decide
    rcases kept r hr with saved | other
    · exact h₃.1 r saved
    · exact (h₃.2.reg r (by revert other; cases r <;> decide)).trans (g₂ r other)
  · have result := h₂.schedule
    simp only [g₁] at result
    rw [← VG.Proof.TripleDes.expandKey_memory s₁.mem ((State.addr (s.gpr .r0))) (s.gpr .r1).toNat valid,
      initialBytes] at result
    change Spec.TripleDes.scheduleAt s₃.mem ((State.addr (s.gpr .r2))) = _
    rw [h₃.2.mem]
    exact result

end VG.Proof.TripleDes.Arm.Key

end

end

end

@[expose] public section

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 16 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 384⟩, ⟨0x3000, 512⟩]

theorem correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa Impl.TripleDes.Arm.Key.expandKey s t s' ∧ abiPreserved s s' ∧ contract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := expand_correct s hs
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.r0, .r1, .r2, .r3] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 := by simp [PublicRegs]

theorem verified : Verified target Impl.TripleDes.Arm.Key.expandKey
    (Proof.TripleDes.expandKeyScratchContract abi) := by
  refine Verified.of_correct correct (expandKey_constantTime _) ?_
  sig_implies [Proof.TripleDes.expandKeyScratchContract, Proof.TripleDes.expandKeyScratchSig, Spec.TripleDes.expandKeyPre, Spec.TripleDes.expandKeyPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr,
    contract, publicRegs_four] [satState] using satState

end VG.Proof.TripleDes.Arm.Key
