module

public import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Composition
public import VerifiedGarbage.Proof.Rc2.X86_64.Lookup
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rc2.X86_64.Save
public import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit

/-! ### `TripleDes.X86_64.Key.Body`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Rc2.X86_64 (Keep)

theorem cmpLength_ok (s : State) :
    ∃ s', runBlock isa [.alu .cmp .rsi (.imm 16)] s = some s' ∧
      s'.zf = some (s.gpr .rsi == 16) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
    rfl, ?_, ?_⟩
  · rw [zf_arithFlags]
    exact congrArg some (by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      change (s.gpr .rsi - (16 : BitVec 64) = (0 : BitVec 64)) ↔ s.gpr .rsi = (16 : BitVec 64)
      bv_omega)
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Components.keep {origin s t : State} {n : Nat} (hs : Components origin s n)
    (ht : Keep [] s t) : Components origin t n :=
  ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r hr => (ht.reg r (by simp)).trans (hs.reg r hr), by rw [ht.mem]; exact hs.frame⟩

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
    (finish : ∀ t, Components origin t 3 → WP isa (.block Impl.TripleDes.X86_64.Key.restore) t Q) :
    WP isa (.seq (Impl.TripleDes.X86_64.Key.component 0 0)
      (.seq (Impl.TripleDes.X86_64.Key.component 8 1)
        (.seq (.block [.alu .cmp .rsi (.imm 16)])
          (.seq (.ite .e (.block Impl.TripleDes.X86_64.Key.copyThird)
            (Impl.TripleDes.X86_64.Key.component 16 2)) (.block Impl.TripleDes.X86_64.Key.restore))))) s Q := by
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
  have flag : s₃.zf = some (decide ((origin.gpr .rsi).toNat = 16)) := by
    rw [flag₃, hs₂.reg .rsi (by decide), beq16_toNat]
  by_cases h16 : (origin.gpr .rsi).toNat = 16
  · apply WP.ite true (by simp only [eval, flag, h16, decide_true])
    · intro _; exact copyThird_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simp only [eval, flag, h16, decide_false])
    · simp
    · intro _
      exact componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

end VG.Proof.TripleDes.X86_64.Key

end

end

/-! ### `TripleDes.X86_64.Key.Save`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

/-- The six callee-saved registers, in slot order. -/
def savedReg (i : Nat) : Reg := (Impl.TripleDes.X86_64.Key.savedRegs).getD i .rdi

theorem save_eq : Impl.TripleDes.X86_64.Key.save = VG.Proof.Rc2.X86_64.saveCode .rcx savedReg 6 := by
  decide +kernel

theorem restore_eq : Impl.TripleDes.X86_64.Key.restore = VG.Proof.Rc2.X86_64.restoreCode .rcx savedReg (List.range 6) := by
  decide +kernel

def Saved (original current : State) : Prop :=
  ∀ i < 6, current.mem.readW (current.gpr .rcx + BitVec.ofNat 64 (8 * i)) 64 =
    original.gpr (savedReg i)

theorem save_ok (s : State)
    (hw : ∀ i < 6, InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block Impl.TripleDes.X86_64.Key.save) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Saved s s' ∧
      Frame [⟨s.gpr .rcx, 48⟩] s.mem s'.mem) := by
  rw [save_eq]
  apply WP.mono (VG.Proof.Rc2.X86_64.saveCode_ok s .rcx savedReg 6 hw)
  intro s' hs
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_, ?_⟩
  · intro i hi
    rw [hs.1, hs.2.2.2]
    exact VG.Proof.Rc2.X86_64.saveMem_read _ _ _ 6 (by decide) i hi
  · rw [hs.2.2.2]
    exact VG.Proof.Rc2.X86_64.saveMem_frame _ _ _ 6 (by decide)

theorem savedReg_separate : ∀ i < 6, savedReg i ≠ .rcx := by decide +kernel

theorem restore_ok (original s : State) (hsaved : Saved original s)
    (hread : ∀ i < 6, InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block Impl.TripleDes.X86_64.Key.restore) s (fun s' =>
      (∀ r ∈ Impl.TripleDes.X86_64.Key.savedRegs, s'.gpr r = original.gpr r) ∧
      VG.Proof.Rc2.X86_64.Keep (Impl.TripleDes.X86_64.Key.savedRegs) s s') := by
  rw [restore_eq]
  have hregs : (List.range 6).map savedReg = Impl.TripleDes.X86_64.Key.savedRegs := by decide +kernel
  have h := VG.Proof.Rc2.X86_64.restoreCode_ok s .rcx savedReg (List.range 6) original.gpr
    (fun i hi => savedReg_separate i (List.mem_range.mp hi))
    (fun i hi => hread i (List.mem_range.mp hi))
    (fun i hi => hsaved i (List.mem_range.mp hi))
  rw [hregs] at h
  exact h



end VG.Proof.TripleDes.X86_64.Key

end

end


@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64

 theorem expand_correct (s : State) (hs : contract.pre s) :
    WP isa Impl.TripleDes.X86_64.Key.expandKey s (fun s' => gprPreserved s s' ∧ contract.post s s') := by
  obtain ⟨hrd, hwr, keyOutput, keyScratch, outputScratch, retOutput, retScratch, valid⟩ := hs
  have scratchWrites : ∀ i < 6, InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rcx, 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  rw [Impl.TripleDes.X86_64.Key.expandKey]
  apply WP.seq
  apply WP.mono (save_ok s scratchWrites)
  intro s₁ h₁
  have g₁ (r : Reg) : s₁.gpr r = s.gpr r := congrFun h₁.1 r
  have hp : Permissions s₁ := by
    constructor
    · intro offset hoff
      rw [h₁.2.1, h₁.2.2.1, g₁, hrd, hwr]
      exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp,
        Offset.contains_base _ (by simpa only [g₁] using hoff) (by
          have bound := BitVec.isLt (s.gpr .rsi)
          rw [g₁] at hoff
          omega_using [hoff, bound])⟩
    · intro offset hoff
      rw [h₁.2.2.1, g₁, hwr]
      exact ⟨⟨s.gpr .rdx, 384⟩, by simp, Offset.contains_base _ hoff (by omega_using [hoff])⟩
    · simpa only [keyR, outputR, g₁] using keyOutput
    · simpa only [g₁] using valid
  apply body_ok s₁ s₁ hp ⟨fun _ h => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  intro s₂ h₂
  have g₂ (r : Reg) (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp]) : s₂.gpr r = s.gpr r :=
    (h₂.reg r hr).trans (g₁ r)
  have frame₂ : Frame [⟨s.gpr .rdx, 384⟩] s₁.mem s₂.mem := by
    have h := h₂.frame
    rw [outputR, g₁] at h
    exact h
  have saved₂ : Saved s s₂ := by
    intro i hi
    have sub : Region.Sub ⟨s.gpr .rcx + BitVec.ofNat 64 (8 * i), 8⟩ ⟨s.gpr .rcx, 512⟩ :=
      Offset.sub_base _ (by omega_using [hi])
    have mem := frame₂.readW (a := s.gpr .rcx + BitVec.ofNat 64 (8 * i)) (w := 64)
      (r := ⟨s.gpr .rcx + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact (outputScratch.sub_right sub).symm)
      (by decide)
    rw [g₂ .rcx (by decide)]
    have saved₁ := h₁.2.2.2.1 i hi
    rw [g₁] at saved₁
    exact mem.trans saved₁
  have scratchReads : ∀ i < 6, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rcx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [h₂.rd, h₂.wr, h₁.2.1, h₁.2.2.1, g₂ .rcx (by decide)]
    obtain ⟨r, hr, hc⟩ := scratchWrites i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.mono (restore_ok s s₂ saved₂ scratchReads)
  intro s₃ h₃
  have scratchFrame : Frame [⟨s.gpr .rcx, 512⟩] s.mem s₁.mem := h₁.2.2.2.2.sub (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨s.gpr .rcx, 512⟩, by simp, Region.sub_prefix (by decide)⟩)
  have initialBytes := VG.Proof.TripleDes.bytesAt_eq_of_frame (s.gpr .rdi) (s.gpr .rsi).toNat
    scratchFrame (Nat.le_of_lt (BitVec.isLt _)) (by simpa using keyScratch)
  constructor
  · constructor
    · intro r hr
      by_cases hrsp : r = .rsp
      · subst r
        exact (h₃.2.reg .rsp (by decide)).trans (g₂ .rsp (by decide))
      · have saved : ∀ r ∈ calleeSaved, r ≠ .rsp → r ∈ Impl.TripleDes.X86_64.Key.savedRegs := by decide
        exact h₃.1 r (saved r hr hrsp)
    · have frame : Frame [⟨s.gpr .rdx, 384⟩, ⟨s.gpr .rcx, 512⟩] s.mem s₃.mem := by
        rw [h₃.2.mem]
        exact (scratchFrame.mono (by simp)).trans (frame₂.mono (by simp))
      apply frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
      simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
        And.intro retOutput retScratch
  · have result := h₂.schedule
    simp only [g₁] at result
    rw [← VG.Proof.TripleDes.expandKey_memory s₁.mem (s.gpr .rdi) (s.gpr .rsi).toNat valid,
      initialBytes] at result
    change Spec.TripleDes.scheduleAt s₃.mem (s.gpr .rdx) = _
    rw [h₃.2.mem]
    exact result

end VG.Proof.TripleDes.X86_64.Key
