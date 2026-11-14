module

public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.AArch64.ConstantTime
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Lit
public import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Loop
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Phase
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Steps
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Rc2.AArch64.Lit
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Rc2.AArch64.Cbc.Contract`, which only this module used -/

section

/-! # CBC's function-level contract -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64

def contract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 128⟩
    let iv : Region := ⟨s.gpr .x1, 8⟩
    let data : Region := ⟨s.gpr .x2, 8 * (s.gpr .x3).toNat⟩
    let buf : Region := ⟨s.gpr .x4, 512⟩
    s.rd = [key] ∧ s.wr = [iv, data, buf] ∧ key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧
      (s.gpr .x2).toNat + 8 * (s.gpr .x3).toNat ≤ 2 ^ 64
  post s s' :=
    let out := Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x1)) (Spec.Rc2.blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    Spec.Rc2.blocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat = out.1 ∧
      Spec.Rc2.blockAt s'.mem (s.gpr .x1) = out.2
  pub := PublicRegs [.x0, .x1, .x2, .x3, .x4]

end VG.Proof.Rc2.AArch64.Cbc

end

end

/-! ### `Rc2.AArch64.Cbc.IO`, which only this module used -/

section

/-! # CBC register saves, setup, and restoration -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

/-- The registers the code saves in `buf`, and where. -/
abbrev saved : List (Reg × Nat) := [(.x23, 264), (.x24, 272), (.x30, 280)]

/-- The memory after the saves. -/
abbrev savedMem (s : State) : Mem := Spill.saveMem s.mem (s.gpr .x4) s.gpr saved

theorem save_eq : Impl.Rc2.AArch64.Cbc.save = Spill.saveCode .x4 saved := rfl

theorem restore_eq : Impl.Rc2.AArch64.Cbc.restore = Spill.restoreCode .x2 saved := rfl

theorem savedMem_frame (s : State) : Frame [⟨s.gpr .x4, 512⟩] s.mem (savedMem s) :=
  Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem setup_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.AArch64.Cbc.setup s = some s' ∧
      s'.gpr .x23 = s.gpr .x1 ∧ s'.gpr .x24 = s.gpr .x3 ∧
      s'.gpr .x1 = s.gpr .x2 ∧ s'.gpr .x2 = s.gpr .x4 ∧
      zeroCount s' = some (s.gpr .x3 == 0) ∧ Keep [.x23, .x24, .x1, .x2] s s' := by
  refine ⟨_, by
    simp only [Impl.Rc2.AArch64.Cbc.setup, rr, runBlock_cons, exec]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · unfold zeroCount
    simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, BitVec.setWidth_eq, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

end VG.Proof.Rc2.AArch64.Cbc

end

end


/-! # Verified RC2-CBC encryption and decryption -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64

/-- The save, the setup, the blocks (`mid`, as the loop over them), and the restore. -/
theorem cbc_body_correct (d : Spec.Rc2.Direction) (mid : Prog isa)
    (hmid : ∀ s n, 8 * n ≤ 2 ^ 64 → StepPre s n → s.gpr .x24 = BitVec.ofNat 64 n →
      WP isa mid s (LoopPost d s n))
    (s : State) (hs : (contract d).pre s) :
    WP isa (.seq (.block (Impl.Rc2.AArch64.Cbc.save ++ Impl.Rc2.AArch64.Cbc.setup))
      (.seq mid (.block Impl.Rc2.AArch64.Cbc.restore))) s
      (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    fit⟩ := hs
  have writes (i : Nat) (hi : i + 8 ≤ 512) : InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 i) 8 := by
    rw [hwr]
    exact ⟨⟨s.gpr .x4, 512⟩, by simp, Offset.contains_base _ hi (by omega_using [hi])⟩
  apply WP.seq
  rw [save_eq]
  refine Spill.save_ok (by decide) (fun p hp => writes p.2 (by revert p; decide)) ?_
  obtain ⟨s₂, run₂, iv₂, count₂, data₂, buf₂, -, keep₂⟩ := setup_ok { s with mem := savedMem s }
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have key₂ : s₂.gpr .x0 = s.gpr .x0 := keep₂.reg .x0 (by decide)
  have rd₂ : s₂.rd = s.rd := keep₂.rd
  have wr₂ : s₂.wr = s.wr := keep₂.wr
  have mem₂ : s₂.mem = savedMem s := keep₂.mem
  have scratchFrame : Frame [⟨s.gpr .x4, 512⟩] s.mem s₂.mem := by
    rw [mem₂]; exact savedMem_frame s
  have initialKey := scheduleAt_frame scratchFrame (s.gpr .x0) (by simpa using keyBuf)
  have initialIv := blockAt_frame scratchFrame (s.gpr .x1) (by simpa using ivBuf)
  have initialData := blocksAt_frame scratchFrame (s.gpr .x2) (s.gpr .x3).toNat (by simpa using dataBuf)
  have hp₂ : StepPre s₂ (s.gpr .x3).toNat := by
    constructor
    · simp only [keyR, ivR, dataR, bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      exact fun _ _ h => h
    · simp only [ivR, dataR, bufR, iv₂, data₂, buf₂, wr₂, hwr]
      exact fun _ _ h => h
    · simpa only [keyR, ivR, key₂, iv₂] using keyIv
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [ivR, dataR, iv₂, data₂] using ivData
    · simpa only [ivR, bufR, iv₂, buf₂] using ivBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
  apply WP.seq
  apply WP.mono (hmid s₂ (s.gpr .x3).toNat (by omega_using [fit]) hp₂ (by simpa using count₂))
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .x2 (by decide) (by decide) (by decide)).trans buf₂
  have reads (i : Nat) (hi : i + 8 ≤ 512) :
      InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .x2 + BitVec.ofNat 64 i) 8 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hsv : Spill.Saved (s₃.gpr .x2) s.gpr saved s₃.mem := fun p hp => by
    have hb : 264 ≤ p.2 ∧ p.2 + 8 ≤ 512 := by revert p; decide
    have h := h₃.scratchRead hp₂ p.2 hb.1 hb.2
    rw [buf₂, mem₂] at h
    rw [buf₃, h]
    exact Spill.saveMem_saved (by decide) _ _ _ p hp
  rw [restore_eq]
  refine WP.mono (Spill.restore_wp rfl (by decide) (by decide)
    (fun p hp => reads p.2 (by revert p; decide)) hsv) fun s₄ h₄ => ?_
  constructor
  · intro r hr
    by_cases hs : r ∈ saved.map Prod.fst
    · exact h₄.gpr_of (.inl hs)
    have hb : r ≠ .x23 ∧ r ≠ .x24 ∧ r ≠ .x30 := by
      simpa only [saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] using hs
    have hsa : ∀ r ∈ preserved, r ≠ .x30 → r ∈ savedAcrossCall := by decide
    have sep : ∀ r ∈ preserved, r ≠ .x23 → r ≠ .x24 → r ∉ [.x23, .x24, .x1, .x2] := by decide
    rw [h₄.other r hs, h₃.callee r (hsa r hr hb.2.2) hb.2.1]
    exact keep₂.reg r (sep r hr hb.1 hb.2.1)
  · have out := h₃.data
    have iv := h₃.iv
    rw [key₂, iv₂, data₂, initialKey, initialIv, initialData] at out iv
    constructor
    · rw [h₄.mem]; exact out
    · rw [h₄.mem]; exact iv

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.AArch64.Cbc.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := cbc_body_correct .encrypt _
    (fun s n bound hp count => maybeLoop_ok .encrypt s n bound hp count) s hs
  change Exec isa Impl.Rc2.AArch64.Cbc.encrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.AArch64.Cbc.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := cbc_body_correct .decrypt _
    (fun s n bound hp count => phaseLoop_ok s n bound hp count) s hs
  change Exec isa Impl.Rc2.AArch64.Cbc.decrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

end VG.Proof.Rc2.AArch64.Cbc
