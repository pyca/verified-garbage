module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Ecb.Loop
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Ecb.ConstantTime
public import VerifiedGarbage.Proof.TripleDes.Scratch
import VerifiedGarbage.Proof.TripleDes.EcbMemory
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Ecb
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ConstantTime

/-! # Triple DES ECB on PPC64LE, verified with its working space as an argument -/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Ecb

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

/-- The memory after `save`: the return address at 512 and `r31` at 520 of
the scratch buffer. -/
def savedMem (s : State) : Mem :=
  (s.mem.writeW (s.gpr .r6 + BitVec.ofNat 64 512) s.lr).writeW
    (s.gpr .r6 + BitVec.ofNat 64 520) (s.gpr .r31)

theorem save_ok (s : State)
    (hw : ∀ i, 512 ≤ i → i + 8 ≤ 1024 → InRegions s.wr (s.gpr .r6 + BitVec.ofNat 64 i) 8) :
    ∃ s', runBlock isa Impl.TripleDes.PPC64LE.Ecb.save s = some s' ∧
      Kept [.r0] { s with mem := savedMem s } s' ∧ s'.lr = s.lr := by
  let s₁ := s.write .r0 s.lr
  have h₆ : s₁.gpr .r6 = s.gpr .r6 := gpr_write_of_ne _ _ (by decide)
  have h₃₁ : s₁.gpr .r31 = s.gpr .r31 := gpr_write_of_ne _ _ (by decide)
  let s₂ : State := { s₁ with mem := s₁.mem.writeW (s₁.gpr .r6 + BitVec.ofNat 64 512) (s₁.gpr .r0) }
  let s₃ : State := { s₂ with mem := s₂.mem.writeW (s₂.gpr .r6 + BitVec.ofNat 64 520) (s₂.gpr .r31) }
  have w₁ : InRegions s₁.wr (s₁.gpr .r6 + BitVec.ofNat 64 512) 8 := by
    rw [h₆]; exact hw 512 (by decide) (by decide)
  have w₂ : InRegions s₂.wr (s₂.gpr .r6 + BitVec.ofNat 64 520) 8 := by
    change InRegions s₁.wr (s₁.gpr .r6 + _) 8
    rw [h₆]; exact hw 520 (by decide) (by decide)
  refine ⟨s₃, ?_, ⟨fun r hr => ?_, ?_, rfl, rfl⟩, rfl⟩
  · rw [Impl.TripleDes.PPC64LE.Ecb.save, runBlock_cons, exec_mflr, runStep_some, runBlock_cons,
      exec_store_d (by decide) (by decide) w₁, runStep_some, runBlock_cons,
      exec_store_d (by decide) (by decide) w₂, runStep_some, runBlock_nil]
  · exact gpr_write_of_ne _ _ (fun h => hr (by simp [h]))
  · change (s.mem.writeW (s₁.gpr .r6 + BitVec.ofNat 64 512) (s₁.gpr .r0)).writeW
      (s₁.gpr .r6 + BitVec.ofNat 64 520) (s₁.gpr .r31) = savedMem s
    rw [h₆, h₃₁, gpr_write_self]; rfl

theorem savedMem_frame (s : State) :
    Frame [⟨s.gpr .r6, 1024⟩] s.mem (savedMem s) :=
  ((Frame.refl _ _).writeW List.mem_cons_self _
    (Offset.contains_base _ (by decide : 512 + 8 ≤ 1024) (by decide))).writeW List.mem_cons_self _
    (Offset.contains_base _ (by decide : 520 + 8 ≤ 1024) (by decide))

theorem savedMem_link (s : State) :
    (savedMem s).readW (s.gpr .r6 + BitVec.ofNat 64 512) 64 = s.lr := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self64]

theorem savedMem_r31 (s : State) :
    (savedMem s).readW (s.gpr .r6 + BitVec.ofNat 64 520) 64 = s.gpr .r31 := by
  rw [savedMem, Mem.readW_writeW_self64]

theorem setup_ok (s : State) :
    ∃ s', runBlock isa Impl.TripleDes.PPC64LE.Ecb.setup s = some s' ∧
      s'.gpr .r31 = s.gpr .r5 ∧ s'.gpr .r5 = s.gpr .r6 ∧ Kept [.r31, .r5] s s' := by
  let s₁ := s.write .r31 (s.gpr .r5 ||| s.gpr .r5)
  let s₂ := s₁.write .r5 (s₁.gpr .r6 ||| s₁.gpr .r6)
  refine ⟨s₂, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩⟩
  · rw [Impl.TripleDes.PPC64LE.Ecb.setup, rr, rr, runBlock_cons, exec_logic, runStep_some,
      runBlock_cons, exec_logic, runStep_some, runBlock_nil]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.or_self]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.or_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [s₂, s₁, gpr_write, hr.1, hr.2, ite_false]

theorem restore_ok (s : State) (lr r31 : BitVec 64)
    (hr : ∀ i, 512 ≤ i → i + 8 ≤ 1024 →
      InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 i) 8)
    (hlr : s.mem.readW (s.gpr .r5 + BitVec.ofNat 64 512) 64 = lr)
    (h31 : s.mem.readW (s.gpr .r5 + BitVec.ofNat 64 520) 64 = r31) :
    ∃ s', runBlock isa Impl.TripleDes.PPC64LE.Ecb.restore s = some s' ∧
      s'.lr = lr ∧ s'.gpr .r31 = r31 ∧ Kept [.r0, .r31] s s' := by
  let s₁ := s.write .r0 (s.mem.readW (s.gpr .r5 + BitVec.ofNat 64 512) 64)
  let s₂ : State := { s₁ with lr := s₁.gpr .r0 }
  have h₅ : s₂.gpr .r5 = s.gpr .r5 :=
    gpr_write_of_ne s (s.mem.readW (s.gpr .r5 + BitVec.ofNat 64 512) 64) (by decide : Reg.r5 ≠ .r0)
  let s₃ := s₂.write .r31 (s₂.mem.readW (s₂.gpr .r5 + BitVec.ofNat 64 520) 64)
  have r₂ : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .r5 + BitVec.ofNat 64 520) 8 := by
    change InRegions (s.rd ++ s.wr) (s₂.gpr .r5 + _) 8
    rw [h₅]; exact hr 520 (by decide) (by decide)
  refine ⟨s₃, ?_, ?_, ?_, ⟨fun r hr' => ?_, rfl, rfl, rfl⟩⟩
  · rw [Impl.TripleDes.PPC64LE.Ecb.restore, runBlock_cons,
      exec_load_d (by decide) (by decide) (hr 512 (by decide) (by decide)), runStep_some,
      runBlock_cons, exec_mtlr, runStep_some, runBlock_cons,
      exec_load_d (by decide) (by decide) r₂, runStep_some, runBlock_nil]
  · change s₁.gpr .r0 = lr
    rw [gpr_write_self]; exact hlr
  · rw [gpr_write_self]
    change s.mem.readW (s₂.gpr .r5 + _) 64 = r31
    rw [h₅]; exact h31
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [s₃, s₂, s₁, gpr_write, hr'.1, hr'.2, ite_false]

theorem LoopPost.scratchRead {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : LoopPost d s n s') (hp : StepPre s n) (i : Nat) (hi : 512 ≤ i ∧ i + 8 ≤ 1024) :
    s'.mem.readW (s.gpr .r5 + BitVec.ofNat 64 i) 64 =
      s.mem.readW (s.gpr .r5 + BitVec.ofNat 64 i) 64 := by
  have sub : Region.Sub ⟨s.gpr .r5 + BitVec.ofNat 64 i, 8⟩ (bufR s) :=
    Offset.sub_base _ hi.2
  have sep : (Region.mk (s.gpr .r5 + BitVec.ofNat 64 i) 8).Disjoint ⟨s.gpr .r5, 512⟩ :=
    Offset.disjoint_base _ (by omega) (by omega)
  apply h.mem.readW (r := ⟨s.gpr .r5 + BitVec.ofNat 64 i, 8⟩) (Region.contains_self _ _)
    (hn := by decide)
  simpa only [loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] using And.intro ((hp.dataBuf.sub_right sub).symm) sep

def contract (d : Spec.TripleDes.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 384⟩
    let data : Region := ⟨s.gpr .r4, 8 * (s.gpr .r5).toNat⟩
    let buf : Region := ⟨s.gpr .r6, 1024⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ (s.gpr .r4).toNat + 8 * (s.gpr .r5).toNat ≤ 2 ^ 64
  post s s' :=
    Spec.TripleDes.blocksAt s'.mem (s.gpr .r4) (s.gpr .r5).toNat =
      Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)) d
        (Spec.TripleDes.blocksAt s.mem (s.gpr .r4) (s.gpr .r5).toNat)
  pub := PublicRegs [.r3, .r4, .r5, .r6]

theorem ecb_correct (d : Spec.TripleDes.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.TripleDes.PPC64LE.Ecb.ecb d) s
      (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧
        (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit⟩ := hs
  have writes : ∀ i, 512 ≤ i → i + 8 ≤ 1024 →
      InRegions s.wr (s.gpr .r6 + BitVec.ofNat 64 i) 8 := by
    intro i _ hi
    rw [hwr]
    exact ⟨⟨s.gpr .r6, 1024⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  rw [Impl.TripleDes.PPC64LE.Ecb.ecb]
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁, lr₁⟩ := save_ok s writes
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, count₂, buf₂, keep₂⟩ := setup_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g₁ (r : Reg) (hr : r ≠ .r0) : s₁.gpr r = s.gpr r := keep₁.reg r (by simpa using hr)
  rw [g₁ .r5 (by decide)] at count₂
  rw [g₁ .r6 (by decide)] at buf₂
  have key₂ := (keep₂.reg .r3 (by decide)).trans (g₁ .r3 (by decide))
  have data₂ := (keep₂.reg .r4 (by decide)).trans (g₁ .r4 (by decide))
  have rd₂ := keep₂.rd.trans keep₁.rd
  have wr₂ := keep₂.wr.trans keep₁.wr
  have mem₂ : s₂.mem = savedMem s := keep₂.mem.trans keep₁.mem
  have scratchFrame : Frame [⟨s.gpr .r6, 1024⟩] s.mem s₂.mem := by
    rw [mem₂]; exact savedMem_frame s
  have initialKey := VG.Proof.TripleDes.scheduleAt_eq_of_frame (s.gpr .r3) scratchFrame
    (by simpa using keyBuf)
  have initialData := VG.Proof.TripleDes.blocksAt_frame scratchFrame (s.gpr .r4)
    (s.gpr .r5).toNat (by simpa using dataBuf)
  have hp₂ : StepPre s₂ (s.gpr .r5).toNat := by
    constructor
    · simp only [keyR, dataR, bufR, key₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      exact fun _ _ h => h
    · simp only [dataR, bufR, data₂, buf₂, wr₂, hwr]
      exact fun _ _ h => h
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
    · rw [data₂]; exact fit
  have flag : isa.eval (.zero .d .r31) s₂ = some (decide ((s.gpr .r5).toNat = 0)) := by
    change VG.PPC64LE.eval (.zero .d .r31) s₂ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, count₂]
    refine congrArg some ?_
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (s.gpr .r5).toNat hp₂
    (by rw [count₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]) flag)
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := h₃.buf.trans buf₂
  have readable : ∀ i, 512 ≤ i → i + 8 ≤ 1024 →
      InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .r5 + BitVec.ofNat 64 i) 8 := by
    intro i h1 h2
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes i h1 h2
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have link : s₃.mem.readW (s₃.gpr .r5 + BitVec.ofNat 64 512) 64 = s.lr := by
    have h := h₃.scratchRead hp₂ 512 (by decide)
    rw [buf₂, mem₂, savedMem_link] at h
    rw [buf₃]; exact h
  have saved31 : s₃.mem.readW (s₃.gpr .r5 + BitVec.ofNat 64 520) 64 = s.gpr .r31 := by
    have h := h₃.scratchRead hp₂ 520 (by decide)
    rw [buf₂, mem₂, savedMem_r31] at h
    rw [buf₃]; exact h
  obtain ⟨s₄, run₄, lr₄, r31₄, keep₄⟩ := restore_ok s₃ s.lr (s.gpr .r31) readable link saved31
  refine WP.of_runBlock ⟨s₄, run₄, ?_, lr₄, ?_⟩
  · intro r hr
    by_cases h31 : r = .r31
    · subst r; exact r31₄
    have h0 : r ≠ .r0 := by revert hr; cases r <;> decide
    have h5 : r ≠ .r5 := by revert hr; cases r <;> decide
    rw [keep₄.reg r (by simp [h0, h31]), h₃.callee r hr h31, keep₂.reg r (by simp [h31, h5]),
      g₁ r h0]
  · have out := h₃.data
    rw [key₂, data₂, initialKey, initialData] at out
    change Spec.TripleDes.blocksAt s₄.mem (s.gpr .r4) (s.gpr .r5).toNat = _
    rw [keep₄.mem]; exact out

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.PPC64LE.Ecb.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hl, hp⟩ := ecb_correct .encrypt s hs
  exact ⟨t, s', he, ⟨ha, Exec.sp he, hl⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.PPC64LE.Ecb.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hl, hp⟩ := ecb_correct .decrypt s hs
  exact ⟨t, s', he, ⟨ha, Exec.sp he, hl⟩, hp⟩

def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩]

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.r3, .r4, .r5, .r6] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
      s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 := by
  simp [PublicRegs]

theorem encrypt_verified : Verified target Impl.TripleDes.PPC64LE.Ecb.encrypt
    (Proof.TripleDes.ecbEncryptScratchContract abi 0) := by
  refine Verified.of_correct encrypt_correct (ecbEncrypt_constantTime _) ?_
  sig_implies [Proof.TripleDes.ecbEncryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, contract,
    publicRegs_four] [satState] using satState

theorem decrypt_verified : Verified target Impl.TripleDes.PPC64LE.Ecb.decrypt
    (Proof.TripleDes.ecbDecryptScratchContract abi 0) := by
  refine Verified.of_correct decrypt_correct (ecbDecrypt_constantTime _) ?_
  sig_implies [Proof.TripleDes.ecbDecryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, contract,
    publicRegs_four] [satState] using satState

end VG.Proof.TripleDes.PPC64LE.Ecb
