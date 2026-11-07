module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Loops
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.CtrSetup
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.CtrFinish
public import VerifiedGarbage.Proof.Aes.PPC64LE.Base
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: CTR's contract permits a final counter store after the shared data loops.
/-! # POWER8 AES CTR correctness -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Proof.Aes.Memory
open VG.Impl.Aes.PPC64LE.Crypto (counterBase)

def ctrGprs : List Reg := [.r0, .r8, .r6, .r7, .r9, .r10, .r11, .r12]

theorem ctr32_ok (s : State) (hs : Proof.Aes.ctr32PPC64LE.pre s) :
    WP isa Impl.Aes.PPC64LE.Crypto.ctr32 s fun t => Keep ctrGprs s t ∧ Proof.Aes.ctr32PPC64LE.post s t := by
  obtain ⟨hrd, hwr, _, hsep, _, hcd, _, _, hbound, hnr⟩ := hs
  let n := (s.gpr .r7).toNat
  let nr := (s.gpr .r4).toNat
  let D := s.gpr .r6
  let C := s.gpr .r5
  let icb := Spec.Gcm.blockAt s.mem C
  have hnrlt : nr < 15 := by rcases hnr with h | h | h <;> omega
  have hnrmin : 1 < nr := by rcases hnr with h | h | h <;> omega
  have hsize : 16*n ≤ 2^64 := by omega
  rw [Impl.Aes.PPC64LE.Crypto.ctr32]
  by_cases hz : s.gpr .r7 = 0
  · refine WP.ite true (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hz]; rfl)
      (fun _ => WP.block_nil ?_) (by simp)
    refine ⟨Keep.refl _ _, ?_⟩
    simp only [Proof.Aes.ctr32PPC64LE, hz, show (0 : BitVec 64).toNat = 0 from rfl,
      Spec.Gcm.blocksAt, List.range_zero, List.map_nil, Spec.Gcm.ctr32, Spec.Gcm.keystream,
      List.length_nil, List.zipWith_nil_left, Nat.repeat]
    exact ⟨True.intro, True.intro⟩
  · refine WP.ite false (by simpa only [eval, State.read, Size.bits, BitVec.setWidth_eq,
        Option.some.injEq, beq_eq_false_iff_ne] using hz) (by simp) (fun _ => ?_)
    have hcr : (⟨s.gpr .r5, 16⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd, hwr]; simp
    refine WP.seq (WP.mono (ctr_setup_ok s hcr) fun base hb => ?_)
    have hc : LoopConfig false true .r0 base nr n D D := by
      refine ⟨⟨hb.zero, hb.mask, ?_, hnrmin, hnrlt, ?_⟩, hsize, ?_, ?_, fun _ => rfl, ?_,
        by rw [hb.zero, BitVec.sub_self]; rfl, by decide, Or.inl rfl⟩
      · rw [hb.effects.keep.gpr (by decide)]
        simp only [nr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · intro j hj
        rw [hb.effects.keep.2.1, hb.effects.keep.2.2, hb.effects.keep.gpr (by decide), hrd, hwr]
        exact ⟨⟨s.gpr .r3, 240⟩, by simp,
          Offset.contains_base _ (d := 16*j) (n := 16) (k := 240) (by omega) (by omega)⟩
      · rw [hb.effects.keep.2.2, hwr]; simp only [List.mem_cons]; exact Or.inr (Or.inl rfl)
      · rw [hb.effects.keep.gpr (by decide)]; exact hsep
      · rw [hb.effects.keep.2.2, hwr]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have hi : LoopInv false true base nr n D D icb 0 base := by
      refine ⟨by omega, Keep.refl _ _, ?_, ?_, Processed.refl _ _ _ _, Frame.refl _ _, hb.mask,
        fun _ => hb.control, ?_, ?_⟩
      · rw [hb.effects.keep.gpr (by decide)]
        simp only [Nat.mul_zero, BitVec.add_zero]; rfl
      · rw [hb.effects.keep.gpr (by decide)]
        simp only [Nat.sub_zero, n, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · intro _; rw [hb.baseValue]
      · intro _; simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hb.word
    refine WP.seq (WP.mono (batches_ok hc hi) fun u hu => ?_)
    have hC : u.gpr .r5 = C := (hu.keep.gpr (by decide)).trans (hb.effects.keep.gpr (by decide))
    have hoff : u.gpr .r11 = 12 := (hu.keep.gpr (by decide)).trans hb.offset
    have hwu : InRegions u.wr (u.gpr .r5 + u.gpr .r11) 4 := by
      rw [hu.keep.2.2, hb.effects.keep.2.2, hC, hoff, hwr]
      exact ⟨⟨C, 16⟩, by exact List.mem_cons_self, Offset.contains_base _ (d := 12) (n := 4) (k := 16) (by decide) (by decide)⟩
    have hstore : WP isa (.block [.storeRev .w .r8 .r5 .r11]) u
        (· = {u with mem := u.mem.writeW (C + 12) (rev32 ((u.gpr .r8).setWidth 32))}) := by
      apply WP.of_runBlock
      rw [runBlock_cons, exec_storeRev_w (by decide) hwu, runStep_some, runBlock_nil, hC, hoff]
      simp only [Option.some.injEq, exists_eq_left']
    refine WP.mono hstore fun t ht => ?_
    subst t
    have hf : Frame [⟨C, 16⟩] u.mem (u.mem.writeW (C+12) (rev32 ((u.gpr .r8).setWidth 32))) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (d := 12) (n := 4) (k := 16) (by decide) (by decide))
    have hp := hu.processed.frame hf (by simpa only [List.mem_singleton, forall_eq] using hcd.symm) hsize
    have hsched : schedule nr base = schedule nr s := by rw [schedule, hb.effects.mem, hb.effects.keep.gpr (by decide)]
    rw [hsched, hb.effects.mem] at hp
    refine ⟨(hb.effects.keep.trans hu.keep).mono (by simp [ctrGprs, loopGprs]), ?_, ?_⟩
    · exact ctr_processed hp
    · apply counter_after (word := (u.gpr .r8).setWidth 32) (hu.counter rfl)
      intro i hi
      change (u.mem.write (C+12) 4 (rev32 ((u.gpr .r8).setWidth 32))) (C + BitVec.ofNat 64 i) = _
      rw [Mem.write, show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl,
        Offset.sub_toNat' C (by omega) (by omega)]
      by_cases hil : i < 12
      · rw [ite_eq_right (show ¬12 ≤ i by omega), ite_eq_right (show ¬2^64+i-12 < 4 by omega), ite_eq_left hil]
        have hframe := hu.frame.trans (Frame.refl _ _)
        rw [hb.effects.mem] at hframe
        exact hframe.bytes (R := ⟨C, 16⟩) (by simpa only [List.mem_singleton, forall_eq] using hcd) (by change 16 ≤ 2^64; decide) hi
      · rw [ite_eq_left (show 12 ≤ i by omega), ite_eq_left (show i-12 < 4 by omega), ite_eq_right hil]

def ctrToGprs : List Reg := [.r0, .r8, .r6, .r7, .r9, .r10, .r11, .r12]

/-- `r9 := r8 - r6`. -/
theorem sub_ok (s : State) : WP isa (.block [.sub .r9 .r8 .r6]) s fun t =>
    t.gpr .r9 = s.gpr .r8 - s.gpr .r6 ∧ Local [.r9] [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, reduceExec, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  exact ⟨RegUpd.gpr_write_self .., Local.write s .r9 _⟩

/-- `r11 := r9`. -/
theorem mov11_ok (s : State) : WP isa (.block [Impl.Aes.PPC64LE.Crypto.mov .r11 .r9]) s fun t =>
    t.gpr .r11 = s.gpr .r9 ∧ Local [.r11] [] s t := by
  apply WP.of_runBlock
  simp only [Impl.Aes.PPC64LE.Crypto.mov, runBlock_cons, reduceExec, runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left']
  exact ⟨by rw [RegUpd.gpr_write_self, BitVec.or_self], Local.write s .r11 _⟩

theorem ctr32To_ok (s : State) (hs : Proof.Aes.ctr32ToPPC64LE.pre s) :
    WP isa Impl.Aes.PPC64LE.Crypto.ctr32To s fun t =>
      Keep ctrToGprs s t ∧ Proof.Aes.ctr32ToPPC64LE.post s t := by
  obtain ⟨hrd, hwr, hsep, hcd, hsd, hbD, hbE, hnr⟩ := hs
  let n := (s.gpr .r7).toNat
  let nr := (s.gpr .r4).toNat
  let D := s.gpr .r6
  let E := s.gpr .r8
  let C := s.gpr .r5
  let icb := Spec.Gcm.blockAt s.mem C
  have hnrlt : nr < 15 := by rcases hnr with h | h | h <;> omega
  have hnrmin : 1 < nr := by rcases hnr with h | h | h <;> omega
  have hsize : 16*n ≤ 2^64 := by omega
  rw [Impl.Aes.PPC64LE.Crypto.ctr32To]
  by_cases hz : s.gpr .r7 = 0
  · refine WP.ite true (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hz]; rfl)
      (fun _ => WP.block_nil ?_) (by simp)
    refine ⟨Keep.refl _ _, ?_⟩
    simp only [Proof.Aes.ctr32ToPPC64LE, hz, show (0 : BitVec 64).toNat = 0 from rfl,
      Spec.Gcm.blocksAt, List.range_zero, List.map_nil, Spec.Gcm.ctr32, Spec.Gcm.keystream,
      List.length_nil, List.zipWith_nil_left, Nat.repeat]
    exact ⟨True.intro, True.intro⟩
  · refine WP.ite false (by simpa only [eval, State.read, Size.bits, BitVec.setWidth_eq,
        Option.some.injEq, beq_eq_false_iff_ne] using hz) (by simp) (fun _ => ?_)
    refine WP.seq ?_
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (sub_ok s) fun s₁ ⟨h9, e₁⟩ => ?_
    have hcr : (⟨s₁.gpr .r5, 16⟩ : Region) ∈ s₁.rd ++ s₁.wr := by
      rw [e₁.keep.gpr (by decide), e₁.keep.2.1, e₁.keep.2.2, hrd, hwr]; simp
    refine WP.mono (ctr_setup_ok s₁ hcr) fun b₁ hb => ?_
    refine WP.mono (mov11_ok b₁) fun base ⟨h11, e₂⟩ => ?_
    have e := (e₁.trans hb.effects).trans e₂
    have hm₁ : s₁.mem = s.mem := e₁.mem
    have h15 : s₁.gpr .r5 = s.gpr .r5 := e₁.keep.gpr (by decide)
    have hzero : base.gpr .r0 = 0 := (e₂.keep.gpr (by decide)).trans hb.zero
    have hmask : base.vpr Impl.Aes.PPC64LE.Crypto.mask = Impl.Aes.PPC64LE.Crypto.byteMask := (e₂.v _ (by simp)).trans hb.mask
    have hc : LoopConfig false true .r11 base nr n D E := by
      refine ⟨⟨hzero, hmask, ?_, hnrmin, hnrlt, ?_⟩, hsize, ?_, ?_, fun _ => rfl, ?_, ?_, by decide, Or.inr hsd⟩
      · rw [e.keep.gpr (by decide)]
        simp only [nr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · intro j hj
        rw [e.keep.2.1, e.keep.2.2, e.keep.gpr (by decide), hrd, hwr]
        exact ⟨⟨s.gpr .r3, 240⟩, by simp,
          Offset.contains_base _ (d := 16*j) (n := 16) (k := 240) (by omega) (by omega)⟩
      · rw [e.keep.2.2, hwr]; simp only [List.mem_cons]; exact Or.inr (Or.inl rfl)
      · rw [e.keep.gpr (by decide)]; exact hsep
      · rw [e.keep.2.1, e.keep.2.2, hrd]
        exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · rw [h11, e₂.keep.gpr (by decide) |>.symm.trans (e₂.keep.gpr (by decide))]
        rw [hb.effects.keep.gpr (by decide), h9]
    have hi : LoopInv false true base nr n D E icb 0 base := by
      refine ⟨by omega, Keep.refl _ _, ?_, ?_, Processed.refl _ _ _ _, Frame.refl _ _, hmask,
        fun _ => ?_, ?_, ?_⟩
      · rw [e.keep.gpr (by decide)]
        simp only [Nat.mul_zero, BitVec.add_zero]; rfl
      · rw [e.keep.gpr (by decide)]
        simp only [Nat.sub_zero, n, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · rw [e₂.v _ (by simp)]; exact hb.control
      · intro _; rw [e₂.v _ (by simp), hb.baseValue, h15, hm₁]
      · intro _
        rw [e₂.keep.gpr (by decide)]
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, h15, hm₁] using hb.word
    refine WP.seq (WP.mono (batches_ok hc hi) fun u hu => ?_)
    have hC : u.gpr .r5 = C := (hu.keep.gpr (by decide)).trans ((e.keep.gpr (by decide)))
    have hstore : WP isa (.block [.li .r11 12, .storeRev .w .r8 .r5 .r11]) u
        (· = {u.write .r11 12 with mem := u.mem.writeW (C + 12) (rev32 ((u.gpr .r8).setWidth 32))}) := by
      have hwu : InRegions (u.write .r11 12).wr ((u.write .r11 12).gpr .r5 + (u.write .r11 12).gpr .r11) 4 := by
        rw [RegUpd.wr_write, RegUpd.gpr_write_self, RegUpd.gpr_write, ite_eq_right (by decide), hC,
          hu.keep.2.2, e.keep.2.2, hwr]
        exact ⟨⟨C, 16⟩, by exact List.mem_cons_self,
          Offset.contains_base _ (d := 12) (n := 4) (k := 16) (by decide) (by decide)⟩
      apply WP.of_runBlock
      rw [runBlock_cons, show exec (.li .r11 12) u = some (u.write .r11 12) from rfl, runStep_some, runBlock_cons, exec_storeRev_w (by decide) hwu,
        runStep_some, runBlock_nil, RegUpd.gpr_write_self, RegUpd.gpr_write, ite_eq_right (by decide), hC,
        RegUpd.gpr_write, ite_eq_right (by decide)]
      simp only [Option.some.injEq, exists_eq_left', RegUpd.mem_write]
    refine WP.mono hstore fun t ht => ?_
    subst t
    have hf : Frame [⟨C, 16⟩] u.mem (u.mem.writeW (C+12) (rev32 ((u.gpr .r8).setWidth 32))) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (d := 12) (n := 4) (k := 16) (by decide) (by decide))
    have hp := hu.processed.frame hf (by simpa only [List.mem_singleton, forall_eq] using hcd.symm) hsize
    have hbm : base.mem = s.mem := e.mem
    have hsched : schedule nr base = schedule nr s := by
      rw [schedule, hbm, e.keep.gpr (by decide)]
    rw [hsched, hbm] at hp
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨fun r hr => ?_, by simp only [RegUpd.rd_write]; rw [hu.keep.2.1, e.keep.2.1],
        by simp only [RegUpd.wr_write]; rw [hu.keep.2.2, e.keep.2.2]⟩
      have h11 : r ≠ .r11 := fun h => hr (by simp [h, ctrToGprs])
      change (u.write .r11 12).gpr r = s.gpr r
      rw [RegUpd.gpr_write, ite_eq_right h11, hu.keep.gpr (fun h => hr (by revert h; cases r <;> decide)),
        e.keep.gpr (fun h => hr (by revert h; cases r <;> decide))]
    · exact ctr_processed hp
    · have hframe := hu.frame
      rw [hbm] at hframe
      apply counter_after (word := (u.gpr .r8).setWidth 32) (hu.counter rfl)
      intro i hi
      change (u.mem.write (C+12) 4 (rev32 ((u.gpr .r8).setWidth 32))) (C + BitVec.ofNat 64 i) = _
      rw [Mem.write, show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl,
        Offset.sub_toNat' C (by omega) (by omega)]
      by_cases hil : i < 12
      · rw [ite_eq_right (show ¬12 ≤ i by omega), ite_eq_right (show ¬2^64+i-12 < 4 by omega), ite_eq_left hil]
        exact hframe.bytes (R := ⟨C, 16⟩) (by simpa only [List.mem_singleton, forall_eq] using hcd)
          (by change 16 ≤ 2^64; decide) hi
      · rw [ite_eq_left (show 12 ≤ i by omega), ite_eq_left (show i-12 < 4 by omega), ite_eq_right hil]

end VG.Proof.Aes.PPC64LE.Crypto
