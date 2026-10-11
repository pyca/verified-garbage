import VerifiedGarbage.Proof.Blowfish.Arm.KeyEnc

/-!
# Blowfish on ARMv7: key expansion

`expandKey_correct`: our caller's registers saved, the initial schedule
written, the key XORed into the P-array, the 521 encryptions, and the
registers restored.
-/

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

/-- What key expansion may assume: the key readable, the schedule and the
working space writable, apart, none wrapping around, and a valid key length. -/
structure KeyPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r2), 4168⟩, ⟨State.addr (s.gpr .r3), 64⟩]
  keySch : (⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 4168⟩
  keyBuf : (⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 64⟩
  schBuf : (⟨State.addr (s.gpr .r2), 4168⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 64⟩
  fitKey : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  fitSch : (s.gpr .r2).toNat + 4168 ≤ 2 ^ 32
  fitBuf : (s.gpr .r3).toNat + 64 ≤ 2 ^ 32
  valid : validKey (s.gpr .r1).toNat

/-- What key expansion guarantees. -/
structure KeyPost (s t : State) : Prop where
  regs : ∀ r ∈ preserved, t.gpr r = s.gpr r
  sched : scheduleAt t.mem (State.addr (s.gpr .r2)) =
    expandKey (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)

theorem expandKey_head_eq :
    save ++ initSchedule =
      saved.map (fun p => Instr.str p.1 .r3 p.2) ++
        (([.dp .add .r11 .r2 (imm 0), .dp .add .r12 .r2 (imm pOff)] : List Instr) ++
          (List.range 1042).flatMap initStore) := by
  unfold initSchedule save; rfl

theorem expandKey_correct {s : State} (h : KeyPre s) : WP isa Impl.Blowfish.Arm.expandKey s (KeyPost s) := by
  obtain ⟨hrd, hwr, ks, kb, sb, fKey, fSch, fBuf, valid⟩ := h
  have hL := valid.1
  have hL' := valid.2
  have bR : (⟨State.addr (s.gpr .r3), 64⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have sR : (⟨State.addr (s.gpr .r2), 4168⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  let key := bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
  unfold Impl.Blowfish.Arm.expandKey
  apply WP.seq
  rw [expandKey_head_eq]
  refine Spill.save_slots_ok saved_slots (by omega) (fun d _ hd =>
    ⟨_, bR, Offset.contains_base _ (by omega) (by omega)⟩) ?_
  let s₁ : State := { s with mem := Spill.saveMem s.mem (State.addr (s.gpr .r3)) s.gpr saved }
  have F₁ : Frame [⟨State.addr (s.gpr .r3), 64⟩] s.mem s₁.mem :=
    (Spill.saveMem_frame s.mem _ s.gpr (L := 36) (by decide) saved (by decide)).sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  have S₁ : Spill.Saved s₁.mem (State.addr (s.gpr .r3)) s.gpr saved :=
    Spill.saveMem_saved _ _ _ _ saved_slots
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r11, .r12] (Q := fun t => t.gpr .r11 = s.gpr .r2 + BitVec.ofNat 32 0 ∧
      t.gpr .r12 = s.gpr .r2 + BitVec.ofNat 32 4096 ∧ t.mem = s₁.mem)
    (by brun [pOff]; rfl) (by decide)) fun u₂ ⟨⟨u₂11, u₂12, u₂m⟩, u₂k⟩ => ?_
  have k₂ : Keep [.r11, .r12] s u₂ := u₂k
  refine WP.mono (initSchedule_steps u₂ fSch u₂11 u₂12
    (by rw [k₂.2.2.1]; exact ⟨_, sR, Region.contains_self _ _⟩) 1042 (by decide)) fun u₃ I₃ => ?_
  have k₃ : Keep [.r11, .r12, .r9] s u₃ := k₂.trans I₃.keep
  -- the key into the P-array
  have KE : KeyEnv (s.gpr .r0) (s.gpr .r1).toNat u₃ :=
    ⟨by rw [k₃.gpr (by decide)], by rw [k₃.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by omega, hL', fKey, by rw [keep_reads k₃, hrd]; exact ⟨_, List.mem_cons_self, Region.contains_self _ _⟩⟩
  have dKP : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
      ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 4096, 72⟩ := ks.sub_right (Offset.sub_base _ (by decide))
  apply WP.seq
  refine WP.mono (keyP_run KE (by rw [k₃.gpr (by decide)]) fSch
    (by rw [k₃.2.2.1]; exact ⟨_, sR, Offset.contains_base _ (by decide) (by omega)⟩) dKP) fun u₄ I₄ => ?_
  have k₄ : Keep [.r11, .r12, .r9, .r4, .r5, .r6, .r7, .r8] s u₄ := (k₃.trans I₄.keep).mono (by decide)
  -- the memory so far
  have m₃ : Frame [⟨State.addr (s.gpr .r3), 64⟩, ⟨State.addr (s.gpr .r2), 4168⟩] s.mem u₃.mem := by
    refine (F₁.mono (by simp)).trans ?_
    rw [← u₂m]
    exact I₃.frame.mono (by simp)
  have hkey : bytesAt u₃.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat = key :=
    bytesAt_frame m₃ fun c hc r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact kb _ (Offset.contains_base _ (by omega) (by omega))
      · exact ks _ (Offset.contains_base _ (by omega) (by omega))
  have hP : ∀ i < 18, u₄.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4096 + 4 * i)) 32 =
      initial.getD i 0 ^^^ Spec.Blowfish.keyWord key i := fun i hi => by
    rw [I₄.done i hi, hkey, table_P I₃.bytes hi]
  have hS : ∀ o < 4096, u₄.mem (State.addr (s.gpr .r2) + BitVec.ofNat 64 o) = initByte o := fun o ho => by
    rw [I₄.frame _ fun r hr => ?_, I₃.bytes o (by omega)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact (Offset.disjoint _ (d := o) (n := 1) (e := 4096) (k := 72) (by omega) (by omega) (by decide)) _
      (Region.contains_self _ _)
  have hK : scheduleAt u₄.mem (State.addr (s.gpr .r2)) = keyed key := keyed_of_mem hS hP
  -- the encryptions
  have EE : EncEnv (s.gpr .r2) (s.gpr .r3) s :=
    ⟨fSch, fBuf, ⟨_, sR, Region.contains_self _ _⟩, ⟨_, bR, Region.contains_self _ _⟩, sb⟩
  have F₄ : Frame [⟨State.addr (s.gpr .r2), 4168⟩] s₁.mem u₄.mem := by
    rw [← u₂m]
    exact I₃.frame.trans (I₄.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩)
  apply WP.seq
  refine WP.mono (WP.keep [.r0, .r1, .r2] (Q := fun t => t.gpr .r0 = s.gpr .r2 ∧ t.gpr .r1 = 0#32 ∧
      t.gpr .r2 = 0#32 ∧ t.mem = u₄.mem)
    (by brun [k₄.gpr (show Reg.r2 ∉ [Reg.r11, Reg.r12, Reg.r9, Reg.r4, Reg.r5, Reg.r6, Reg.r7, Reg.r8] by decide)])
    (by decide)) fun u₅ ⟨⟨a0, a1, a2, am⟩, ak⟩ => ?_
  have I₅ : EncInv key (s.gpr .r2) (s.gpr .r3) s.gpr s 0 u₅ := by
    refine ⟨by decide, a0, ?_, by rw [am, hK, ksIter_zero], by rw [a1, a2, ksIter_zero]; rfl,
      saved_frame S₁ (by rw [am]; exact F₄.mono (by simp)) sb, ?_, by rw [ak.2.1, I₄.keep.2.1, I₃.keep.2.1, u₂k.2.1],
      by rw [ak.2.2.1, I₄.keep.2.2.1, I₃.keep.2.2.1, u₂k.2.2.1]⟩
    · rw [ak.gpr (by decide), I₄.keep.gpr (by decide), I₃.keep.gpr (by decide), u₂k.gpr (by decide)]
    · rw [am]
      have F₄' : Frame [⟨State.addr (s.gpr .r3), 64⟩, ⟨State.addr (s.gpr .r2), 4168⟩] u₃.mem u₄.mem := by
        refine I₄.frame.sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub_base _ (by decide)⟩
      exact (m₃.trans F₄').mono (by simp)
  apply WP.seq
  refine WP.mono (encryptP_run EE I₅) fun u₆ I₆ => ?_
  apply WP.seq
  refine WP.mono (encryptS_run EE I₆) fun u₇ I₇ => ?_
  refine WP.mono (restore_run (u := u₇) (by rw [I₇.r3]; omega) (fun d hd => ?_)
    (by rw [I₇.r3]; exact I₇.saved)) fun t ⟨tr, tm⟩ => ⟨tr, by rw [tm, I₇.sched, expandKey_eq]⟩
  rw [I₇.rd, I₇.wr, I₇.r3]
  exact region_in (inRegions_off EE.wrB (by omega))

end VG.Proof.Blowfish.Arm
