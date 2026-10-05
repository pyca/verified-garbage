import VerifiedGarbage.Proof.Aes.Arm.Ctr32
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Impl.CmacAes.Arm
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Arm.Call`. -/
section

/-!
# AES-CMAC on ARMv7: calling `vg_aes_ctr32` on one block

`ctr_call`: the frame that pushes `vg_aes_ctr32`'s stack arguments (`n = 1`
in `ra` and the working space `S` in `rb`) around its call, with the counter
block `C` and one data block `D` holding zeros: `D` then holds `CIPH_K(C)`, as
bytes (`Cmac.aesWith`), and only `C`, `D`, `S` and the 8 bytes below the stack
pointer change in memory.
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm

theorem ofBytes_zeros : Spec.Gcm.ofBytes (Spec.Cmac.zeros 16) = 0 := by decide

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 32 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem storeWords_two (m : Mem) (a : BitVec 32) (x y : BitVec 32) :
    storeWords m a [x, y] = (m.writeW (State.addr a) x).writeW (State.addr (a + 4)) y := rfl

/-- Addresses below a pointer do not wrap. -/
theorem addr_sub {a : BitVec 32} {k : Nat} (h : k ≤ a.toNat) :
    State.addr (a - BitVec.ofNat 32 k) = State.addr a - BitVec.ofNat 64 k := by
  simp only [State.addr]
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt (a := a.toNat) (by omega)]
  omega

/-- The 8 bytes below the stack pointer, where the frame pushes the stack arguments. -/
abbrev below (s : State) : Region := ⟨State.addr s.sp - 8, 8⟩

/-- What a call of `vg_aes_ctr32` on one block needs. -/
structure CallPre (s : State) (W C D S : BitVec 32) (R : Nat) (ra rb : Reg) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = C
  r3 : s.gpr .r3 = D
  hra : s.gpr ra = 1
  hrb : s.gpr rb = S
  regs : regList [ra, rb] = true
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hsp : 8 ≤ s.sp.toNat
  wc : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  wd : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr D, 16⟩
  ws : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  cd : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr D, 16⟩
  cs : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  ds : (⟨State.addr D, 16⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  bw : (VG.Proof.CmacAes.Arm.below s).Disjoint ⟨State.addr W, 240⟩
  bc : (VG.Proof.CmacAes.Arm.below s).Disjoint ⟨State.addr C, 16⟩
  bd : (VG.Proof.CmacAes.Arm.below s).Disjoint ⟨State.addr D, 16⟩
  bs : (VG.Proof.CmacAes.Arm.below s).Disjoint ⟨State.addr S, 2048⟩
  hW : W.toNat + 240 ≤ 2 ^ 32
  hC : C.toNat + 16 ≤ 2 ^ 32
  hD : D.toNat + 16 ≤ 2 ^ 32
  hS : S.toNat + 2048 ≤ 2 ^ 32
  reads : Covers [⟨State.addr W, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 16⟩, ⟨State.addr D, 16⟩, ⟨State.addr S, 2048⟩] s.wr
  zero : Spec.Aes.bytesAt s.mem (State.addr D) 16 = Spec.Cmac.zeros 16

/-- What a call of `vg_aes_ctr32` on one block leaves. -/
structure CallPost (s : State) (W C D S : BitVec 32) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 16⟩, ⟨State.addr D, 16⟩, ⟨State.addr S, 2048⟩, VG.Proof.CmacAes.Arm.below s] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (State.addr D) 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (State.addr W) (16 * (R + 1)))
      (Spec.Aes.bytesAt s.mem (State.addr C) 16)

theorem e8 (ra rb : Reg) : BitVec.ofNat 32 (4 * [ra, rb].length) = 8 := rfl

/-- The regions `vg_aes_ctr32` is called with. -/
abbrev ctrRd (s : State) (W : BitVec 32) : List Region := [⟨State.addr W, 240⟩, VG.Proof.CmacAes.Arm.below s]
abbrev ctrWr (C D S : BitVec 32) : List Region :=
  [⟨State.addr C, 16⟩, ⟨State.addr D, 16⟩, ⟨State.addr S, 2048⟩]

/-- The state `vg_aes_ctr32` runs from, with the permissions it is given. -/
abbrev ctrView (s : State) (ra rb : Reg) (W C D S : BitVec 32) : State :=
  (pushed [ra, rb] s).callEntry.withRegions (VG.Proof.CmacAes.Arm.ctrRd s W) (VG.Proof.CmacAes.Arm.ctrWr C D S)

namespace CallPre
variable {s : State} {W C D S : BitVec 32} {R : Nat} {ra rb : Reg} (h : VG.Proof.CmacAes.Arm.CallPre s W C D S R ra rb)
include h

theorem hA : State.addr (s.sp - 8) = State.addr s.sp - 8 := VG.Proof.CmacAes.Arm.addr_sub h.hsp

theorem hspA : (s.sp - 8).toNat = s.sp.toNat - 8 :=
  BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact h.hsp)

theorem hA4 : State.addr (s.sp - 8 + BitVec.ofNat 32 4) = State.addr s.sp - 8 + 4 := by
  have := s.sp.isLt
  rw [addr_add (by rw [h.hspA]; omega), h.hA]; rfl

theorem amem : (pushed [ra, rb] s).mem =
    (s.mem.writeW (State.addr s.sp - 8) (1 : BitVec 32)).writeW (State.addr s.sp - 8 + 4) S := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [ra, rb].length)) [s.gpr ra, s.gpr rb] = _
  rw [VG.Proof.CmacAes.Arm.e8, VG.Proof.CmacAes.Arm.storeWords_two, h.hA, show (s.sp - 8 + 4 : BitVec 32) = s.sp - 8 + BitVec.ofNat 32 4 from rfl, h.hA4,
    h.hra, h.hrb]

theorem fA : Frame [VG.Proof.CmacAes.Arm.below s] s.mem (pushed [ra, rb] s).mem := by
  rw [h.amem]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left]; decide

omit h in
theorem sp_view : (VG.Proof.CmacAes.Arm.ctrView s ra rb W C D S).sp = s.sp - 8 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, VG.Proof.CmacAes.Arm.e8]

theorem arg0 : stackArg (VG.Proof.CmacAes.Arm.ctrView s ra rb W C D S) 0 = 1 := by
  have := h.hsp
  rw [stackArg, show stackArgAddr (VG.Proof.CmacAes.Arm.ctrView s ra rb W C D S) 0 = State.addr s.sp - 8 by
      unfold stackArgAddr; rw [VG.Proof.CmacAes.Arm.CallPre.sp_view, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from
        BitVec.add_zero _, h.hA],
    State.withRegions_mem, State.callEntry_mem, h.amem, Mem.readW_writeW_sep
    (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem arg1 : stackArg (VG.Proof.CmacAes.Arm.ctrView s ra rb W C D S) 1 = S := by
  rw [stackArg, show stackArgAddr (VG.Proof.CmacAes.Arm.ctrView s ra rb W C D S) 1 = State.addr s.sp - 8 + 4 by
      unfold stackArgAddr; rw [VG.Proof.CmacAes.Arm.CallPre.sp_view]; exact h.hA4,
    State.withRegions_mem, State.callEntry_mem, h.amem, Mem.readW_writeW_self32]

omit h in
theorem view_gpr (r : Reg) (hr : r ∉ linkRegs) : (VG.Proof.CmacAes.Arm.ctrView s ra rb W C D S).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

theorem pre : Proof.Aes.ctr32Arm.pre (VG.Proof.CmacAes.Arm.ctrView s ra rb W C D S) := by
  have hR := VG.Proof.CmacAes.Arm.toNat_rounds h.rounds
  have hsa : stackArgAddr (VG.Proof.CmacAes.Arm.ctrView s ra rb W C D S) 0 = State.addr s.sp - 8 := by
    unfold stackArgAddr; rw [VG.Proof.CmacAes.Arm.CallPre.sp_view, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from
      BitVec.add_zero _, h.hA]
  simp only [Proof.Aes.ctr32Arm, h.arg0, h.arg1, hsa, VG.Proof.CmacAes.Arm.CallPre.view_gpr .r0 (by decide), VG.Proof.CmacAes.Arm.CallPre.view_gpr .r1 (by decide),
    VG.Proof.CmacAes.Arm.CallPre.view_gpr .r2 (by decide), VG.Proof.CmacAes.Arm.CallPre.view_gpr .r3 (by decide), h.r0, h.r1, h.r2, h.r3, hR, State.withRegions_rd,
    State.withRegions_wr, VG.Proof.CmacAes.Arm.CallPre.sp_view, h.hspA, show (1 : BitVec 32).toNat = 1 from rfl, Nat.mul_one]
  refine ⟨trivial, trivial, h.wc, ?_, h.ws, ?_, h.cs, ?_, h.bc.symm, ?_, h.bs.symm, h.hW, h.hC, ?_, h.hS, ?_,
    h.rounds⟩
  · simpa using h.wd
  · simpa using h.cd
  · simpa using h.ds
  · simpa [VG.Proof.CmacAes.Arm.below] using h.bd.symm
  · simpa using h.hD
  · have := s.sp.isLt; omega

/-- The stack arguments are the frame. -/
theorem cov : Covers (VG.Proof.CmacAes.Arm.ctrRd s W ++ VG.Proof.CmacAes.Arm.ctrWr C D S) ((pushed [ra, rb] s).rd ++ (pushed [ra, rb] s).wr) := by
  intro x n' ⟨r, hr, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨r', hr', hc'⟩ := h.reads x n' ⟨_, List.mem_singleton_self _, hc⟩
    refine ⟨r', ?_, hc'⟩
    rcases List.mem_append.mp hr' with h' | h'
    · exact List.mem_append_left _ h'
    · exact List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ h')
  · refine ⟨_, List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_self ..), ?_⟩
    rwa [VG.Proof.CmacAes.Arm.e8, h.hA]
  all_goals
    obtain ⟨r', hr', hc'⟩ := h.writes x n' ⟨_, by simp, hc⟩
    exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr'), hc'⟩

theorem covW : Covers (VG.Proof.CmacAes.Arm.ctrWr C D S) (pushed [ra, rb] s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

end CallPre

theorem ctr_noCalls : Impl.Aes.Arm.ctr32.noCalls = true := by decide +kernel

theorem ctr_call {s : State} {W C D S : BitVec 32} {R : Nat} {ra rb : Reg} (h : VG.Proof.CmacAes.Arm.CallPre s W C D S R ra rb) :
    WP isa (ctrCall ra rb) s (VG.Proof.CmacAes.Arm.CallPost s W C D S R) := by
  refine WP.frame (rs := [ra, rb]) (r := ra) h.regs (by simpa using h.hsp) (by simp) ?_
  refine WP.call (k := Proof.Aes.ctr32Arm) Proof.Aes.Arm.ctr32_correct
    (rd := VG.Proof.CmacAes.Arm.ctrRd s W) (wr := VG.Proof.CmacAes.Arm.ctrWr C D S) h.pre h.cov h.covW ?_ VG.Proof.CmacAes.Arm.ctr_noCalls
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  have hR := VG.Proof.CmacAes.Arm.toNat_rounds h.rounds
  have hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  -- The memory of the frame.
  have fBelow : Frame [⟨State.addr C, 16⟩, ⟨State.addr D, 16⟩, ⟨State.addr S, 2048⟩]
      (pushed [ra, rb] s).mem s₂.mem := hf
  have bytesW : Spec.Aes.bytesAt (pushed [ra, rb] s).mem (State.addr W) (16 * (R + 1)) =
      Spec.Aes.bytesAt s.mem (State.addr W) (16 * (R + 1)) :=
    Proof.Cmac.bytesAt_frame h.fA (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bw.symm.sub_left (Region.sub_prefix hR')).symm.symm) (by omega)
  have bytesC : Spec.Aes.bytesAt (pushed [ra, rb] s).mem (State.addr C) 16 =
      Spec.Aes.bytesAt s.mem (State.addr C) 16 :=
    Proof.Cmac.bytesAt_frame16 h.fA (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bc.symm)
  have bytesD : Spec.Aes.bytesAt (pushed [ra, rb] s).mem (State.addr D) 16 =
      Spec.Aes.bytesAt s.mem (State.addr D) 16 :=
    Proof.Cmac.bytesAt_frame16 h.fA (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bd.symm)
  obtain ⟨hdata, -⟩ := hpost
  simp only [State.withRegions_mem, State.callEntry_mem, CallPre.view_gpr .r0 (by decide),
    CallPre.view_gpr .r1 (by decide), CallPre.view_gpr .r2 (by decide), CallPre.view_gpr .r3 (by decide), h.r0, h.r1, h.r2,
    h.r3, hR, h.arg0, show (1 : BitVec 32).toNat = 1 from rfl] at hdata
  have one : ∀ m : Mem, Spec.Gcm.blocksAt m (State.addr D) 1 = [Spec.Gcm.blockAt m (State.addr D)] :=
    fun m => by simp [Spec.Gcm.blocksAt]
  have bD : Spec.Gcm.blockAt (pushed [ra, rb] s).mem (State.addr D) = 0 := by
    rw [Spec.Gcm.blockAt, bytesD, h.zero, VG.Proof.CmacAes.Arm.ofBytes_zeros]
  rw [one, one, bD, Proof.Cmac.ctr32_one, List.cons.injEq] at hdata
  -- The register the pop loads is the one pushed.
  have slot : s₂.mem.readW (State.addr (pushed [ra, rb] s).sp) 32 = 1 := by
    rw [pushed_sp, VG.Proof.CmacAes.Arm.e8, h.hA]
    have := fBelow.readW (r := ⟨State.addr s.sp - 8, 4⟩) (a := State.addr s.sp - 8) (w := 32)
      (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (h.bc.sub_left (Region.sub_prefix (by decide))).symm.symm
      · exact (h.bd.sub_left (Region.sub_prefix (by decide)))
      · exact (h.bs.sub_left (Region.sub_prefix (by decide)))) (by decide)
    rw [this, h.amem, Mem.readW_writeW_sep
      (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, pushed_sp, VG.Proof.CmacAes.Arm.e8]; exact BitVec.sub_add_cancel _ _
  · by_cases hra : r = ra
    · subst hra
      show (s₂.setReg r (s₂.mem.readW (State.addr s₂.sp) 32)).gpr r = _
      rw [VG.Arm.RegUpd.gpr_setReg_self, hsp₂, slot, h.hra]
    · rw [popped_gpr hra, hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    refine (h.fA.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (fBelow.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem, Proof.Cmac.bytesAt_blockAt, hdata.1, Spec.Gcm.blockAt, bytesW, bytesC,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _)]

/-- Calls of `vg_aes_ctr32` on one block, with the same arguments and stack
pointer in both runs, are constant time. -/
theorem ctr_rel {W C D S sp₀ : BitVec 32} {R : Nat} {ra rb : Reg} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.CmacAes.Arm.CallPre s₁ W C D S R ra rb ∧ VG.Proof.CmacAes.Arm.CallPre s₂ W C D S R ra rb ∧ s₁.sp = sp₀ ∧
      s₂.sp = sp₀) :
    RelCT isa P (ctrCall ra rb) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, h₁, h₂⟩ := h _ _ hp; rw [h₁, h₂]) ?_
  refine RelCT.call Proof.Aes.Arm.ctr32_correct Proof.Aes.Arm.ctr32_ct
    [⟨State.addr W, 240⟩, ⟨State.addr sp₀ - 8, 8⟩] (VG.Proof.CmacAes.Arm.ctrWr C D S) fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_
  obtain ⟨h₁, h₂, sp₁, sp₂⟩ := h _ _ hp
  rw [push_pushed h₁.regs (by simpa using h₁.hsp), Option.some.injEq] at pa
  rw [push_pushed h₂.regs (by simpa using h₂.hsp), Option.some.injEq] at pb
  subst pa pb
  have e₁ : VG.Proof.CmacAes.Arm.ctrRd s₁ W = [⟨State.addr W, 240⟩, ⟨State.addr sp₀ - 8, 8⟩] := by rw [VG.Proof.CmacAes.Arm.ctrRd, VG.Proof.CmacAes.Arm.below, sp₁]
  have e₂ : VG.Proof.CmacAes.Arm.ctrRd s₂ W = [⟨State.addr W, 240⟩, ⟨State.addr sp₀ - 8, 8⟩] := by rw [VG.Proof.CmacAes.Arm.ctrRd, VG.Proof.CmacAes.Arm.below, sp₂]
  have p₁ := h₁.pre (C := C) (D := D) (S := S)
  have p₂ := h₂.pre (C := C) (D := D) (S := S)
  rw [VG.Proof.CmacAes.Arm.ctrView, e₁] at p₁
  rw [VG.Proof.CmacAes.Arm.ctrView, e₂] at p₂
  refine ⟨p₁, p₂, ?_, e₁ ▸ h₁.cov, h₁.covW, e₂ ▸ h₂.cov, h₂.covW⟩
  have a₁ := h₁.arg0 (C := C) (D := D) (S := S)
  have b₁ := h₁.arg1 (C := C) (D := D) (S := S)
  have a₂ := h₂.arg0 (C := C) (D := D) (S := S)
  have b₂ := h₂.arg1 (C := C) (D := D) (S := S)
  rw [VG.Proof.CmacAes.Arm.ctrView, e₁] at a₁ b₁
  rw [VG.Proof.CmacAes.Arm.ctrView, e₂] at a₂ b₂
  simp only [Proof.Aes.ctr32Arm, a₁, b₁, a₂, b₂, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, pushed_sp, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), pushed_gpr, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1,
    h₂.r2, h₂.r3, sp₁, sp₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.CmacAes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Arm.Words`. -/
section

/-!
# AES-CMAC on ARMv7: blocks formed a word at a time

Weakest preconditions of the instruction sequences the functions build blocks
with: the XOR of the blocks at `pb + pd` and `qb + qd` stored at `cb + cd`
through two temporaries (`xorBlk`, which leaves `Cmac.xor4Mem`), and four
stores of a zero register (`zeroBlk`, which leaves `Cmac.zero4`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd WP.cons op2_reg wp_ldr wp_str)

/-- The words of the blocks at `pb + pd` and `qb + qd`, XORed through `t₁`
and `t₂` and stored at `cb + cd`. -/
def xorBlk (t₁ t₂ pb qb cb : Reg) (pd qd cd : Nat) : List Instr :=
  [.ldr t₁ pb pd, .ldr t₂ qb qd, .dp .eor t₁ t₁ (.reg t₂), .str t₁ cb cd,
   .ldr t₁ pb (pd + 4), .ldr t₂ qb (qd + 4), .dp .eor t₁ t₁ (.reg t₂), .str t₁ cb (cd + 4),
   .ldr t₁ pb (pd + 8), .ldr t₂ qb (qd + 8), .dp .eor t₁ t₁ (.reg t₂), .str t₁ cb (cd + 8),
   .ldr t₁ pb (pd + 12), .ldr t₂ qb (qd + 12), .dp .eor t₁ t₁ (.reg t₂), .str t₁ cb (cd + 12)]

/-- `z` stored in the four words at `b + d`. -/
def zeroBlk (z b : Reg) (d : Nat) : List Instr :=
  [.str z b d, .str z b (d + 4), .str z b (d + 8), .str z b (d + 12)]

/-- `s'` is `s` with memory `m`, and `t₁` and `t₂` clobbered. -/
structure Step (s s' : State) (t₁ t₂ : Reg) (m : Mem) : Prop where
  gpr : ∀ r, r ≠ t₁ → r ≠ t₂ → s'.gpr r = s.gpr r
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2} {y : BitVec 32}
    (ho : o.eval s = some y) (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho]) (k _ (MdStream.Arm.Upd.setReg _ _ _))

/-- One word. -/
theorem xw_ok {t₁ t₂ pb qb cb : Reg} {pd qd cd : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    {P Q' C : Addr} (h12 : t₁ ≠ t₂) (hq : qb ≠ t₁) (hc₁ : cb ≠ t₁) (hc₂ : cb ≠ t₂)
    (hpd : pd < 4096) (hqd : qd < 4096) (hcd : cd < 4096)
    (hP : State.addr (s.gpr pb + BitVec.ofNat 32 pd) = P) (hQ : State.addr (s.gpr qb + BitVec.ofNat 32 qd) = Q')
    (hC : State.addr (s.gpr cb + BitVec.ofNat 32 cd) = C)
    (rP : InRegions (s.rd ++ s.wr) P 4) (rQ : InRegions (s.rd ++ s.wr) Q' 4) (wC : InRegions s.wr C 4)
    (k : ∀ s', VG.Proof.CmacAes.Arm.Step s s' t₁ t₂ (s.mem.writeW C (s.mem.readW P 32 ^^^ s.mem.readW Q' 32)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.ldr t₁ pb pd :: .ldr t₂ qb qd :: .dp .eor t₁ t₁ (.reg t₂) :: .str t₁ cb cd :: is)) s Q := by
  subst hQ hC
  refine wp_ldr hpd hP rP fun s₁ u₁ => ?_
  refine wp_ldr hqd (by rw [u₁.other _ hq]) (by rw [u₁.rd, u₁.wr]; exact rQ) fun s₂ u₂ => ?_
  refine VG.Proof.CmacAes.Arm.wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_str hcd (by rw [u₃.other _ hc₁, u₂.other _ hc₂, u₁.other _ hc₁])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact wC) fun s₄ u₄ => k s₄ ⟨fun r h₁ h₂ => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.gpr, u₃.other _ h₁, u₂.other _ h₂, u₁.other _ h₁]
  · rw [u₄.mem, u₃.gpr, u₂.other _ h12, u₂.gpr, u₁.gpr, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-- Word `i` of a block that does not wrap the 32-bit space. -/
theorem addr_word {b : BitVec 32} {d : Nat} (i : Nat) (h : b.toNat + d + 16 ≤ 2 ^ 32) (hi : i ≤ 12) :
    State.addr (b + BitVec.ofNat 32 (d + i)) = State.addr b + BitVec.ofNat 64 d + BitVec.ofNat 64 i := by
  rw [addr_add (by omega), Offset.add_add]

theorem in_word {rs : List Region} {P : Addr} (h : Covers [⟨P, 16⟩] rs) {i : Nat} (hi : i ≤ 12) :
    InRegions rs (P + BitVec.ofNat 64 i) 4 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base P (by omega) (by omega)⟩

theorem in_word0 {rs : List Region} {P : Addr} (h : Covers [⟨P, 16⟩] rs) : InRegions rs P 4 := by
  have c := Offset.contains_base P (d := 0) (n := 4) (k := 16) (by decide) (by decide)
  rw [show P + BitVec.ofNat 64 0 = P from BitVec.add_zero P] at c
  exact h _ _ ⟨_, List.mem_singleton_self _, c⟩

/-- The XOR of the blocks at `pb + pd` and `qb + qd`, stored at `cb + cd`. -/
theorem xorBlk_ok {t₁ t₂ pb qb cb : Reg} {pd qd cd : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (h12 : t₁ ≠ t₂) (hp₁ : pb ≠ t₁) (hp₂ : pb ≠ t₂) (hq₁ : qb ≠ t₁) (hq₂ : qb ≠ t₂) (hc₁ : cb ≠ t₁)
    (hc₂ : cb ≠ t₂) (hpd : pd + 12 < 4096) (hqd : qd + 12 < 4096) (hcd : cd + 12 < 4096)
    (fp : (s.gpr pb).toNat + pd + 16 ≤ 2 ^ 32) (fq : (s.gpr qb).toNat + qd + 16 ≤ 2 ^ 32)
    (fc : (s.gpr cb).toNat + cd + 16 ≤ 2 ^ 32)
    (rP : Covers [⟨State.addr (s.gpr pb) + BitVec.ofNat 64 pd, 16⟩] (s.rd ++ s.wr))
    (rQ : Covers [⟨State.addr (s.gpr qb) + BitVec.ofNat 64 qd, 16⟩] (s.rd ++ s.wr))
    (wC : Covers [⟨State.addr (s.gpr cb) + BitVec.ofNat 64 cd, 16⟩] s.wr)
    (k : ∀ s', VG.Proof.CmacAes.Arm.Step s s' t₁ t₂ (Proof.Cmac.xor4Mem s.mem (State.addr (s.gpr cb) + BitVec.ofNat 64 cd)
        (State.addr (s.gpr pb) + BitVec.ofNat 64 pd) (State.addr (s.gpr qb) + BitVec.ofNat 64 qd)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (VG.Proof.CmacAes.Arm.xorBlk t₁ t₂ pb qb cb pd qd cd ++ is)) s Q := by
  simp only [VG.Proof.CmacAes.Arm.xorBlk, List.cons_append, List.nil_append]
  refine VG.Proof.CmacAes.Arm.xw_ok h12 hq₁ hc₁ hc₂ (by omega) (by omega) (by omega) (addr_add (by omega)) (addr_add (by omega))
    (addr_add (by omega)) (VG.Proof.CmacAes.Arm.in_word0 rP) (VG.Proof.CmacAes.Arm.in_word0 rQ) (VG.Proof.CmacAes.Arm.in_word0 wC) fun s₁ g₁ => ?_
  have e₁ : ∀ r, r ≠ t₁ → r ≠ t₂ → s₁.gpr r = s.gpr r := g₁.gpr
  refine VG.Proof.CmacAes.Arm.xw_ok (P := State.addr (s.gpr pb) + BitVec.ofNat 64 pd + BitVec.ofNat 64 4)
    (Q' := State.addr (s.gpr qb) + BitVec.ofNat 64 qd + BitVec.ofNat 64 4)
    (C := State.addr (s.gpr cb) + BitVec.ofNat 64 cd + BitVec.ofNat 64 4) h12 hq₁ hc₁ hc₂ (by omega) (by omega) (by omega)
    (by rw [e₁ _ hp₁ hp₂]; exact VG.Proof.CmacAes.Arm.addr_word 4 fp (by decide))
    (by rw [e₁ _ hq₁ hq₂]; exact VG.Proof.CmacAes.Arm.addr_word 4 fq (by decide))
    (by rw [e₁ _ hc₁ hc₂]; exact VG.Proof.CmacAes.Arm.addr_word 4 fc (by decide))
    (by rw [g₁.rd, g₁.wr]; exact VG.Proof.CmacAes.Arm.in_word rP (by decide)) (by rw [g₁.rd, g₁.wr]; exact VG.Proof.CmacAes.Arm.in_word rQ (by decide))
    (by rw [g₁.wr]; exact VG.Proof.CmacAes.Arm.in_word wC (by decide)) fun s₂ g₂ => ?_
  have e₂ : ∀ r, r ≠ t₁ → r ≠ t₂ → s₂.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g₂.gpr r h₁ h₂, e₁ r h₁ h₂]
  refine VG.Proof.CmacAes.Arm.xw_ok (P := State.addr (s.gpr pb) + BitVec.ofNat 64 pd + BitVec.ofNat 64 8)
    (Q' := State.addr (s.gpr qb) + BitVec.ofNat 64 qd + BitVec.ofNat 64 8)
    (C := State.addr (s.gpr cb) + BitVec.ofNat 64 cd + BitVec.ofNat 64 8) h12 hq₁ hc₁ hc₂ (by omega) (by omega) (by omega)
    (by rw [e₂ _ hp₁ hp₂]; exact VG.Proof.CmacAes.Arm.addr_word 8 fp (by decide))
    (by rw [e₂ _ hq₁ hq₂]; exact VG.Proof.CmacAes.Arm.addr_word 8 fq (by decide))
    (by rw [e₂ _ hc₁ hc₂]; exact VG.Proof.CmacAes.Arm.addr_word 8 fc (by decide))
    (by rw [g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact VG.Proof.CmacAes.Arm.in_word rP (by decide))
    (by rw [g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact VG.Proof.CmacAes.Arm.in_word rQ (by decide))
    (by rw [g₂.wr, g₁.wr]; exact VG.Proof.CmacAes.Arm.in_word wC (by decide)) fun s₃ g₃ => ?_
  have e₃ : ∀ r, r ≠ t₁ → r ≠ t₂ → s₃.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g₃.gpr r h₁ h₂, e₂ r h₁ h₂]
  refine VG.Proof.CmacAes.Arm.xw_ok (P := State.addr (s.gpr pb) + BitVec.ofNat 64 pd + BitVec.ofNat 64 12)
    (Q' := State.addr (s.gpr qb) + BitVec.ofNat 64 qd + BitVec.ofNat 64 12)
    (C := State.addr (s.gpr cb) + BitVec.ofNat 64 cd + BitVec.ofNat 64 12) h12 hq₁ hc₁ hc₂ (by omega) (by omega) (by omega)
    (by rw [e₃ _ hp₁ hp₂]; exact VG.Proof.CmacAes.Arm.addr_word 12 fp (by decide))
    (by rw [e₃ _ hq₁ hq₂]; exact VG.Proof.CmacAes.Arm.addr_word 12 fq (by decide))
    (by rw [e₃ _ hc₁ hc₂]; exact VG.Proof.CmacAes.Arm.addr_word 12 fc (by decide))
    (by rw [g₃.rd, g₃.wr, g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact VG.Proof.CmacAes.Arm.in_word rP (by decide))
    (by rw [g₃.rd, g₃.wr, g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact VG.Proof.CmacAes.Arm.in_word rQ (by decide))
    (by rw [g₃.wr, g₂.wr, g₁.wr]; exact VG.Proof.CmacAes.Arm.in_word wC (by decide)) fun s₄ g₄ => k s₄ ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r h₁ h₂; rw [g₄.gpr r h₁ h₂, e₃ r h₁ h₂]
  · rw [g₄.mem, g₃.mem, g₂.mem, g₁.mem]; rfl
  · rw [g₄.rd, g₃.rd, g₂.rd, g₁.rd]
  · rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr]
  · rw [g₄.sp, g₃.sp, g₂.sp, g₁.sp]

/-- The block at `b + d` zeroed, from a register `z` holding zero. -/
theorem zeroBlk_ok {z b : Reg} {d : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hz : s.gpr z = 0) (hd : d + 12 < 4096) (fb : (s.gpr b).toNat + d + 16 ≤ 2 ^ 32)
    (wB : Covers [⟨State.addr (s.gpr b) + BitVec.ofNat 64 d, 16⟩] s.wr)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = Proof.Cmac.zero4 s.mem (State.addr (s.gpr b) + BitVec.ofNat 64 d) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (VG.Proof.CmacAes.Arm.zeroBlk z b d ++ is)) s Q := by
  simp only [VG.Proof.CmacAes.Arm.zeroBlk, List.cons_append, List.nil_append]
  refine wp_str (by omega) (addr_add (by omega)) (VG.Proof.CmacAes.Arm.in_word0 wB) fun s₁ u₁ => ?_
  refine wp_str (a := State.addr (s.gpr b) + BitVec.ofNat 64 d + BitVec.ofNat 64 4) (by omega)
    (by rw [u₁.gpr]; exact VG.Proof.CmacAes.Arm.addr_word 4 fb (by decide))
    (by rw [u₁.wr]; exact VG.Proof.CmacAes.Arm.in_word wB (by decide)) fun s₂ u₂ => ?_
  refine wp_str (a := State.addr (s.gpr b) + BitVec.ofNat 64 d + BitVec.ofNat 64 8) (by omega)
    (by rw [u₂.gpr, u₁.gpr]; exact VG.Proof.CmacAes.Arm.addr_word 8 fb (by decide))
    (by rw [u₂.wr, u₁.wr]; exact VG.Proof.CmacAes.Arm.in_word wB (by decide)) fun s₃ u₃ => ?_
  refine wp_str (a := State.addr (s.gpr b) + BitVec.ofNat 64 d + BitVec.ofNat 64 12) (by omega)
    (by rw [u₃.gpr, u₂.gpr, u₁.gpr]; exact VG.Proof.CmacAes.Arm.addr_word 12 fb (by decide))
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact VG.Proof.CmacAes.Arm.in_word wB (by decide)) fun s₄ u₄ => k s₄ ?_ ?_ ?_ ?_ ?_
  · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr, hz]; rfl
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]

end VG.Proof.CmacAes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Arm.UpdateLoop`. -/
section

section

section

/-!
# AES-CMAC on ARMv7: the contracts the proofs are written against

The artifacts' contracts are the shared ones of `Spec/Cmac/Contract.lean`,
which imply these (`Verified.lean`). Each function pushes `vg_aes_ctr32`'s two
stack arguments in the 8 bytes below the stack pointer, which may not overlap
any buffer.
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm

/-- `CIPH_K` for AES with the key schedule at `w` for `R` rounds, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) (R : Nat) : Spec.Cmac.Cipher :=
  Spec.Cmac.aesWith R (Spec.Aes.bytesAt m w (16 * (R + 1)))

/-- `vg_cmac_aes_update(schedule = r0, rounds = r1, state = r2, data = r3, n = [sp], scratch = [sp + 4])`. -/
def updateArm : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let state : Region := ⟨State.addr (s.gpr .r2), 16⟩
    let data : Region := ⟨State.addr (s.gpr .r3), 16 * (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 2176⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩
    s.rd = [sched, data, args] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ state.Disjoint args ∧ scr.Disjoint args ∧
      below.Disjoint sched ∧ below.Disjoint data ∧ below.Disjoint state ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 16 * (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 2176 ≤ 2 ^ 32 ∧
      8 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r2)) 16 =
      Spec.Cmac.chain (VG.Proof.CmacAes.Arm.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
        (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r2)) 16)
        (Spec.Cmac.blocksAt s.mem (State.addr (s.gpr .r3)) 16 (stackArg s 0).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-- `vg_cmac_aes_subkeys(schedule = r0, rounds = r1, subkeys = r2, scratch = r3)`. -/
def subkeysArm : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let subk : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let scr : Region := ⟨State.addr (s.gpr .r3), 2176⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩
    s.rd = [sched] ∧ s.wr = [subk, scr] ∧
      sched.Disjoint subk ∧ sched.Disjoint scr ∧ subk.Disjoint scr ∧
      below.Disjoint sched ∧ below.Disjoint subk ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 2176 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    let ks := Spec.Cmac.subkeys (VG.Proof.CmacAes.Arm.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) 16
    Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r2)) 32 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3

/-- `vg_cmac_aes_finalize(key = r0, rounds = r1, state = r2, last = r3, last_len = [sp], scratch = [sp + 4])`. -/
def finalizeArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 272⟩
    let state : Region := ⟨State.addr (s.gpr .r2), 16⟩
    let last : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 2176⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩
    s.rd = [key, last, args] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ state.Disjoint args ∧ scr.Disjoint args ∧
      below.Disjoint key ∧ below.Disjoint last ∧ below.Disjoint state ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + 272 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 2176 ≤ 2 ^ 32 ∧
      8 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14) ∧
      (stackArg s 0).toNat ≤ 16
  post s s' :=
    let ciph := VG.Proof.CmacAes.Arm.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0) + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < (stackArg s 0).toNat) →
      Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r2)) 16 =
        Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r2)) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.CmacAes.Arm

end

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_update`, the blocks before and in the loop

The invariant after `k` blocks (`LInv`): the registers hold the arguments
(`r7` the next block, `r8` the blocks left), only the state, the first 2064
bytes of the scratch buffer and the 8 bytes below the stack pointer have
changed since the registers were saved, and the state is the chaining value
after the first `k` blocks.
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_subs wp_cmp wp_ldrSp saveMem
  saveList_ok saveMem_frame readW_writeW_save cmp0 ofNat_beq_zero sub_ofNat)

section
variable (s₀ : State)

abbrev W : BitVec 32 := s₀.gpr .r0
abbrev R : Nat := (s₀.gpr .r1).toNat
abbrev St : BitVec 32 := s₀.gpr .r2
abbrev Dp : BitVec 32 := s₀.gpr .r3
abbrev N : Nat := (stackArg s₀ 0).toNat
abbrev S : BitVec 32 := stackArg s₀ 1

abbrev schR : Region := ⟨State.addr (VG.Proof.CmacAes.Arm.W s₀), 240⟩
abbrev stR : Region := ⟨State.addr (VG.Proof.CmacAes.Arm.St s₀), 16⟩
abbrev dataR : Region := ⟨State.addr (VG.Proof.CmacAes.Arm.Dp s₀), 16 * VG.Proof.CmacAes.Arm.N s₀⟩
abbrev scrR : Region := ⟨State.addr (VG.Proof.CmacAes.Arm.S s₀), 2176⟩
abbrev argsR : Region := ⟨stackArgAddr s₀ 0, 8⟩
abbrev belowR : Region := ⟨State.addr s₀.sp - BitVec.ofNat 64 8, 8⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := VG.Proof.CmacAes.Arm.ciphAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.W s₀)) (VG.Proof.CmacAes.Arm.R s₀)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.Dp s₀)) 16 (VG.Proof.CmacAes.Arm.N s₀)

/-- The memory after saving the registers in the scratch buffer. -/
def savedMem : Mem := VG.Arm.Spill.saveMem s₀.mem (State.addr (VG.Proof.CmacAes.Arm.S s₀)) s₀.gpr saved

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacAes.Arm.schR s₀, VG.Proof.CmacAes.Arm.dataR s₀, VG.Proof.CmacAes.Arm.argsR s₀]
  wr : s₀.wr = [VG.Proof.CmacAes.Arm.stR s₀, VG.Proof.CmacAes.Arm.scrR s₀]
  sch_st : (VG.Proof.CmacAes.Arm.schR s₀).Disjoint (VG.Proof.CmacAes.Arm.stR s₀)
  sch_scr : (VG.Proof.CmacAes.Arm.schR s₀).Disjoint (VG.Proof.CmacAes.Arm.scrR s₀)
  data_st : (VG.Proof.CmacAes.Arm.dataR s₀).Disjoint (VG.Proof.CmacAes.Arm.stR s₀)
  data_scr : (VG.Proof.CmacAes.Arm.dataR s₀).Disjoint (VG.Proof.CmacAes.Arm.scrR s₀)
  st_scr : (VG.Proof.CmacAes.Arm.stR s₀).Disjoint (VG.Proof.CmacAes.Arm.scrR s₀)
  st_args : (VG.Proof.CmacAes.Arm.stR s₀).Disjoint (VG.Proof.CmacAes.Arm.argsR s₀)
  scr_args : (VG.Proof.CmacAes.Arm.scrR s₀).Disjoint (VG.Proof.CmacAes.Arm.argsR s₀)
  b_sch : (VG.Proof.CmacAes.Arm.belowR s₀).Disjoint (VG.Proof.CmacAes.Arm.schR s₀)
  b_data : (VG.Proof.CmacAes.Arm.belowR s₀).Disjoint (VG.Proof.CmacAes.Arm.dataR s₀)
  b_st : (VG.Proof.CmacAes.Arm.belowR s₀).Disjoint (VG.Proof.CmacAes.Arm.stR s₀)
  b_scr : (VG.Proof.CmacAes.Arm.belowR s₀).Disjoint (VG.Proof.CmacAes.Arm.scrR s₀)
  sch_fit : (VG.Proof.CmacAes.Arm.W s₀).toNat + 240 ≤ 2 ^ 32
  st_fit : (VG.Proof.CmacAes.Arm.St s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (VG.Proof.CmacAes.Arm.Dp s₀).toNat + 16 * VG.Proof.CmacAes.Arm.N s₀ ≤ 2 ^ 32
  scr_fit : (VG.Proof.CmacAes.Arm.S s₀).toNat + 2176 ≤ 2 ^ 32
  sp8 : 8 ≤ s₀.sp.toNat
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rounds : VG.Proof.CmacAes.Arm.R s₀ = 10 ∨ VG.Proof.CmacAes.Arm.R s₀ = 12 ∨ VG.Proof.CmacAes.Arm.R s₀ = 14

theorem UPre.of {s₀ : State} (h : updateArm.pre s₀) : VG.Proof.CmacAes.Arm.UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = VG.Proof.CmacAes.Arm.W s₀
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = VG.Proof.CmacAes.Arm.St s₀
  r7 : s.gpr .r7 = VG.Proof.CmacAes.Arm.Dp s₀ + BitVec.ofNat 32 (16 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (VG.Proof.CmacAes.Arm.N s₀ - k)
  r10 : s.gpr .r10 = VG.Proof.CmacAes.Arm.S s₀
  r11 : s.gpr .r11 = s₀.gpr .r11
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.CmacAes.Arm.stR s₀, ⟨State.addr (VG.Proof.CmacAes.Arm.S s₀), 2064⟩, VG.Proof.CmacAes.Arm.belowR s₀] (VG.Proof.CmacAes.Arm.savedMem s₀) s.mem
  state : Spec.Aes.bytesAt s.mem (State.addr (VG.Proof.CmacAes.Arm.St s₀)) 16 =
    Spec.Cmac.chain (VG.Proof.CmacAes.Arm.ciph s₀) (Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.St s₀)) 16) ((VG.Proof.CmacAes.Arm.blks s₀).take k)

/-! ## Addresses and regions -/

theorem add0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

section
variable {s₀ : State} (hp : VG.Proof.CmacAes.Arm.UPre s₀)
include hp

theorem UPre.scrA {d : Nat} (hd : d < 2176) :
    State.addr (VG.Proof.CmacAes.Arm.S s₀ + BitVec.ofNat 32 d) = State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.scr_fit; have := (VG.Proof.CmacAes.Arm.S s₀).isLt; omega)

theorem UPre.dataA {k : Nat} (hk : k < VG.Proof.CmacAes.Arm.N s₀) :
    State.addr (VG.Proof.CmacAes.Arm.Dp s₀ + BitVec.ofNat 32 (16 * k)) = State.addr (VG.Proof.CmacAes.Arm.Dp s₀) + BitVec.ofNat 64 (16 * k) :=
  addr_add (by have := hp.data_fit; have := (VG.Proof.CmacAes.Arm.Dp s₀).isLt; omega)

theorem UPre.dataN {k : Nat} (hk : k < VG.Proof.CmacAes.Arm.N s₀) :
    (VG.Proof.CmacAes.Arm.Dp s₀ + BitVec.ofNat 32 (16 * k)).toNat = (VG.Proof.CmacAes.Arm.Dp s₀).toNat + 16 * k := by
  have := hp.data_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem UPre.scrN {d : Nat} (hd : d < 2176) : (VG.Proof.CmacAes.Arm.S s₀ + BitVec.ofNat 32 d).toNat = (VG.Proof.CmacAes.Arm.S s₀).toNat + d := by
  have := hp.scr_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

omit hp in
theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 2176) :
    Region.Sub ⟨State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 d, n⟩ (VG.Proof.CmacAes.Arm.scrR s₀) :=
  Offset.sub_base _ h

omit hp in
theorem UPre.data_sub {k : Nat} (hk : k < VG.Proof.CmacAes.Arm.N s₀) :
    Region.Sub ⟨State.addr (VG.Proof.CmacAes.Arm.Dp s₀) + BitVec.ofNat 64 (16 * k), 16⟩ (VG.Proof.CmacAes.Arm.dataR s₀) :=
  Offset.sub_base _ (by omega)

theorem UPre.arg1 : stackArgAddr s₀ 1 = stackArgAddr s₀ 0 + BitVec.ofNat 64 4 := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega), addr_add (by omega)]
  simp

theorem UPre.arg_in {k : Nat} (hk : k < 2) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨VG.Proof.CmacAes.Arm.argsR s₀, by simp [hp.rd], ?_⟩
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · simpa using Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  · rw [hp.arg1]; exact Offset.contains_base _ (by decide) (by decide)

omit hp in
theorem UPre.arg_sub : Region.Sub ⟨stackArgAddr s₀ 0, 4⟩ (VG.Proof.CmacAes.Arm.argsR s₀) := Region.sub_prefix (by decide)

end

/-! ## Saving the registers -/

theorem saved_bound : ∀ p ∈ saved, 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2096 := by decide

theorem saved_ne_r12 : ∀ p ∈ saved, p.1 ≠ .r12 := by decide

export VG.Arm.Spill (saveMem_congr)

theorem saved_slots : Spill.Slots 2064 2096 saved := by decide

theorem savedMem_frame (s₀ : State) : Frame [⟨State.addr (VG.Proof.CmacAes.Arm.S s₀), 2096⟩] s₀.mem (VG.Proof.CmacAes.Arm.savedMem s₀) :=
  Spill.saveMem_frame _ _ _ (by decide) saved (by decide)

/-- Each slot holds the register saved there. -/
theorem savedMem_slot (s₀ : State) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (VG.Proof.CmacAes.Arm.savedMem s₀).readW (State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
  Spill.saveMem_saved (State.addr (VG.Proof.CmacAes.Arm.S s₀)) s₀.gpr s₀.mem saved VG.Proof.CmacAes.Arm.saved_slots (r, d) h

/-! ## The prologue -/

theorem prologue_wp {s₀ : State} (hp : VG.Proof.CmacAes.Arm.UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ fun s => VG.Proof.CmacAes.Arm.LInv s₀ 0 s ∧ s.z = decide (VG.Proof.CmacAes.Arm.N s₀ = 0) := by
  have hsc := hp.scr_fit
  rw [show save ++ setup = .ldrSp .r12 4 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++ setup) from rfl]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = VG.Proof.CmacAes.Arm.S s₀ := u₁.gpr
  refine VG.Arm.Spill.saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := VG.Proof.CmacAes.Arm.saved_bound p hp'
    rw [h12, u₁.wr, hp.wr]
    exact ⟨by omega, by omega, ⟨VG.Proof.CmacAes.Arm.scrR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩⟩
  have hm₂ : s₂.mem = VG.Proof.CmacAes.Arm.savedMem s₀ := by
    rw [m₂, u₁.mem, h12, VG.Proof.CmacAes.Arm.savedMem]
    exact VG.Arm.Spill.saveMem_congr _ _ _ fun p hp' => u₁.other _ (VG.Proof.CmacAes.Arm.saved_ne_r12 p hp')
  have harg : s₂.mem.readW (stackArgAddr s₀ 0) 32 = stackArg s₀ 0 := by
    rw [hm₂]
    exact (VG.Proof.CmacAes.Arm.savedMem_frame s₀).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.scr_args.symm.sub_left UPre.arg_sub).sub_right (Region.sub_prefix (by decide))) (by decide)
  simp only [setup, mov]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
        exact hp.arg_in (by decide)) fun s₇ u₇ => ?_
  refine wp_mov (op2_reg _ _) fun s₈ u₈ => wp_cmp (op2_imm (by decide)) fun s₉ f₉ z₉ => WP.block_nil ?_
  have r8 : s₉.gpr .r8 = stackArg s₀ 0 := by
    rw [f₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, harg]
  have mm : s₉.mem = VG.Proof.CmacAes.Arm.savedMem s₀ := by
    rw [f₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
  have a0 : stackArg s₀ 0 = BitVec.ofNat 32 (VG.Proof.CmacAes.Arm.N s₀) := by simp [VG.Proof.CmacAes.Arm.N]
  have stS : Spec.Aes.bytesAt (VG.Proof.CmacAes.Arm.savedMem s₀) (State.addr (VG.Proof.CmacAes.Arm.St s₀)) 16 =
      Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.St s₀)) 16 :=
    Proof.Cmac.bytesAt_frame16 (VG.Proof.CmacAes.Arm.savedMem_frame s₀) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (Region.sub_prefix (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, u₁.other]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g₂, u₁.other]
    exact (BitVec.add_zero _).symm
  · rw [r8, a0]; rfl
  · simp (disch := decide) only [f₉.gpr, u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, h12]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂,
      u₁.other]
  · rw [f₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [f₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [f₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  · rw [mm]; exact Frame.refl _ _
  · rw [mm, stS]; rfl
  · rw [z₉, show s₈.gpr .r8 = s₉.gpr .r8 from (congrFun f₉.gpr _).symm, r8, a0]
    exact cmp0 (stackArg s₀ 0).isLt

end VG.Proof.CmacAes.Arm

end

/-!
# AES-CMAC on ARMv7: the loop of `vg_cmac_aes_update`

One block keeps the loop invariant (`body_ok`): the counter block is `C ⊕ Mᵢ`
and the state is zeroed (`Cmac.chainMem4`), and the call of `vg_aes_ctr32`
leaves `CIPH_K(C ⊕ Mᵢ)` in the state.
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_subs eval_ne ofNat_beq_zero sub_ofNat)

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < VG.Proof.CmacAes.Arm.N s₀) :
    (VG.Proof.CmacAes.Arm.blks s₀).take (k + 1) =
      (VG.Proof.CmacAes.Arm.blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.Dp s₀) + BitVec.ofNat 64 (16 * k)) 16] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

/-! ## Memory outside the writable regions -/

/-- The regions the function writes, with the stack below it. -/
abbrev Big (s₀ : State) : List Region := [VG.Proof.CmacAes.Arm.stR s₀, VG.Proof.CmacAes.Arm.scrR s₀, VG.Proof.CmacAes.Arm.belowR s₀]

section
variable {s₀ : State} (hp : VG.Proof.CmacAes.Arm.UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (VG.Proof.CmacAes.Arm.Big s₀) s₀.mem m) :
    Spec.Aes.bytesAt m (State.addr (VG.Proof.CmacAes.Arm.W s₀)) (16 * (VG.Proof.CmacAes.Arm.R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.W s₀)) (16 * (VG.Proof.CmacAes.Arm.R s₀ + 1)) := by
  have hR : 16 * (VG.Proof.CmacAes.Arm.R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.sch_st.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.b_sch.symm.sub_left (Region.sub_prefix hR)

theorem UPre.block_bytes {m : Mem} (hf : Frame (VG.Proof.CmacAes.Arm.Big s₀) s₀.mem m) {k : Nat} (hk : k < VG.Proof.CmacAes.Arm.N s₀) :
    Spec.Aes.bytesAt m (State.addr (VG.Proof.CmacAes.Arm.Dp s₀) + BitVec.ofNat 64 (16 * k)) 16 =
      Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.Dp s₀) + BitVec.ofNat 64 (16 * k)) 16 := by
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.data_st.sub_left (UPre.data_sub hk)
  · exact hp.data_scr.sub_left (UPre.data_sub hk)
  · exact hp.b_data.symm.sub_left (UPre.data_sub hk)

omit hp in
theorem UPre.big_of {m : Mem} (hf : Frame [VG.Proof.CmacAes.Arm.stR s₀, ⟨State.addr (VG.Proof.CmacAes.Arm.S s₀), 2064⟩, VG.Proof.CmacAes.Arm.belowR s₀] (VG.Proof.CmacAes.Arm.savedMem s₀) m) :
    Frame (VG.Proof.CmacAes.Arm.Big s₀) s₀.mem m := by
  have f₀ : Frame (VG.Proof.CmacAes.Arm.Big s₀) s₀.mem (VG.Proof.CmacAes.Arm.savedMem s₀) :=
    (VG.Proof.CmacAes.Arm.savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.Arm.scrR s₀, by simp, Region.sub_prefix (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.CmacAes.Arm.stR s₀, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.CmacAes.Arm.scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.Arm.belowR s₀, by simp, fun _ h => h⟩)

end

/-! ## One block -/

/-- The counter block's address. -/
abbrev Cb (s₀ : State) : BitVec 32 := VG.Proof.CmacAes.Arm.S s₀ + BitVec.ofNat 32 2048

/-- What the code before the call leaves. -/
structure BodyA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : VG.Proof.CmacAes.Arm.CallPre s₁ (VG.Proof.CmacAes.Arm.W s₀) (VG.Proof.CmacAes.Arm.Cb s₀) (VG.Proof.CmacAes.Arm.St s₀) (VG.Proof.CmacAes.Arm.S s₀) (VG.Proof.CmacAes.Arm.R s₀) .r9 .r10
  keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = Proof.Cmac.chainMem4 s.mem (State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 2048) (State.addr (VG.Proof.CmacAes.Arm.St s₀))
    (State.addr (VG.Proof.CmacAes.Arm.Dp s₀) + BitVec.ofNat 64 (16 * k))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem chainIn_eq : chainIn ++ updArgs = VG.Proof.CmacAes.Arm.xorBlk .r0 .r1 .r6 .r7 .r10 0 0 2048 ++
    (.mov .r0 (.imm 0) :: (VG.Proof.CmacAes.Arm.zeroBlk .r0 .r6 0 ++
      ([.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .dp .add .r2 .r10 (.imm (BitVec.ofNat 32 2048)),
       .mov .r3 (.reg .r6), .mov .r9 (.imm 1)] : List Instr))) := rfl

theorem bodyA_wp {s₀ : State} (hp : VG.Proof.CmacAes.Arm.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.Arm.N s₀) {s : State} (h : VG.Proof.CmacAes.Arm.LInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (VG.Proof.CmacAes.Arm.BodyA s₀ k s) := by
  have hRegs : s.rd ++ s.wr = [VG.Proof.CmacAes.Arm.schR s₀, VG.Proof.CmacAes.Arm.dataR s₀, VG.Proof.CmacAes.Arm.argsR s₀, VG.Proof.CmacAes.Arm.stR s₀, VG.Proof.CmacAes.Arm.scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [VG.Proof.CmacAes.Arm.stR s₀, VG.Proof.CmacAes.Arm.scrR s₀] := by rw [h.wr, hp.wr]
  have hsc := hp.scr_fit
  have hst := hp.st_fit
  have hdf := hp.data_fit
  have qN := hp.dataN hk
  rw [VG.Proof.CmacAes.Arm.chainIn_eq]
  refine VG.Proof.CmacAes.Arm.xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h.r6]; omega) (by rw [h.r7, qN]; omega)
    (by rw [h.r10]; omega) ?_ ?_ ?_ fun s₁ g₁ => ?_
  · rw [h.r6, VG.Proof.CmacAes.Arm.add0, hRegs]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.Arm.stR s₀, by simp, 0, by simp, by simp⟩
  · rw [h.r7, VG.Proof.CmacAes.Arm.add0, hp.dataA hk, hRegs]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.Arm.dataR s₀, by simp, 16 * k, rfl, by simp; omega⟩
  · rw [h.r10, hW]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.Arm.scrR s₀, by simp, 2048, rfl, by simp⟩
  have e₁ : ∀ r, r ≠ .r0 → r ≠ .r1 → s₁.gpr r = s.gpr r := g₁.gpr
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have r6₂ : s₂.gpr .r6 = VG.Proof.CmacAes.Arm.St s₀ := by rw [u₂.other _ (by decide), e₁ _ (by decide) (by decide), h.r6]
  refine Proof.CmacAes.Arm.zeroBlk_ok u₂.gpr (by decide) (by rw [r6₂]; omega) ?_ fun s₃ G₃ m₃ rd₃ wr₃ sp₃ => ?_
  · rw [r6₂, VG.Proof.CmacAes.Arm.add0, u₂.wr, g₁.wr, hW]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.Arm.stR s₀, by simp, 0, by simp, by simp⟩
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_add (op2_imm (by decide)) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ =>
    wp_mov (op2_imm (by decide)) fun s₈ u₈ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → s₈.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h9 => by
      rw [u₈.other _ h9, u₇.other _ h3, u₆.other _ h2, u₅.other _ h1, u₄.other _ h0, G₃, u₂.other _ h0,
        e₁ _ h0 h1]
  have sp₈ : s₈.sp = s₀.sp := by
    rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, g₁.sp, h.sp]
  have rd₈ : s₈.rd = s.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, g₁.rd]
  have wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, g₁.wr]
  have mem₈ : s₈.mem = Proof.Cmac.chainMem4 s.mem (State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 2048)
      (State.addr (VG.Proof.CmacAes.Arm.St s₀)) (State.addr (VG.Proof.CmacAes.Arm.Dp s₀) + BitVec.ofNat 64 (16 * k)) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, r6₂, u₂.mem, g₁.mem, h.r6, h.r7, h.r10, VG.Proof.CmacAes.Arm.add0, VG.Proof.CmacAes.Arm.add0,
      hp.dataA hk]
    rfl
  have hb : VG.Proof.CmacAes.Arm.below s₈ = VG.Proof.CmacAes.Arm.belowR s₀ := by rw [VG.Proof.CmacAes.Arm.below, sp₈]; rfl
  have cA : State.addr (VG.Proof.CmacAes.Arm.Cb s₀) = State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 2048 := hp.scrA (by decide)
  have cSt : (⟨State.addr (VG.Proof.CmacAes.Arm.Cb s₀), 16⟩ : Region).Disjoint (VG.Proof.CmacAes.Arm.stR s₀) := by
    rw [cA]; exact hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, u₈.gpr, ?_, by decide, hp.rounds, by rw [sp₈]; exact hp.sp8, ?_, hp.sch_st, ?_, cSt,
    ?_, ?_, by rw [hb]; exact hp.b_sch, ?_, by rw [hb]; exact hp.b_st, ?_, hp.sch_fit, ?_, hp.st_fit, ?_, ?_, ?_,
    ?_⟩, keep, by rw [sp₈, h.sp], mem₈, rd₈, wr₈⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      G₃, u₂.other _ (by decide), e₁ _ (by decide) (by decide), h.r4]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      G₃, u₂.other _ (by decide), e₁ _ (by decide) (by decide), h.r5]
    simp [VG.Proof.CmacAes.Arm.R]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      G₃, u₂.other _ (by decide), e₁ _ (by decide) (by decide), h.r10]
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      G₃, r6₂]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r10]
  · rw [cA]; exact hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  · exact hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  · rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega)
  · exact hp.st_scr.sub_right (Region.sub_prefix (by decide))
  · rw [hb, cA]; exact hp.b_scr.sub_right (UPre.scr_sub (by decide))
  · rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide))
  · rw [hp.scrN (by decide)]; omega
  · omega
  · rw [rd₈, wr₈, hRegs]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.Arm.schR s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₈, hW, cA]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.CmacAes.Arm.scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨VG.Proof.CmacAes.Arm.stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.CmacAes.Arm.scrR s₀, by simp, 0, by simp, by simp⟩
  · rw [mem₈]; exact Proof.Cmac.chainMem4_state _ _ _ _

theorem body_ok {s₀ : State} (hp : VG.Proof.CmacAes.Arm.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.Arm.N s₀) {s : State} (h : VG.Proof.CmacAes.Arm.LInv s₀ k s) :
    WP isa body s fun s' => VG.Proof.CmacAes.Arm.LInv s₀ (k + 1) s' ∧ s'.z = decide (VG.Proof.CmacAes.Arm.N s₀ - (k + 1) = 0) := by
  have hdf := hp.data_fit
  have hN := (stackArg s₀ 0).isLt
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Arm.bodyA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Arm.ctr_call a.pre) fun s₂ h₂ => ?_)
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_subs (op2_imm (by decide)) fun s₄ u₄ z₄ => WP.block_nil ?_
  have g (r : Reg) (hr : r ∈ preserved) (hlr : r ≠ .lr) (h7 : r ≠ .r7) (h8 : r ≠ .r8) (h9 : r ≠ .r9) :
      s₄.gpr r = s.gpr r := by
    have : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₄.other _ h8, u₃.other _ h7, h₂.saved r hr hlr, a.keep r this.1 this.2.1 this.2.2.1 this.2.2.2 h9]
  have r7₂ : s₂.gpr .r7 = VG.Proof.CmacAes.Arm.Dp s₀ + BitVec.ofNat 32 (16 * k) := by
    rw [h₂.saved .r7 (by simp [preserved]) (by decide), a.keep _ (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r7]
  have r8₃ : s₃.gpr .r8 = BitVec.ofNat 32 (VG.Proof.CmacAes.Arm.N s₀ - k) := by
    rw [u₃.other _ (by decide), h₂.saved .r8 (by simp [preserved]) (by decide),
      a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r8]
  have dec : BitVec.ofNat 32 (VG.Proof.CmacAes.Arm.N s₀ - k) - 1 = BitVec.ofNat 32 (VG.Proof.CmacAes.Arm.N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega)]; rfl
  -- Memory.
  have bigS := UPre.big_of h.frame
  have cA : State.addr (VG.Proof.CmacAes.Arm.Cb s₀) = State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 2048 := hp.scrA (by decide)
  have f₁ : Frame [⟨State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 2048, 16⟩, VG.Proof.CmacAes.Arm.stR s₀] s.mem s₁.mem := by
    rw [a.mem]; exact Proof.Cmac.chainMem4_frame _ _ _ _
  have big₁ : Frame (VG.Proof.CmacAes.Arm.Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.CmacAes.Arm.scrR s₀, by simp, UPre.scr_sub (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.Arm.stR s₀, by simp, fun _ h => h⟩)
  have cst : (⟨State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint (VG.Proof.CmacAes.Arm.stR s₀) :=
    hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  have cq : (⟨State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint
      ⟨State.addr (VG.Proof.CmacAes.Arm.Dp s₀) + BitVec.ofNat 64 (16 * k), 16⟩ :=
    (hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))).sub_right (UPre.data_sub hk)
  have out := h₂.out
  rw [UPre.sched_bytes hp big₁, cA, a.mem, Proof.Cmac.chainMem4_counter _ cst cq, h.state,
    UPre.block_bytes hp bigS hk] at out
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [g .r4 (by simp [preserved]) (by decide) (by decide) (by decide) (by decide), h.r4]
  · rw [g .r5 (by simp [preserved]) (by decide) (by decide) (by decide) (by decide), h.r5]
  · rw [g .r6 (by simp [preserved]) (by decide) (by decide) (by decide) (by decide), h.r6]
  · rw [u₄.other _ (by decide), u₃.gpr, r7₂, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega)]
  · rw [u₄.gpr, r8₃, dec]
  · rw [g .r10 (by simp [preserved]) (by decide) (by decide) (by decide) (by decide), h.r10]
  · rw [g .r11 (by simp [preserved]) (by decide) (by decide) (by decide) (by decide), h.r11]
  · rw [u₄.sp, u₃.sp, h₂.sp, a.sp, h.sp]
  · rw [u₄.rd, u₃.rd, h₂.rd, a.rd, h.rd]
  · rw [u₄.wr, u₃.wr, h₂.wr, a.wr, h.wr]
  · have hb : VG.Proof.CmacAes.Arm.below s₁ = VG.Proof.CmacAes.Arm.belowR s₀ := by rw [VG.Proof.CmacAes.Arm.below, a.sp, h.sp]; rfl
    rw [u₄.mem, u₃.mem]
    refine h.frame.trans ((f₁.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr (VG.Proof.CmacAes.Arm.S s₀), 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.Arm.stR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨State.addr (VG.Proof.CmacAes.Arm.S s₀), 2064⟩, by simp, by rw [cA]; exact Offset.sub_base _ (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.Arm.stR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨State.addr (VG.Proof.CmacAes.Arm.S s₀), 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.Arm.belowR s₀, by simp, by rw [hb]; exact fun _ h => h⟩
  · rw [u₄.mem, u₃.mem, out, VG.Proof.CmacAes.Arm.take_succ_blks s₀ hk, Proof.Cmac.chain_append, Proof.Cmac.chain_single]
  · rw [z₄, r8₃, dec]; exact ofNat_beq_zero (by omega)

theorem loop_ok {s₀ : State} (hp : VG.Proof.CmacAes.Arm.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.Arm.N s₀) {s : State} (h : VG.Proof.CmacAes.Arm.LInv s₀ k s) :
    WP isa (.loop body .ne) s (VG.Proof.CmacAes.Arm.LInv s₀ (VG.Proof.CmacAes.Arm.N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := VG.Proof.CmacAes.Arm.LInv s₀ (VG.Proof.CmacAes.Arm.N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = VG.Proof.CmacAes.Arm.N s₀ - j ∧ j < VG.Proof.CmacAes.Arm.N s₀ ∧ VG.Proof.CmacAes.Arm.LInv s₀ j t) ?_ (VG.Proof.CmacAes.Arm.N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (VG.Proof.CmacAes.Arm.body_ok hp hk h) fun s' ⟨h', hz⟩ => ?_
  have ev : isa.eval .ne s' = some !decide (VG.Proof.CmacAes.Arm.N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s' = _; rw [eval_ne, hz]
  by_cases hz' : VG.Proof.CmacAes.Arm.N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [show VG.Proof.CmacAes.Arm.N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [ev]; simp [hz'], VG.Proof.CmacAes.Arm.N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

end VG.Proof.CmacAes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Arm.UpdateCorrect`. -/
section

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_update` is correct
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd wp_ldr eval_eq)

/-! ## Restoring the registers -/

theorem saved_eq : saved = saved.take 7 ++ [(.r10, 2088)] := rfl

theorem slot_read {s₀ : State} (hp : VG.Proof.CmacAes.Arm.UPre s₀) {m : Mem}
    (hf : Frame [VG.Proof.CmacAes.Arm.stR s₀, ⟨State.addr (VG.Proof.CmacAes.Arm.S s₀), 2064⟩, VG.Proof.CmacAes.Arm.belowR s₀] (VG.Proof.CmacAes.Arm.savedMem s₀) m) {d : Nat} (h₁ : 2064 ≤ d)
    (h₂ : d + 4 ≤ 2096) :
    m.readW (State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 d) 32 = (VG.Proof.CmacAes.Arm.savedMem s₀).readW (State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_scr.symm.sub_left (UPre.scr_sub (by omega))
    · exact Offset.disjoint_base _ h₁ (by omega)
    · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega))) (by decide)

theorem epilogue_wp {s₀ : State} (hp : VG.Proof.CmacAes.Arm.UPre s₀) {s : State} (h : VG.Proof.CmacAes.Arm.LInv s₀ (VG.Proof.CmacAes.Arm.N s₀) s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ updateArm.post s₀ s' := by
  have hsc := hp.scr_fit
  have rdwr : s.rd ++ s.wr = [VG.Proof.CmacAes.Arm.schR s₀, VG.Proof.CmacAes.Arm.dataR s₀, VG.Proof.CmacAes.Arm.argsR s₀, VG.Proof.CmacAes.Arm.stR s₀, VG.Proof.CmacAes.Arm.scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have inS : ∀ d, d + 4 ≤ 2176 → InRegions (s.rd ++ s.wr) (State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact ⟨VG.Proof.CmacAes.Arm.scrR s₀, by simp, Offset.contains_base _ hd (by omega)⟩
  have sl : ∀ r d, (r, d) ∈ saved → s.mem.readW (State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
    fun r d hrd => by
      have hb := VG.Proof.CmacAes.Arm.saved_bound _ hrd
      rw [VG.Proof.CmacAes.Arm.slot_read hp h.frame hb.1 hb.2, VG.Proof.CmacAes.Arm.savedMem_slot s₀ hrd]
  rw [restore, VG.Proof.CmacAes.Arm.saved_eq, ← List.append_nil (List.map _ _)]
  refine Spill.restoreBase_ok (by decide) (fun p hp' => ?_) fun s₂ ld ho m₁ _ _ sp₁ => WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · have hb := VG.Proof.CmacAes.Arm.saved_bound p (by rw [VG.Proof.CmacAes.Arm.saved_eq]; exact hp')
    exact ⟨by omega, by rw [h.r10]; omega, by rw [h.r10]; exact inS _ (by omega)⟩
  · by_cases hs : r ∈ saved.map Prod.fst
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hs
      rw [ld p (by rw [← VG.Proof.CmacAes.Arm.saved_eq]; exact hp'), h.r10, sl _ _ hp']
    · have hk : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → r = .r11 := by decide
      rw [hk r hr hs, ho _ (by decide), h.r11]
  · rw [sp₁, h.sp]
  · show Spec.Aes.bytesAt s₂.mem (State.addr (VG.Proof.CmacAes.Arm.St s₀)) 16 = Spec.Cmac.chain (VG.Proof.CmacAes.Arm.ciph s₀) _ (VG.Proof.CmacAes.Arm.blks s₀)
    rw [m₁, h.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

/-! ## The whole function -/

theorem mid_wp {s₀ : State} (hp : VG.Proof.CmacAes.Arm.UPre s₀) {s₁ : State} (h : VG.Proof.CmacAes.Arm.LInv s₀ 0 s₁) (hz : s₁.z = decide (VG.Proof.CmacAes.Arm.N s₀ = 0)) :
    WP isa (.ite .eq (.block []) (.loop body .ne)) s₁ (VG.Proof.CmacAes.Arm.LInv s₀ (VG.Proof.CmacAes.Arm.N s₀)) := by
  have ev : isa.eval .eq s₁ = some (decide (VG.Proof.CmacAes.Arm.N s₀ = 0)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz]
  by_cases hn : VG.Proof.CmacAes.Arm.N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact VG.Proof.CmacAes.Arm.loop_ok hp (by omega) h

theorem update_wp {s₀ : State} (h0 : updateArm.pre s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ updateArm.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (VG.Proof.CmacAes.Arm.prologue_wp hp) fun s₁ ⟨h₁, hz⟩ =>
    WP.seq (WP.mono (VG.Proof.CmacAes.Arm.mid_wp hp h₁ hz) fun _ h₂ => VG.Proof.CmacAes.Arm.epilogue_wp hp h₂))

end VG.Proof.CmacAes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Arm.Subkeys`. -/
section

section

/-!
# AES-CMAC on ARMv7: doubling a block in four 32-bit words

`dbl src dst` loads a block as four byte-reversed words (`rev`), the block as
a big-endian integer (`Cmac.ofBytes_rev4`), doubles the integer a word at a
time (`Cmac.dbl_words4`), and stores the words byte-reversed again
(`Cmac.le4_rev4`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_sub wp_and wp_orr wp_rev wp_ldr wp_str)

theorem rev_eq (a : BitVec 32) : rev a = byteRev32 a := rfl

/-- The memory after `dbl src dst`, with `r6` pointing at `A`. -/
def dblMem (m : Mem) (A : Addr) (src dst : Nat) : Mem :=
  let P := A + BitVec.ofNat 64 src
  let b₀ := byteRev32 (m.readW P 32)
  let b₁ := byteRev32 (m.readW (P + BitVec.ofNat 64 4) 32)
  let b₂ := byteRev32 (m.readW (P + BitVec.ofNat 64 8) 32)
  let b₃ := byteRev32 (m.readW (P + BitVec.ofNat 64 12) 32)
  Proof.Cmac.store4 m (A + BitVec.ofNat 64 dst) (byteRev32 (Proof.Cmac.dblW0 b₀ b₁))
    (byteRev32 (Proof.Cmac.dblW0 b₁ b₂)) (byteRev32 (Proof.Cmac.dblW0 b₂ b₃)) (byteRev32 (Proof.Cmac.dblW3 b₀ b₃))

theorem dblMem_frame (m : Mem) (A : Addr) (src dst : Nat) :
    Frame [⟨A + BitVec.ofNat 64 dst, 16⟩] m (VG.Proof.CmacAes.Arm.dblMem m A src dst) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem dblMem_bytes (m : Mem) (A : Addr) (src dst : Nat) :
    Spec.Aes.bytesAt (VG.Proof.CmacAes.Arm.dblMem m A src dst) (A + BitVec.ofNat 64 dst) 16 =
      Spec.Cmac.dbl 16 (Spec.Aes.bytesAt m (A + BitVec.ofNat 64 src) 16) := by
  simp only [VG.Proof.CmacAes.Arm.dblMem]
  rw [Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_rev4, Proof.Cmac.dbl_words4,
    Proof.Cmac.dbl_eq (Proof.Cmac.bytesAt_length _ _ _), Proof.Cmac.ofBytes_rev4]

/-- `dbl src dst`, with `r6` pointing at `K`. -/
theorem dbl_wp {is : List Instr} {s : State} {Q : State → Prop} {K : BitVec 32} {src dst : Nat}
    (h6 : s.gpr .r6 = K) (hs : src + 12 < 4096) (hd : dst + 12 < 4096)
    (fs : K.toNat + src + 16 ≤ 2 ^ 32) (fd : K.toNat + dst + 16 ≤ 2 ^ 32)
    (rS : Covers [⟨State.addr K + BitVec.ofNat 64 src, 16⟩] (s.rd ++ s.wr))
    (wD : Covers [⟨State.addr K + BitVec.ofNat 64 dst, 16⟩] s.wr)
    (k : ∀ s', (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → s'.gpr r = s.gpr r) →
      s'.mem = VG.Proof.CmacAes.Arm.dblMem s.mem (State.addr K) src dst → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      WP isa (.block is) s' Q) :
    WP isa (.block (dbl src dst ++ is)) s Q := by
  simp only [dbl, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr K + BitVec.ofNat 64 src) (by omega) (by rw [h6]; exact addr_add (by omega))
    (VG.Proof.CmacAes.Arm.in_word0 rS) fun s₁ u₁ => ?_
  refine wp_ldr (a := State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 4) (by omega)
    (by rw [u₁.other _ (by decide), h6]; exact VG.Proof.CmacAes.Arm.addr_word 4 fs (by decide))
    (by rw [u₁.rd, u₁.wr]; exact VG.Proof.CmacAes.Arm.in_word rS (by decide)) fun s₂ u₂ => ?_
  refine wp_ldr (a := State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 8) (by omega)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h6]; exact VG.Proof.CmacAes.Arm.addr_word 8 fs (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact VG.Proof.CmacAes.Arm.in_word rS (by decide)) fun s₃ u₃ => ?_
  refine wp_ldr (a := State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 12) (by omega)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h6]
        exact VG.Proof.CmacAes.Arm.addr_word 12 fs (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact VG.Proof.CmacAes.Arm.in_word rS (by decide)) fun s₄ u₄ => ?_
  refine wp_rev fun s₅ u₅ => wp_rev fun s₆ u₆ => wp_rev fun s₇ u₇ => wp_rev fun s₈ u₈ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₉ u₉ => wp_mov (op2_imm (by decide)) fun s₁₀ u₁₀ =>
    wp_sub (op2_reg _ _) fun s₁₁ u₁₁ => wp_and (op2_imm (by decide)) fun s₁₂ u₁₂ => ?_
  refine wp_mov (op2_lsl (by decide)) fun s₁₃ u₁₃ => wp_orr (op2_lsr (by decide)) fun s₁₄ u₁₄ =>
    wp_mov (op2_lsl (by decide)) fun s₁₅ u₁₅ => wp_orr (op2_lsr (by decide)) fun s₁₆ u₁₆ =>
    wp_mov (op2_lsl (by decide)) fun s₁₇ u₁₇ => wp_orr (op2_lsr (by decide)) fun s₁₈ u₁₈ =>
    wp_mov (op2_lsl (by decide)) fun s₁₉ u₁₉ => VG.Proof.CmacAes.Arm.wp_eor (op2_reg _ _) fun s₂₀ u₂₀ => ?_
  refine wp_rev fun s₂₁ u₂₁ => wp_rev fun s₂₂ u₂₂ => wp_rev fun s₂₃ u₂₃ => wp_rev fun s₂₄ u₂₄ => ?_
  have g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → s₂₄.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h4 h12 => by
      rw [u₂₄.other _ h3, u₂₃.other _ h2, u₂₂.other _ h1, u₂₁.other _ h0, u₂₀.other _ h3, u₁₉.other _ h3,
        u₁₈.other _ h2, u₁₇.other _ h2, u₁₆.other _ h1, u₁₅.other _ h1, u₁₄.other _ h0, u₁₃.other _ h0,
        u₁₂.other _ h12, u₁₁.other _ h12, u₁₀.other _ h4, u₉.other _ h12, u₈.other _ h3, u₇.other _ h2,
        u₆.other _ h1, u₅.other _ h0, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  have g6 : s₂₄.gpr .r6 = K := by
    rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h6]
  have m24 : s₂₄.mem = s.mem := by
    rw [u₂₄.mem, u₂₃.mem, u₂₂.mem, u₂₁.mem, u₂₀.mem, u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem, u₁₄.mem,
      u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem,
      u₁.mem]
  have rd24 : s₂₄.rd = s.rd := by
    rw [u₂₄.rd, u₂₃.rd, u₂₂.rd, u₂₁.rd, u₂₀.rd, u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd,
      u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr24 : s₂₄.wr = s.wr := by
    rw [u₂₄.wr, u₂₃.wr, u₂₂.wr, u₂₁.wr, u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, u₁₃.wr,
      u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp24 : s₂₄.sp = s.sp := by
    rw [u₂₄.sp, u₂₃.sp, u₂₂.sp, u₂₁.sp, u₂₀.sp, u₁₉.sp, u₁₈.sp, u₁₇.sp, u₁₆.sp, u₁₅.sp, u₁₄.sp, u₁₃.sp,
      u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  -- The four words.
  have w₀ : s₁.gpr .r0 = s.mem.readW (State.addr K + BitVec.ofNat 64 src) 32 := u₁.gpr
  have w₁ : s₂.gpr .r1 = s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 4) 32 := by
    rw [u₂.gpr, u₁.mem]
  have w₂ : s₃.gpr .r2 = s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 8) 32 := by
    rw [u₃.gpr, u₂.mem, u₁.mem]
  have w₃ : s₄.gpr .r3 = s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 12) 32 := by
    rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
  have b₀ : s₈.gpr .r0 = byteRev32 (s.mem.readW (State.addr K + BitVec.ofNat 64 src) 32) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), w₀, VG.Proof.CmacAes.Arm.rev_eq]
  have b₁ : s₈.gpr .r1 = byteRev32 (s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 4) 32) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), w₁, VG.Proof.CmacAes.Arm.rev_eq]
  have b₂ : s₈.gpr .r2 = byteRev32 (s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 8) 32) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      w₂, VG.Proof.CmacAes.Arm.rev_eq]
  have b₃ : s₈.gpr .r3 = byteRev32 (s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 12) 32) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), w₃, VG.Proof.CmacAes.Arm.rev_eq]
  have mask : s₁₂.gpr .r12 = ((0 : BitVec 32) - (s₈.gpr .r0 >>> 31)) &&& 0x87 := by
    rw [u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, u₁₀.other _ (by decide), u₉.gpr]
  have v₀ : s₂₄.gpr .r0 = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .r0) (s₈.gpr .r1)) := by
    rw [u₂₄.other _ (by decide), u₂₃.other _ (by decide), u₂₂.other _ (by decide), u₂₁.gpr, VG.Proof.CmacAes.Arm.rev_eq,
      u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.gpr, u₁₃.gpr, u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₉.other _ (by decide)]
    rfl
  have v₁ : s₂₄.gpr .r1 = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .r1) (s₈.gpr .r2)) := by
    rw [u₂₄.other _ (by decide), u₂₃.other _ (by decide), u₂₂.gpr, VG.Proof.CmacAes.Arm.rev_eq, u₂₁.other _ (by decide),
      u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₆.gpr, u₁₅.gpr, u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₄.other _ (by decide),
      u₁₃.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₂.other _ (by decide),
      u₁₁.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₉.other _ (by decide)]
    rfl
  have v₂ : s₂₄.gpr .r2 = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .r2) (s₈.gpr .r3)) := by
    rw [u₂₄.other _ (by decide), u₂₃.gpr, VG.Proof.CmacAes.Arm.rev_eq, u₂₂.other _ (by decide), u₂₁.other _ (by decide),
      u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.gpr, u₁₇.gpr, u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₅.other _ (by decide),
      u₁₄.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₉.other _ (by decide)]
    rfl
  have v₃ : s₂₄.gpr .r3 = byteRev32 (Proof.Cmac.dblW3 (s₈.gpr .r0) (s₈.gpr .r3)) := by
    rw [u₂₄.gpr, VG.Proof.CmacAes.Arm.rev_eq, u₂₃.other _ (by decide), u₂₂.other _ (by decide), u₂₁.other _ (by decide), u₂₀.gpr,
      u₁₉.gpr, u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₇.other _ (by decide), u₁₆.other _ (by decide), u₁₆.other _ (by decide), u₁₅.other _ (by decide),
      u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide),
      u₁₃.other _ (by decide), mask, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide)]
    rfl
  refine wp_str (a := State.addr K + BitVec.ofNat 64 dst) (by omega) (by rw [g6]; exact addr_add (by omega))
    (by rw [wr24]; exact VG.Proof.CmacAes.Arm.in_word0 wD) fun s₂₅ v₂₅ => ?_
  refine wp_str (a := State.addr K + BitVec.ofNat 64 dst + BitVec.ofNat 64 4) (by omega)
    (by rw [v₂₅.gpr, g6]; exact VG.Proof.CmacAes.Arm.addr_word 4 fd (by decide))
    (by rw [v₂₅.wr, wr24]; exact VG.Proof.CmacAes.Arm.in_word wD (by decide)) fun s₂₆ v₂₆ => ?_
  refine wp_str (a := State.addr K + BitVec.ofNat 64 dst + BitVec.ofNat 64 8) (by omega)
    (by rw [v₂₆.gpr, v₂₅.gpr, g6]; exact VG.Proof.CmacAes.Arm.addr_word 8 fd (by decide))
    (by rw [v₂₆.wr, v₂₅.wr, wr24]; exact VG.Proof.CmacAes.Arm.in_word wD (by decide)) fun s₂₇ v₂₇ => ?_
  refine wp_str (a := State.addr K + BitVec.ofNat 64 dst + BitVec.ofNat 64 12) (by omega)
    (by rw [v₂₇.gpr, v₂₆.gpr, v₂₅.gpr, g6]; exact VG.Proof.CmacAes.Arm.addr_word 12 fd (by decide))
    (by rw [v₂₇.wr, v₂₆.wr, v₂₅.wr, wr24]; exact VG.Proof.CmacAes.Arm.in_word wD (by decide)) fun s₂₈ v₂₈ => k s₂₈ ?_ ?_ ?_ ?_ ?_
  · intro r h0 h1 h2 h3 h4 h12
    rw [v₂₈.gpr, v₂₇.gpr, v₂₆.gpr, v₂₅.gpr, g r h0 h1 h2 h3 h4 h12]
  · rw [v₂₈.mem, v₂₇.mem, v₂₆.mem, v₂₅.mem, v₂₇.gpr, v₂₆.gpr, v₂₅.gpr, m24, v₀, v₁, v₂, v₃, b₀, b₁, b₂, b₃]
    rfl
  · rw [v₂₈.rd, v₂₇.rd, v₂₆.rd, v₂₅.rd, rd24]
  · rw [v₂₈.wr, v₂₇.wr, v₂₆.wr, v₂₅.wr, wr24]
  · rw [v₂₈.sp, v₂₇.sp, v₂₆.sp, v₂₅.sp, sp24]

end VG.Proof.CmacAes.Arm

end

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_subkeys`

`L = CIPH_K(0)` is computed into the first block of the subkeys (a zero
counter block and a zero data block), then doubled there (`K1`) and into the
second block (`K2`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg wp_mov wp_add wp_ldr saveMem saveList_ok saveMem_frame
  readW_writeW_save)

section
variable (s₀ : State)

/-- The subkeys. -/
abbrev Kb : BitVec 32 := s₀.gpr .r2
/-- The scratch buffer. -/
abbrev Sc : BitVec 32 := s₀.gpr .r3

abbrev kR : Region := ⟨State.addr (VG.Proof.CmacAes.Arm.Kb s₀), 32⟩
abbrev scR : Region := ⟨State.addr (VG.Proof.CmacAes.Arm.Sc s₀), 2176⟩

end

/-- The precondition, by name. -/
structure SPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacAes.Arm.schR s₀]
  wr : s₀.wr = [VG.Proof.CmacAes.Arm.kR s₀, VG.Proof.CmacAes.Arm.scR s₀]
  sch_k : (VG.Proof.CmacAes.Arm.schR s₀).Disjoint (VG.Proof.CmacAes.Arm.kR s₀)
  sch_scr : (VG.Proof.CmacAes.Arm.schR s₀).Disjoint (VG.Proof.CmacAes.Arm.scR s₀)
  k_scr : (VG.Proof.CmacAes.Arm.kR s₀).Disjoint (VG.Proof.CmacAes.Arm.scR s₀)
  b_sch : (VG.Proof.CmacAes.Arm.belowR s₀).Disjoint (VG.Proof.CmacAes.Arm.schR s₀)
  b_k : (VG.Proof.CmacAes.Arm.belowR s₀).Disjoint (VG.Proof.CmacAes.Arm.kR s₀)
  b_scr : (VG.Proof.CmacAes.Arm.belowR s₀).Disjoint (VG.Proof.CmacAes.Arm.scR s₀)
  sch_fit : (VG.Proof.CmacAes.Arm.W s₀).toNat + 240 ≤ 2 ^ 32
  k_fit : (VG.Proof.CmacAes.Arm.Kb s₀).toNat + 32 ≤ 2 ^ 32
  scr_fit : (VG.Proof.CmacAes.Arm.Sc s₀).toNat + 2176 ≤ 2 ^ 32
  sp8 : 8 ≤ s₀.sp.toNat
  rounds : VG.Proof.CmacAes.Arm.R s₀ = 10 ∨ VG.Proof.CmacAes.Arm.R s₀ = 12 ∨ VG.Proof.CmacAes.Arm.R s₀ = 14

theorem SPre.of {s₀ : State} (h : subkeysArm.pre s₀) : VG.Proof.CmacAes.Arm.SPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩

/-- The registers `subkeys` saves, and where. -/
def saved4 : List (Reg × Nat) := [(.r4, 2064), (.r5, 2068), (.r6, 2072), (.lr, 2076)]

theorem subkeysPre_eq : subkeysPre = saved4.map (fun p => Instr.str p.1 .r3 p.2) ++
    (.mov .r6 (.reg .r2) :: .mov .r5 (.reg .r3) :: .mov .r12 (.imm 0) :: (VG.Proof.CmacAes.Arm.zeroBlk .r12 .r3 2048 ++
      (VG.Proof.CmacAes.Arm.zeroBlk .r12 .r2 0 ++ ([.dp .add .r2 .r5 (.imm (BitVec.ofNat 32 2048)), .mov .r3 (.reg .r6),
        .mov .r4 (.imm 1)] : List Instr)))) := rfl

theorem subkeysPost_eq : subkeysPost = dbl 0 0 ++ (dbl 0 16 ++
    ([(.r4, 2064), (.r6, 2072), (.lr, 2076)].map (fun (p : Reg × Nat) => Instr.ldr p.1 .r5 p.2) ++
      ([.ldr .r5 .r5 2068] : List Instr))) := rfl

theorem saved4_slot (m : Mem) (B : Addr) (g : Reg → BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ VG.Proof.CmacAes.Arm.saved4) :
    (VG.Arm.Spill.saveMem m B g VG.Proof.CmacAes.Arm.saved4).readW (B + BitVec.ofNat 64 d) 32 = g r :=
  Spill.saveMem_saved (lo := 2064) (hi := 2080) B g m VG.Proof.CmacAes.Arm.saved4 (by decide) (r, d) h

/-- The memory before the call. -/
def preMem (s₀ : State) : Mem :=
  Proof.Cmac.zero4 (Proof.Cmac.zero4 (VG.Arm.Spill.saveMem s₀.mem (State.addr (VG.Proof.CmacAes.Arm.Sc s₀)) s₀.gpr VG.Proof.CmacAes.Arm.saved4)
    (State.addr (VG.Proof.CmacAes.Arm.Sc s₀) + BitVec.ofNat 64 2048)) (State.addr (VG.Proof.CmacAes.Arm.Kb s₀))

/-- What the code before the call leaves. -/
structure SAfter (s₀ s : State) : Prop where
  pre : VG.Proof.CmacAes.Arm.CallPre s (VG.Proof.CmacAes.Arm.W s₀) (VG.Proof.CmacAes.Arm.Sc s₀ + BitVec.ofNat 32 2048) (VG.Proof.CmacAes.Arm.Kb s₀) (VG.Proof.CmacAes.Arm.Sc s₀) (VG.Proof.CmacAes.Arm.R s₀) .r4 .r5
  keep : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s.gpr r = s₀.gpr r
  r5 : s.gpr .r5 = VG.Proof.CmacAes.Arm.Sc s₀
  r6 : s.gpr .r6 = VG.Proof.CmacAes.Arm.Kb s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = VG.Proof.CmacAes.Arm.preMem s₀

theorem pre_wp {s₀ : State} (hp : VG.Proof.CmacAes.Arm.SPre s₀) : WP isa (.block subkeysPre) s₀ (VG.Proof.CmacAes.Arm.SAfter s₀) := by
  have kf := hp.k_fit
  have sf := hp.scr_fit
  have sf' : (s₀.gpr .r3).toNat + 2176 ≤ 2 ^ 32 := sf
  have hR := hp.rounds
  have hRb : 16 * (VG.Proof.CmacAes.Arm.R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have cK : ∀ d n, d + n ≤ 32 → Covers [⟨State.addr (VG.Proof.CmacAes.Arm.Kb s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Arm.kR s₀, by simp, d, rfl, h⟩
  have cS : ∀ d n, d + n ≤ 2176 → Covers [⟨State.addr (VG.Proof.CmacAes.Arm.Sc s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Arm.scR s₀, by simp, d, rfl, h⟩
  have rw' : ∀ {rs a n}, Covers rs s₀.wr → InRegions rs a n → InRegions (s₀.rd ++ s₀.wr) a n :=
    fun h hi => by obtain ⟨r, hr, hc⟩ := h _ _ hi; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have cKr : ∀ d n, d + n ≤ 32 → Covers [⟨State.addr (VG.Proof.CmacAes.Arm.Kb s₀) + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) :=
    fun d n h a k hi => rw' (cK d n h) hi
  have aS : ∀ {d}, d < 2176 → State.addr (VG.Proof.CmacAes.Arm.Sc s₀ + BitVec.ofNat 32 d) = State.addr (VG.Proof.CmacAes.Arm.Sc s₀) + BitVec.ofNat 64 d :=
    fun _ => addr_add (by omega)
  -- Before the call.
  rw [VG.Proof.CmacAes.Arm.subkeysPre_eq]
  refine VG.Arm.Spill.saveList_ok VG.Proof.CmacAes.Arm.saved4 s₀ _ (fun p hp' => ?_) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · have hb : 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2080 := by
      simp only [VG.Proof.CmacAes.Arm.saved4, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl <;> decide
    exact ⟨by omega, by omega, cS p.2 4 (by omega) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩⟩
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_imm (by decide)) fun s₄ u₄ => ?_
  have r3₄ : s₄.gpr .r3 = VG.Proof.CmacAes.Arm.Sc s₀ := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  refine Proof.CmacAes.Arm.zeroBlk_ok u₄.gpr (by decide) (by rw [r3₄]; omega)
    (by rw [r3₄, u₄.wr, u₃.wr, u₂.wr, wr₁]; exact cS 2048 16 (by decide)) fun s₅ G₅ m₅ rd₅ wr₅ sp₅ => ?_
  have r2₅ : s₅.gpr .r2 = VG.Proof.CmacAes.Arm.Kb s₀ := by
    rw [G₅, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  refine Proof.CmacAes.Arm.zeroBlk_ok (by rw [G₅, u₄.gpr]) (by decide) (by rw [r2₅]; omega)
    (by rw [r2₅, VG.Proof.CmacAes.Arm.add0, wr₅, u₄.wr, u₃.wr, u₂.wr, wr₁]; simpa using cK 0 16 (by decide))
    fun s₆ G₆ m₆ rd₆ wr₆ sp₆ => ?_
  refine wp_add (op2_imm (by decide)) fun s₇ u₇ => wp_mov (op2_reg _ _) fun s₈ u₈ =>
    wp_mov (op2_imm (by decide)) fun s₉ u₉ => WP.block_nil ?_
  have keep₉ : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s₉.gpr r = s₀.gpr r :=
    fun r h2 h3 h4 h5 h6 h12 => by
      rw [u₉.other _ h4, u₈.other _ h3, u₇.other _ h2, G₆, G₅, u₄.other _ h12, u₃.other _ h5, u₂.other _ h6, g₁]
  have r5₉ : s₉.gpr .r5 = VG.Proof.CmacAes.Arm.Sc s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), G₆, G₅, u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), g₁]
  have r6₉ : s₉.gpr .r6 = VG.Proof.CmacAes.Arm.Kb s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), G₆, G₅, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁]
  have sp₉ : s₉.sp = s₀.sp := by rw [u₉.sp, u₈.sp, u₇.sp, sp₆, sp₅, u₄.sp, u₃.sp, u₂.sp, sp₁]
  have rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, u₄.rd, u₃.rd, u₂.rd, rd₁]
  have wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅, u₄.wr, u₃.wr, u₂.wr, wr₁]
  have mem₉ : s₉.mem = VG.Proof.CmacAes.Arm.preMem s₀ := by
    rw [u₉.mem, u₈.mem, u₇.mem, m₆, r2₅, VG.Proof.CmacAes.Arm.add0, m₅, r3₄, u₄.mem, u₃.mem, u₂.mem, m₁]; rfl
  -- The memory before the call.
  have cA : State.addr (VG.Proof.CmacAes.Arm.Sc s₀ + BitVec.ofNat 32 2048) = State.addr (VG.Proof.CmacAes.Arm.Sc s₀) + BitVec.ofNat 64 2048 := aS (by decide)
  have kC : (⟨State.addr (VG.Proof.CmacAes.Arm.Kb s₀), 16⟩ : Region).Disjoint ⟨State.addr (VG.Proof.CmacAes.Arm.Sc s₀) + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  have hb : VG.Proof.CmacAes.Arm.below s₉ = VG.Proof.CmacAes.Arm.belowR s₀ := by rw [VG.Proof.CmacAes.Arm.below, sp₉]; rfl
  have pre : VG.Proof.CmacAes.Arm.CallPre s₉ (VG.Proof.CmacAes.Arm.W s₀) (VG.Proof.CmacAes.Arm.Sc s₀ + BitVec.ofNat 32 2048) (VG.Proof.CmacAes.Arm.Kb s₀) (VG.Proof.CmacAes.Arm.Sc s₀) (VG.Proof.CmacAes.Arm.R s₀) .r4 .r5 :=
    { r0 := keep₉ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      r1 := by
        rw [keep₉ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [VG.Proof.CmacAes.Arm.R]
      r2 := by
        rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, G₆, G₅, u₄.other _ (by decide), u₃.gpr,
          u₂.other _ (by decide), g₁]
      r3 := by rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), G₆, G₅, u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.gpr, g₁]
      hra := u₉.gpr
      hrb := r5₉
      regs := by decide
      rounds := hR
      hsp := by rw [sp₉]; exact hp.sp8
      wc := by rw [cA]; exact hp.sch_scr.sub_right (Offset.sub_base _ (by decide))
      wd := hp.sch_k.sub_right (Region.sub_prefix (by decide))
      ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
      cd := by rw [cA]; exact kC.symm
      cs := by rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega)
      ds := (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      bw := by rw [hb]; exact hp.b_sch
      bc := by rw [hb, cA]; exact hp.b_scr.sub_right (Offset.sub_base _ (by decide))
      bd := by rw [hb]; exact hp.b_k.sub_right (Region.sub_prefix (by decide))
      bs := by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide))
      hW := hp.sch_fit
      hC := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
          Nat.mod_eq_of_lt (by omega)]; omega
      hD := by omega
      hS := by omega
      reads := by
        rw [rd₉, wr₉, hp.rd]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨VG.Proof.CmacAes.Arm.schR s₀, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₉, hp.wr, cA]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨VG.Proof.CmacAes.Arm.scR s₀, by simp, 2048, rfl, by simp⟩
        · exact ⟨VG.Proof.CmacAes.Arm.kR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨VG.Proof.CmacAes.Arm.scR s₀, by simp, 0, by simp, by simp⟩
      zero := by rw [mem₉, VG.Proof.CmacAes.Arm.preMem]; exact Proof.Cmac.zero4_bytes _ _ }
  exact ⟨pre, keep₉, r5₉, r6₉, sp₉, rd₉, wr₉, mem₉⟩

theorem subkeys_wp {s₀ : State} (h0 : subkeysArm.pre s₀) :
    WP isa subkeys s₀ fun s' => abiPreserved s₀ s' ∧ subkeysArm.post s₀ s' := by
  have hp := SPre.of h0
  have kf := hp.k_fit
  have sf := hp.scr_fit
  have sf' : (s₀.gpr .r3).toNat + 2176 ≤ 2 ^ 32 := sf
  have hR := hp.rounds
  have hRb : 16 * (VG.Proof.CmacAes.Arm.R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have cK : ∀ d n, d + n ≤ 32 → Covers [⟨State.addr (VG.Proof.CmacAes.Arm.Kb s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Arm.kR s₀, by simp, d, rfl, h⟩
  have cS : ∀ d n, d + n ≤ 2176 → Covers [⟨State.addr (VG.Proof.CmacAes.Arm.Sc s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Arm.scR s₀, by simp, d, rfl, h⟩
  have rw' : ∀ {rs a n}, Covers rs s₀.wr → InRegions rs a n → InRegions (s₀.rd ++ s₀.wr) a n :=
    fun h hi => by obtain ⟨r, hr, hc⟩ := h _ _ hi; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have cKr : ∀ d n, d + n ≤ 32 → Covers [⟨State.addr (VG.Proof.CmacAes.Arm.Kb s₀) + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) :=
    fun d n h a k hi => rw' (cK d n h) hi
  have aS : ∀ {d}, d < 2176 → State.addr (VG.Proof.CmacAes.Arm.Sc s₀ + BitVec.ofNat 32 d) = State.addr (VG.Proof.CmacAes.Arm.Sc s₀) + BitVec.ofNat 64 d :=
    fun _ => addr_add (by omega)
  unfold subkeys
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Arm.pre_wp hp) fun s₉ a => ?_)
  obtain ⟨pre, keep₉, r5₉, r6₉, sp₉, rd₉, wr₉, mem₉⟩ := a
  -- The memory before the call.
  have cA : State.addr (VG.Proof.CmacAes.Arm.Sc s₀ + BitVec.ofNat 32 2048) = State.addr (VG.Proof.CmacAes.Arm.Sc s₀) + BitVec.ofNat 64 2048 := aS (by decide)
  have kC : (⟨State.addr (VG.Proof.CmacAes.Arm.Kb s₀), 16⟩ : Region).Disjoint ⟨State.addr (VG.Proof.CmacAes.Arm.Sc s₀) + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  have f₉ : Frame [VG.Proof.CmacAes.Arm.scR s₀, VG.Proof.CmacAes.Arm.kR s₀] s₀.mem s₉.mem := by
    rw [mem₉, VG.Proof.CmacAes.Arm.preMem]
    refine (((VG.Arm.Spill.saveMem_frame _ _ _ (L := 2176) (by decide) VG.Proof.CmacAes.Arm.saved4 (by decide)).sub fun r hr => ?_).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ?_)).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ?_) <;>
    simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨VG.Proof.CmacAes.Arm.scR s₀, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.CmacAes.Arm.scR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.Arm.kR s₀, by simp, Region.sub_prefix (by decide)⟩
  have zC : Spec.Aes.bytesAt s₉.mem (State.addr (VG.Proof.CmacAes.Arm.Sc s₀) + BitVec.ofNat 64 2048) 16 = Spec.Cmac.zeros 16 := by
    rw [mem₉, VG.Proof.CmacAes.Arm.preMem, Proof.Cmac.zero4, Proof.Cmac.bytesAt_frame16 (Proof.Cmac.frame_store4 _ _ _ _ _) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact kC.symm)]
    exact Proof.Cmac.zero4_bytes _ _
  have hb : VG.Proof.CmacAes.Arm.below s₉ = VG.Proof.CmacAes.Arm.belowR s₀ := by rw [VG.Proof.CmacAes.Arm.below, sp₉]; rfl
  -- The call.
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Arm.ctr_call pre) fun s₁₀ h₁₀ => ?_)
  have sv (r : Reg) (hr : r ∈ preserved) (hlr : r ≠ .lr) : s₁₀.gpr r = s₉.gpr r := h₁₀.saved r hr hlr
  have r6₁₀ : s₁₀.gpr .r6 = VG.Proof.CmacAes.Arm.Kb s₀ := by rw [sv .r6 (by simp [preserved]) (by decide), r6₉]
  have rdwr₁₀ : s₁₀.rd ++ s₁₀.wr = s₀.rd ++ s₀.wr := by rw [h₁₀.rd, h₁₀.wr, rd₉, wr₉]
  have wr₁₀ : s₁₀.wr = s₀.wr := by rw [h₁₀.wr, wr₉]
  have L : Spec.Aes.bytesAt s₁₀.mem (State.addr (VG.Proof.CmacAes.Arm.Kb s₀)) 16 = VG.Proof.CmacAes.Arm.ciph s₀ (Spec.Cmac.zeros 16) := by
    rw [h₁₀.out, cA, zC, Proof.Cmac.bytesAt_frame f₉ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
      · exact hp.sch_k.sub_left (Region.sub_prefix hRb)) (by omega)]
  -- After the call.
  rw [VG.Proof.CmacAes.Arm.subkeysPost_eq]
  refine VG.Proof.CmacAes.Arm.dbl_wp r6₁₀ (by decide) (by decide) (by omega) (by omega)
    (by rw [rdwr₁₀]; exact cKr 0 16 (by decide)) (by rw [wr₁₀]; exact cK 0 16 (by decide))
    fun s₁₁ g₁₁ m₁₁ rd₁₁ wr₁₁ sp₁₁ => ?_
  have r6₁₁ : s₁₁.gpr .r6 = VG.Proof.CmacAes.Arm.Kb s₀ := by
    rw [g₁₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r6₁₀]
  refine VG.Proof.CmacAes.Arm.dbl_wp r6₁₁ (by decide) (by decide) (by omega) (by omega)
    (by rw [rd₁₁, wr₁₁, rdwr₁₀]; exact cKr 0 16 (by decide)) (by rw [wr₁₁, wr₁₀]; exact cK 16 16 (by decide))
    fun s₁₂ g₁₂ m₁₂ rd₁₂ wr₁₂ sp₁₂ => ?_
  have k₁₂ : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → s₁₂.gpr r = s₁₀.gpr r :=
    fun r h0 h1 h2 h3 h4 h12 => by rw [g₁₂ r h0 h1 h2 h3 h4 h12, g₁₁ r h0 h1 h2 h3 h4 h12]
  have r5₁₂ : s₁₂.gpr .r5 = VG.Proof.CmacAes.Arm.Sc s₀ := by
    rw [k₁₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      sv .r5 (by simp [preserved]) (by decide), r5₉]
  have rdwr₁₂ : s₁₂.rd ++ s₁₂.wr = s₀.rd ++ s₀.wr := by rw [rd₁₂, wr₁₂, rd₁₁, wr₁₁, rdwr₁₀]
  have inS : ∀ d, d + 4 ≤ 2176 → InRegions (s₁₂.rd ++ s₁₂.wr) (State.addr (VG.Proof.CmacAes.Arm.Sc s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [rdwr₁₂]
      exact rw' (cS d 4 hd) ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine Spill.restoreList_ok [(.r4, 2064), (.r6, 2072), (.lr, 2076)] s₁₂ _ (by decide) (fun p hp' => ?_)
    fun s₁₃ ld₁₃ ho₁₃ m₁₃ rd₁₃ wr₁₃ sp₁₃ => ?_
  · have hb : 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2080 ∧ p.1 ≠ .r5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl <;> decide
    exact ⟨hb.2.2, by omega, by rw [r5₁₂]; omega, by rw [r5₁₂]; exact inS _ (by omega)⟩
  refine wp_ldr (a := State.addr (VG.Proof.CmacAes.Arm.Sc s₀) + BitVec.ofNat 64 2068) (by decide)
    (by rw [ho₁₃ _ (by decide), r5₁₂]; exact aS (by decide))
    (by rw [rd₁₃, wr₁₃]; exact inS _ (by decide)) fun s₁₄ u₁₄ => WP.block_nil ?_
  -- The slots.
  have slotD : ∀ d, 2064 ≤ d → d + 4 ≤ 2080 →
      ∀ r ∈ [⟨State.addr (VG.Proof.CmacAes.Arm.Sc s₀ + BitVec.ofNat 32 2048), 16⟩, ⟨State.addr (VG.Proof.CmacAes.Arm.Kb s₀), 16⟩,
        ⟨State.addr (VG.Proof.CmacAes.Arm.Sc s₀), 2048⟩, VG.Proof.CmacAes.Arm.below s₉], (⟨State.addr (VG.Proof.CmacAes.Arm.Sc s₀) + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r := by
    intro d h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [cA]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact (hp.k_scr.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by decide))
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · rw [hb]; exact hp.b_scr.symm.sub_left (Offset.sub_base _ (by omega))
  have slotK : ∀ d, 2064 ≤ d → d + 4 ≤ 2080 → ∀ e, e ≤ 16 →
      (⟨State.addr (VG.Proof.CmacAes.Arm.Sc s₀) + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint ⟨State.addr (VG.Proof.CmacAes.Arm.Kb s₀) + BitVec.ofNat 64 e, 16⟩ :=
    fun d h₁ h₂ e he => (hp.k_scr.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
  have slot : ∀ r d, (r, d) ∈ VG.Proof.CmacAes.Arm.saved4 → s₁₂.mem.readW (State.addr (VG.Proof.CmacAes.Arm.Sc s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
    intro r d hrd
    have hd : 2064 ≤ d ∧ d + 4 ≤ 2080 := by
      simp only [VG.Proof.CmacAes.Arm.saved4, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
      omega
    rw [m₁₂, VG.Proof.CmacAes.Arm.dblMem_frame _ _ _ _ |>.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact slotK d hd.1 hd.2 16 (by decide)) (by decide),
      m₁₁, VG.Proof.CmacAes.Arm.dblMem_frame _ _ _ _ |>.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact slotK d hd.1 hd.2 0 (by decide)) (by decide),
      h₁₀.frame.readW (Region.contains_self _ _) (slotD d hd.1 hd.2) (by decide), mem₉, VG.Proof.CmacAes.Arm.preMem,
      Proof.Cmac.zero4, Proof.Cmac.readW_store4_of_sep _ _ _ _
        ((hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by omega))),
      Proof.Cmac.zero4, Proof.Cmac.readW_store4_of_sep _ _ _ _ (Offset.disjoint _ (by omega) (by omega) (by omega)),
      VG.Proof.CmacAes.Arm.saved4_slot _ _ _ hrd]
  refine ⟨⟨fun r hr => ?_, by rw [u₁₄.sp, sp₁₃, sp₁₂, sp₁₁, h₁₀.sp, sp₉]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₁₄.other _ (by decide), ld₁₃ (.r4, 2064) (by simp), r5₁₂, slot .r4 2064 (by decide)]
    · rw [u₁₄.gpr, m₁₃, slot .r5 2068 (by decide)]
    · rw [u₁₄.other _ (by decide), ld₁₃ (.r6, 2072) (by simp), r5₁₂, slot .r6 2072 (by decide)]
    all_goals first
      | rw [u₁₄.other _ (by decide), ld₁₃ (.lr, 2076) (by simp), r5₁₂, slot .lr 2076 (by decide)]
      | rw [u₁₄.other _ (by decide), ho₁₃ _ (by decide),
          k₁₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          sv _ (by simp [preserved]) (by decide),
          keep₉ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · show Spec.Aes.bytesAt s₁₄.mem (State.addr (VG.Proof.CmacAes.Arm.Kb s₀)) 32 = _
    have b₁₁ : Spec.Aes.bytesAt s₁₁.mem (State.addr (VG.Proof.CmacAes.Arm.Kb s₀)) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₁₀.mem (State.addr (VG.Proof.CmacAes.Arm.Kb s₀)) 16) := by
      have := VG.Proof.CmacAes.Arm.dblMem_bytes s₁₀.mem (State.addr (VG.Proof.CmacAes.Arm.Kb s₀)) 0 0
      rw [VG.Proof.CmacAes.Arm.add0] at this; rw [m₁₁, this]
    have lo : Spec.Aes.bytesAt s₁₂.mem (State.addr (VG.Proof.CmacAes.Arm.Kb s₀)) 16 = Spec.Aes.bytesAt s₁₁.mem (State.addr (VG.Proof.CmacAes.Arm.Kb s₀)) 16 := by
      rw [m₁₂]
      exact Proof.Cmac.bytesAt_frame16 (VG.Proof.CmacAes.Arm.dblMem_frame _ _ _ _) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base _ (by decide) (by omega)).symm
    have hi : Spec.Aes.bytesAt s₁₂.mem (State.addr (VG.Proof.CmacAes.Arm.Kb s₀) + BitVec.ofNat 64 16) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₁₁.mem (State.addr (VG.Proof.CmacAes.Arm.Kb s₀)) 16) := by
      have := VG.Proof.CmacAes.Arm.dblMem_bytes s₁₁.mem (State.addr (VG.Proof.CmacAes.Arm.Kb s₀)) 0 16
      rw [VG.Proof.CmacAes.Arm.add0] at this; rw [m₁₂, this]
    rw [u₁₄.mem, m₁₃, Proof.Cmac.bytesAt_32, lo, hi, b₁₁, L]
    rfl

end VG.Proof.CmacAes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Arm.Finalize`. -/
section

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_finalize`, the last block

The steps that form the last block `Mₙ` (§6.2 step 4) in the counter block,
before the chaining value is XORed in: `Mₙ* ⊕ K1` for a complete block
(`full_wp`), else `Mₙ*` copied a byte at a time onto zeros (`copy_wp`), `0x80`
after it, and the block XORed with `K2` (`partial_wp`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_subs wp_cmp wp_ldr wp_ldrb wp_strb
  wp_ldrSp saveMem saveList_ok saveMem_frame readW_writeW_save eval_eq eval_ne sub_beq ofNat_beq_zero sub_ofNat)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame)

section
variable (s₀ : State)

/-- The key: the schedule and the subkeys `K1` and `K2` after it. -/
abbrev keyR : Region := ⟨State.addr (VG.Proof.CmacAes.Arm.W s₀), 272⟩
/-- The last bytes `Mₙ*`. -/
abbrev lastR : Region := ⟨State.addr (VG.Proof.CmacAes.Arm.Dp s₀), VG.Proof.CmacAes.Arm.N s₀⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes. -/
abbrev mn : List Byte :=
  Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.W s₀) + BitVec.ofNat 64 240) 16)
    (Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.W s₀) + BitVec.ofNat 64 256) 16)
    (Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.Dp s₀)) (VG.Proof.CmacAes.Arm.N s₀))

/-- The counter block. -/
abbrev Ca : Addr := State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 2048

end

/-- The precondition, by name. -/
structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacAes.Arm.keyR s₀, VG.Proof.CmacAes.Arm.lastR s₀, VG.Proof.CmacAes.Arm.argsR s₀]
  wr : s₀.wr = [VG.Proof.CmacAes.Arm.stR s₀, VG.Proof.CmacAes.Arm.scrR s₀]
  key_st : (VG.Proof.CmacAes.Arm.keyR s₀).Disjoint (VG.Proof.CmacAes.Arm.stR s₀)
  key_scr : (VG.Proof.CmacAes.Arm.keyR s₀).Disjoint (VG.Proof.CmacAes.Arm.scrR s₀)
  last_st : (VG.Proof.CmacAes.Arm.lastR s₀).Disjoint (VG.Proof.CmacAes.Arm.stR s₀)
  last_scr : (VG.Proof.CmacAes.Arm.lastR s₀).Disjoint (VG.Proof.CmacAes.Arm.scrR s₀)
  st_scr : (VG.Proof.CmacAes.Arm.stR s₀).Disjoint (VG.Proof.CmacAes.Arm.scrR s₀)
  st_args : (VG.Proof.CmacAes.Arm.stR s₀).Disjoint (VG.Proof.CmacAes.Arm.argsR s₀)
  scr_args : (VG.Proof.CmacAes.Arm.scrR s₀).Disjoint (VG.Proof.CmacAes.Arm.argsR s₀)
  b_key : (VG.Proof.CmacAes.Arm.belowR s₀).Disjoint (VG.Proof.CmacAes.Arm.keyR s₀)
  b_last : (VG.Proof.CmacAes.Arm.belowR s₀).Disjoint (VG.Proof.CmacAes.Arm.lastR s₀)
  b_st : (VG.Proof.CmacAes.Arm.belowR s₀).Disjoint (VG.Proof.CmacAes.Arm.stR s₀)
  b_scr : (VG.Proof.CmacAes.Arm.belowR s₀).Disjoint (VG.Proof.CmacAes.Arm.scrR s₀)
  key_fit : (VG.Proof.CmacAes.Arm.W s₀).toNat + 272 ≤ 2 ^ 32
  st_fit : (VG.Proof.CmacAes.Arm.St s₀).toNat + 16 ≤ 2 ^ 32
  last_fit : (VG.Proof.CmacAes.Arm.Dp s₀).toNat + VG.Proof.CmacAes.Arm.N s₀ ≤ 2 ^ 32
  scr_fit : (VG.Proof.CmacAes.Arm.S s₀).toNat + 2176 ≤ 2 ^ 32
  sp8 : 8 ≤ s₀.sp.toNat
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rounds : VG.Proof.CmacAes.Arm.R s₀ = 10 ∨ VG.Proof.CmacAes.Arm.R s₀ = 12 ∨ VG.Proof.CmacAes.Arm.R s₀ = 14
  len : VG.Proof.CmacAes.Arm.N s₀ ≤ 16

theorem FPre.of {s₀ : State} (h : finalizeArm.pre s₀) : VG.Proof.CmacAes.Arm.FPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v⟩

section
variable {s₀ : State} (hp : VG.Proof.CmacAes.Arm.FPre s₀)
include hp

theorem FPre.arg1 : stackArgAddr s₀ 1 = stackArgAddr s₀ 0 + BitVec.ofNat 64 4 := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega), addr_add (by omega)]
  simp

theorem FPre.arg_in {k : Nat} (hk : k < 2) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨VG.Proof.CmacAes.Arm.argsR s₀, by simp [hp.rd], ?_⟩
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · simpa using Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  · rw [hp.arg1]; exact Offset.contains_base _ (by decide) (by decide)

theorem FPre.cS {d n : Nat} (h : d + n ≤ 2176) :
    Covers [⟨State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := by
  rw [hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Arm.scrR s₀, by simp, d, rfl, h⟩

theorem FPre.cKey {d n : Nat} (h : d + n ≤ 272) :
    Covers [⟨State.addr (VG.Proof.CmacAes.Arm.W s₀) + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) := by
  rw [hp.rd]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Arm.keyR s₀, by simp, d, rfl, h⟩

theorem FPre.cLast {d n : Nat} (h : d + n ≤ VG.Proof.CmacAes.Arm.N s₀) :
    Covers [⟨State.addr (VG.Proof.CmacAes.Arm.Dp s₀) + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) := by
  rw [hp.rd]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Arm.lastR s₀, by simp, d, rfl, h⟩

theorem FPre.ca_key {d n : Nat} (h : d + n ≤ 272) :
    (⟨VG.Proof.CmacAes.Arm.Ca s₀, 16⟩ : Region).Disjoint ⟨State.addr (VG.Proof.CmacAes.Arm.W s₀) + BitVec.ofNat 64 d, n⟩ :=
  (hp.key_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ h)

theorem FPre.ca_last : (⟨VG.Proof.CmacAes.Arm.Ca s₀, 16⟩ : Region).Disjoint (VG.Proof.CmacAes.Arm.lastR s₀) :=
  hp.last_scr.symm.sub_left (Offset.sub_base _ (by decide))

end

theorem in_of_cov {rs : List Region} {a : Addr} {n : Nat} (h : Covers [⟨a, n⟩] rs) : InRegions rs a n :=
  h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem cov_mono {rs rs' : List Region} {r : Region} (h : Covers [r] rs) (e : rs = rs') : Covers [r] rs' := e ▸ h

/-! ## Saving the registers -/

/-- The registers `finalize` saves, and where. -/
def fsaved : List (Reg × Nat) := [(.r4, 2064), (.r5, 2068), (.lr, 2072)]

/-- The memory after saving them. -/
def fsMem (s₀ : State) : Mem := VG.Arm.Spill.saveMem s₀.mem (State.addr (VG.Proof.CmacAes.Arm.S s₀)) s₀.gpr VG.Proof.CmacAes.Arm.fsaved

theorem finSave_eq : finSave = .ldrSp .r12 4 :: (fsaved.map (fun p => Instr.str p.1 .r12 p.2) ++
    ([.mov .r5 (.reg .r12), .ldrSp .r4 0, .cmp .r4 (.imm 16)] : List Instr)) := rfl

theorem fsMem_frame (s₀ : State) : Frame [VG.Proof.CmacAes.Arm.scrR s₀] s₀.mem (VG.Proof.CmacAes.Arm.fsMem s₀) :=
  VG.Arm.Spill.saveMem_frame _ _ _ (by decide) VG.Proof.CmacAes.Arm.fsaved (by decide)

theorem fsMem_slot (s₀ : State) {r : Reg} {d : Nat} (h : (r, d) ∈ VG.Proof.CmacAes.Arm.fsaved) :
    (VG.Proof.CmacAes.Arm.fsMem s₀).readW (State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
  Spill.saveMem_saved (lo := 2064) (hi := 2076) (State.addr (VG.Proof.CmacAes.Arm.S s₀)) s₀.gpr s₀.mem VG.Proof.CmacAes.Arm.fsaved (by decide) (r, d) h

/-- What `finSave` leaves. -/
structure FS (s₀ s : State) : Prop where
  keep : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s.gpr r = s₀.gpr r
  r4 : s.gpr .r4 = BitVec.ofNat 32 (VG.Proof.CmacAes.Arm.N s₀)
  r5 : s.gpr .r5 = VG.Proof.CmacAes.Arm.S s₀
  z : s.z = decide (VG.Proof.CmacAes.Arm.N s₀ = 16)
  mem : s.mem = VG.Proof.CmacAes.Arm.fsMem s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finSave_wp {s₀ : State} (hp : VG.Proof.CmacAes.Arm.FPre s₀) : WP isa (.block finSave) s₀ (VG.Proof.CmacAes.Arm.FS s₀) := by
  have hsc := hp.scr_fit
  rw [VG.Proof.CmacAes.Arm.finSave_eq]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = VG.Proof.CmacAes.Arm.S s₀ := u₁.gpr
  refine VG.Arm.Spill.saveList_ok VG.Proof.CmacAes.Arm.fsaved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb : 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2076 := by
      simp only [VG.Proof.CmacAes.Arm.fsaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl <;> decide
    rw [h12, u₁.wr]
    exact ⟨by omega, by omega, VG.Proof.CmacAes.Arm.in_of_cov (hp.cS (d := p.2) (n := 4) (by omega))⟩
  have hm₂ : s₂.mem = VG.Proof.CmacAes.Arm.fsMem s₀ := by
    rw [m₂, u₁.mem, h12, VG.Proof.CmacAes.Arm.fsMem]
    exact VG.Arm.Spill.saveMem_congr _ _ _ fun p hp' => u₁.other _ (by
      simp only [VG.Proof.CmacAes.Arm.fsaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl <;> decide)
  have harg : s₂.mem.readW (stackArgAddr s₀ 0) 32 = stackArg s₀ 0 := by
    rw [hm₂]
    exact (VG.Proof.CmacAes.Arm.fsMem_frame s₀).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.scr_args.symm.sub_left UPre.arg_sub) (by decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact hp.arg_in (by decide)) fun s₄ u₄ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_
  have a0 : stackArg s₀ 0 = BitVec.ofNat 32 (VG.Proof.CmacAes.Arm.N s₀) := by simp [VG.Proof.CmacAes.Arm.N]
  have r4 : s₅.gpr .r4 = BitVec.ofNat 32 (VG.Proof.CmacAes.Arm.N s₀) := by rw [f₅.gpr, u₄.gpr, u₃.mem, harg, a0]
  refine ⟨fun r h4 h5 h12' => ?_, r4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₅.gpr, u₄.other _ h4, u₃.other _ h5, g₂, u₁.other _ h12']
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, g₂, h12]
  · rw [z₅, show s₄.gpr .r4 = s₅.gpr .r4 from (congrFun f₅.gpr _).symm, r4,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, sub_beq (by have := hp.len; omega) (by decide)]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [f₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [f₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [f₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]

/-! ## The last block -/

/-- What the branch on the length leaves: `Mₙ` in the counter block. -/
structure BPost (s₀ s : State) : Prop where
  keep : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → r ≠ .lr → s.gpr r = s₀.gpr r
  r5 : s.gpr .r5 = VG.Proof.CmacAes.Arm.S s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨VG.Proof.CmacAes.Arm.Ca s₀, 16⟩] (VG.Proof.CmacAes.Arm.fsMem s₀) s.mem
  blk : Spec.Aes.bytesAt s.mem (VG.Proof.CmacAes.Arm.Ca s₀) 16 = VG.Proof.CmacAes.Arm.mn s₀

section
variable {s₀ : State} (hp : VG.Proof.CmacAes.Arm.FPre s₀)
include hp

theorem FPre.key_bytes {d : Nat} (h : d + 16 ≤ 272) :
    Spec.Aes.bytesAt (VG.Proof.CmacAes.Arm.fsMem s₀) (State.addr (VG.Proof.CmacAes.Arm.W s₀) + BitVec.ofNat 64 d) 16 =
      Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.W s₀) + BitVec.ofNat 64 d) 16 :=
  Proof.Cmac.bytesAt_frame16 (VG.Proof.CmacAes.Arm.fsMem_frame s₀) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.key_scr.sub_left (Offset.sub_base _ h)

theorem FPre.last_bytes : Spec.Aes.bytesAt (VG.Proof.CmacAes.Arm.fsMem s₀) (State.addr (VG.Proof.CmacAes.Arm.Dp s₀)) (VG.Proof.CmacAes.Arm.N s₀) =
    Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.Dp s₀)) (VG.Proof.CmacAes.Arm.N s₀) :=
  Proof.Cmac.bytesAt_frame (VG.Proof.CmacAes.Arm.fsMem_frame s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.last_scr) (by have := hp.len; omega)

end

theorem full_eq : full = VG.Proof.CmacAes.Arm.xorBlk .r12 .lr .r3 .r0 .r5 0 240 2048 ++ [] := rfl

theorem full_wp {s₀ : State} (hp : VG.Proof.CmacAes.Arm.FPre s₀) (hL : VG.Proof.CmacAes.Arm.N s₀ = 16) {s : State} (h : VG.Proof.CmacAes.Arm.FS s₀ s) :
    WP isa (.block full) s (VG.Proof.CmacAes.Arm.BPost s₀) := by
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have lf := hp.last_fit
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have r3 : s.gpr .r3 = VG.Proof.CmacAes.Arm.Dp s₀ := h.keep _ (by decide) (by decide) (by decide)
  have r0 : s.gpr .r0 = VG.Proof.CmacAes.Arm.W s₀ := h.keep _ (by decide) (by decide) (by decide)
  rw [VG.Proof.CmacAes.Arm.full_eq]
  refine VG.Proof.CmacAes.Arm.xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [r3]; omega) (by rw [r0]; omega) (by rw [h.r5]; omega)
    (by rw [r3, VG.Proof.CmacAes.Arm.add0, hrw]; exact hp.cLast (d := 0) (n := 16) (by omega) |> fun c => by simpa using c)
    (by rw [r0, hrw]; exact hp.cKey (by decide)) (by rw [h.r5, h.wr]; exact hp.cS (by decide))
    fun s' g' => WP.block_nil ?_
  refine ⟨fun r h3 h4 h5 h12 hlr => by rw [g'.gpr r h12 hlr, h.keep r h4 h5 h12], by rw [g'.gpr _ (by decide)
    (by decide), h.r5], by rw [g'.sp, h.sp], by rw [g'.rd, h.rd], by rw [g'.wr, h.wr], ?_, ?_⟩
  · rw [g'.mem, h.mem, h.r5]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  · rw [g'.mem, h.mem, h.r5, r3, r0, VG.Proof.CmacAes.Arm.add0, Proof.Cmac.xor4Mem_bytes _
      (Proof.Cmac.Sep4.of_disjoint (hp.ca_last.sub_right (Region.sub_prefix (by omega))))
      (Proof.Cmac.Sep4.of_disjoint (hp.ca_key (by decide))), hp.key_bytes (by decide)]
    have lb := hp.last_bytes
    rw [hL] at lb
    rw [lb]
    simp only [VG.Proof.CmacAes.Arm.mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, hL, ite_true]
    exact Proof.Cmac.xor_comm _ _

/-! ## Copying the last bytes -/

theorem byte_rt32 (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem copy_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L) (hL : L ≤ 16)
    (h3 : s.gpr .r3 = p) (hlr : s.gpr .lr = c) (h4 : s.gpr .r4 = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + 16 ≤ 2 ^ 32)
    (hr : Covers [⟨State.addr p, L⟩] (s.rd ++ s.wr)) (hw : Covers [⟨State.addr c, 16⟩] s.wr)
    (hd : (⟨State.addr p, L⟩ : Region).Disjoint ⟨State.addr c, 16⟩) :
    WP isa copy s fun s' =>
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) L) ∧
      s'.gpr .lr = c + BitVec.ofNat 32 L ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block [.ldrb .r12 .r3 0, .strb .r12 .lr 0, .dp .add .r3 .r3 (.imm 1),
      .dp .add .lr .lr (.imm 1), .subs .r4 .r4 (.imm 1)]) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r3 = p + BitVec.ofNat 32 i ∧
      t.gpr .lr = c + BitVec.ofNat 32 i ∧ t.gpr .r4 = BitVec.ofNat 32 (L - i) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [h3]; exact (BitVec.add_zero p).symm, by rw [hlr]; exact (BitVec.add_zero c).symm, by rw [h4, Nat.sub_zero],
      by simp [Spec.Aes.bytesAt, VG.WriteBytes.writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, x3, xlr, x4, mem, g, sp, rd, wr⟩
  have aP : State.addr (p + BitVec.ofNat 32 i) = State.addr p + BitVec.ofNat 64 i := addr_add (by omega)
  have aC : State.addr (c + BitVec.ofNat 32 i) = State.addr c + BitVec.ofNat 64 i := addr_add (by omega)
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 i) (by decide) (by rw [x3, BitVec.add_zero, aP])
    (by rw [rd, wr]; exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₁ u₁ => ?_
  refine wp_strb (a := State.addr c + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), xlr, BitVec.add_zero, aC])
    (by rw [u₁.wr, wr]; exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₂ v₂ => ?_
  refine wp_add (op2_imm (by decide)) fun t₃ u₃ => wp_add (op2_imm (by decide)) fun t₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun t₅ u₅ z₅ => WP.block_nil ?_
  have hlen : (Spec.Aes.bytesAt s.mem (State.addr p) i).length = i := Proof.Cmac.bytesAt_length _ _ _
  have hx : VG.WriteBytes.writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) (State.addr p + BitVec.ofNat 64 i) =
      s.mem (State.addr p + BitVec.ofNat 64 i) :=
    (VG.WriteBytes.writeBytes_frame s.mem (State.addr c) _ (R := ⟨State.addr c, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t₅.mem = VG.WriteBytes.writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, u₁.gpr, u₁.mem, mem, VG.Proof.CmacAes.Arm.byte_rt32, hx, Proof.Cmac.bytesAt_succ,
      VG.WriteBytes.writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega), hlen]
  have x4' : t₅.gpr .r4 = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x4,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega)]; rfl
  have ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    show VG.Arm.eval .ne t₅ = _
    rw [eval_ne, z₅, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x4,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub,
      ofNat_beq_zero (by omega)]
  have gg : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → t₅.gpr r = s.gpr r := fun r h₃ h₄ h₁₂ hl => by
    rw [u₅.other _ h₄, u₄.other _ hl, u₃.other _ h₃, v₂.gpr, u₁.other _ h₁₂, g r h₃ h₄ h₁₂ hl]
  have xlr' : t₅.gpr .lr = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xlr,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have x3' : t₅.gpr .r3 = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), x3,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have sp' : t₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, v₂.sp, u₁.sp, sp]
  have rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  have wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [xlr', he], gg, sp', rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega, x3', xlr', x4', hmem, gg,
      sp', rd', wr'⟩

/-! ## A partial last block -/

theorem zero_eq : zero = .mov .r12 (.imm 0) :: (VG.Proof.CmacAes.Arm.zeroBlk .r12 .r5 2048 ++
    ([.dp .add .lr .r5 (.imm (BitVec.ofNat 32 2048)), .cmp .r4 (.imm 0)] : List Instr)) := rfl

theorem padK2_eq : padK2 = .mov .r12 (.imm 0x80) :: .strb .r12 .lr 0 ::
    (VG.Proof.CmacAes.Arm.xorBlk .r12 .lr .r5 .r0 .r5 2048 256 2048 ++ []) := rfl

theorem b80 : ((0x80 : BitVec 32).setWidth 8 : Byte) = 0x80 := by decide

theorem partial_wp {s₀ : State} (hp : VG.Proof.CmacAes.Arm.FPre s₀) (hL : VG.Proof.CmacAes.Arm.N s₀ < 16) {s : State} (h : VG.Proof.CmacAes.Arm.FS s₀ s) :
    WP isa partialBlock s (VG.Proof.CmacAes.Arm.BPost s₀) := by
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have lf := hp.last_fit
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have cA : State.addr (VG.Proof.CmacAes.Arm.S s₀ + BitVec.ofNat 32 2048) = VG.Proof.CmacAes.Arm.Ca s₀ := addr_add (by omega)
  -- Zero the counter block.
  refine WP.seq ?_
  rw [VG.Proof.CmacAes.Arm.zero_eq]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine Proof.CmacAes.Arm.zeroBlk_ok u₁.gpr (by decide) (by rw [u₁.other _ (by decide), h.r5]; omega)
    (by rw [u₁.other _ (by decide), h.r5, u₁.wr, h.wr]; exact hp.cS (by decide)) fun s₂ G₂ m₂ rd₂ wr₂ sp₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ => WP.block_nil ?_
  have r5₂ : s₂.gpr .r5 = VG.Proof.CmacAes.Arm.S s₀ := by rw [G₂, u₁.other _ (by decide), h.r5]
  have mem₄ : s₄.mem = Proof.Cmac.zero4 (VG.Proof.CmacAes.Arm.fsMem s₀) (VG.Proof.CmacAes.Arm.Ca s₀) := by
    rw [f₄.mem, u₃.mem, m₂, u₁.other _ (by decide), h.r5, u₁.mem, h.mem]
  have k₄ : ∀ r, r ≠ .r12 → r ≠ .lr → s₄.gpr r = s.gpr r := fun r h12 hlr => by
    rw [f₄.gpr, u₃.other _ hlr, G₂, u₁.other _ h12]
  have lr₄ : s₄.gpr .lr = VG.Proof.CmacAes.Arm.S s₀ + BitVec.ofNat 32 2048 := by rw [f₄.gpr, u₃.gpr, r5₂]
  have r4₄ : s₄.gpr .r4 = BitVec.ofNat 32 (VG.Proof.CmacAes.Arm.N s₀) := by
    rw [k₄ _ (by decide) (by decide), h.r4]
  have sp₄ : s₄.sp = s.sp := by rw [f₄.sp, u₃.sp, sp₂, u₁.sp]
  have rd₄ : s₄.rd = s.rd := by rw [f₄.rd, u₃.rd, rd₂, u₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [f₄.wr, u₃.wr, wr₂, u₁.wr]
  have ev : isa.eval .eq s₄ = some (decide (VG.Proof.CmacAes.Arm.N s₀ = 0)) := by
    show VG.Arm.eval .eq s₄ = _
    rw [eval_eq, z₄, show s₃.gpr .r4 = s₄.gpr .r4 from (congrFun f₄.gpr _).symm, r4₄,
      MdStream.Arm.cmp0 (by omega)]
  have fz : Frame [⟨VG.Proof.CmacAes.Arm.Ca s₀, 16⟩] (VG.Proof.CmacAes.Arm.fsMem s₀) (Proof.Cmac.zero4 (VG.Proof.CmacAes.Arm.fsMem s₀) (VG.Proof.CmacAes.Arm.Ca s₀)) :=
    Proof.Cmac.frame_store4 _ _ _ _ _
  have lastZ : Spec.Aes.bytesAt (Proof.Cmac.zero4 (VG.Proof.CmacAes.Arm.fsMem s₀) (VG.Proof.CmacAes.Arm.Ca s₀)) (State.addr (VG.Proof.CmacAes.Arm.Dp s₀)) (VG.Proof.CmacAes.Arm.N s₀) =
      Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.Dp s₀)) (VG.Proof.CmacAes.Arm.N s₀) := by
    rw [Proof.Cmac.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.ca_last.symm) (by omega), hp.last_bytes]
  have keyZ : Spec.Aes.bytesAt (Proof.Cmac.zero4 (VG.Proof.CmacAes.Arm.fsMem s₀) (VG.Proof.CmacAes.Arm.Ca s₀)) (State.addr (VG.Proof.CmacAes.Arm.W s₀) + BitVec.ofNat 64 256) 16 =
      Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.W s₀) + BitVec.ofNat 64 256) 16 := by
    rw [Proof.Cmac.bytesAt_frame16 fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hp.ca_key (by decide)).symm), hp.key_bytes (by decide)]
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₅ : State) =>
      s₅.mem = VG.WriteBytes.writeBytes (Proof.Cmac.zero4 (VG.Proof.CmacAes.Arm.fsMem s₀) (VG.Proof.CmacAes.Arm.Ca s₀)) (VG.Proof.CmacAes.Arm.Ca s₀)
        (Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.Dp s₀)) (VG.Proof.CmacAes.Arm.N s₀)) ∧
      s₅.gpr .lr = VG.Proof.CmacAes.Arm.S s₀ + BitVec.ofNat 32 (2048 + VG.Proof.CmacAes.Arm.N s₀) ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s₅.gpr r = s.gpr r) ∧
      s₅.sp = s.sp ∧ s₅.rd = s.rd ∧ s₅.wr = s.wr) ?_ fun s₅ h₅ => ?_)
  · by_cases hL0 : VG.Proof.CmacAes.Arm.N s₀ = 0
    · refine WP.ite true (by rw [ev]; simp [hL0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [mem₄, hL0]; simp [Spec.Aes.bytesAt, VG.WriteBytes.writeBytes_nil], by rw [lr₄, hL0], fun r h₃ h₄ h₁₂ hl =>
        k₄ r h₁₂ hl, sp₄, rd₄, wr₄⟩
    · refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (VG.Proof.CmacAes.Arm.copy_wp (p := VG.Proof.CmacAes.Arm.Dp s₀) (c := VG.Proof.CmacAes.Arm.S s₀ + BitVec.ofNat 32 2048) (L := VG.Proof.CmacAes.Arm.N s₀) (by omega) (by omega)
        (by rw [k₄ _ (by decide) (by decide), h.keep _ (by decide) (by decide) (by decide)]) lr₄ r4₄ lf
        (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
          Nat.mod_eq_of_lt (by omega)]; omega)
        (by rw [rd₄, wr₄, hrw]; simpa using hp.cLast (d := 0) (n := VG.Proof.CmacAes.Arm.N s₀) (by omega))
        (by rw [cA, wr₄, h.wr]; exact hp.cS (by decide)) (by rw [cA]; exact hp.ca_last.symm)) ?_
      rintro s₅ ⟨m₅, lr₅, g₅, sp₅, rd₅, wr₅⟩
      refine ⟨by rw [m₅, mem₄, cA, lastZ], by rw [lr₅, Offset.add_add], fun r h₃ h₄ h₁₂ hl => by
        rw [g₅ r h₃ h₄ h₁₂ hl, k₄ r h₁₂ hl], by rw [sp₅, sp₄], by rw [rd₅, rd₄], by rw [wr₅, wr₄]⟩
  · obtain ⟨m₅, lr₅, g₅, sp₅, rd₅, wr₅⟩ := h₅
    rw [VG.Proof.CmacAes.Arm.padK2_eq]
    have aL : State.addr (VG.Proof.CmacAes.Arm.S s₀ + BitVec.ofNat 32 (2048 + VG.Proof.CmacAes.Arm.N s₀)) = VG.Proof.CmacAes.Arm.Ca s₀ + BitVec.ofNat 64 (VG.Proof.CmacAes.Arm.N s₀) := by
      rw [addr_add (by omega), Offset.add_add]
    refine wp_mov (op2_imm (by decide)) fun s₆ u₆ => ?_
    refine wp_strb (a := VG.Proof.CmacAes.Arm.Ca s₀ + BitVec.ofNat 64 (VG.Proof.CmacAes.Arm.N s₀)) (by decide)
      (by rw [u₆.other _ (by decide), lr₅, BitVec.add_zero, aL])
      (by
        rw [u₆.wr, wr₅, h.wr]
        show InRegions s₀.wr (State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (VG.Proof.CmacAes.Arm.N s₀)) 1
        rw [Offset.add_add]
        exact VG.Proof.CmacAes.Arm.in_of_cov (hp.cS (d := 2048 + VG.Proof.CmacAes.Arm.N s₀) (n := 1) (by omega))) fun s₇ v₇ => ?_
    have g₇ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s₇.gpr r = s.gpr r := fun r h₃ h₄ h₁₂ hl => by
      rw [v₇.gpr, u₆.other _ h₁₂, g₅ r h₃ h₄ h₁₂ hl]
    have r5₇ : s₇.gpr .r5 = VG.Proof.CmacAes.Arm.S s₀ := by
      rw [g₇ _ (by decide) (by decide) (by decide) (by decide), h.r5]
    have r0₇ : s₇.gpr .r0 = VG.Proof.CmacAes.Arm.W s₀ := by
      rw [g₇ _ (by decide) (by decide) (by decide) (by decide), h.keep _ (by decide) (by decide) (by decide)]
    have hlen : (Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.Dp s₀)) (VG.Proof.CmacAes.Arm.N s₀)).length = VG.Proof.CmacAes.Arm.N s₀ :=
      Proof.Cmac.bytesAt_length _ _ _
    have m₇ : s₇.mem = (VG.WriteBytes.writeBytes (Proof.Cmac.zero4 (VG.Proof.CmacAes.Arm.fsMem s₀) (VG.Proof.CmacAes.Arm.Ca s₀)) (VG.Proof.CmacAes.Arm.Ca s₀)
        (Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.Dp s₀)) (VG.Proof.CmacAes.Arm.N s₀))).writeW (VG.Proof.CmacAes.Arm.Ca s₀ + BitVec.ofNat 64 (VG.Proof.CmacAes.Arm.N s₀))
        (0x80 : Byte) := by
      rw [v₇.mem, u₆.gpr, u₆.mem, m₅, VG.Proof.CmacAes.Arm.b80]
    refine VG.Proof.CmacAes.Arm.xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by rw [r5₇]; omega) (by rw [r0₇]; omega) (by rw [r5₇]; omega)
      (by rw [r5₇, v₇.rd, v₇.wr, u₆.rd, u₆.wr, rd₅, wr₅, hrw]
          exact fun a n hi => (hp.cS (d := 2048) (n := 16) (by decide)) a n hi |>
            fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
      (by rw [r0₇, v₇.rd, v₇.wr, u₆.rd, u₆.wr, rd₅, wr₅, hrw]; exact hp.cKey (by decide))
      (by rw [r5₇, v₇.wr, u₆.wr, wr₅, h.wr]; exact hp.cS (by decide)) fun s₈ g₈ => WP.block_nil ?_
    have fW : Frame [⟨VG.Proof.CmacAes.Arm.Ca s₀, 16⟩] (VG.Proof.CmacAes.Arm.fsMem s₀) s₇.mem := by
      rw [m₇]
      refine (fz.trans (VG.WriteBytes.writeBytes_frame _ _ _ ?_)).trans
        ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega)))
      rw [hlen]; simpa using Offset.contains_base (VG.Proof.CmacAes.Arm.Ca s₀) (d := 0) (n := VG.Proof.CmacAes.Arm.N s₀) (k := 16) (by omega) (by decide)
    have pad : Spec.Aes.bytesAt s₇.mem (VG.Proof.CmacAes.Arm.Ca s₀) 16 =
        Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.Dp s₀)) (VG.Proof.CmacAes.Arm.N s₀) ++ [0x80] ++ Spec.Cmac.zeros (16 - VG.Proof.CmacAes.Arm.N s₀ - 1) := by
      have := Proof.Cmac.padded_bytes (Proof.Cmac.zero4 (VG.Proof.CmacAes.Arm.fsMem s₀) (VG.Proof.CmacAes.Arm.Ca s₀)) (VG.Proof.CmacAes.Arm.Ca s₀)
        (Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.Dp s₀)) (VG.Proof.CmacAes.Arm.N s₀)) (by rw [hlen]; exact hL)
        (Proof.Cmac.zero4_bytes _ _)
      rw [hlen] at this
      rw [m₇]; exact this
    have k2 : Spec.Aes.bytesAt s₇.mem (State.addr (VG.Proof.CmacAes.Arm.W s₀) + BitVec.ofNat 64 256) 16 =
        Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.W s₀) + BitVec.ofNat 64 256) 16 := by
      rw [Proof.Cmac.bytesAt_frame16 fW (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hp.ca_key (by decide)).symm), hp.key_bytes (by decide)]
    refine ⟨fun r h₃ h₄ h₅ h₁₂ hl => by rw [g₈.gpr r h₁₂ hl, g₇ r h₃ h₄ h₁₂ hl, h.keep r h₄ h₅ h₁₂],
      by rw [g₈.gpr _ (by decide) (by decide), r5₇], by rw [g₈.sp, v₇.sp, u₆.sp, sp₅, h.sp],
      by rw [g₈.rd, v₇.rd, u₆.rd, rd₅, h.rd], by rw [g₈.wr, v₇.wr, u₆.wr, wr₅, h.wr], ?_, ?_⟩
    · rw [g₈.mem, r5₇]; exact fW.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)
    · rw [g₈.mem, r5₇, r0₇, Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _)
        (Proof.Cmac.Sep4.of_disjoint (hp.ca_key (by decide))), pad, k2]
      simp only [VG.Proof.CmacAes.Arm.mn, Spec.Cmac.lastBlock, hlen, show VG.Proof.CmacAes.Arm.N s₀ ≠ 16 by omega, ite_false]
      exact Proof.Cmac.xor_comm _ _

end VG.Proof.CmacAes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Arm.UpdateCT`. -/
section

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_update` is constant time

The taint analysis does not analyse frames, so two runs from states that agree
on the public arguments are related piece by piece (`RelCT`): the taint
analysis covers the code between the calls, from the public arguments for the
prologue and from the registers the correctness proof pins to them (`LInv`)
afterwards, and each call of `vg_aes_ctr32`, in its frame, is constant time by
its own proof (`ctr_rel`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (eval_eq eval_ne)

/-- The registers holding our variables in the loop. -/
abbrev vars : List Reg := [.r4, .r5, .r6, .r7, .r8, .r10]

section
variable {s₀ s₀' : State} (hq : updateArm.pub s₀ s₀')
include hq

theorem pub_sp : s₀.sp = s₀'.sp := hq.1
theorem pub_W : VG.Proof.CmacAes.Arm.W s₀ = VG.Proof.CmacAes.Arm.W s₀' := hq.2.1
theorem pub_r1 : s₀.gpr .r1 = s₀'.gpr .r1 := hq.2.2.1
theorem pub_R : VG.Proof.CmacAes.Arm.R s₀ = VG.Proof.CmacAes.Arm.R s₀' := by rw [VG.Proof.CmacAes.Arm.R, VG.Proof.CmacAes.Arm.R, VG.Proof.CmacAes.Arm.pub_r1 hq]
theorem pub_St : VG.Proof.CmacAes.Arm.St s₀ = VG.Proof.CmacAes.Arm.St s₀' := hq.2.2.2.1
theorem pub_Dp : VG.Proof.CmacAes.Arm.Dp s₀ = VG.Proof.CmacAes.Arm.Dp s₀' := hq.2.2.2.2.1
theorem pub_N : VG.Proof.CmacAes.Arm.N s₀ = VG.Proof.CmacAes.Arm.N s₀' := by rw [VG.Proof.CmacAes.Arm.N, VG.Proof.CmacAes.Arm.N, hq.2.2.2.2.2.1]
theorem pub_S : VG.Proof.CmacAes.Arm.S s₀ = VG.Proof.CmacAes.Arm.S s₀' := hq.2.2.2.2.2.2
theorem pub_Cb : VG.Proof.CmacAes.Arm.Cb s₀ = VG.Proof.CmacAes.Arm.Cb s₀' := by rw [VG.Proof.CmacAes.Arm.Cb, VG.Proof.CmacAes.Arm.Cb, VG.Proof.CmacAes.Arm.pub_S hq]

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : VG.Proof.CmacAes.Arm.LInv s₀ k s₁) (h₂ : VG.Proof.CmacAes.Arm.LInv s₀' k s₂) :
    ∀ r ∈ VG.Proof.CmacAes.Arm.vars, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [VG.Proof.CmacAes.Arm.vars, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r4, h₂.r4, VG.Proof.CmacAes.Arm.pub_W hq]
  · rw [h₁.r5, h₂.r5, VG.Proof.CmacAes.Arm.pub_r1 hq]
  · rw [h₁.r6, h₂.r6, VG.Proof.CmacAes.Arm.pub_St hq]
  · rw [h₁.r7, h₂.r7, VG.Proof.CmacAes.Arm.pub_Dp hq]
  · rw [h₁.r8, h₂.r8, VG.Proof.CmacAes.Arm.pub_N hq]
  · rw [h₁.r10, h₂.r10, VG.Proof.CmacAes.Arm.pub_S hq]

end

/-! ## One block -/

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : VG.Proof.CmacAes.Arm.CallPre s (VG.Proof.CmacAes.Arm.W s₀) (VG.Proof.CmacAes.Arm.Cb s₀) (VG.Proof.CmacAes.Arm.St s₀) (VG.Proof.CmacAes.Arm.S s₀) (VG.Proof.CmacAes.Arm.R s₀) .r9 .r10
  r7 : s.gpr .r7 = VG.Proof.CmacAes.Arm.Dp s₀ + BitVec.ofNat 32 (16 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (VG.Proof.CmacAes.Arm.N s₀ - k)
  sp : s.sp = s₀.sp

theorem bodyMid_wp {s₀ : State} (hp : VG.Proof.CmacAes.Arm.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.Arm.N s₀) {s : State} (h : VG.Proof.CmacAes.Arm.LInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (VG.Proof.CmacAes.Arm.Mid s₀ k) :=
  WP.mono (VG.Proof.CmacAes.Arm.bodyA_wp hp hk h) fun _ hb =>
    ⟨hb.pre, by rw [hb.keep .r7 (by decide) (by decide) (by decide) (by decide) (by decide), h.r7],
      by rw [hb.keep .r8 (by decide) (by decide) (by decide) (by decide) (by decide), h.r8],
      by rw [hb.sp, h.sp]⟩

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  r7 : s.gpr .r7 = VG.Proof.CmacAes.Arm.Dp s₀ + BitVec.ofNat 32 (16 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (VG.Proof.CmacAes.Arm.N s₀ - k)

theorem call_after {s₀ : State} {k : Nat} {s : State} (h : VG.Proof.CmacAes.Arm.Mid s₀ k s) :
    WP isa (ctrCall .r9 .r10) s (VG.Proof.CmacAes.Arm.After s₀ k) :=
  WP.mono (VG.Proof.CmacAes.Arm.ctr_call h.pre) fun _ hc =>
    ⟨by rw [hc.saved .r7 (by simp [preserved]) (by decide), h.r7],
      by rw [hc.saved .r8 (by simp [preserved]) (by decide), h.r8]⟩

/-- The relation before a block, in two runs. -/
def BRel (s₀ s₀' : State) (k : Nat) (s₁ s₂ : State) : Prop :=
  (k < VG.Proof.CmacAes.Arm.N s₀ ∧ VG.Proof.CmacAes.Arm.LInv s₀ k s₁) ∧ (k < VG.Proof.CmacAes.Arm.N s₀' ∧ VG.Proof.CmacAes.Arm.LInv s₀' k s₂)

theorem body_ct {s₀ s₀' : State} (hp : VG.Proof.CmacAes.Arm.UPre s₀) (hp' : VG.Proof.CmacAes.Arm.UPre s₀') (hq : updateArm.pub s₀ s₀') (k : Nat) :
    RelCT isa (VG.Proof.CmacAes.Arm.BRel s₀ s₀' k) body fun _ _ => True := by
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r7, .r8]) (.block advance) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => k < VG.Proof.CmacAes.Arm.N s₀ ∧ VG.Proof.CmacAes.Arm.LInv s₀ k s) (F' := fun s => k < VG.Proof.CmacAes.Arm.N s₀' ∧ VG.Proof.CmacAes.Arm.LInv s₀' k s)
    (G := VG.Proof.CmacAes.Arm.Mid s₀ k) (G' := VG.Proof.CmacAes.Arm.Mid s₀' k) (Taint.ofRegs VG.Proof.CmacAes.Arm.vars)
    (fun _ _ h h' => Taint.agree_ofRegs (LInv.agree hq h.2 h'.2)) ⟨_, by taint_decide⟩
    (fun _ h => VG.Proof.CmacAes.Arm.bodyMid_wp hp h.1 h.2) (fun _ h => VG.Proof.CmacAes.Arm.bodyMid_wp hp' h.1 h.2)
  have c := rel_wp (F := VG.Proof.CmacAes.Arm.Mid s₀ k) (F' := VG.Proof.CmacAes.Arm.Mid s₀' k) (G := VG.Proof.CmacAes.Arm.After s₀ k) (G' := VG.Proof.CmacAes.Arm.After s₀' k)
    (VG.Proof.CmacAes.Arm.ctr_rel (sp₀ := s₀.sp) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [VG.Proof.CmacAes.Arm.pub_W hq, VG.Proof.CmacAes.Arm.pub_Cb hq, VG.Proof.CmacAes.Arm.pub_St hq, VG.Proof.CmacAes.Arm.pub_S hq, VG.Proof.CmacAes.Arm.pub_R hq]; exact h.2.pre, h.1.sp,
        h.2.sp.trans (VG.Proof.CmacAes.Arm.pub_sp hq).symm⟩)
    (fun _ h => VG.Proof.CmacAes.Arm.call_after h) (fun _ h => VG.Proof.CmacAes.Arm.call_after h)
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => VG.Proof.CmacAes.Arm.After s₀ k s₁ ∧ VG.Proof.CmacAes.Arm.After s₀' k s₂) (Taint.ofRegs [.r7, .r8])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r7, h.2.r7, VG.Proof.CmacAes.Arm.pub_Dp hq]
      · rw [h.1.r8, h.2.r8, VG.Proof.CmacAes.Arm.pub_N hq]) hB
  exact a.seq (c.seq b)

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = VG.Proof.CmacAes.Arm.N s₀ - k ∧ VG.Proof.CmacAes.Arm.BRel s₀ s₀' k s₁ s₂

theorem loop_ct {s₀ s₀' : State} (hp : VG.Proof.CmacAes.Arm.UPre s₀) (hp' : VG.Proof.CmacAes.Arm.UPre s₀') (hq : updateArm.pub s₀ s₀') (n : Nat) :
    RelCT isa (VG.Proof.CmacAes.Arm.LRel s₀ s₀' n) (.loop body .ne) fun s₁ s₂ => VG.Proof.CmacAes.Arm.LInv s₀ (VG.Proof.CmacAes.Arm.N s₀) s₁ ∧ VG.Proof.CmacAes.Arm.LInv s₀' (VG.Proof.CmacAes.Arm.N s₀') s₂ := by
  refine RelCT.loop (M := isa) (VG.Proof.CmacAes.Arm.LRel s₀ s₀') (fun n => ?_) n
  have hN := VG.Proof.CmacAes.Arm.pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : VG.Proof.CmacAes.Arm.LRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = VG.Proof.CmacAes.Arm.N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  have ct := (VG.Proof.CmacAes.Arm.body_ct hp hp' hq k).wp
    (F₁ := fun (s : State) => (VG.Proof.CmacAes.Arm.LInv s₀ (k + 1) s ∧ s.z = decide (VG.Proof.CmacAes.Arm.N s₀ - (k + 1) = 0)) ∧ k < VG.Proof.CmacAes.Arm.N s₀)
    (F₂ := fun (s : State) => VG.Proof.CmacAes.Arm.LInv s₀' (k + 1) s ∧ s.z = decide (VG.Proof.CmacAes.Arm.N s₀' - (k + 1) = 0))
    fun _ _ h => ⟨WP.mono (VG.Proof.CmacAes.Arm.body_ok hp h.1.1 h.1.2) fun _ r => ⟨r, h.1.1⟩, VG.Proof.CmacAes.Arm.body_ok hp' h.2.1 h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨⟨l₁, z₁⟩, hk⟩, ⟨l₂, z₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide (VG.Proof.CmacAes.Arm.N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s₁ = _; rw [eval_ne, z₁]
  have e₂ : isa.eval .ne s₂ = some !decide (VG.Proof.CmacAes.Arm.N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN]
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : VG.Proof.CmacAes.Arm.N s₀ = k + 1 := by
      have : VG.Proof.CmacAes.Arm.N s₀ - (k + 1) = 0 := by simpa using hf
      omega
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : VG.Proof.CmacAes.Arm.N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨VG.Proof.CmacAes.Arm.N s₀ - (k + 1), by omega, k + 1, rfl, ⟨by omega, l₁⟩, ⟨by omega, l₂⟩⟩

/-! ## The whole function -/

theorem update_rel {s₀ s₀' : State} (h0 : updateArm.pre s₀) (h0' : updateArm.pre s₀')
    (hq : updateArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') update fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  obtain ⟨_, hpro⟩ : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 8) (.block (save ++ setup)) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hepi⟩ : ∃ h, (taint.check (Taint.ofRegs [.r10]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have hN := VG.Proof.CmacAes.Arm.pub_N hq
  have hsp := VG.Proof.CmacAes.Arm.pub_sp hq
  have wfA : ∀ {s : State}, VG.Proof.CmacAes.Arm.UPre s →
      s.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 8⟩ r := fun {s} h => by
    have e : (⟨State.addr s.sp, 8⟩ : Region) = VG.Proof.CmacAes.Arm.argsR s := by simp [stackArgAddr]
    refine ⟨h.sp_fit, ?_⟩
    rw [e, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact h.st_args.symm
    · exact h.scr_args.symm
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => VG.Proof.CmacAes.Arm.LInv s₀ 0 s ∧ s.z = decide (VG.Proof.CmacAes.Arm.N s₀ = 0)) (G' := fun s => VG.Proof.CmacAes.Arm.LInv s₀' 0 s ∧ s.z = decide (VG.Proof.CmacAes.Arm.N s₀' = 0))
    (argTaint [.r0, .r1, .r2, .r3] 8)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) hsp (wfA hp) (wfA hp')
        (argMem_of (j := 2) hsp hp.sp_fit fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.2.1
        · exact hq.2.2.1
        · exact hq.2.2.2.1
        · exact hq.2.2.2.2.1
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact hq.2.2.2.2.2.1
        · exact hq.2.2.2.2.2.2) ⟨_, hpro⟩
    (fun s e => by rw [e]; exact VG.Proof.CmacAes.Arm.prologue_wp hp) (fun s e => by rw [e]; exact VG.Proof.CmacAes.Arm.prologue_wp hp')
  have ev {s : State} (h : s.z = decide (VG.Proof.CmacAes.Arm.N s₀ = 0)) : isa.eval .eq s = some (decide (VG.Proof.CmacAes.Arm.N s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h]
  have ev' {s : State} (h : s.z = decide (VG.Proof.CmacAes.Arm.N s₀' = 0)) : isa.eval .eq s = some (decide (VG.Proof.CmacAes.Arm.N s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h, hN]
  have nil := RelCT.taint (A := taint)
    (P := fun a b => ((VG.Proof.CmacAes.Arm.LInv s₀ 0 a ∧ a.z = decide (VG.Proof.CmacAes.Arm.N s₀ = 0)) ∧ (VG.Proof.CmacAes.Arm.LInv s₀' 0 b ∧ b.z = decide (VG.Proof.CmacAes.Arm.N s₀' = 0))) ∧
      isa.eval .eq a = some true) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr)
    hnil
  have mid : RelCT isa (fun a b => (VG.Proof.CmacAes.Arm.LInv s₀ 0 a ∧ a.z = decide (VG.Proof.CmacAes.Arm.N s₀ = 0)) ∧ (VG.Proof.CmacAes.Arm.LInv s₀' 0 b ∧ b.z = decide (VG.Proof.CmacAes.Arm.N s₀' = 0)))
      (.ite .eq (.block []) (.loop body .ne)) (fun a b => VG.Proof.CmacAes.Arm.LInv s₀ (VG.Proof.CmacAes.Arm.N s₀) a ∧ VG.Proof.CmacAes.Arm.LInv s₀' (VG.Proof.CmacAes.Arm.N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1.2, ev' h.2.2]) ?_ ?_
    · refine (nil.wp (F₁ := VG.Proof.CmacAes.Arm.LInv s₀ (VG.Proof.CmacAes.Arm.N s₀)) (F₂ := VG.Proof.CmacAes.Arm.LInv s₀' (VG.Proof.CmacAes.Arm.N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : VG.Proof.CmacAes.Arm.N s₀ = 0 := by
        have := h.2; rw [ev h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1)⟩
    · refine (VG.Proof.CmacAes.Arm.loop_ct hp hp' hq (VG.Proof.CmacAes.Arm.N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ⟨?_, h.1.1.1⟩, ⟨?_, h.1.2.1⟩⟩)
        fun _ _ h => h
      all_goals
        have := h.2; rw [ev h.1.1.2] at this
        have : VG.Proof.CmacAes.Arm.N s₀ ≠ 0 := by simpa using this
        omega
  have epi := RelCT.taint (A := taint) (P := fun a b => VG.Proof.CmacAes.Arm.LInv s₀ (VG.Proof.CmacAes.Arm.N s₀) a ∧ VG.Proof.CmacAes.Arm.LInv s₀' (VG.Proof.CmacAes.Arm.N s₀') b)
    (Taint.ofRegs [.r10]) (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.r10, h.2.r10, VG.Proof.CmacAes.Arm.pub_S hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h).seq (mid.seq epi)

theorem update_ct : ConstantTime isa updateArm.pre updateArm.pub update :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.Arm.update_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Arm.Verified`. -/
section

section

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_subkeys` is constant time

The code before the call and after it is checked by the taint analysis, from
the registers the correctness proof pins (the arguments, then `r5` and `r6`);
the call of `vg_aes_ctr32`, in its frame, is constant time by its own proof
(`ctr_rel`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm

/-- What is known after the call. -/
structure SPost (s₀ : State) (s : State) : Prop where
  r5 : s.gpr .r5 = VG.Proof.CmacAes.Arm.Sc s₀
  r6 : s.gpr .r6 = VG.Proof.CmacAes.Arm.Kb s₀

theorem spost_wp {s₀ s : State} (h : VG.Proof.CmacAes.Arm.SAfter s₀ s) : WP isa (ctrCall .r4 .r5) s (VG.Proof.CmacAes.Arm.SPost s₀) :=
  WP.mono (VG.Proof.CmacAes.Arm.ctr_call h.pre) fun _ hc =>
    ⟨by rw [hc.saved .r5 (by simp [preserved]) (by decide), h.r5],
      by rw [hc.saved .r6 (by simp [preserved]) (by decide), h.r6]⟩

theorem subkeys_rel {s₀ s₀' : State} (h0 : subkeysArm.pre s₀) (h0' : subkeysArm.pre s₀')
    (hq : subkeysArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') subkeys fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄⟩ := hq
  have hp := SPre.of h0
  have hp' := SPre.of h0'
  have eW : VG.Proof.CmacAes.Arm.W s₀' = VG.Proof.CmacAes.Arm.W s₀ := q₁.symm
  have eR : VG.Proof.CmacAes.Arm.R s₀' = VG.Proof.CmacAes.Arm.R s₀ := by rw [VG.Proof.CmacAes.Arm.R, VG.Proof.CmacAes.Arm.R, q₂]
  have eK : VG.Proof.CmacAes.Arm.Kb s₀' = VG.Proof.CmacAes.Arm.Kb s₀ := q₃.symm
  have eS : VG.Proof.CmacAes.Arm.Sc s₀' = VG.Proof.CmacAes.Arm.Sc s₀ := q₄.symm
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.r0, .r1, .r2, .r3]) (.block subkeysPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r5, .r6]) (.block subkeysPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := VG.Proof.CmacAes.Arm.SAfter s₀) (G' := VG.Proof.CmacAes.Arm.SAfter s₀')
    (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun s s' e e' => by
      subst e e'
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) ⟨_, hA⟩
    (fun s e => by rw [e]; exact VG.Proof.CmacAes.Arm.pre_wp hp) (fun s e => by rw [e]; exact VG.Proof.CmacAes.Arm.pre_wp hp')
  have c := rel_wp (F := VG.Proof.CmacAes.Arm.SAfter s₀) (F' := VG.Proof.CmacAes.Arm.SAfter s₀') (G := VG.Proof.CmacAes.Arm.SPost s₀) (G' := VG.Proof.CmacAes.Arm.SPost s₀')
    (VG.Proof.CmacAes.Arm.ctr_rel (sp₀ := s₀.sp) fun s₁ s₂ h =>
      ⟨h.1.pre, by have := h.2.pre; rwa [eW, eS, eK, eR] at this, h.1.sp, h.2.sp.trans q₀.symm⟩)
    (fun _ h => VG.Proof.CmacAes.Arm.spost_wp h) (fun _ h => VG.Proof.CmacAes.Arm.spost_wp h)
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => VG.Proof.CmacAes.Arm.SPost s₀ s₁ ∧ VG.Proof.CmacAes.Arm.SPost s₀' s₂) (Taint.ofRegs [.r5, .r6])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r5, h.2.r5, eS]
      · rw [h.1.r6, h.2.r6, eK]) hB
  exact a.seq (c.seq b)

theorem subkeys_ct : ConstantTime isa subkeysArm.pre subkeysArm.pub subkeys :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.Arm.subkeys_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Arm

end

section

section

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_finalize` is correct

Before the call, the counter block holds `Mₙ ⊕ C`, for the last block `Mₙ` of
§6.2 step 4 and the chaining value `C` at `state`, and the state is zeroed;
the call leaves `CIPH_K(C ⊕ Mₙ)` there (`finalize_raw_wp`, whatever the
32 bytes after the key schedule hold, as AES-SIV's key context needs), and
that is the MAC when they are the subkeys of its cipher (`finalize_wp`,
`Cmac.macFull_split`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg wp_mov wp_add wp_ldr eval_eq)

/-! ## Up to the call -/

/-- What the code before the call leaves. -/
structure FMid (s₀ s : State) : Prop where
  pre : VG.Proof.CmacAes.Arm.CallPre s (VG.Proof.CmacAes.Arm.W s₀) (VG.Proof.CmacAes.Arm.S s₀ + BitVec.ofNat 32 2048) (VG.Proof.CmacAes.Arm.St s₀) (VG.Proof.CmacAes.Arm.S s₀) (VG.Proof.CmacAes.Arm.R s₀) .r4 .r5
  blk : Spec.Aes.bytesAt s.mem (VG.Proof.CmacAes.Arm.Ca s₀) 16 =
    Spec.Cmac.xor (VG.Proof.CmacAes.Arm.mn s₀) (Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.St s₀)) 16)
  frame : Frame [⟨VG.Proof.CmacAes.Arm.Ca s₀, 16⟩, VG.Proof.CmacAes.Arm.stR s₀] (VG.Proof.CmacAes.Arm.fsMem s₀) s.mem
  r5 : s.gpr .r5 = VG.Proof.CmacAes.Arm.S s₀
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .lr → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finArgs_eq : finArgs = VG.Proof.CmacAes.Arm.xorBlk .r12 .lr .r5 .r2 .r5 2048 0 2048 ++
    (.mov .r12 (.imm 0) :: (VG.Proof.CmacAes.Arm.zeroBlk .r12 .r2 0 ++
      ([.mov .r3 (.reg .r2), .dp .add .r2 .r5 (.imm (BitVec.ofNat 32 2048)), .mov .r4 (.imm 1)] :
        List Instr))) := rfl

theorem preserved_ne {r : Reg} (hr : r ∈ preserved) : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem finArgs_wp {s₀ : State} (hp : VG.Proof.CmacAes.Arm.FPre s₀) {s : State} (h : VG.Proof.CmacAes.Arm.BPost s₀ s) :
    WP isa (.block finArgs) s (VG.Proof.CmacAes.Arm.FMid s₀) := by
  have sf := hp.scr_fit
  have tf := hp.st_fit
  have hR := hp.rounds
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have r2 : s.gpr .r2 = VG.Proof.CmacAes.Arm.St s₀ := h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have cA : State.addr (VG.Proof.CmacAes.Arm.S s₀ + BitVec.ofNat 32 2048) = VG.Proof.CmacAes.Arm.Ca s₀ := addr_add (by omega)
  have cSt : (⟨VG.Proof.CmacAes.Arm.Ca s₀, 16⟩ : Region).Disjoint (VG.Proof.CmacAes.Arm.stR s₀) := hp.st_scr.symm.sub_left (Offset.sub_base _ (by decide))
  have wSt : Covers [VG.Proof.CmacAes.Arm.stR s₀] s₀.wr := by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.Arm.stR s₀, by simp, 0, by simp, by simp⟩
  rw [VG.Proof.CmacAes.Arm.finArgs_eq]
  refine VG.Proof.CmacAes.Arm.xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h.r5]; omega) (by rw [r2]; omega) (by rw [h.r5]; omega)
    (by
      rw [h.r5, hrw]
      exact fun a n hi => (hp.cS (d := 2048) (n := 16) (by decide)) a n hi |>
        fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (by
      rw [r2, VG.Proof.CmacAes.Arm.add0, hrw]
      exact fun a n hi => wSt a n hi |> fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [h.r5, h.wr]; exact hp.cS (by decide)) fun s₁ g₁ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have r2₂ : s₂.gpr .r2 = VG.Proof.CmacAes.Arm.St s₀ := by rw [u₂.other _ (by decide), g₁.gpr _ (by decide) (by decide), r2]
  refine Proof.CmacAes.Arm.zeroBlk_ok u₂.gpr (by decide) (by rw [r2₂]; omega)
    (by rw [r2₂, VG.Proof.CmacAes.Arm.add0, u₂.wr, g₁.wr, h.wr]; exact wSt) fun s₃ G₃ m₃ rd₃ wr₃ sp₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s₆.gpr r = s.gpr r :=
    fun r h2 h3 h4 h12 hlr => by
      rw [u₆.other _ h4, u₅.other _ h2, u₄.other _ h3, G₃, u₂.other _ h12, g₁.gpr _ h12 hlr]
  have r5₆ : s₆.gpr .r5 = VG.Proof.CmacAes.Arm.S s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r5]
  have sp₆ : s₆.sp = s₀.sp := by rw [u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, g₁.sp, h.sp]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, g₁.rd, h.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, g₁.wr, h.wr]
  have mem₆ : s₆.mem = Proof.Cmac.zero4 (Proof.Cmac.xor4Mem s.mem (VG.Proof.CmacAes.Arm.Ca s₀) (VG.Proof.CmacAes.Arm.Ca s₀) (State.addr (VG.Proof.CmacAes.Arm.St s₀)))
      (State.addr (VG.Proof.CmacAes.Arm.St s₀)) := by
    rw [u₆.mem, u₅.mem, u₄.mem, m₃, r2₂, VG.Proof.CmacAes.Arm.add0, u₂.mem, g₁.mem, h.r5, r2, VG.Proof.CmacAes.Arm.add0]
  have hb : VG.Proof.CmacAes.Arm.below s₆ = VG.Proof.CmacAes.Arm.belowR s₀ := by rw [VG.Proof.CmacAes.Arm.below, sp₆]; rfl
  have stS : Spec.Aes.bytesAt s.mem (State.addr (VG.Proof.CmacAes.Arm.St s₀)) 16 = Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.St s₀)) 16 :=
    Proof.Cmac.bytesAt_frame16 ((VG.Proof.CmacAes.Arm.fsMem_frame s₀).trans (h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.Arm.scrR s₀, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩)) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.st_scr
  refine ⟨?_, ?_, ?_, r5₆, fun r hr h4 h5 hlr => ?_, sp₆, rd₆, wr₆⟩
  · exact
    { r0 := by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
          h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]
      r1 := by
        rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
          h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [VG.Proof.CmacAes.Arm.R]
      r2 := by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), G₃, u₂.other _ (by decide),
          g₁.gpr _ (by decide) (by decide), h.r5]
      r3 := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, G₃, r2₂]
      hra := u₆.gpr
      hrb := r5₆
      regs := by decide
      rounds := hR
      hsp := by rw [sp₆]; exact hp.sp8
      wc := by rw [cA]; exact (hp.ca_key (d := 0) (n := 240) (by decide)).symm |> fun d => by simpa using d
      wd := hp.key_st.sub_left (Region.sub_prefix (by decide))
      ws := (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      cd := by rw [cA]; exact cSt
      cs := by rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega)
      ds := hp.st_scr.sub_right (Region.sub_prefix (by decide))
      bw := by rw [hb]; exact hp.b_key.sub_right (Region.sub_prefix (by decide))
      bc := by rw [hb, cA]; exact hp.b_scr.sub_right (Offset.sub_base _ (by decide))
      bd := by rw [hb]; exact hp.b_st
      bs := by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide))
      hW := by have := hp.key_fit; omega
      hC := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
          Nat.mod_eq_of_lt (by omega)]; omega
      hD := tf
      hS := by omega
      reads := by
        rw [rd₆, wr₆, hp.rd]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨VG.Proof.CmacAes.Arm.keyR s₀, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₆, hp.wr, cA]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨VG.Proof.CmacAes.Arm.scrR s₀, by simp, 2048, rfl, by simp⟩
        · exact ⟨VG.Proof.CmacAes.Arm.stR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨VG.Proof.CmacAes.Arm.scrR s₀, by simp, 0, by simp, by simp⟩
      zero := by rw [mem₆]; exact Proof.Cmac.zero4_bytes _ _ }
  · rw [mem₆, Proof.Cmac.zero4, Proof.Cmac.bytesAt_frame16 (Proof.Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cSt),
      Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint cSt), h.blk, stS]
  · rw [mem₆]
    refine ((h.frame.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)).mono (by simp)).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp))
  · have hne := VG.Proof.CmacAes.Arm.preserved_ne hr
    rw [keep r hne.2.2.1 hne.2.2.2.1 h4 hne.2.2.2.2 hlr, h.keep r hne.2.2.2.1 h4 h5 hne.2.2.2.2 hlr]

theorem finPre_wp {s₀ : State} (hp : VG.Proof.CmacAes.Arm.FPre s₀) : WP isa finPre s₀ (VG.Proof.CmacAes.Arm.FMid s₀) := by
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Arm.finSave_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.CmacAes.Arm.BPost s₀) ?_ fun _ h => VG.Proof.CmacAes.Arm.finArgs_wp hp h)
  have ev : isa.eval .eq s₁ = some (decide (VG.Proof.CmacAes.Arm.N s₀ = 16)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, h₁.z]
  by_cases hL : VG.Proof.CmacAes.Arm.N s₀ = 16
  · exact WP.ite true (by rw [ev]; simp [hL]) (fun _ => VG.Proof.CmacAes.Arm.full_wp hp hL h₁) (fun h => by cases h)
  · exact WP.ite false (by rw [ev]; simp [hL]) (fun h => by cases h)
      (fun _ => VG.Proof.CmacAes.Arm.partial_wp hp (by have := hp.len; omega) h₁)

/-! ## The whole function -/

/-- What `vg_cmac_aes_finalize` leaves in the state, from the subkeys after
the key schedule, whatever they are. -/
def finalizeRaw (s₀ s' : State) : Prop :=
  Spec.Aes.bytesAt s'.mem (State.addr (VG.Proof.CmacAes.Arm.St s₀)) 16 =
    VG.Proof.CmacAes.Arm.ciph s₀ (Spec.Cmac.xor (VG.Proof.CmacAes.Arm.mn s₀) (Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.St s₀)) 16))

/-- `finalizeArm` with `finalizeRaw` as its postcondition. -/
def finalizeRawArm : Contract isa := { VG.Proof.CmacAes.Arm.finalizeArm with
                                                        post := VG.Proof.CmacAes.Arm.finalizeRaw }

theorem finalize_raw_wp {s₀ : State} (h0 : finalizeArm.pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ VG.Proof.CmacAes.Arm.finalizeRaw s₀ s' := by
  have hp := FPre.of h0
  have hR := hp.rounds
  have hRb : 16 * (VG.Proof.CmacAes.Arm.R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have sf := hp.scr_fit
  have cA : State.addr (VG.Proof.CmacAes.Arm.S s₀ + BitVec.ofNat 32 2048) = VG.Proof.CmacAes.Arm.Ca s₀ := addr_add (by omega)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Arm.finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Arm.ctr_call h₁.pre) fun s₂ h₂ => ?_)
  have r5₂ : s₂.gpr .r5 = VG.Proof.CmacAes.Arm.S s₀ := by rw [h₂.saved .r5 (by simp [preserved]) (by decide), h₁.r5]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]
  have inS : ∀ d, d + 4 ≤ 2176 → InRegions (s₂.rd ++ s₂.wr) (State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [rdwr₂]
      obtain ⟨r, hr, hc⟩ := VG.Proof.CmacAes.Arm.in_of_cov (hp.cS (d := d) (n := 4) hd)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [show ([.ldr .r4 .r5 2064, .ldr .lr .r5 2072, .ldr .r5 .r5 2068] : List Instr) =
    [(.r4, 2064), (.lr, 2072)].map (fun (p : Reg × Nat) => Instr.ldr p.1 .r5 p.2) ++ [.ldr .r5 .r5 2068] from rfl]
  refine Spill.restoreList_ok [(.r4, 2064), (.lr, 2072)] s₂ _ (by decide) (fun p hp' => ?_)
    fun s₃ ld₃ ho₃ m₃ rd₃ wr₃ sp₃ => ?_
  · have hb : 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2076 ∧ p.1 ≠ .r5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl <;> decide
    exact ⟨hb.2.2, by omega, by rw [r5₂]; omega, by rw [r5₂]; exact inS _ (by omega)⟩
  refine wp_ldr (a := State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 2068) (by decide)
    (by rw [ho₃ _ (by decide), r5₂]; exact addr_add (by omega))
    (by rw [rd₃, wr₃]; exact inS _ (by decide)) fun s₄ u₄ => WP.block_nil ?_
  -- The slots, which nothing after the save writes.
  have slot : ∀ r d, (r, d) ∈ VG.Proof.CmacAes.Arm.fsaved → s₂.mem.readW (State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
    intro r d hrd
    have hd : 2064 ≤ d ∧ d + 4 ≤ 2076 := by
      simp only [VG.Proof.CmacAes.Arm.fsaved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
      omega
    rw [h₂.frame.readW (r := ⟨State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [cA]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
        · exact hp.st_scr.symm.sub_left (Offset.sub_base _ (by omega))
        · exact Offset.disjoint_base _ (by omega) (by omega)
        · rw [VG.Proof.CmacAes.Arm.below, h₁.sp]; exact hp.b_scr.symm.sub_left (Offset.sub_base _ (by omega))) (by decide),
      h₁.frame.readW (r := ⟨State.addr (VG.Proof.CmacAes.Arm.S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)
        · exact hp.st_scr.symm.sub_left (Offset.sub_base _ (by omega))) (by decide),
      VG.Proof.CmacAes.Arm.fsMem_slot s₀ hrd]
  have sch : Spec.Aes.bytesAt s₁.mem (State.addr (VG.Proof.CmacAes.Arm.W s₀)) (16 * (VG.Proof.CmacAes.Arm.R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.W s₀)) (16 * (VG.Proof.CmacAes.Arm.R s₀ + 1)) := by
    have f : Frame [VG.Proof.CmacAes.Arm.scrR s₀, VG.Proof.CmacAes.Arm.stR s₀] s₀.mem s₁.mem :=
      (((VG.Proof.CmacAes.Arm.fsMem_frame s₀).mono (by simp)).trans (h₁.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨VG.Proof.CmacAes.Arm.scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
        · exact ⟨VG.Proof.CmacAes.Arm.stR s₀, by simp, fun _ h => h⟩))
    exact Proof.Cmac.bytesAt_frame f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.key_scr.sub_left (Region.sub_prefix (by omega))
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega))) (by omega)
  refine ⟨⟨fun r hr => ?_, by rw [u₄.sp, sp₃, h₂.sp, h₁.sp]⟩, ?_⟩
  · by_cases h4 : r = .r4
    · subst h4; rw [u₄.other _ (by decide), ld₃ (.r4, 2064) (by simp), r5₂, slot .r4 2064 (by decide)]
    by_cases h5 : r = .r5
    · subst h5; rw [u₄.gpr, m₃, slot .r5 2068 (by decide)]
    by_cases hlr : r = .lr
    · subst hlr; rw [u₄.other _ (by decide), ld₃ (.lr, 2072) (by simp), r5₂, slot .lr 2072 (by decide)]
    rw [u₄.other _ h5, ho₃ _ (by simp [h4, hlr]), h₂.saved r hr hlr, h₁.keep r hr h4 h5 hlr]
  · show Spec.Aes.bytesAt s₄.mem (State.addr (VG.Proof.CmacAes.Arm.St s₀)) 16 = _
    rw [u₄.mem, m₃, h₂.out, sch, cA, h₁.blk]

theorem finalize_wp {s₀ : State} (h0 : finalizeArm.pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ finalizeArm.post s₀ s' := by
  have hp := FPre.of h0
  refine WP.mono (VG.Proof.CmacAes.Arm.finalize_raw_wp h0) fun s' ⟨ab, raw⟩ => ⟨ab, fun hk msg hm hne hst => ?_⟩
  have hk' : Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacAes.Arm.W s₀) + BitVec.ofNat 64 240) 32 =
      (Spec.Cmac.subkeys (VG.Proof.CmacAes.Arm.ciph s₀) 16).1 ++ (Spec.Cmac.subkeys (VG.Proof.CmacAes.Arm.ciph s₀) 16).2 := hk
  obtain ⟨e1, e2⟩ := Proof.Cmac.k1k2 (Proof.Cmac.subkeys_aes_length _ _) hk'
  show Spec.Aes.bytesAt s'.mem (State.addr (VG.Proof.CmacAes.Arm.St s₀)) 16 = _
  rw [raw, VG.Proof.CmacAes.Arm.mn, e1, e2, hst,
    Proof.Cmac.macFull_split _ hm (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
      (by rw [Proof.Cmac.bytesAt_length]; exact hne), Proof.Cmac.xor_comm]

end VG.Proof.CmacAes.Arm

end

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_finalize` is constant time

The code before the call is checked by the taint analysis, from the public
arguments (its branches and the copy loop depend only on `last_len`), the call
of `vg_aes_ctr32`, in its frame, is constant time by its own proof
(`ctr_rel`), its arguments pinned by the correctness proof (`FMid`), and the
restore after it by the taint analysis again, from `r5` (the scratch buffer).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm

/-- The restore after the call. -/
abbrev finEnd : List Instr := [.ldr .r4 .r5 2064, .ldr .lr .r5 2072, .ldr .r5 .r5 2068]

theorem finalize_rel {s₀ s₀' : State} (h0 : finalizeArm.pre s₀) (h0' : finalizeArm.pre s₀')
    (hq : finalizeArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finalize fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, q₅, q₆⟩ := hq
  have hp := FPre.of h0
  have hp' := FPre.of h0'
  have eW : VG.Proof.CmacAes.Arm.W s₀' = VG.Proof.CmacAes.Arm.W s₀ := q₁.symm
  have eR : VG.Proof.CmacAes.Arm.R s₀' = VG.Proof.CmacAes.Arm.R s₀ := by rw [VG.Proof.CmacAes.Arm.R, VG.Proof.CmacAes.Arm.R, q₂]
  have eSt : VG.Proof.CmacAes.Arm.St s₀' = VG.Proof.CmacAes.Arm.St s₀ := q₃.symm
  have eS : VG.Proof.CmacAes.Arm.S s₀' = VG.Proof.CmacAes.Arm.S s₀ := q₆.symm
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 8) finPre h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r5]) (.block VG.Proof.CmacAes.Arm.finEnd) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have wfA : ∀ {s : State}, VG.Proof.CmacAes.Arm.FPre s →
      s.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 8⟩ r := fun {s} h => by
    have e : (⟨State.addr s.sp, 8⟩ : Region) = VG.Proof.CmacAes.Arm.argsR s := by simp [stackArgAddr]
    refine ⟨h.sp_fit, ?_⟩
    rw [e, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact h.st_args.symm
    · exact h.scr_args.symm
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := VG.Proof.CmacAes.Arm.FMid s₀) (G' := VG.Proof.CmacAes.Arm.FMid s₀')
    (argTaint [.r0, .r1, .r2, .r3] 8)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) q₀ (wfA hp) (wfA hp')
        (argMem_of (j := 2) q₀ hp.sp_fit fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact q₅
        · exact q₆) ⟨_, hA⟩
    (fun s e => by rw [e]; exact VG.Proof.CmacAes.Arm.finPre_wp hp) (fun s e => by rw [e]; exact VG.Proof.CmacAes.Arm.finPre_wp hp')
  have c := rel_wp (F := VG.Proof.CmacAes.Arm.FMid s₀) (F' := VG.Proof.CmacAes.Arm.FMid s₀') (G := fun s => s.gpr .r5 = VG.Proof.CmacAes.Arm.S s₀)
    (G' := fun s => s.gpr .r5 = VG.Proof.CmacAes.Arm.S s₀')
    (VG.Proof.CmacAes.Arm.ctr_rel (sp₀ := s₀.sp) fun s₁ s₂ h =>
      ⟨h.1.pre, by have := h.2.pre; rwa [eW, eS, eSt, eR] at this, h.1.sp, h.2.sp.trans q₀.symm⟩)
    (fun _ h => WP.mono (VG.Proof.CmacAes.Arm.ctr_call h.pre) fun _ hc => by rw [hc.saved .r5 (by simp [preserved]) (by decide), h.r5])
    (fun _ h => WP.mono (VG.Proof.CmacAes.Arm.ctr_call h.pre) fun _ hc => by rw [hc.saved .r5 (by simp [preserved]) (by decide), h.r5])
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => s₁.gpr .r5 = VG.Proof.CmacAes.Arm.S s₀ ∧ s₂.gpr .r5 = VG.Proof.CmacAes.Arm.S s₀')
    (Taint.ofRegs [.r5]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1, h.2, eS]) hB
  exact a.seq (c.seq b)

theorem finalize_ct : ConstantTime isa finalizeArm.pre finalizeArm.pub finalize :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.Arm.finalize_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Arm

end

/-!
# AES-CMAC on ARMv7: `Verified`

Correctness and constant time, a state satisfying each precondition, and the
shared contracts of `Spec/Cmac/Contract.lean`, with 8 bytes of stack: each
call of `vg_aes_ctr32` pushes its two stack arguments.
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm

/-- A state satisfying `vg_cmac_aes_update`'s precondition (with no blocks,
and the scratch buffer at 0, which the zero stack arguments point at). -/
def updSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x3000, 0⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0, 2176⟩]

theorem update_verified : Verified Arm.target update (Spec.Cmac.aesUpdateContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.CmacAes.Arm.update_wp hs) VG.Proof.CmacAes.Arm.update_ct (by
    sig_implies [Spec.Cmac.aesUpdateContract, Spec.Cmac.aesUpdateSig, VG.Proof.CmacAes.Arm.updateArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [updSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.CmacAes.Arm.updSat)

/-- A state satisfying `vg_cmac_aes_subkeys`'s precondition. -/
def subSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 32⟩, ⟨0x3000, 2176⟩]

theorem subkeys_verified : Verified Arm.target subkeys (Spec.Cmac.aesSubkeysContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.CmacAes.Arm.subkeys_wp hs) VG.Proof.CmacAes.Arm.subkeys_ct (by
    sig_implies [Spec.Cmac.aesSubkeysContract, Spec.Cmac.aesSubkeysSig, VG.Proof.CmacAes.Arm.subkeysArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [subSat] using VG.Proof.CmacAes.Arm.subSat)

/-- A state satisfying `vg_cmac_aes_finalize`'s precondition (with no last
bytes, and the scratch buffer at 0). -/
def finSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x3000, 0⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0, 2176⟩]

theorem finalize_verified : Verified Arm.target finalize (Spec.Cmac.aesFinalizeContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.CmacAes.Arm.finalize_wp hs) VG.Proof.CmacAes.Arm.finalize_ct (by
    sig_implies [Spec.Cmac.aesFinalizeContract, Spec.Cmac.aesFinalizeSig, VG.Proof.CmacAes.Arm.finalizeArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.CmacAes.Arm.finSat)

end VG.Proof.CmacAes.Arm

end
