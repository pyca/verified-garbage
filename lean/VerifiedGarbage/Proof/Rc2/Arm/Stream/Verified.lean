import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Rc2.Arm.Stream.Common
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Rc2.Arm.Stream.Long
import VerifiedGarbage.Proof.Rc2.Scratch

section

/-! # Streaming RC2-CBC on ARMv7: the update functions

Without a complete block, the data is appended to the pending bytes
(`short_ok`); otherwise, after the copies (`long_ok`), the CBC function runs
on `out` and `lr` is restored (`call_ok`). -/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.WriteBytes VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_add wp_ldr wp_ldrSp wp_cmp eval_eq cmp0)

/-- The postcondition of `update`: the callee-saved registers and the contract's. -/
abbrev UpdPost (d : Spec.Rc2.Direction) (s s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (updateContract d).post s s'

/-- With `out_len = 0` (so `pending_len + len < 8`). -/
theorem short_ok (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hz : (stackArg s 1).toNat = 0) (t : State) (ht : Keep s t) :
    WP isa short t (UpdPost d s) := by
  obtain ⟨_, _, hrd, hwr, ctxData, _, _, _, _, _, _, _, _, _, _, _, _, _, fitC, fitD, _, _, hp, hN⟩ := hs
  have hshort : (s.gpr .r1).toNat + (s.gpr .r3).toNat < 8 := by omega
  have hNlt := (s.gpr .r3).isLt
  rw [short]
  refine WP.seq (wp_add (op2_reg _ _) fun t₁ u₁ => WP.block_nil ?_)
  have g₁ (r : Reg) (h₁ : r ≠ .r12) (h₂ : r ≠ .r1) : t₁.gpr r = s.gpr r := by
    rw [u₁.other _ h₂, ht.reg _ h₁]
  have r1₁ : t₁.gpr .r1 = s.gpr .r0 + BitVec.ofNat 32 (s.gpr .r1).toNat := by
    rw [u₁.gpr, ht.reg _ (by decide), ht.reg _ (by decide), ← ofNat_toNat32]
  have hD : State.addr (t₁.gpr .r1) + BitVec.ofNat 64 136 =
      State.addr (s.gpr .r0) + BitVec.ofNat 64 (136 + (s.gpr .r1).toNat) := by
    rw [r1₁, addr_add (by omega), Offset.add_add, Nat.add_comm]
  have dstSub : Region.Sub ⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 (136 + (s.gpr .r1).toNat), (s.gpr .r3).toNat⟩
      ⟨State.addr (s.gpr .r0), 144⟩ := Offset.sub_base _ (by omega)
  apply WP.mono (copy_ok (s := t₁) (src := .r2) (dst := .r1) (cnt := .r3) (so := 0) (dd := 136)
    (L := (s.gpr .r3).toNat) (A := State.addr (s.gpr .r2))
    (B := State.addr (s.gpr .r0) + BitVec.ofNat 64 (136 + (s.gpr .r1).toNat))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₁ _ (by decide) (by decide)]; exact ofNat_toNat32 _) hNlt
    (by rw [g₁ _ (by decide) (by decide)]; omega)
    (by rw [r1₁, toNat_add32 (by omega)]; omega)
    (by rw [g₁ _ (by decide) (by decide)]; exact add0 _) hD
    (fun _ => by
      rw [u₁.rd, u₁.wr, ht.rd, ht.wr, ← add0 (State.addr (s.gpr .r2))]
      exact cov1 (len := (s.gpr .r3).toNat) (by rw [hrd]; simp) (by omega))
    (fun _ => by rw [u₁.wr, ht.wr]; exact cov1 (len := 144) (by rw [hwr]; simp) (by omega))
    (fun _ => ctxData.symm.sub_right dstSub))
  intro s' c'
  have m' : s'.mem = writeBytes s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (136 + (s.gpr .r1).toNat))
      (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) := by
    rw [← ht.mem, ← u₁.mem]; exact c'.mem
  have frame : Frame [⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 (136 + (s.gpr .r1).toNat), (s.gpr .r3).toNat⟩]
      s.mem s'.mem := by
    rw [m']; exact writeBytes_frame' _ _ _ (Proof.Rc2.bytesAt_length _ _ _)
  refine ⟨fun r hr => ?_, ?_⟩
  · by_cases hl : r = .lr
    · subst hl; rw [c'.keep _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide)]
    · obtain ⟨_, h1, h2, h3, h12⟩ := preserved_ne hr hl
      rw [c'.keep _ h2 h1 h3 h12, g₁ _ h12 h1]
  · show Spec.Rc2.contextAt s'.mem _ d _ = _ ∧ _
    rw [hN]
    refine update_post_short hshort ?_ ?_ ?_
    · exact Proof.Rc2.scheduleAt_frame frame _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega))
    · rw [e128]
      exact Proof.Rc2.blockAt_frame frame _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega))
    · rw [e136, Proof.Rc2.bytesAt_add, Offset.add_add,
        Proof.Rc2.bytesAt_frame frame _ _ (by omega) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)),
        m', bytesAt_writeBytes_self _ _ (Proof.Rc2.bytesAt_length _ _ _) (by omega)]

/-- Regions the call leaves alone. -/
theorem callSep {C O S : BitVec 32} {OL : Nat} {sp : Addr} (R : Region)
    (hiv : R.Disjoint ⟨State.addr C + BitVec.ofNat 64 128, 8⟩)
    (hout : R.Disjoint ⟨State.addr O, OL⟩) (hbuf : R.Disjoint ⟨State.addr S, 512⟩)
    (hst : R.Disjoint ⟨sp, 8⟩) :
    ∀ r ∈ [(⟨State.addr C + BitVec.ofNat 64 128, 8⟩ : Region), ⟨State.addr O, OL⟩, ⟨State.addr S, 512⟩,
      ⟨sp, 8⟩], R.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hiv
  · exact hout
  · exact hbuf
  · exact hst

/-- Regions the copies leave alone. -/
theorem midSep {C O S : BitVec 32} {OL : Nat} (R : Region) (hout : R.Disjoint ⟨State.addr O, OL⟩)
    (hpend : R.Disjoint ⟨State.addr C + BitVec.ofNat 64 136, 8⟩)
    (hlr : R.Disjoint ⟨State.addr S + BitVec.ofNat 64 512, 4⟩) :
    ∀ r ∈ [(⟨State.addr O, OL⟩ : Region), ⟨State.addr C + BitVec.ofNat 64 136, 8⟩,
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩], R.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hout
  · exact hpend
  · exact hlr

theorem ivSub (C : BitVec 32) : Region.Sub ⟨State.addr C + BitVec.ofNat 64 128, 8⟩ ⟨State.addr C, 144⟩ :=
  Offset.sub_base _ (by decide)
theorem keySub (C : BitVec 32) : Region.Sub ⟨State.addr C, 128⟩ ⟨State.addr C, 144⟩ :=
  Region.sub_prefix (by decide)
theorem pendSub (C : BitVec 32) : Region.Sub ⟨State.addr C + BitVec.ofNat 64 136, 8⟩ ⟨State.addr C, 144⟩ :=
  Offset.sub_base _ (by decide)
theorem bufSub (S : BitVec 32) : Region.Sub ⟨State.addr S, 512⟩ ⟨State.addr S, 576⟩ :=
  Region.sub_prefix (by decide)
theorem lrSub (S : BitVec 32) : Region.Sub ⟨State.addr S + BitVec.ofNat 64 512, 4⟩ ⟨State.addr S, 576⟩ :=
  Offset.sub_base _ (by decide)

theorem eN {OL : Nat} (h8 : OL % 8 = 0) (hOL : OL < 2 ^ 32) : 8 * (BitVec.ofNat 32 (OL / 8)).toNat = OL := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

theorem eI {C : BitVec 32} (h : C.toNat + 144 ≤ 2 ^ 32) :
    State.addr (C + 128) = State.addr C + BitVec.ofNat 64 128 := addr_add (k := 128) (by omega)

/-- The arguments of the CBC function. -/
theorem mid_pre (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (t : State) (ht : Mid s t) :
    CbcPre t (s.gpr .r0) (s.gpr .r0 + 128) (stackArg s 0) (BitVec.ofNat 32 ((stackArg s 1).toNat / 8))
      (stackArg s 2) := by
  obtain ⟨sp8, _, _, hwr, _, ctxOut, ctxScr, _, _, _, outScr, _, _, bCtx, _, bOut, bScr, _, fitC, _, fitO,
    fitS, hp, hN⟩ := hs
  have eN' := eN (OL := (stackArg s 1).toNat) (by omega) (stackArg s 1).isLt
  have eI' := eI fitC
  have eb : (⟨State.addr t.sp - 8, 8⟩ : Region) = ⟨State.addr s.sp - 8, 8⟩ := by rw [ht.sp]
  refine ⟨ht.r0, ht.r1, ht.r2, ht.r3, ht.r12, by rw [ht.sp]; exact sp8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by omega, by show (s.gpr .r0 + BitVec.ofNat 32 128).toNat + 8 ≤ _; rw [toNat_add32 (by omega)]; omega,
    by rw [eN']; exact fitO, by omega, ?_, ?_⟩
  · rw [eI']; exact Offset.base_disjoint _ (by decide) (by decide)
  · rw [eN']; exact ctxOut.sub_left (keySub _)
  · exact (ctxScr.sub_left (keySub _)).sub_right (bufSub _)
  · rw [eI', eN']; exact ctxOut.sub_left (ivSub _)
  · rw [eI']; exact (ctxScr.sub_left (ivSub _)).sub_right (bufSub _)
  · rw [eN']; exact outScr.sub_right (bufSub _)
  · show (Region.mk (State.addr t.sp - 8) 8).Disjoint _; rw [eb]; exact bCtx.sub_right (keySub _)
  · show (Region.mk (State.addr t.sp - 8) 8).Disjoint _; rw [eb, eI']; exact bCtx.sub_right (ivSub _)
  · show (Region.mk (State.addr t.sp - 8) 8).Disjoint _; rw [eb, eN']; exact bOut
  · show (Region.mk (State.addr t.sp - 8) 8).Disjoint _; rw [eb]; exact bScr.sub_right (bufSub _)
  · rw [ht.rd, ht.wr, hwr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr (s.gpr .r0), 144⟩, by simp, 0, (add0 _).symm, by simp⟩
  · rw [ht.wr, hwr, eI', eN']
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨State.addr (s.gpr .r0), 144⟩, by simp, 128, rfl, by simp⟩
      · exact ⟨⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩, by simp, 0, (add0 _).symm, by simp⟩
      · exact ⟨⟨State.addr (stackArg s 2), 576⟩, by simp, 0, (add0 _).symm, by simp⟩

/-- The update's postcondition, from the memory the call leaves. -/
theorem post_ok (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hnz : (stackArg s 1).toNat ≠ 0) (t : State) (ht : Mid s t) (u : State)
    (hu : CbcPost d t (s.gpr .r0) (s.gpr .r0 + 128) (stackArg s 0)
      (BitVec.ofNat 32 ((stackArg s 1).toNat / 8)) (stackArg s 2) u) :
    (updateContract d).post s u := by
  obtain ⟨_, _, _, _, _, ctxOut, ctxScr, _, _, _, _, _, _, bCtx, _, _, _, _, fitC, _, _, _, hp, hN⟩ := hs
  have frame₁ := ht.frame
  have out₁ := ht.out
  have pend₁ := ht.pend
  obtain ⟨_, _, _, _, frame₂, data₂, iv₂⟩ := hu
  have hOLlt := (stackArg s 1).isLt
  have eb : below t = ⟨State.addr s.sp - 8, 8⟩ := by simp only [below, ht.sp]
  rw [eI fitC, eN (by omega) hOLlt, eb] at frame₂
  rw [eI fitC, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show (stackArg s 1).toNat / 8 < 2 ^ 32 by omega)] at data₂ iv₂
  show Spec.Rc2.contextAt u.mem _ d _ = _ ∧ _
  rw [hN] at out₁ pend₁ data₂ iv₂ frame₁ frame₂ ctxOut ⊢
  rw [Nat.mul_div_cancel _ (by decide : 0 < 8)] at data₂ iv₂
  have keyMid := Proof.Rc2.scheduleAt_frame frame₁ _ (midSep _ (ctxOut.sub_left (keySub _))
    (Offset.base_disjoint _ (by decide) (by decide)) ((ctxScr.sub_left (keySub _)).sub_right (lrSub _)))
  refine update_post_long hp (by omega) out₁ keyMid ?_ ?_ ?_ data₂ iv₂
  · rw [e128]
    exact Proof.Rc2.blockAt_frame frame₁ _ (midSep _ (ctxOut.sub_left (ivSub _))
      (Offset.disjoint _ (by decide) (by decide) (by decide)) ((ctxScr.sub_left (ivSub _)).sub_right (lrSub _)))
  · rw [e136, Proof.Rc2.bytesAt_frame frame₂ _ _ (by omega) (callSep _
        (Offset.disjoint _ (by omega) (by omega) (by decide)) (ctxOut.sub_left (Offset.sub_base _ (by omega)))
        ((ctxScr.sub_left (Offset.sub_base _ (by omega))).sub_right (bufSub _))
        (bCtx.symm.sub_left (Offset.sub_base _ (by omega)))), pend₁]
  · exact Proof.Rc2.scheduleAt_frame frame₂ _ (callSep _ (Offset.base_disjoint _ (by decide) (by decide))
      (ctxOut.sub_left (keySub _)) ((ctxScr.sub_left (keySub _)).sub_right (bufSub _))
      (bCtx.symm.sub_left (keySub _)))

/-- `lr` back from `scratch + 512`, after the call. -/
theorem restore_ok (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hnz : (stackArg s 1).toNat ≠ 0) (t : State) (ht : Mid s t) (u : State)
    (hu : CbcPost d t (s.gpr .r0) (s.gpr .r0 + 128) (stackArg s 0)
      (BitVec.ofNat 32 ((stackArg s 1).toNat / 8)) (stackArg s 2) u) :
    WP isa (.block restoreLr) u (UpdPost d s) := by
  have hpost := post_ok d s hs hnz t ht u hu
  obtain ⟨_, spfit, hrd, hwr, _, ctxOut, ctxScr, ctxArgs, _, _, outScr, outArgs, scrArgs, bCtx, _, bOut,
    bScr, bArgs, fitC, _, _, fitS, hp, hN⟩ := hs
  have frame₁ := ht.frame
  have lr₁ := ht.lr
  obtain ⟨rd₂, wr₂, sp₂, saved₂, frame₂, _, _⟩ := hu
  have hOLlt := (stackArg s 1).isLt
  have eb : below t = ⟨State.addr s.sp - 8, 8⟩ := by simp only [below, ht.sp]
  rw [eI fitC, eN (by omega) hOLlt, eb] at frame₂
  have argR (i : Nat) (hi : i < 3) : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4 :=
    argIn (by rw [hrd]; simp) hi spfit
  rw [show restoreLr = [.ldrSp .r12 8, .ldr .lr .r12 512] from rfl]
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide) (by rw [sp₂, ht.sp]; rfl)
    (by rw [rd₂, wr₂, ht.rd, ht.wr]; exact argR 2 (by decide)) fun u₁ v₁ => ?_
  have hc2 : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s 2) (32 / 8) := by
    rw [stackArgAddr_eq s (i := 2) (by decide) spfit]; exact Offset.contains_base _ (by decide) (by decide)
  have argsS : u.mem.readW (stackArgAddr s 2) 32 = stackArg s 2 := by
    rw [frame₂.readW hc2 (callSep _ (ctxArgs.symm.sub_right (ivSub _)) outArgs.symm
        (scrArgs.symm.sub_right (bufSub _)) bArgs.symm) (by decide),
      stackArg_frame frame₁ spfit (midSep _ outArgs.symm (ctxArgs.symm.sub_right (pendSub _))
        (scrArgs.symm.sub_right (lrSub _))) (by decide)]
  refine wp_ldr (a := State.addr (stackArg s 2) + BitVec.ofNat 64 512) (by decide)
    (by rw [v₁.gpr, argsS]; exact addr_add (by omega))
    (by rw [v₁.rd, v₁.wr, rd₂, wr₂, ht.rd, ht.wr, hwr]
        exact ⟨⟨State.addr (stackArg s 2), 576⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun u₂ v₂ => WP.block_nil ?_
  have lr₂ : u₂.gpr .lr = s.gpr .lr := by
    rw [v₂.gpr, v₁.mem, frame₂.readW (r := ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩)
      (Region.contains_self _ _)
      (callSep _ ((ctxScr.sub_left (ivSub _)).sub_right (lrSub _)).symm (outScr.sub_right (lrSub _)).symm
        (Offset.disjoint_base _ (by decide) (by decide)) (bScr.sub_right (lrSub _)).symm) (by decide), lr₁]
  have mem₂ : u₂.mem = u.mem := by rw [v₂.mem, v₁.mem]
  refine ⟨fun r hr => ?_, ?_⟩
  · by_cases hl : r = .lr
    · subst hl; rw [lr₂]
    · obtain ⟨_, _, _, _, h12⟩ := preserved_ne hr hl
      rw [v₂.other _ hl, v₁.other _ h12, saved₂ r hr hl, ht.callee r hr hl]
  · show Spec.Rc2.contextAt u₂.mem _ d _ = _ ∧ Spec.Rc2.bytesAt u₂.mem _ _ = _
    rw [mem₂]; exact hpost

/-- The call of the CBC function, `lr` restored, and the update's postcondition. -/
theorem call_ok (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hnz : (stackArg s 1).toNat ≠ 0) (t : State) (ht : Mid s t) :
    WP isa (.seq (cbcCall d) (.block restoreLr)) t (UpdPost d s) :=
  WP.seq (WP.mono (cbc_call (d := d) (mid_pre d s hs t ht)) fun u hu => restore_ok d s hs hnz t ht u hu)

/-- The stack arguments after the call are those on entry. -/
theorem args_after (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (t : State) (ht : Mid s t) (u : State)
    (hu : CbcPost d t (s.gpr .r0) (s.gpr .r0 + 128) (stackArg s 0)
      (BitVec.ofNat 32 ((stackArg s 1).toNat / 8)) (stackArg s 2) u) :
    ∀ i < 3, stackArg u i = stackArg s i := by
  obtain ⟨_, spfit, _, _, _, _, _, ctxArgs, _, _, _, outArgs, scrArgs, _, _, _, _, bArgs, fitC, _, _, _, hp,
    hN⟩ := hs
  have frame₂ := hu.frame
  have hOLlt := (stackArg s 1).isLt
  have eb : below t = ⟨State.addr s.sp - 8, 8⟩ := by simp only [below, ht.sp]
  rw [eI fitC, eN (by omega) hOLlt, eb] at frame₂
  intro i hi
  have hc : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s i) (32 / 8) := by
    rw [stackArgAddr_eq s hi spfit]; exact Offset.contains_base _ (by omega) (by omega)
  have ea : stackArgAddr u i = stackArgAddr s i := by unfold stackArgAddr; rw [hu.sp, ht.sp]
  rw [stackArg, ea, frame₂.readW hc (callSep _ (ctxArgs.symm.sub_right (ivSub _)) outArgs.symm
      (scrArgs.symm.sub_right (bufSub _)) bArgs.symm) (by decide),
    stackArg_frame ht.frame spfit (midSep _ outArgs.symm (ctxArgs.symm.sub_right (pendSub _))
      (scrArgs.symm.sub_right (lrSub _))) hi]

/-- The test of `out_len`. -/
theorem b0_wp (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s) :
    WP isa (.block [.ldrSp .r12 4, .cmp .r12 (.imm 0)]) s
      (fun t => Keep s t ∧ t.z = decide ((stackArg s 1).toNat = 0)) := by
  refine wp_ldrSp (a := stackArgAddr s 1) (by decide) rfl
    (argIn (by rw [hs.2.2.1]; simp) (by decide) hs.2.1) fun t₁ u₁ => wp_cmp (op2_imm (by decide)) fun t₂ f₂ z₂ =>
      WP.block_nil ⟨⟨fun r hr => by rw [f₂.gpr, u₁.other _ hr], by rw [f₂.mem, u₁.mem],
        by rw [f₂.rd, u₁.rd], by rw [f₂.wr, u₁.wr], by rw [f₂.sp, u₁.sp]⟩, ?_⟩
  rw [z₂, u₁.gpr, ofNat_toNat32 (s.mem.readW (stackArgAddr s 1) 32), cmp0 (BitVec.isLt _)]; rfl

theorem update_wp (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s) :
    WP isa (update d) s (UpdPost d s) := by
  rw [update]
  refine WP.seq (WP.mono (b0_wp d s hs) fun t₂ ⟨ht, hz⟩ => ?_)
  refine WP.ite (decide ((stackArg s 1).toNat = 0)) (by rw [← hz]; rfl) (fun h => ?_) fun h => ?_
  · exact short_ok d s hs (of_decide_eq_true h) t₂ ht
  · exact long_ok d s hs (of_decide_eq_false h) t₂ ht fun t' ht' => call_ok d s hs (of_decide_eq_false h) t' ht'

theorem update_correct (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s) :
    ∃ t s', Exec isa (update d) s t s' ∧ abiPreserved s s' ∧ (updateContract d).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := update_wp d s hs
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

end VG.Proof.Rc2.Arm.Stream

end

section

section

/-! # Streaming RC2-CBC on ARMv7: `vg_rc2_cbc_init`

The checks of the lengths (`checks_ok`), then, if they pass, the IV copied to
`ctx + 128` and `lr` saved (`args_ok`), the call of `vg_rc2_expand_key`
(`key_call`), and `lr` restored with 0 returned (`tail_ok`). -/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_sub wp_cmp wp_ldr wp_str
  wp_ldrSp eval_ne sub_beq)

theorem range7 (x : BitVec 32) :
    ((x - 1) >>> 7 - 0 == 0) = decide (1 ≤ x.toNat ∧ x.toNat ≤ 128) := by
  rw [show ((x - 1) >>> 7 - 0 : BitVec 32) = (x - 1) >>> 7 from BitVec.sub_zero _]
  have e : ((x - 1) >>> 7).toNat = (2 ^ 32 - 1 + x.toNat) % 2 ^ 32 / 128 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]; rfl
  have h := x.isLt
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, e, show (0 : BitVec 32).toNat = 0 from rfl]
  omega

theorem range10 (x : BitVec 32) :
    ((x - 1) >>> 10 - 0 == 0) = decide (1 ≤ x.toNat ∧ x.toNat ≤ 1024) := by
  rw [show ((x - 1) >>> 10 - 0 : BitVec 32) = (x - 1) >>> 10 from BitVec.sub_zero _]
  have e : ((x - 1) >>> 10).toNat = (2 ^ 32 - 1 + x.toNat) % 2 ^ 32 / 1024 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]; rfl
  have h := x.isLt
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, e, show (0 : BitVec 32).toNat = 0 from rfl]
  omega

theorem eq8 (x : BitVec 32) : (x - 8 == 0) = decide (x.toNat = 8) := by
  rw [ofNat_toNat32 x, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, sub_beq x.isLt (by decide),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem setWidth_append (a b : BitVec 32) : BitVec.setWidth 32 (a ++ b) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append]
  have := b.isLt
  rw [Nat.shiftLeft_eq, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt this]
  omega

theorem wp_mov_imm {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (he : encodable v = true) (k : WP isa (.block is) (s.setReg d v) Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (by simp [exec, Op2.eval, he]) k

/-- The lengths are valid. -/
abbrev IValid (s : State) : Prop :=
  (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128) ∧ (1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024) ∧
    (stackArg s 0).toNat = 8

/-- The error code for invalid lengths. -/
abbrev ICode (s : State) : Nat :=
  if ¬(1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128) then 1
  else if ¬(1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024) then 2 else 3

/-- What the checks leave. -/
structure CheckPost (s c : State) : Prop where
  keep : ∀ r, r ≠ .r0 → r ≠ .r12 → c.gpr r = s.gpr r
  mem : c.mem = s.mem
  rd : c.rd = s.rd
  wr : c.wr = s.wr
  sp : c.sp = s.sp
  z : c.z = decide (IValid s)
  ok : IValid s → c.gpr .r0 = s.gpr .r0
  err : ¬ IValid s → (c.gpr .r0).toNat = ICode s

theorem checks_ok (s : State) (hs : initContract.pre s) : WP isa checks s (CheckPost s) := by
  obtain ⟨_, spfit, hrd, _⟩ := hs
  rw [checks]
  refine WP.seq (wp_sub (op2_imm (by decide)) fun c₁ u₁ => wp_mov (op2_lsr (by decide)) fun c₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun c₃ f₃ z₃ => WP.block_nil ?_)
  have hk : c₃.z = decide (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128) := by
    rw [z₃, u₂.gpr, u₁.gpr, range7]
  have g₃ (r : Reg) (h : r ≠ .r12) : c₃.gpr r = s.gpr r := by rw [f₃.gpr, u₂.other _ h, u₁.other _ h]
  have mem₃ : c₃.mem = s.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
  have rd₃ : c₃.rd = s.rd := by rw [f₃.rd, u₂.rd, u₁.rd]
  have wr₃ : c₃.wr = s.wr := by rw [f₃.wr, u₂.wr, u₁.wr]
  have sp₃ : c₃.sp = s.sp := by rw [f₃.sp, u₂.sp, u₁.sp]
  refine WP.ite (!decide (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128))
    (by show eval .ne c₃ = _; rw [eval_ne, hk]) (fun hb => wp_mov_imm (by decide) (WP.block_nil ?_)) fun hb => ?_
  · have hb : ¬(1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128) := fun h => by simp [h] at hb
    refine ⟨fun r h0 h12 => by rw [gpr_setReg_of_ne _ _ h0, g₃ r h12], by rw [mem_setReg, mem₃],
      by rw [rd_setReg, rd₃], by rw [wr_setReg, wr₃], by rw [sp_setReg, sp₃], ?_, fun h => absurd h.1 hb,
      fun _ => ?_⟩
    · rw [z_setReg, hk]; simp only [IValid, hb, false_and, decide_false]
    · rw [gpr_setReg_self]; simp only [ICode, hb, not_false_eq_true, ite_true]; rfl
  have hb : 1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128 := by simpa using hb
  refine WP.seq (wp_sub (op2_imm (by decide)) fun c₄ u₄ => wp_mov (op2_lsr (by decide)) fun c₅ u₅ =>
    wp_cmp (op2_imm (by decide)) fun c₆ f₆ z₆ => WP.block_nil ?_)
  have he : c₆.z = decide (1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024) := by
    rw [z₆, u₅.gpr, u₄.gpr, g₃ _ (by decide), range10]
  have g₆ (r : Reg) (h : r ≠ .r12) : c₆.gpr r = s.gpr r := by rw [f₆.gpr, u₅.other _ h, u₄.other _ h, g₃ r h]
  have mem₆ : c₆.mem = s.mem := by rw [f₆.mem, u₅.mem, u₄.mem, mem₃]
  have rd₆ : c₆.rd = s.rd := by rw [f₆.rd, u₅.rd, u₄.rd, rd₃]
  have wr₆ : c₆.wr = s.wr := by rw [f₆.wr, u₅.wr, u₄.wr, wr₃]
  have sp₆ : c₆.sp = s.sp := by rw [f₆.sp, u₅.sp, u₄.sp, sp₃]
  refine WP.ite (!decide (1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024))
    (by show eval .ne c₆ = _; rw [eval_ne, he]) (fun hb' => wp_mov_imm (by decide) (WP.block_nil ?_)) fun hb' => ?_
  · have hb' : ¬(1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024) := fun h => by simp [h] at hb'
    refine ⟨fun r h0 h12 => by rw [gpr_setReg_of_ne _ _ h0, g₆ r h12], by rw [mem_setReg, mem₆],
      by rw [rd_setReg, rd₆], by rw [wr_setReg, wr₆], by rw [sp_setReg, sp₆], ?_, fun h => absurd h.2.1 hb',
      fun _ => ?_⟩
    · rw [z_setReg, he]; simp only [IValid, hb', false_and, and_false, decide_false]
    · rw [gpr_setReg_self]; simp only [ICode, hb, hb', not_false_eq_true, ite_true]
      rfl
  have hb' : 1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024 := by simpa using hb'
  rw [show checkIv = [.ldrSp .r12 0, .cmp .r12 (.imm 8)] from rfl]
  refine WP.seq (wp_ldrSp (a := stackArgAddr s 0) (by decide) (by rw [sp₆]; rfl)
    (by rw [rd₆, wr₆]; exact argIn (by rw [hrd]; simp) (by decide) spfit) fun c₇ u₇ =>
      wp_cmp (op2_imm (by decide)) fun c₈ f₈ z₈ => WP.block_nil ?_)
  have hi : c₈.z = decide ((stackArg s 0).toNat = 8) := by
    rw [z₈, u₇.gpr, mem₆, eq8]; rfl
  have g₈ (r : Reg) (h : r ≠ .r12) : c₈.gpr r = s.gpr r := by rw [f₈.gpr, u₇.other _ h, g₆ r h]
  have mem₈ : c₈.mem = s.mem := by rw [f₈.mem, u₇.mem, mem₆]
  have rd₈ : c₈.rd = s.rd := by rw [f₈.rd, u₇.rd, rd₆]
  have wr₈ : c₈.wr = s.wr := by rw [f₈.wr, u₇.wr, wr₆]
  have sp₈ : c₈.sp = s.sp := by rw [f₈.sp, u₇.sp, sp₆]
  refine WP.ite (!decide ((stackArg s 0).toNat = 8))
    (by show eval .ne c₈ = _; rw [eval_ne, hi]) (fun hb'' => wp_mov_imm (by decide) (WP.block_nil ?_))
    fun hb'' => WP.block_nil ?_
  · have hb'' : ¬(stackArg s 0).toNat = 8 := by simpa using hb''
    refine ⟨fun r h0 h12 => by rw [gpr_setReg_of_ne _ _ h0, g₈ r h12], by rw [mem_setReg, mem₈],
      by rw [rd_setReg, rd₈], by rw [wr_setReg, wr₈], by rw [sp_setReg, sp₈], ?_, fun h => absurd h.2.2 hb'',
      fun _ => ?_⟩
    · rw [z_setReg, hi]; simp only [IValid, hb'', and_false, decide_false]
    · rw [gpr_setReg_self]; simp only [ICode, hb, hb']; rfl
  · have hb'' : (stackArg s 0).toNat = 8 := by simpa using hb''
    refine ⟨fun r _ h12 => g₈ r h12, mem₈, rd₈, wr₈, sp₈, ?_, fun _ => g₈ _ (by decide),
      fun h => absurd ⟨hb, hb', hb''⟩ h⟩
    rw [hi]; simp only [IValid, hb, hb', hb'', and_self, decide_true]

end VG.Proof.Rc2.Arm.Stream

end

/-! # Streaming RC2-CBC on ARMv7: `vg_rc2_cbc_init` once the lengths are valid

-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_ldr wp_str wp_ldrSp eval_ne)

/-- The state before the call of `vg_rc2_expand_key`, from the entry state `s`. -/
structure ArgsPost (s u : State) : Prop where
  r0 : u.gpr .r0 = s.gpr .r0
  r1 : u.gpr .r1 = s.gpr .r1
  r2 : u.gpr .r2 = s.gpr .r2
  r3 : u.gpr .r3 = stackArg s 1
  r12 : u.gpr .r12 = stackArg s 2
  callee : ∀ r ∈ preserved, r ≠ .lr → u.gpr r = s.gpr r
  sp : u.sp = s.sp
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  frame : Frame [⟨State.addr (stackArg s 1) + BitVec.ofNat 64 128, 8⟩,
    ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩] s.mem u.mem
  lr : u.mem.readW (State.addr (stackArg s 2) + BitVec.ofNat 64 512) 32 = s.gpr .lr
  iv : Spec.Rc2.blockAt u.mem (State.addr (stackArg s 1) + BitVec.ofNat 64 128) =
    Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r3))

theorem args_ok (s : State) (hs : initContract.pre s) (hv : IValid s) (c : State) (hc : CheckPost s c) :
    WP isa (.block initArgs) c (ArgsPost s) := by
  obtain ⟨_, spfit, hrd, hwr, _, _, ivCtx, ivScr, ctxScr, ctxArgs, scrArgs, _, _, _, _, _, _, fitIV,
    fitC, fitS⟩ := hs
  have hL : (stackArg s 0).toNat = 8 := hv.2.2
  rw [hL] at ivCtx ivScr fitIV hrd
  have g (r : Reg) (h : r ≠ .r12) : c.gpr r = s.gpr r := by
    by_cases h0 : r = .r0
    · subst h0; exact hc.ok hv
    · exact hc.keep r h0 h
  have argR (i : Nat) (hi : i < 3) : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4 :=
    argIn (by rw [hrd]; simp) hi spfit
  generalize hIV : s.gpr .r3 = IV at *
  generalize hCt : stackArg s 1 = Ct at *
  generalize hS : stackArg s 2 = S at *
  generalize hLR : s.gpr .lr = LR at *
  have lrSub : Region.Sub ⟨State.addr S + BitVec.ofNat 64 512, 4⟩ ⟨State.addr S, 576⟩ := Offset.sub_base _ (by decide)
  have ivSub' : Region.Sub ⟨State.addr Ct + BitVec.ofNat 64 128, 8⟩ ⟨State.addr Ct, 144⟩ :=
    Offset.sub_base _ (by decide)
  have argsSep : ∀ r ∈ [(⟨State.addr Ct + BitVec.ofNat 64 128, 8⟩ : Region),
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩], (Region.mk (stackArgAddr s 0) 12).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ctxArgs.symm.sub_right ivSub'
    · exact scrArgs.symm.sub_right lrSub
  rw [show initArgs = [.ldrSp .r12 8, .str .lr .r12 512, .ldr .lr .r3 0, .ldr .r3 .r3 4, .ldrSp .r12 4,
    .str .lr .r12 128, .str .r3 .r12 132, .mov .r3 (.reg .r12), .ldrSp .r12 8] from rfl]
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide) (by rw [hc.sp]; rfl)
    (by rw [hc.rd, hc.wr]; exact argR 2 (by decide)) fun u₁ v₁ => ?_
  have r12₁ : u₁.gpr .r12 = S := by rw [v₁.gpr, hc.mem]; exact hS
  refine wp_str (a := State.addr S + BitVec.ofNat 64 512) (by decide) (by rw [r12₁]; exact addr_add (by omega))
    (by rw [v₁.wr, hc.wr, hwr]; exact ⟨⟨State.addr S, 576⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun u₂ v₂ => ?_
  have m₂ : u₂.mem = s.mem.writeW (State.addr S + BitVec.ofNat 64 512) LR := by
    rw [v₂.mem, v₁.mem, hc.mem, v₁.other _ (by decide), g _ (by decide), hLR]
  have f₂ : Frame [⟨State.addr Ct + BitVec.ofNat 64 128, 8⟩, ⟨State.addr S + BitVec.ofNat 64 512, 4⟩]
      s.mem u₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  have r3₂ : u₂.gpr .r3 = IV := by rw [v₂.gpr, v₁.other _ (by decide), g _ (by decide), hIV]
  have ivR : InRegions (u₂.rd ++ u₂.wr) (State.addr IV) 8 := by
    rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, hc.rd, hc.wr, hrd]; exact ⟨_, by simp, Region.contains_self _ _⟩
  have ivRead (k : Nat) (hk : k ≤ 4) : u₂.mem.readW (State.addr IV + BitVec.ofNat 64 k) 32 =
      s.mem.readW (State.addr IV + BitVec.ofNat 64 k) 32 := by
    rw [m₂]
    refine Mem.readW_writeW_sep (ivScr.sep (Offset.contains_base _ (by omega) (by omega)) ?_) (by decide)
    exact Offset.contains_base _ (by decide) (by decide)
  refine wp_ldr (a := State.addr IV + BitVec.ofNat 64 0) (by decide)
    (by rw [r3₂]; exact addr_add (by omega))
    (by obtain ⟨r, hr, hc'⟩ := ivR; exact ⟨r, hr, by rw [add0]; unfold Region.Contains at hc' ⊢; omega⟩)
    fun u₃ v₃ => ?_
  refine wp_ldr (a := State.addr IV + BitVec.ofNat 64 4) (by decide)
    (by rw [v₃.other _ (by decide), r3₂]; exact addr_add (by omega))
    (by rw [v₃.rd, v₃.wr]; exact (Cbc.halves ivR).2) fun u₄ v₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s 1) (by decide) (by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp, hc.sp]; rfl)
    (by rw [v₄.rd, v₄.wr, v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, hc.rd, hc.wr]; exact argR 1 (by decide))
    fun u₅ v₅ => ?_
  have r12₅ : u₅.gpr .r12 = Ct := by
    rw [v₅.gpr, v₄.mem, v₃.mem, stackArg_frame f₂ spfit argsSep (by decide)]; exact hCt
  have wr₅ : u₅.wr = s.wr := by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, hc.wr]
  refine wp_str (a := State.addr Ct + BitVec.ofNat 64 128) (by decide) (by rw [r12₅]; exact addr_add (by omega))
    (by rw [wr₅, hwr]; exact ⟨⟨State.addr Ct, 144⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩) fun u₆ v₆ => ?_
  refine wp_str (a := State.addr Ct + BitVec.ofNat 64 128 + BitVec.ofNat 64 4) (by decide)
    (by rw [v₆.gpr, r12₅, Offset.add_add]; exact addr_add (by omega))
    (by rw [v₆.wr, wr₅, hwr, Offset.add_add]; exact ⟨⟨State.addr Ct, 144⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun u₇ v₇ => wp_mov (op2_reg _ _) fun u₈ v₈ => ?_
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide)
    (by rw [v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, hc.sp]; rfl)
    (by rw [v₈.rd, v₈.wr, v₇.rd, v₇.wr, v₆.rd, v₆.wr, v₅.rd, wr₅, v₄.rd, v₃.rd, v₂.rd, v₁.rd, hc.rd]
        exact argR 2 (by decide)) fun u₉ v₉ => WP.block_nil ?_
  -- The memory.
  have w0 : u₅.gpr .lr = s.mem.readW (State.addr IV + BitVec.ofNat 64 0) 32 := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, ivRead 0 (by decide)]
  have w1 : u₆.gpr .r3 = s.mem.readW (State.addr IV + BitVec.ofNat 64 4) 32 := by
    rw [v₆.gpr, v₅.other _ (by decide), v₄.gpr, v₃.mem, ivRead 4 (by decide)]
  have m₇ : u₇.mem = u₂.mem.writeW (State.addr Ct + BitVec.ofNat 64 128)
      (s.mem.readW (State.addr IV + BitVec.ofNat 64 4) 32 ++ s.mem.readW (State.addr IV + BitVec.ofNat 64 0) 32) := by
    rw [v₇.mem, w1, v₆.mem, w0, v₅.mem, v₄.mem, v₃.mem, VG.Proof.Rc2.Word32.write64_pair]
  have mem₉ : u₉.mem = u₇.mem := by rw [v₉.mem, v₈.mem]
  have f₇ : Frame [⟨State.addr Ct + BitVec.ofNat 64 128, 8⟩, ⟨State.addr S + BitVec.ofNat 64 512, 4⟩]
      s.mem u₇.mem := by
    rw [m₇]; exact f₂.writeW (by simp) _ (Region.contains_self _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr hl => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.gpr, v₆.gpr, v₅.other _ (by decide),
      v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), g _ (by decide)]
  · rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.gpr, v₆.gpr, v₅.other _ (by decide),
      v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), g _ (by decide)]
  · rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.gpr, v₆.gpr, v₅.other _ (by decide),
      v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), g _ (by decide)]
  · rw [v₉.other _ (by decide), v₈.gpr, v₇.gpr, v₆.gpr, r12₅, hCt]
  · rw [v₉.gpr, v₈.mem, stackArg_frame f₇ spfit argsSep (by decide)]
  · obtain ⟨h0, h1, h2, h3, h12⟩ := preserved_ne hr hl
    rw [v₉.other _ h12, v₈.other _ h3, v₇.gpr, v₆.gpr, v₅.other _ h12, v₄.other _ h3, v₃.other _ hl, v₂.gpr,
      v₁.other _ h12, g _ h12]
  · rw [v₉.sp, v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, hc.sp]
  · rw [v₉.rd, v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, hc.rd]
  · rw [v₉.wr, v₈.wr, v₇.wr, v₆.wr, wr₅]
  · rw [hCt, hS, mem₉]; exact f₇
  · rw [hS, hLR, mem₉, m₇, Mem.readW_writeW_sep (((ctxScr.sub_left ivSub').sub_right lrSub).symm.sep (Region.contains_self _ _)
      (Region.contains_self _ _)) (by decide), m₂, Mem.readW_writeW_self32]
  · rw [hCt, hIV, mem₉, m₇, Proof.Rc2.blockAt_store64, add0, ← VG.Proof.Rc2.Word32.read64_pair,
      ← Proof.Rc2.blockAt_read64]

end VG.Proof.Rc2.Arm.Stream

end

section

/-!
# Streaming RC2-CBC on ARMv7: the update functions are constant time

The taint analysis does not analyse frames, so two runs from states that agree
on the public arguments are related piece by piece (`RelCT`): the test of
`out_len`, the copies before the call and the restore of `lr` after it are
checked by the taint analysis, from the public arguments (in registers and on
the stack), whose values in each run the correctness proofs pin; the branch on
`out_len` agrees in both runs; and the call of the CBC function, in its frame,
is constant time by its own proof (`cbc_rel`).
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (eval_eq)

theorem wp_nil_inv {s : State} {Q : State → Prop} (h : WP isa (.block []) s Q) : Q s := by
  obtain ⟨_, _, he, hq⟩ := h
  cases he with
  | block h => simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]; exact hq

theorem sa0' (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  unfold stackArgAddr; rw [show s.sp + BitVec.ofNat 32 (4 * 0) = s.sp from BitVec.add_zero _]

/-- Two states agree on the registers `rs` and the 12 bytes of stack arguments. -/
theorem agree12 {rs : List Reg} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) (hsp : s₁.sp = s₂.sp)
    (fit : s₁.sp.toNat + 12 ≤ 2 ^ 32)
    (hw₁ : ∀ r ∈ s₁.wr, Region.Disjoint ⟨stackArgAddr s₁ 0, 12⟩ r)
    (hw₂ : ∀ r ∈ s₂.wr, Region.Disjoint ⟨stackArgAddr s₂ 0, 12⟩ r)
    (ha : ∀ i < 3, stackArg s₁ i = stackArg s₂ i) : VG.Arm.Taint.Agree (argTaint rs 12) s₁ s₂ :=
  agree_argTaint h hsp ⟨fit, by rw [← sa0']; exact hw₁⟩ ⟨hsp ▸ fit, by rw [← sa0']; exact hw₂⟩
    (argMem_of (j := 3) hsp fit ha)

/-- The code before the call, its pieces associated to the left. -/
def prefixL : Prog isa :=
  .seq (.seq (.seq (.seq (.seq (.seq (.block toOut) (copy .r0 136 .lr 0 .r1)) (.block middle))
    (copy .r2 0 .lr 0 .r1)) (.block toPending)) (copy .r2 0 .lr 136 .r3)) (.block cbcArgs)

theorem prefix_wp (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hnz : (stackArg s 1).toNat ≠ 0) (t : State) (ht : Keep s t) : WP isa prefixL t (Mid s) := by
  have h := long_ok' d s hs hnz t ht (tail := .block []) (Q := Mid s) fun t' h => WP.block_nil h
  rw [longWith] at h
  have h := WP.assoc' (WP.assoc' (WP.assoc' (WP.assoc' (WP.assoc' (WP.assoc' h)))))
  exact WP.mono (WP.seq_iff.mp h) fun _ h => wp_nil_inv h

theorem b0_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12)
    (.block [.ldrSp .r12 4, .cmp .r12 (.imm 0)]) hc).isSome = true := ⟨_, by taint_decide⟩
theorem short_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12) short hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem prefix_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12) prefixL hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem restore_taint : ∃ hc, (VG.Taint.check taint (argTaint [] 12) (.block restoreLr) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem stackArg_keep {s t : State} (ht : Keep s t) (i : Nat) : stackArg t i = stackArg s i := by
  unfold stackArg stackArgAddr; rw [ht.mem, ht.sp]

theorem wrSep (d : Spec.Rc2.Direction) {s : State} (h : (updateContract d).pre s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨stackArgAddr s 0, 12⟩ r := by
  obtain ⟨_, _, _, hwr, _, _, _, ctxArgs, _, _, _, outArgs, scrArgs, _⟩ := h
  rw [hwr]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ctxArgs.symm
  · exact outArgs.symm
  · exact scrArgs.symm

theorem update_rel (d : Spec.Rc2.Direction) {s₀ s₀' : State} (h0 : (updateContract d).pre s₀)
    (h0' : (updateContract d).pre s₀') (hq : (updateContract d).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (update d) fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := hq
  have fit := h0.2.1
  have qa : ∀ i < 3, stackArg s₀ i = stackArg s₀' i := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact q₅
    · exact q₆
    · exact q₇
  have regs : ∀ r ∈ ([.r0, .r1, .r2, .r3] : List Reg), s₀.gpr r = s₀'.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  have keepAgree : ∀ t t', Keep s₀ t → Keep s₀' t' →
      VG.Arm.Taint.Agree (argTaint [.r0, .r1, .r2, .r3] 12) t t' := fun t t' k k' =>
    agree12 (fun r hr => by
        have hr12 : r ≠ .r12 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> decide
        rw [k.reg r hr12, k'.reg r hr12]; exact regs r hr)
      (by rw [k.sp, k'.sp, q₀]) (by rw [k.sp]; exact fit)
      (by rw [k.wr, show stackArgAddr t 0 = stackArgAddr s₀ 0 by unfold stackArgAddr; rw [k.sp]]; exact wrSep d h0)
      (by rw [k'.wr, show stackArgAddr t' 0 = stackArgAddr s₀' 0 by unfold stackArgAddr; rw [k'.sp]]
          exact wrSep d h0')
      (fun i hi => by rw [stackArg_keep k, stackArg_keep k']; exact qa i hi)
  rw [update]
  refine RelCT.seq (rel_agree (F := (· = s₀)) (F' := (· = s₀'))
    (G := fun t => Keep s₀ t ∧ t.z = decide ((stackArg s₀ 1).toNat = 0))
    (G' := fun t => Keep s₀' t ∧ t.z = decide ((stackArg s₀' 1).toNat = 0))
    (argTaint [.r0, .r1, .r2, .r3] 12)
    (fun s s' e e' => by
      subst e e'
      exact agree12 regs q₀ fit (wrSep d h0) (wrSep d h0') qa) b0_taint
    (fun s e => e ▸ b0_wp d s₀ h0) (fun s e => e ▸ b0_wp d s₀' h0')) ?_
  refine RelCT.ite (fun t t' ⟨⟨_, z⟩, ⟨_, z'⟩⟩ => by
    show eval .eq t = eval .eq t'; rw [eval_eq, eval_eq, z, z', q₆]) ?_ ?_
  · refine (rel_agree (F := fun t => Keep s₀ t ∧ (stackArg s₀ 1).toNat = 0)
      (F' := fun t => Keep s₀' t ∧ (stackArg s₀' 1).toNat = 0) (G := fun _ => True) (G' := fun _ => True)
      (argTaint [.r0, .r1, .r2, .r3] 12) (fun t t' k k' => keepAgree t t' k.1 k'.1) short_taint
      (fun t k => WP.mono (short_ok d s₀ h0 k.2 t k.1) fun _ _ => trivial)
      (fun t k => WP.mono (short_ok d s₀' h0' k.2 t k.1) fun _ _ => trivial)).mono ?_ fun _ _ _ => trivial
    rintro t t' ⟨⟨⟨k, z⟩, ⟨k', z'⟩⟩, he⟩
    have h1 : (stackArg s₀ 1).toNat = 0 := by
      change eval .eq t = _ at he
      rw [eval_eq, z] at he; exact of_decide_eq_true (Option.some.inj he)
    exact ⟨⟨k, h1⟩, ⟨k', by rw [← q₆]; exact h1⟩⟩
  by_cases hz0 : (stackArg s₀ 1).toNat = 0
  · refine RelCT.of_false fun t t' ⟨⟨⟨_, z⟩, _⟩, he⟩ => ?_
    change eval .eq t = _ at he
    rw [eval_eq, z, hz0] at he; simp at he
  have hz0' : (stackArg s₀' 1).toNat ≠ 0 := by rw [← q₆]; exact hz0
  rw [long_eq, longWith]
  apply RelCT.assoc; apply RelCT.assoc; apply RelCT.assoc; apply RelCT.assoc; apply RelCT.assoc
  apply RelCT.assoc
  refine RelCT.mono (P := fun t t' => (Keep s₀ t ∧ (stackArg s₀ 1).toNat ≠ 0) ∧
    (Keep s₀' t' ∧ (stackArg s₀' 1).toNat ≠ 0)) ?_ ?_ fun _ _ h => h
  · refine RelCT.seq (rel_agree (F := fun t => Keep s₀ t ∧ (stackArg s₀ 1).toNat ≠ 0)
      (F' := fun t => Keep s₀' t ∧ (stackArg s₀' 1).toNat ≠ 0) (G := Mid s₀) (G' := Mid s₀')
      (argTaint [.r0, .r1, .r2, .r3] 12) (fun t t' k k' => keepAgree t t' k.1 k'.1) prefix_taint
      (fun t k => prefix_wp d s₀ h0 k.2 t k.1) (fun t k => prefix_wp d s₀' h0' k.2 t k.1)) ?_
    have hct : RelCT isa (fun t t' => Mid s₀ t ∧ Mid s₀' t') (cbcCall d) fun _ _ => True :=
      cbc_rel (sp₀ := s₀.sp) fun t t' ⟨m, m'⟩ => ⟨mid_pre d s₀ h0 t m, by
        have := mid_pre d s₀' h0' t' m'; rwa [← q₁, ← q₅, ← q₆, ← q₇] at this, m.sp, m'.sp.trans q₀.symm⟩
    refine RelCT.seq (rel_wp (G := fun u => ∃ t, Mid s₀ t ∧ CbcPost d t (s₀.gpr .r0) (s₀.gpr .r0 + 128)
        (stackArg s₀ 0) (BitVec.ofNat 32 ((stackArg s₀ 1).toNat / 8)) (stackArg s₀ 2) u)
      (G' := fun u => ∃ t, Mid s₀' t ∧ CbcPost d t (s₀'.gpr .r0) (s₀'.gpr .r0 + 128)
        (stackArg s₀' 0) (BitVec.ofNat 32 ((stackArg s₀' 1).toNat / 8)) (stackArg s₀' 2) u) hct
      (fun t m => WP.mono (cbc_call (mid_pre d s₀ h0 t m)) fun u hu => ⟨t, m, hu⟩)
      (fun t m => WP.mono (cbc_call (mid_pre d s₀' h0' t m)) fun u hu => ⟨t, m, hu⟩)) ?_
    refine rel_agree (argTaint [] 12) (fun u u' ⟨t, m, c⟩ ⟨t', m', c'⟩ => ?_) restore_taint
      (fun u ⟨t, m, c⟩ => WP.mono (restore_ok d s₀ h0 hz0 t m u c) fun _ _ => trivial)
      (fun u ⟨t, m, c⟩ => WP.mono (restore_ok d s₀' h0' hz0' t m u c) fun _ _ => trivial) |>.mono
      (fun _ _ h => h) fun _ _ _ => trivial
    exact agree12 (fun r hr => (List.not_mem_nil hr).elim) (by rw [c.sp, m.sp, c'.sp, m'.sp, q₀])
      (by rw [c.sp, m.sp]; exact fit)
      (by rw [c.wr, m.wr, show stackArgAddr u 0 = stackArgAddr s₀ 0 by unfold stackArgAddr; rw [c.sp, m.sp]]
          exact wrSep d h0)
      (by rw [c'.wr, m'.wr, show stackArgAddr u' 0 = stackArgAddr s₀' 0 by unfold stackArgAddr; rw [c'.sp, m'.sp]]
          exact wrSep d h0')
      (fun i hi => by rw [args_after d s₀ h0 t m u c i hi, args_after d s₀' h0' t' m' u' c' i hi]; exact qa i hi)
  · intro t t' ⟨⟨⟨k, _⟩, ⟨k', _⟩⟩, _⟩
    exact ⟨⟨k, hz0⟩, ⟨k', hz0'⟩⟩

theorem update_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (updateContract d).pre (updateContract d).pub (update d) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (update_rel d h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Rc2.Arm.Stream

end

section

/-! # Streaming RC2-CBC on ARMv7: `vg_rc2_cbc_init` is correct

-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd op2_reg wp_ldr wp_ldrSp eval_ne)

/-- The postcondition of `init`: the callee-saved registers and the contract's. -/
abbrev InitPost (s s' : State) : Prop := (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ initContract.post s s'

theorem key_pre (s : State) (hs : initContract.pre s) (hv : IValid s) (u : State) (hu : ArgsPost s u) :
    KeyPre u (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (stackArg s 1) (stackArg s 2) := by
  obtain ⟨sp8, _, hrd, hwr, keyCtx, keyScr, _, _, ctxScr, _, _, bKey, _, bCtx, bScr, _, fitK, _, fitC, fitS⟩ := hs
  have p128 : Region.Sub ⟨State.addr (stackArg s 1), 128⟩ ⟨State.addr (stackArg s 1), 144⟩ :=
    Region.sub_prefix (by decide)
  have p512 : Region.Sub ⟨State.addr (stackArg s 2), 512⟩ ⟨State.addr (stackArg s 2), 576⟩ :=
    Region.sub_prefix (by decide)
  have eb : (⟨State.addr u.sp - 8, 8⟩ : Region) = ⟨State.addr s.sp - 8, 8⟩ := by rw [hu.sp]
  refine ⟨hu.r0, hu.r1, hu.r2, hu.r3, hu.r12, by rw [hu.sp]; exact sp8,
    ⟨hv.1.1, hv.1.2, hv.2.1.1, hv.2.1.2⟩, keyCtx.sub_right p128, keyScr.sub_right p512,
    (ctxScr.sub_left p128).sub_right p512, ?_, ?_, ?_, fitK, by omega, by omega, ?_, ?_⟩
  · show (Region.mk (State.addr u.sp - 8) 8).Disjoint _; rw [eb]; exact bKey
  · show (Region.mk (State.addr u.sp - 8) 8).Disjoint _; rw [eb]; exact bCtx.sub_right p128
  · show (Region.mk (State.addr u.sp - 8) 8).Disjoint _; rw [eb]; exact bScr.sub_right p512
  · rw [hu.rd, hu.wr, hrd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, by simp, 0, (add0 _).symm, by simp⟩
  · rw [hu.wr, hwr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr (stackArg s 1), 144⟩, by simp, 0, (add0 _).symm, by simp⟩
      · exact ⟨⟨State.addr (stackArg s 2), 576⟩, by simp, 0, (add0 _).symm, by simp⟩

theorem tail_ok (s : State) (hs : initContract.pre s) (hv : IValid s) (u : State) (hu : ArgsPost s u)
    (v : State) (hk : KeyPost u (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (stackArg s 1) (stackArg s 2) v) :
    WP isa (.block (restoreLr ++ ([.mov .r0 (.imm 0)] : List Instr))) v (InitPost s) := by
  obtain ⟨_, spfit, hrd, hwr, keyCtx, keyScr, _, _, ctxScr, ctxArgs, scrArgs, bKey, _, bCtx, bScr, bArgs,
    fitK, _, fitC, fitS⟩ := hs
  have eb : below u = ⟨State.addr s.sp - 8, 8⟩ := by simp only [below, hu.sp]
  have frame₂ := hk.frame
  rw [eb] at frame₂
  have p128 : Region.Sub ⟨State.addr (stackArg s 1), 128⟩ ⟨State.addr (stackArg s 1), 144⟩ :=
    Region.sub_prefix (by decide)
  have i128 : Region.Sub ⟨State.addr (stackArg s 1) + BitVec.ofNat 64 128, 8⟩ ⟨State.addr (stackArg s 1), 144⟩ :=
    Offset.sub_base _ (by decide)
  have p512 : Region.Sub ⟨State.addr (stackArg s 2), 512⟩ ⟨State.addr (stackArg s 2), 576⟩ :=
    Region.sub_prefix (by decide)
  have l512 : Region.Sub ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩ ⟨State.addr (stackArg s 2), 576⟩ :=
    Offset.sub_base _ (by decide)
  rw [show restoreLr ++ [.mov .r0 (.imm 0)] = [.ldrSp .r12 8, .ldr .lr .r12 512, .mov .r0 (.imm 0)] from rfl]
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide) (by rw [hk.sp, hu.sp]; rfl)
    (by rw [hk.rd, hk.wr, hu.rd, hu.wr]; exact argIn (by rw [hrd]; simp) (by decide) spfit) fun v₁ w₁ => ?_
  have hc2 : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s 2) (32 / 8) := by
    rw [stackArgAddr_eq s (i := 2) (by decide) spfit]; exact Offset.contains_base _ (by decide) (by decide)
  have argsS : v.mem.readW (stackArgAddr s 2) 32 = stackArg s 2 := by
    rw [frame₂.readW hc2 (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ctxArgs.symm.sub_right p128
        · exact scrArgs.symm.sub_right p512
        · exact bArgs.symm) (by decide)]
    refine stackArg_frame hu.frame spfit (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ctxArgs.symm.sub_right i128
    · exact scrArgs.symm.sub_right l512
  refine wp_ldr (a := State.addr (stackArg s 2) + BitVec.ofNat 64 512) (by decide)
    (by rw [w₁.gpr, argsS]; exact addr_add (by omega))
    (by rw [w₁.rd, w₁.wr, hk.rd, hk.wr, hu.rd, hu.wr, hwr]
        exact ⟨⟨State.addr (stackArg s 2), 576⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun v₂ w₂ => wp_mov_imm (by decide) (WP.block_nil ?_)
  have lr₂ : v₂.gpr .lr = s.gpr .lr := by
    rw [w₂.gpr, w₁.mem, frame₂.readW (r := ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ((ctxScr.sub_left p128).sub_right l512).symm
        · exact Offset.disjoint_base _ (by decide) (by decide)
        · exact (bScr.sub_right l512).symm) (by decide), hu.lr]
  have mem₂ : v₂.mem = v.mem := by rw [w₂.mem, w₁.mem]
  refine ⟨fun r hr => ?_, ?_⟩
  · by_cases hl : r = .lr
    · subst hl; rw [gpr_setReg_of_ne _ _ (by decide), lr₂]
    · obtain ⟨h0, _, _, _, h12⟩ := preserved_ne hr hl
      rw [gpr_setReg_of_ne _ _ h0, w₂.other _ hl, w₁.other _ h12, hk.saved r hr hl, hu.callee r hr hl]
  · have hsched : Spec.Rc2.scheduleAt (v₂.setReg .r0 0).mem (State.addr (stackArg s 1)) =
        Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (s.gpr .r2).toNat := by
      rw [mem_setReg, mem₂, hk.sched, Proof.Rc2.bytesAt_frame hu.frame _ _ (by omega) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact keyCtx.sub_right i128
        · exact keyScr.sub_right l512)]
    have hiv : Spec.Rc2.blockAt (v₂.setReg .r0 0).mem (State.addr (stackArg s 1) + 128) =
        Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r3)) := by
      rw [mem_setReg, mem₂, e128, Proof.Rc2.blockAt_frame frame₂ _ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint_base _ (by decide) (by decide)
        · exact (ctxScr.sub_left i128).sub_right p512
        · exact (bCtx.sub_right i128).symm), hu.iv]
    exact init_post hv.1 hv.2.1 hv.2.2 (by rw [setWidth_append, gpr_setReg_self]) hsched hiv

theorem init_wp (s : State) (hs : initContract.pre s) : WP isa init s (InitPost s) := by
  rw [init]
  refine WP.seq (WP.mono (checks_ok s hs) fun c hc => ?_)
  by_cases hv : IValid s
  · refine WP.ite false (by show eval .ne c = _; rw [eval_ne, hc.z]; simp [hv]) (fun h => absurd h (by simp))
      fun _ => ?_
    rw [initBody]
    exact WP.seq (WP.mono (args_ok s hs hv c hc) fun u hu =>
      WP.seq (WP.mono (key_call (key_pre s hs hv u hu)) fun v hk => tail_ok s hs hv u hu v hk))
  · refine WP.ite true (by show eval .ne c = _; rw [eval_ne, hc.z]; simp [hv]) (fun _ => WP.block_nil ?_)
      (fun h => absurd h (by simp))
    refine ⟨fun r hr => ?_, ?_⟩
    · have h : r ≠ .r0 ∧ r ≠ .r12 := by
        by_cases hl : r = .lr
        · subst hl; decide
        · obtain ⟨h0, _, _, _, h12⟩ := preserved_ne hr hl; exact ⟨h0, h12⟩
      exact hc.keep r h.1 h.2
    · exact init_post_error (by rw [setWidth_append]; exact hc.err hv) hv

theorem init_correct (s : State) (hs : initContract.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initContract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := init_wp s hs
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

end VG.Proof.Rc2.Arm.Stream

end

section

/-!
# Streaming RC2-CBC on ARMv7: `vg_rc2_cbc_init` is constant time

As for the updates (`Stream/UpdateCT.lean`): the checks, the copy of the IV
and the restore of `lr` are checked by the taint analysis, from the public
arguments; the branch on the checks agrees in both runs, as the lengths are
public; and the call of `vg_rc2_expand_key`, in its frame, is constant time by
its own proof (`key_rel`).
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (eval_ne)

/-- The stack arguments after the call are those on entry. -/
theorem args_after_key (s : State) (hs : initContract.pre s) (u : State) (hu : ArgsPost s u) (v : State)
    (hk : KeyPost u (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (stackArg s 1) (stackArg s 2) v) :
    ∀ i < 3, stackArg v i = stackArg s i := by
  obtain ⟨_, spfit, _, _, _, _, _, _, _, ctxArgs, scrArgs, _, _, _, _, bArgs, _⟩ := hs
  have eb : below u = ⟨State.addr s.sp - 8, 8⟩ := by simp only [below, hu.sp]
  have frame₂ := hk.frame
  rw [eb] at frame₂
  intro i hi
  have hc : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s i) (32 / 8) := by
    rw [stackArgAddr_eq s hi spfit]; exact Offset.contains_base _ (by omega) (by omega)
  have ea : stackArgAddr v i = stackArgAddr s i := by unfold stackArgAddr; rw [hk.sp, hu.sp]
  rw [stackArg, ea, frame₂.readW hc (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ctxArgs.symm.sub_right (Region.sub_prefix (by decide))
      · exact scrArgs.symm.sub_right (Region.sub_prefix (by decide))
      · exact bArgs.symm) (by decide)]
  refine stackArg_frame hu.frame spfit (fun r hr => ?_) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ctxArgs.symm.sub_right (Offset.sub_base _ (by decide))
  · exact scrArgs.symm.sub_right (Offset.sub_base _ (by decide))

theorem iwrSep {s : State} (h : initContract.pre s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨stackArgAddr s 0, 12⟩ r := by
  obtain ⟨_, _, _, hwr, _, _, _, _, _, ctxArgs, scrArgs, _⟩ := h
  rw [hwr]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ctxArgs.symm
  · exact scrArgs.symm

theorem checks_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12) checks hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem initArgs_taint :
    ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12) (.block initArgs) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem tail_taint :
    ∃ hc, (VG.Taint.check taint (argTaint [] 12) (.block (restoreLr ++ ([.mov .r0 (.imm 0)] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem init_rel {s₀ s₀' : State} (h0 : initContract.pre s₀) (h0' : initContract.pre s₀')
    (hq : initContract.pub s₀ s₀') : RelCT isa (fun a b => a = s₀ ∧ b = s₀') init fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := hq
  have fit := h0.2.1
  have qa : ∀ i < 3, stackArg s₀ i = stackArg s₀' i := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact q₅
    · exact q₆
    · exact q₇
  have regs : ∀ r ∈ ([.r0, .r1, .r2, .r3] : List Reg), s₀.gpr r = s₀'.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  have hvq : IValid s₀ ↔ IValid s₀' := by simp only [IValid, q₂, q₃, q₅]
  rw [init]
  refine RelCT.seq (rel_agree (F := (· = s₀)) (F' := (· = s₀')) (G := CheckPost s₀) (G' := CheckPost s₀')
    (argTaint [.r0, .r1, .r2, .r3] 12)
    (fun s s' e e' => by
      subst e e'
      exact agree12 regs q₀ fit (iwrSep h0) (iwrSep h0') qa) checks_taint
    (fun s e => e ▸ checks_ok s₀ h0) (fun s e => e ▸ checks_ok s₀' h0')) ?_
  refine RelCT.ite (fun c c' ⟨hc, hc'⟩ => by
    show eval .ne c = eval .ne c'; rw [eval_ne, eval_ne, hc.z, hc'.z]; simp only [hvq]) ?_ ?_
  · exact RelCT.block_nil fun _ _ _ => trivial
  by_cases hv : IValid s₀
  swap
  · refine RelCT.of_false fun c c' ⟨⟨hc, _⟩, he⟩ => ?_
    change eval .ne c = _ at he
    rw [eval_ne, hc.z] at he; simp [hv] at he
  have hv' : IValid s₀' := hvq.mp hv
  rw [initBody]
  refine RelCT.mono (P := fun c c' => CheckPost s₀ c ∧ CheckPost s₀' c') ?_ (fun _ _ h => h.1)
    fun _ _ h => h
  refine RelCT.seq (rel_agree (G := ArgsPost s₀) (G' := ArgsPost s₀') (argTaint [.r0, .r1, .r2, .r3] 12)
    (fun c c' hc hc' => ?_) initArgs_taint
    (fun c hc => args_ok s₀ h0 hv c hc) (fun c hc => args_ok s₀' h0' hv' c hc)) ?_
  · have g : ∀ {s c}, IValid s → CheckPost s c → ∀ r ∈ ([.r0, .r1, .r2, .r3] : List Reg), c.gpr r = s.gpr r :=
      fun hv hc r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hc.ok hv
        all_goals exact hc.keep _ (by decide) (by decide)
    have st : ∀ {s c}, CheckPost s c → ∀ i, stackArg c i = stackArg s i := fun hc i => by
      unfold stackArg stackArgAddr; rw [hc.mem, hc.sp]
    exact agree12 (fun r hr => by rw [g hv hc r hr, g hv' hc' r hr]; exact regs r hr)
      (by rw [hc.sp, hc'.sp, q₀]) (by rw [hc.sp]; exact fit)
      (by rw [hc.wr, show stackArgAddr c 0 = stackArgAddr s₀ 0 by unfold stackArgAddr; rw [hc.sp]]
          exact iwrSep h0)
      (by rw [hc'.wr, show stackArgAddr c' 0 = stackArgAddr s₀' 0 by unfold stackArgAddr; rw [hc'.sp]]
          exact iwrSep h0')
      (fun i hi => by rw [st hc, st hc']; exact qa i hi)
  have hct : RelCT isa (fun u u' => ArgsPost s₀ u ∧ ArgsPost s₀' u') keyCall fun _ _ => True :=
    key_rel (sp₀ := s₀.sp) fun u u' ⟨a, a'⟩ => ⟨key_pre s₀ h0 hv u a, by
      have := key_pre s₀' h0' hv' u' a'; rwa [← q₁, ← q₂, ← q₃, ← q₆, ← q₇] at this, a.sp, a'.sp.trans q₀.symm⟩
  refine RelCT.seq (rel_wp (G := fun v => ∃ u, ArgsPost s₀ u ∧
      KeyPost u (s₀.gpr .r0) (s₀.gpr .r1) (s₀.gpr .r2) (stackArg s₀ 1) (stackArg s₀ 2) v)
    (G' := fun v => ∃ u, ArgsPost s₀' u ∧
      KeyPost u (s₀'.gpr .r0) (s₀'.gpr .r1) (s₀'.gpr .r2) (stackArg s₀' 1) (stackArg s₀' 2) v) hct
    (fun u a => WP.mono (key_call (key_pre s₀ h0 hv u a)) fun v hk => ⟨u, a, hk⟩)
    (fun u a => WP.mono (key_call (key_pre s₀' h0' hv' u a)) fun v hk => ⟨u, a, hk⟩)) ?_
  refine (rel_agree (argTaint [] 12) (fun v v' ⟨u, a, k⟩ ⟨u', a', k'⟩ => ?_) tail_taint
    (fun v ⟨u, a, k⟩ => WP.mono (tail_ok s₀ h0 hv u a v k) fun _ _ => trivial)
    (fun v ⟨u, a, k⟩ => WP.mono (tail_ok s₀' h0' hv' u a v k) fun _ _ => trivial)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  exact agree12 (fun r hr => (List.not_mem_nil hr).elim) (by rw [k.sp, a.sp, k'.sp, a'.sp, q₀])
    (by rw [k.sp, a.sp]; exact fit)
    (by rw [k.wr, a.wr, show stackArgAddr v 0 = stackArgAddr s₀ 0 by unfold stackArgAddr; rw [k.sp, a.sp]]
        exact iwrSep h0)
    (by rw [k'.wr, a'.wr, show stackArgAddr v' 0 = stackArgAddr s₀' 0 by unfold stackArgAddr; rw [k'.sp, a'.sp]]
        exact iwrSep h0')
    (fun i hi => by
      rw [args_after_key s₀ h0 u a v k i hi, args_after_key s₀' h0' u' a' v' k' i hi]; exact qa i hi)

theorem init_constantTime : ConstantTime isa initContract.pre initContract.pub init :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Rc2.Arm.Stream

end

/-! # Verified streaming RC2-CBC on ARMv7 -/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm

theorem init_verified : Verified target Impl.Rc2.Arm.Stream.init (Proof.Rc2.cbcInitScratchContract abi 8) :=
  Verified.of_correct init_correct init_constantTime init_implies

theorem encryptUpdate_verified :
    Verified target Impl.Rc2.Arm.Stream.encryptUpdate (Proof.Rc2.cbcEncryptUpdateScratchContract abi 8) :=
  Verified.of_correct (update_correct .encrypt) (update_constantTime .encrypt) (update_implies .encrypt)

theorem decryptUpdate_verified :
    Verified target Impl.Rc2.Arm.Stream.decryptUpdate (Proof.Rc2.cbcDecryptUpdateScratchContract abi 8) :=
  Verified.of_correct (update_correct .decrypt) (update_constantTime .decrypt) (update_implies .decrypt)

end VG.Proof.Rc2.Arm.Stream
