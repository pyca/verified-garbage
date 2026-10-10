import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Lit
import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Steps
import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Long
import VerifiedGarbage.Proof.Rc2.Scratch

section

/-! # Streaming RC2-CBC on x86-64: the update functions -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

def cbcName : Spec.Rc2.Direction → String
  | .encrypt => "vg_rc2_cbc_encrypt"
  | .decrypt => "vg_rc2_cbc_decrypt"

theorem cbcCall_eq (d : Spec.Rc2.Direction) : cbcCall d = .call (cbcName d) (Cbc.cbc d) := by
  cases d <;> rfl

theorem cbc_correct (d : Spec.Rc2.Direction) (s : State) (hs : (Cbc.contract d).pre s) :
    ∃ t s', Exec isa (Cbc.cbc d) s t s' ∧ abiPreserved s s' ∧ (Cbc.contract d).post s s' := by
  cases d
  · exact Cbc.encrypt_correct s hs
  · exact Cbc.decrypt_correct s hs

theorem cbc_noSp (d : Spec.Rc2.Direction) : NoSp (Cbc.cbc d) := by
  have h : ((instrs (Cbc.cbc d)).all fun i => !Taint.clobbers i .rsp) = true := by
    cases d
    · change ((instrs Cbc.encrypt).all _) = true
      rw [← Code.allInstrs_eq]; lit_decide
    · change ((instrs Cbc.decrypt).all _) = true
      rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem cbc_depth (d : Spec.Rc2.Direction) : (Cbc.cbc d).depth = 1 := by
  cases d <;> rfl

/-- The regions the CBC function is given: the schedule, and the chaining
value, `out` and its scratch space. -/
def callRd (s : State) : List Region := [⟨s.gpr .rdi, 128⟩]
def callWr (s : State) : List Region :=
  [⟨s.gpr .rdi + 128, 8⟩, ⟨s.gpr .r8, 8 * ((s.gpr .r9).toNat / 8)⟩, ⟨stackArg s 0, 512⟩]

/-- The CBC function's precondition at the call, and its regions within ours. -/
theorem call_pre (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hnz : (s.gpr .r9).toNat ≠ 0) (t : State) (ht : Mid s t) :
    (Cbc.contract d).pre (t.callEntry.withRegions (callRd s) (callWr s)) ∧
      Covers (callRd s ++ callWr s) (t.rd ++ t.wr) ∧ Covers (callWr s) t.wr := by
  obtain ⟨hsp, _, hrd, hwr, ctxData, ctxOut, ctxBuf, _, dataOut, _, outBuf, _, _, retCtx, _, retOut, retBuf, _,
    stCtx, _, stOut, stBuf, _, _, _, fitOut, _, hp, hN⟩ := hs
  obtain ⟨rdi₁, rsi₁, rdx₁, rcx₁, r8₁, rsp₁, callee₁, rd₁, wr₁, frame₁, out₁, pend₁⟩ := ht
  simp only [callRd, callWr]
  generalize hC : s.gpr .rdi = C at *
  generalize hNN : (s.gpr .r9).toNat = N at *
  generalize hO : s.gpr .r8 = O at *
  generalize hB : stackArg s 0 = B at *
  generalize hSP : s.gpr .rsp = SP at *
  have h8 : 8 ≤ N := by omega_arith
  have hNN8 : 8 * (N / 8) = N := by omega_arith
  have e128 : C + 128 = C + BitVec.ofNat 64 128 := rfl
  have stackSub : Region.Sub (below (SP - 8) 8) (below SP 16) := below_callee _ _
  have retSub : Region.Sub ⟨SP - 8, 8⟩ (below SP 16) := Offset.sub_below SP (by decide) (by decide)
  have ivSub : Region.Sub ⟨C + BitVec.ofNat 64 128, 8⟩ ⟨C, 144⟩ := Offset.sub_base _ (by decide)
  have keySub : Region.Sub ⟨C, 128⟩ ⟨C, 144⟩ := Region.sub_prefix (by decide)
  have bufSub : Region.Sub ⟨B, 512⟩ ⟨B, 576⟩ := Region.sub_prefix (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Cbc.contract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
      rdi₁, rsi₁, rdx₁, rcx₁, r8₁, rsp₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N / 8 < 2 ^ 64 by omega_arith),
      hNN8, e128]
    refine ⟨trivial, trivial, Offset.base_disjoint _ (by decide) (by decide), ctxOut.sub_left keySub,
      (ctxBuf.sub_left keySub).sub_right bufSub, ctxOut.sub_left ivSub, (ctxBuf.sub_left ivSub).sub_right bufSub,
      outBuf.sub_right bufSub, (stCtx.sub_left retSub).sub_right ivSub, stOut.sub_left retSub,
      (stBuf.sub_left retSub).sub_right bufSub, (stCtx.sub_left stackSub).sub_right keySub,
      (stCtx.sub_left stackSub).sub_right ivSub, stOut.sub_left stackSub,
      (stBuf.sub_left stackSub).sub_right bufSub, fitOut⟩
  · rw [rd₁, wr₁, hrd, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨C, 144⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨C, 144⟩, by simp, 128, rfl, by simp⟩
    · exact ⟨⟨O, N⟩, by simp, 0, by simp, by simp only [hNN8]; omega_arith⟩
    · exact ⟨⟨B, 576⟩, by simp, 0, by simp, by simp⟩
  · rw [wr₁, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨C, 144⟩, by simp, 128, rfl, by simp⟩
    · exact ⟨⟨O, N⟩, by simp, 0, by simp, by simp only [hNN8]; omega_arith⟩
    · exact ⟨⟨B, 576⟩, by simp, 0, by simp, by simp⟩

/-- The call of the CBC function, and the update's postcondition. -/
theorem call_ok (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hnz : (s.gpr .r9).toNat ≠ 0) (t : State) (ht : Mid s t) :
    WP isa (cbcCall d) t (fun s' => ((∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64) ∧
      (Spec.Rc2.contextAt s'.mem (s.gpr .rdi) d (((s.gpr .rsi).toNat + (s.gpr .rcx).toNat) % 8) =
        (Spec.Rc2.update (Spec.Rc2.contextAt s.mem (s.gpr .rdi) d (s.gpr .rsi).toNat)
          (Spec.Rc2.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)).1 ∧
      Spec.Rc2.bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat =
        (Spec.Rc2.update (Spec.Rc2.contextAt s.mem (s.gpr .rdi) d (s.gpr .rsi).toNat)
          (Spec.Rc2.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)).2)) := by
  obtain ⟨hpre, hcov, hwcov⟩ := call_pre d s hs hnz t ht
  simp only [callRd, callWr] at hpre hcov hwcov
  obtain ⟨hsp, _, hrd, hwr, ctxData, ctxOut, ctxBuf, _, dataOut, _, outBuf, _, _, retCtx, _, retOut, retBuf, _,
    stCtx, _, stOut, stBuf, _, _, _, fitOut, _, hp, hN⟩ := hs
  obtain ⟨rdi₁, rsi₁, rdx₁, rcx₁, r8₁, rsp₁, callee₁, rd₁, wr₁, frame₁, out₁, pend₁⟩ := ht
  generalize hC : s.gpr .rdi = C at *
  generalize hP : (s.gpr .rsi).toNat = P at *
  generalize hA : s.gpr .rdx = A at *
  generalize hL : (s.gpr .rcx).toNat = L at *
  generalize hO : s.gpr .r8 = O at *
  generalize hNN : (s.gpr .r9).toNat = N at *
  generalize hB : stackArg s 0 = B at *
  generalize hSP : s.gpr .rsp = SP at *
  have h8 : 8 ≤ N := by omega_arith
  have hNN8 : 8 * (N / 8) = N := by omega_arith
  have e128 : C + 128 = C + BitVec.ofNat 64 128 := rfl
  have e136 : C + 136 = C + BitVec.ofNat 64 136 := rfl
  have stackSub : Region.Sub (below (SP - 8) 8) (below SP 16) := below_callee _ _
  have retSub : Region.Sub ⟨SP - 8, 8⟩ (below SP 16) := Offset.sub_below SP (by decide) (by decide)
  have ivSub : Region.Sub ⟨C + BitVec.ofNat 64 128, 8⟩ ⟨C, 144⟩ := Offset.sub_base _ (by decide)
  have keySub : Region.Sub ⟨C, 128⟩ ⟨C, 144⟩ := Region.sub_prefix (by decide)
  have bufSub : Region.Sub ⟨B, 512⟩ ⟨B, 576⟩ := Region.sub_prefix (by decide)
  rw [cbcCall_eq]
  refine WP.call (k := Cbc.contract d) (cbc_correct d) (cbc_noSp d) (by rw [cbc_depth]; decide)
    (rd := [⟨C, 128⟩]) (wr := [⟨C + 128, 8⟩, ⟨O, 8 * (N / 8)⟩, ⟨B, 512⟩]) hpre hcov hwcov ?_
  intro s' rd' wr' callee' frame' _ ⟨s₂, mem₂, _, post₂⟩
  rw [cbc_depth, rsp₁, hNN8, e128] at frame'
  -- What the call leaves.
  have stackFrame : Frame [below SP 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, rsp₁]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (below_call _ (by decide) (by decide))
  have stack8 : Region.Sub (below SP 8) (below SP 16) := Offset.sub_below SP (by decide) (by decide)
  simp only [Cbc.contract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    rdi₁, rsi₁, rdx₁, rcx₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N / 8 < 2 ^ 64 by omega_arith), mem₂] at post₂
  rw [scheduleAt_frame stackFrame C (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((stCtx.sub_left stack8).sub_right keySub).symm),
    blockAt_frame stackFrame (C + 128) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [e128]; exact ((stCtx.sub_left stack8).sub_right ivSub).symm),
    blocksAt_frame stackFrame O (N / 8) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [hNN8]; exact (stOut.sub_left stack8).symm)] at post₂
  -- Regions the call leaves alone.
  have callSep (R : Region) (hiv : R.Disjoint ⟨C + BitVec.ofNat 64 128, 8⟩) (hout : R.Disjoint ⟨O, N⟩)
      (hbuf : R.Disjoint ⟨B, 576⟩) (hst : R.Disjoint (below SP 16)) :
      ∀ r ∈ [(⟨C + BitVec.ofNat 64 128, 8⟩ : Region), ⟨O, N⟩, ⟨B, 512⟩] ++ [below SP 16], R.Disjoint r := by
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hiv
    · exact hout
    · exact hbuf.sub_right bufSub
    · exact hst
  have midSep (R : Region) (hout : R.Disjoint ⟨O, N⟩) (hpend : R.Disjoint ⟨C + BitVec.ofNat 64 136, 8⟩) :
      ∀ r ∈ [(⟨O, N⟩ : Region), ⟨C + BitVec.ofNat 64 136, 8⟩], R.Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hout
    · exact hpend
  have pendSub : Region.Sub ⟨C + BitVec.ofNat 64 136, 8⟩ ⟨C, 144⟩ := Offset.sub_base _ (by decide)
  refine ⟨⟨fun r hr => (callee' r hr).trans (callee₁ r hr), ?_⟩, ?_⟩
  · rw [frame'.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (callSep _ (retCtx.sub_right ivSub) retOut
        retBuf (Offset.base_disjoint_below _ (by decide))) (by decide),
      frame₁.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (midSep _ retOut (retCtx.sub_right pendSub))
        (by decide)]
  · rw [hN] at out₁ pend₁ post₂ ⊢
    rw [Nat.mul_div_cancel _ (by decide : 0 < 8)] at post₂
    have keyMid := scheduleAt_frame frame₁ C (midSep _ (ctxOut.sub_left keySub)
      (Offset.base_disjoint _ (by decide) (by decide)))
    refine update_post_long hp (by omega_arith) out₁ keyMid ?_ ?_ ?_ post₂.1 post₂.2
    · rw [e128]
      exact blockAt_frame frame₁ _ (midSep _ (ctxOut.sub_left ivSub) (Offset.disjoint _ (by decide) (by decide) (by decide)))
    · rw [e136, Proof.Rc2.bytesAt_frame frame' _ _ (by omega_arith) (callSep _
          (Offset.disjoint _ (by omega_arith) (by omega_arith) (by decide)) (ctxOut.sub_left (Offset.sub_base _ (by omega_arith)))
          (ctxBuf.sub_left (Offset.sub_base _ (by omega_arith))) (stCtx.symm.sub_left (Offset.sub_base _ (by omega_arith)))),
        ← e136, pend₁]
    · exact scheduleAt_frame frame' C (callSep _ (Offset.base_disjoint _ (by decide) (by decide))
        (ctxOut.sub_left keySub) (ctxBuf.sub_left keySub) (stCtx.symm.sub_left keySub))

theorem update_body_correct (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s) :
    WP isa (update d) s (fun s' => gprPreserved s s' ∧ (updateContract d).post s s') := by
  obtain ⟨t₁, run₁, zf₁, keep₁⟩ := test_ok s .r9 (toNat_eq _) (s.gpr .r9).isLt
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide ((s.gpr .r9).toNat = 0)) (by simpa [eval] using zf₁) (fun h => ?_) (fun h => ?_)
  · exact short_ok d s hs (of_decide_eq_true h) t₁ keep₁
  · exact WP.seq (WP.mono (long_ok d s hs (of_decide_eq_false h) t₁ keep₁) fun t ht =>
      WP.mono (call_ok d s hs (of_decide_eq_false h) t ht) fun _ h => h)

theorem update_correct (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s) :
    ∃ t s', Exec isa (update d) s t s' ∧ abiPreserved s s' ∧ (updateContract d).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := update_body_correct d s hs
  refine ⟨t, s', he, abiPreserved_of_exec ?_ he ha, hp⟩
  cases d
  · change encryptUpdate.allInstrs _ = true; lit_decide
  · change decryptUpdate.allInstrs _ = true; lit_decide

end VG.Proof.Rc2.X86_64.Stream

end

section

section

/-! # Streaming RC2-CBC on x86-64: `init`'s length checks -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

/-- What `init` returns for invalid lengths, in `initWithEffectiveBits`'s
order, and 0 for valid ones. -/
def code (keyLen effectiveBits ivLen : Nat) : Nat :=
  if ¬(1 ≤ keyLen ∧ keyLen ≤ 128) then 1
  else if ¬(1 ≤ effectiveBits ∧ effectiveBits ≤ 1024) then 2 else if ivLen ≠ 8 then 3 else 0

theorem code_le (a b c : Nat) : code a b c ≤ 3 := by
  unfold code; split <;> (try split) <;> (try split) <;> omega_arith

theorem sub_one_lt (x : BitVec 64) {n : Nat} (hn : n < 2 ^ 64) :
    (x - 1).toNat < n ↔ 1 ≤ x.toNat ∧ x.toNat ≤ n := by
  have := x.isLt
  rw [BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl]
  omega_arith

/-- `mov32 rax, c`, then `r10 = r - 1` compared with `n`: CF is set iff `r` is
in `1..=n`. -/
theorem checkRange_ok (s : State) (r : Reg) (hr : r ≠ .rax) (c n : Nat) (hc : c < 2 ^ 32) (hn : n < 2 ^ 63)
    (hs : (BitVec.signExtend 64 (BitVec.ofNat 32 n)).toNat = n) :
    ∃ s', runBlock isa [.mov32 .rax (.imm (BitVec.ofNat 32 c)), rr .r10 r, .alu .sub .r10 (.imm 1),
        .alu .cmp .r10 (.imm (BitVec.ofNat 32 n))] s = some s' ∧
      s'.gpr .rax = BitVec.ofNat 64 c ∧ s'.cf = some (decide (1 ≤ (s.gpr r).toNat ∧ (s.gpr r).toNat ≤ n)) ∧
      Keep [.rax, .r10] s s' := by
  refine ⟨_, by
    simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
      State.setReg32, Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ⟨fun r' hr' => ?_, rfl, rfl, rfl⟩⟩
  · rw [gpr_arithFlags, gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags, gpr_setReg_of_ne _ _ (by decide),
      gpr_setReg_self]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
      Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega_arith)]
  · simp only [cf_arithFlags, gpr_setReg_self, gpr_setReg_of_ne _ _ hr, hs,
      show BitVec.signExtend 64 (1 : BitVec 32) = 1 by decide, sub_one_lt _ (show n < 2 ^ 64 by omega_arith)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [gpr_arithFlags, gpr_setReg_of_ne _ _ hr'.2, gpr_setReg_of_ne _ _ hr'.1]

theorem checkIv_ok (s : State) :
    ∃ s', runBlock isa checkIv s = some s' ∧
      s'.gpr .rax = BitVec.ofNat 64 3 ∧ s'.zf = some (decide ((s.gpr .r8).toNat = 8)) ∧ Keep [.rax, .r10] s s' := by
  refine ⟨_, by
    simp only [checkIv, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
      State.setReg32, Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨by rw [gpr_arithFlags, gpr_setReg_self]; rfl, ?_, ⟨fun r' hr' => ?_, rfl, rfl, rfl⟩⟩
  · rw [zf_arithFlags, gpr_setReg_of_ne _ _ (by decide), toNat_eq (s.gpr .r8),
      show BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 by decide,
      Offset.ofNat_sub_ofNat_beq (s.gpr .r8).isLt (by decide), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (s.gpr .r8).isLt]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [gpr_arithFlags, gpr_setReg_of_ne _ _ hr'.1]

theorem zero_ok (s : State) :
    ∃ s', runBlock isa [.mov32 .rax (.imm 0)] s = some s' ∧ s'.gpr .rax = BitVec.ofNat 64 0 ∧ Keep [.rax, .r10] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
    rfl, ?_⟩
  refine ⟨by rw [gpr_setReg_self]; rfl, ⟨fun r' hr' => ?_, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
  simp only [gpr_setReg_of_ne _ _ hr'.1]

theorem keep_trans {s s' s'' : State} (h : Keep [.rax, .r10] s s') (h' : Keep [.rax, .r10] s' s'') :
    Keep [.rax, .r10] s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem checks_ok (s : State) :
    WP isa checks s fun t => Keep [.rax, .r10] s t ∧
      t.zf = some (decide (code (s.gpr .rsi).toNat (s.gpr .rdx).toNat (s.gpr .r8).toNat = 0)) ∧
      t.gpr .rax = BitVec.ofNat 64 (code (s.gpr .rsi).toNat (s.gpr .rdx).toNat (s.gpr .r8).toNat) := by
  refine WP.seq (WP.mono (Q := fun (t : State) => Keep [.rax, .r10] s t ∧
      t.gpr .rax = BitVec.ofNat 64 (code (s.gpr .rsi).toNat (s.gpr .rdx).toNat (s.gpr .r8).toNat)) ?_ ?_)
  · obtain ⟨s₁, run₁, rax₁, cf₁, keep₁⟩ := checkRange_ok s .rsi (by decide) 1 128 (by decide) (by decide) (by decide)
    refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
    refine WP.ite _ (by simp only [eval, cf₁]; rfl) (fun h => WP.block_nil ⟨keep₁, ?_⟩) (fun h => ?_)
    · rw [rax₁, code, ite_eq_left_of_eq_true _ _ (eq_true (by simp at h ⊢; omega_arith))]
    obtain ⟨s₂, run₂, rax₂, cf₂, keep₂⟩ := checkRange_ok s₁ .rdx (by decide) 2 1024 (by decide) (by decide) (by decide)
    have hk : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 128 := by simpa using h
    rw [keep₁.reg _ (by decide)] at cf₂
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    refine WP.ite _ (by simp only [eval, cf₂]; rfl) (fun h => WP.block_nil ⟨keep_trans keep₁ keep₂, ?_⟩)
      (fun h => ?_)
    · rw [rax₂, code, ite_eq_right_of_eq_false _ _ (eq_false (fun h => h hk)), ite_eq_left_of_eq_true _ _ (eq_true (by simp at h ⊢; omega_arith))]
    have he : 1 ≤ (s.gpr .rdx).toNat ∧ (s.gpr .rdx).toNat ≤ 1024 := by simpa using h
    obtain ⟨s₃, run₃, rax₃, zf₃, keep₃⟩ := checkIv_ok s₂
    rw [keep₂.reg _ (by decide), keep₁.reg _ (by decide)] at zf₃
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    refine WP.ite _ (by simp only [eval, zf₃]; rfl) (fun h => WP.block_nil ⟨keep_trans (keep_trans keep₁ keep₂) keep₃, ?_⟩)
      (fun h => ?_)
    · rw [rax₃, code, ite_eq_right_of_eq_false _ _ (eq_false (fun h => h hk)), ite_eq_right_of_eq_false _ _ (eq_false (fun h => h he)), ite_eq_left_of_eq_true _ _ (eq_true (by simp at h ⊢; omega_arith))]
    obtain ⟨s₄, run₄, rax₄, keep₄⟩ := zero_ok s₃
    refine WP.of_runBlock ⟨s₄, run₄, keep_trans (keep_trans (keep_trans keep₁ keep₂) keep₃) keep₄, ?_⟩
    rw [rax₄, code, ite_eq_right_of_eq_false _ _ (eq_false (fun h => h hk)), ite_eq_right_of_eq_false _ _ (eq_false (fun h => h he)), ite_eq_right_of_eq_false _ _ (eq_false (by simp at h ⊢; omega_arith))]
  · rintro t ⟨keep, rax⟩
    obtain ⟨t', run, zf, keep'⟩ := test_ok t .rax rax (by have := code_le (s.gpr .rsi).toNat (s.gpr .rdx).toNat (s.gpr .r8).toNat; omega_arith)
    refine WP.of_runBlock ⟨t', run, ⟨fun r hr => (keep'.reg r (by simp)).trans (keep.reg r hr),
      keep'.mem.trans keep.mem, keep'.rd.trans keep.rd, keep'.wr.trans keep.wr⟩, zf, ?_⟩
    rw [keep'.reg _ (by simp), rax]

end VG.Proof.Rc2.X86_64.Stream

end

/-! # Streaming RC2-CBC on x86-64: `vg_rc2_cbc_init` -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

theorem initArgs_ok (s : State) (riv : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 0) 8)
    (wctx : InRegions s.wr (s.gpr .r9 + BitVec.ofNat 64 128) 8)
    (rarg : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa initArgs s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r9 + BitVec.ofNat 64 128) (s.mem.readW (s.gpr .rcx + BitVec.ofNat 64 0) 64) ∧
      s'.gpr .rcx = s.gpr .r9 ∧ s'.gpr .r8 = s'.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, not_false_eq_true, initArgs, rr, memOp, runBlock_cons, runStep_some,
      exec, readSrc, State.load64, State.store64, State.ea, offset_nat, Option.map_some,
      gpr_setReg_self, gpr_setReg_of_ne, rd_setReg, wr_setReg, mem_setReg, riv, wctx]
    simp only [rarg, ite_true, Option.map_some]
    rfl, ?_⟩
  refine ⟨rfl, ?_, ?_, fun r h₁ h₂ h₃ => ?_, rfl, rfl⟩
  · simp only [reduceCtorEq, not_false_eq_true, gpr_setReg_self, gpr_setReg_of_ne]
  · simp only [gpr_setReg_self, mem_setReg]
  · simp only [gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂, gpr_setReg_of_ne _ _ h₃]

/-- The state before the call of key expansion, from the entry state `σ`. -/
structure KeyPre (σ t : State) : Prop where
  rdi : t.gpr .rdi = σ.gpr .rdi
  rsi : t.gpr .rsi = σ.gpr .rsi
  rdx : t.gpr .rdx = σ.gpr .rdx
  rcx : t.gpr .rcx = σ.gpr .r9
  r8 : t.gpr .r8 = stackArg σ 0
  rsp : t.gpr .rsp = σ.gpr .rsp
  callee : ∀ r ∈ calleeSaved, t.gpr r = σ.gpr r
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  mem : t.mem = σ.mem.writeW (σ.gpr .r9 + BitVec.ofNat 64 128) (σ.mem.readW (σ.gpr .rcx) 64)

/-- Valid lengths. -/
def Valid (σ : State) : Prop :=
  (1 ≤ (σ.gpr .rsi).toNat ∧ (σ.gpr .rsi).toNat ≤ 128) ∧ (1 ≤ (σ.gpr .rdx).toNat ∧ (σ.gpr .rdx).toNat ≤ 1024) ∧
    (σ.gpr .r8).toNat = 8

theorem valid_of_code {σ : State} (h : code (σ.gpr .rsi).toNat (σ.gpr .rdx).toNat (σ.gpr .r8).toNat = 0) :
    Valid σ := by
  unfold code at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · refine ⟨?_, ?_, ?_⟩ <;> simp_all

theorem initArgs_pre (σ : State) (hs : initContract.pre σ) (hv : Valid σ) (t : State) (ht : Keep [.rax, .r10] σ t) :
    WP isa (.block initArgs) t (KeyPre σ) := by
  obtain ⟨_, _, hrd, hwr, _, _, _, _, _, ctxArgs, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hs
  have rdwr {a : Addr} {n : Nat} (h : InRegions σ.rd a n) : InRegions (σ.rd ++ σ.wr) a n := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_left _ hr, hc⟩
  have argsAddr : stackArgAddr σ 0 = σ.gpr .rsp + BitVec.ofNat 64 8 := rfl
  obtain ⟨t', run, mem', rcx', r8', g', rd', wr'⟩ := initArgs_ok t
    (by rw [ht.rd, ht.wr, ht.reg _ (by decide)]
        exact rdwr (by rw [hrd]; exact ⟨⟨σ.gpr .rcx, (σ.gpr .r8).toNat⟩, by simp,
          Offset.contains_base _ (by have := hv.2.2; omega_arith) (by decide)⟩))
    (by rw [ht.wr, ht.reg _ (by decide), hwr]
        exact ⟨⟨σ.gpr .r9, 144⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    (by rw [ht.rd, ht.wr, ht.reg _ (by decide), ← argsAddr]
        exact rdwr (by rw [hrd]; exact ⟨⟨stackArgAddr σ 0, 8⟩, by simp, Region.contains_self _ _⟩))
  refine WP.of_runBlock ⟨t', run, ?_⟩
  have m : t'.mem = σ.mem.writeW (σ.gpr .r9 + BitVec.ofNat 64 128) (σ.mem.readW (σ.gpr .rcx) 64) := by
    rw [mem', ht.mem, ht.reg _ (by decide), ht.reg _ (by decide),
      show σ.gpr .rcx + BitVec.ofNat 64 0 = σ.gpr .rcx from BitVec.add_zero _]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, by rw [rd', ht.rd], by rw [wr', ht.wr], m⟩
  · rw [g' _ (by decide) (by decide) (by decide), ht.reg _ (by decide)]
  · rw [g' _ (by decide) (by decide) (by decide), ht.reg _ (by decide)]
  · rw [g' _ (by decide) (by decide) (by decide), ht.reg _ (by decide)]
  · rw [rcx', ht.reg _ (by decide)]
  · rw [r8', ht.reg _ (by decide), m, ← argsAddr]
    exact (frame_store64 _ _ _).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ctxArgs.symm.sub_right (Offset.sub_base _ (by decide))) (by decide)
  · rw [g' _ (by decide) (by decide) (by decide), ht.reg _ (by decide)]
  · have h : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .r8 ∧ r ∉ [Reg.rax, .r10] := by revert hr; revert r; decide
    rw [g' _ h.1 h.2.1 h.2.2.1, ht.reg _ h.2.2.2]

def keyRd (σ : State) : List Region := [⟨σ.gpr .rdi, (σ.gpr .rsi).toNat⟩]
def keyWr (σ : State) : List Region := [⟨σ.gpr .r9, 128⟩, ⟨stackArg σ 0, 512⟩]

/-- Key expansion's precondition at the call, and its regions within ours. -/
theorem key_pre (σ : State) (hs : initContract.pre σ) (hv : Valid σ) (t : State) (ht : KeyPre σ t) :
    keyContract.pre (t.callEntry.withRegions (keyRd σ) (keyWr σ)) ∧
      Covers (keyRd σ ++ keyWr σ) (t.rd ++ t.wr) ∧ Covers (keyWr σ) t.wr := by
  obtain ⟨_, _, hrd, hwr, keyCtx, keyBuf, _, _, ctxBuf, _, _, _, _, _, _, _, _, _, stCtx, stBuf, _, _, _, _, _⟩ := hs
  have keySub : Region.Sub ⟨σ.gpr .r9, 128⟩ ⟨σ.gpr .r9, 144⟩ := Region.sub_prefix (by decide)
  have bufSub : Region.Sub ⟨stackArg σ 0, 512⟩ ⟨stackArg σ 0, 576⟩ := Region.sub_prefix (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [keyContract, keyRd, keyWr, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
      ht.rdi, ht.rsi, ht.rdx, ht.rcx, ht.r8, ht.rsp]
    exact ⟨trivial, trivial, keyCtx.sub_right keySub, keyBuf.sub_right bufSub, (ctxBuf.sub_left keySub).sub_right bufSub,
      stCtx.sub_right keySub, stBuf.sub_right bufSub, hv.1.1, hv.1.2, hv.2.1.1, hv.2.1.2⟩
  · rw [ht.rd, ht.wr, hrd, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [keyRd, keyWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨σ.gpr .rdi, (σ.gpr .rsi).toNat⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨σ.gpr .r9, 144⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨stackArg σ 0, 576⟩, by simp, 0, by simp, by simp⟩
  · rw [ht.wr, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [keyWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨σ.gpr .r9, 144⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨stackArg σ 0, 576⟩, by simp, 0, by simp, by simp⟩

theorem expandKey_noSp : NoSp expandKey := by
  have h : ((instrs expandKey).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem expandKey_depth : expandKey.depth = 0 := rfl

/-- The postcondition of `init`, spelled out. -/
def InitPost (σ s' : State) : Prop :=
  ((∀ r ∈ calleeSaved, s'.gpr r = σ.gpr r) ∧ s'.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64) ∧
  ∀ direction, match Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt σ.mem (σ.gpr .rdi) (σ.gpr .rsi).toNat)
      (Spec.Rc2.bytesAt σ.mem (σ.gpr .rcx) (σ.gpr .r8).toNat) direction (σ.gpr .rdx).toNat with
    | .ok c => (s'.gpr .rax).setWidth 32 = 0 ∧ Spec.Rc2.contextAt s'.mem (σ.gpr .r9) direction 0 = c
    | .error e => ((s'.gpr .rax).setWidth 32).toNat = e.code

theorem keyCall_ok (σ : State) (hs : initContract.pre σ) (hv : Valid σ) (t : State) (ht : KeyPre σ t) :
    WP isa (.seq keyCall (.block [.mov32 .rax (.imm 0)])) t (InitPost σ) := by
  obtain ⟨hpre, hc, hw⟩ := key_pre σ hs hv t ht
  simp only [keyRd, keyWr] at hpre hc hw
  obtain ⟨_, _, hrd, hwr, keyCtx, keyBuf, _, _, ctxBuf, _, _, retKey, _, retCtx, retBuf, _, stKey, _, stCtx, stBuf, _,
    _, _, _, _⟩ := hs
  have pendSub : Region.Sub ⟨σ.gpr .r9 + BitVec.ofNat 64 128, 8⟩ ⟨σ.gpr .r9, 144⟩ := Offset.sub_base _ (by decide)
  have bufSub : Region.Sub ⟨stackArg σ 0, 512⟩ ⟨stackArg σ 0, 576⟩ := Region.sub_prefix (by decide)
  have keySub : Region.Sub ⟨σ.gpr .r9, 128⟩ ⟨σ.gpr .r9, 144⟩ := Region.sub_prefix (by decide)
  refine WP.seq (WP.call (k := keyContract) key_correct expandKey_noSp (by rw [expandKey_depth]; decide)
    hpre hc hw ?_)
  intro s' _ _ callee' frame' _ ⟨s₂, mem₂, _, post₂⟩
  rw [expandKey_depth, ht.rsp] at frame'
  have stackFrame : Frame [below (σ.gpr .rsp) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, ht.rsp]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (below_call _ (by decide) (by decide))
  simp only [keyContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    ht.rdi, ht.rsi, ht.rdx, ht.rcx, mem₂] at post₂
  rw [Proof.Rc2.bytesAt_frame stackFrame _ _ (by omega_arith) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact stKey.symm),
    ht.mem, Proof.Rc2.bytesAt_frame (frame_store64 _ _ _) _ _ (by omega_arith) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact keyCtx.sub_right pendSub)] at post₂
  obtain ⟨s'', run, rax'', keep''⟩ := zero_ok s'
  refine WP.of_runBlock ⟨s'', run, ⟨fun r hr => ?_, ?_⟩, fun direction => ?_⟩
  · rw [keep''.reg r (by revert hr; revert r; decide), callee' r hr, ht.callee r hr]
  · have callSep (R : Region) (hctx : R.Disjoint ⟨σ.gpr .r9, 144⟩) (hbuf : R.Disjoint ⟨stackArg σ 0, 576⟩)
        (hst : R.Disjoint (below (σ.gpr .rsp) 8)) :
        ∀ r ∈ [(⟨σ.gpr .r9, 128⟩ : Region), ⟨stackArg σ 0, 512⟩] ++ [below (σ.gpr .rsp) 8], R.Disjoint r := by
      intro r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hctx.sub_right keySub
      · exact hbuf.sub_right bufSub
      · exact hst
    rw [keep''.mem, frame'.readW (r := ⟨σ.gpr .rsp, 8⟩) (Region.contains_self _ _)
        (callSep _ retCtx retBuf (Offset.base_disjoint_below _ (by decide))) (by decide), ht.mem,
      (frame_store64 _ _ _).readW (r := ⟨σ.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact retCtx.sub_right pendSub) (by decide)]
  · refine init_post (m' := s''.mem) (r := (s''.gpr .rax).setWidth 32) hv.1 hv.2.1 hv.2.2 (by rw [rax'']; rfl) (by rw [keep''.mem]; exact post₂) (iv := σ.gpr .rcx) ?_ direction
    rw [keep''.mem, show σ.gpr .r9 + 128 = σ.gpr .r9 + BitVec.ofNat 64 128 from rfl,
      blockAt_frame frame' _ (fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint_base _ (by decide) (by decide)
        · exact (ctxBuf.sub_left pendSub).sub_right bufSub
        · exact (stCtx.sub_right pendSub).symm),
      ht.mem, blockAt_copy]

theorem code_ne {a b c : Nat} (h : code a b c ≠ 0) :
    code a b c = if ¬(1 ≤ a ∧ a ≤ 128) then 1 else if ¬(1 ≤ b ∧ b ≤ 1024) then 2 else 3 := by
  unfold code at h ⊢
  by_cases h₃ : c ≠ 8
  · simp [h₃]
  · simp only [h₃, ↓reduceIte] at h ⊢
    split at h <;> simp_all

theorem init_body_correct (σ : State) (hs : initContract.pre σ) : WP isa init σ (InitPost σ) := by
  refine WP.seq (WP.mono (checks_ok σ) fun t ⟨keep, zf, rax⟩ => ?_)
  refine WP.ite _ (by simp only [eval, zf]; rfl) (fun h => WP.block_nil ?_) (fun h => ?_)
  · have hc : code (σ.gpr .rsi).toNat (σ.gpr .rdx).toNat (σ.gpr .r8).toNat ≠ 0 := by simpa using h
    have hr : ((t.gpr .rax).setWidth 32).toNat = code (σ.gpr .rsi).toNat (σ.gpr .rdx).toNat (σ.gpr .r8).toNat := by
      have := code_le (σ.gpr .rsi).toNat (σ.gpr .rdx).toNat (σ.gpr .r8).toNat
      rw [rax, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    refine ⟨⟨fun r hr' => keep.reg r (by revert hr'; revert r; decide), by rw [keep.mem]⟩, ?_⟩
    refine init_post_error (hr.trans (code_ne hc)) (fun hv => hc ?_)
    simp only [code, hv.1, hv.2.1, hv.2.2, not_true_eq_false, and_self, ↓reduceIte, ne_eq]
  · have hv := valid_of_code (σ := σ) (by simpa using h)
    exact WP.seq (WP.mono (initArgs_pre σ hs hv t keep) fun t' ht' => keyCall_ok σ hs hv t' ht')

theorem init_correct (σ : State) (hs : initContract.pre σ) :
    ∃ t s', Exec isa init σ t s' ∧ abiPreserved σ s' ∧ initContract.post σ s' := by
  obtain ⟨t, s', he, ha, hp⟩ := init_body_correct σ hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

end VG.Proof.Rc2.X86_64.Stream

end

section

/-! # Streaming RC2-CBC on x86-64: the update functions are constant time

The taint analysis checks the code before the call of the CBC function from
the public arguments; the call is constant time by the CBC function's proof,
with the arguments that correctness fixes (`Mid`), which are the same in two
runs that agree on the public arguments (the scratch pointer among them,
which the analysis cannot follow through its load from the stack). -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

def args : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]

def InitRel (d : Spec.Rc2.Direction) (s₁ s₂ : State) : Prop :=
  (updateContract d).pre s₁ ∧ (updateContract d).pre s₂ ∧ (updateContract d).pub s₁ s₂

/-- After the test of `out_len`, from related entry states. -/
def TestRel (d : Spec.Rc2.Direction) (σ₁ σ₂ s₁ s₂ : State) : Prop :=
  InitRel d σ₁ σ₂ ∧ Keep [] σ₁ s₁ ∧ Keep [] σ₂ s₂ ∧ s₁.zf = some (decide ((σ₁.gpr .r9).toNat = 0)) ∧
    s₂.zf = some (decide ((σ₂.gpr .r9).toNat = 0))

theorem cbc_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (Cbc.contract d).pre (Cbc.contract d).pub (Cbc.cbc d) := by
  cases d
  · exact Cbc.encrypt_constantTime _
  · exact Cbc.decrypt_constantTime _

theorem testRel_args {d : Spec.Rc2.Direction} {σ₁ σ₂ s₁ s₂ : State} (h : TestRel d σ₁ σ₂ s₁ s₂) :
    ∀ r ∈ args, s₁.gpr r = s₂.gpr r := by
  intro r hr
  rw [h.2.1.reg r (by simp), h.2.2.1.reg r (by simp)]
  exact h.1.2.2.1 r hr

theorem update_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (updateContract d).pre (updateContract d).pub (update d) := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  -- The test of `out_len`.
  have test : RelCT isa (InitRel d) (.block [.alu .test .r9 (.reg .r9)])
      (fun s₁ s₂ => ∃ σ₁ σ₂, TestRel d σ₁ σ₂ s₁ s₂) := by
    have ct := RelCT.taint (P := InitRel d) (A := taint) (Taint.ofRegs args)
      (fun _ _ h => Taint.agree_ofRegs h.2.2.1) (c := .block [.alu .test .r9 (.reg .r9)]) (by taint_decide)
    have hw (s : State) : WP isa (.block [.alu .test .r9 (.reg .r9)]) s
        (fun s' => Keep [] s s' ∧ s'.zf = some (decide ((s.gpr .r9).toNat = 0))) := by
      obtain ⟨s', run, zf, keep⟩ := test_ok s .r9 (toNat_eq _) (s.gpr .r9).isLt
      exact WP.of_runBlock ⟨s', run, keep, zf⟩
    refine (ct.wpDep (F := fun (s s' : State) => Keep [] s s' ∧ s'.zf = some (decide ((s.gpr .r9).toNat = 0)))
      (fun s₁ s₂ _ => ⟨hw s₁, hw s₂⟩)).mono (fun _ _ h => h) ?_
    rintro s₁ s₂ ⟨-, σ₁, σ₂, hp, ⟨k₁, z₁⟩, ⟨k₂, z₂⟩⟩
    exact ⟨σ₁, σ₂, hp, k₁, k₂, z₁, z₂⟩
  change RelCT isa (InitRel d) (.seq _ (.ite .e short (.seq longPre (cbcCall d)))) (fun _ _ => True)
  refine test.seq (RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => ?_)
  by_cases hI : InitRel d σ₁ σ₂
  swap
  · exact RelCT.of_false fun _ _ h => hI h.1
  obtain ⟨hp₁, hp₂, hpub, hB⟩ := hI
  refine RelCT.ite (fun s₁ s₂ h => ?_) ?_ ?_
  · simp only [eval, h.2.2.2.1, h.2.2.2.2, hpub .r9 (by decide)]
  · -- No complete block: the taint analysis alone.
    exact RelCT.taint (A := taint) (Taint.ofRegs args) (fun _ _ h => Taint.agree_ofRegs (testRel_args h.1))
      (by taint_decide)
  · -- The copies, then the call.
    by_cases hz : (σ₁.gpr .r9).toNat = 0
    · refine RelCT.of_false fun s₁ s₂ h => ?_
      have e := h.2; simp only [eval, h.1.2.2.2.1, hz] at e; simp at e
    have hz₂ : (σ₂.gpr .r9).toNat ≠ 0 := by rw [← hpub .r9 (by decide)]; exact hz
    have pre := (RelCT.taint (A := taint) (Taint.ofRegs args)
      (P := fun s₁ s₂ => TestRel d σ₁ σ₂ s₁ s₂ ∧ isa.eval .e s₁ = some false)
      (fun _ _ h => Taint.agree_ofRegs (testRel_args h.1)) (c := longPre)
      (by taint_decide)).wp (F₁ := Mid σ₁) (F₂ := Mid σ₂) fun s₁ s₂ h =>
        ⟨long_ok d σ₁ hp₁ hz s₁ h.1.2.1, long_ok d σ₂ hp₂ hz₂ s₂ h.1.2.2.1⟩
    refine RelCT.seq pre ?_
    have hrd : callRd σ₂ = callRd σ₁ := by simp only [callRd, hpub .rdi (by decide)]
    have hwr : callWr σ₂ = callWr σ₁ := by
      simp only [callWr, hpub .rdi (by decide), hpub .r8 (by decide), hpub .r9 (by decide), hB]
    rw [cbcCall_eq]
    refine RelCT.call (cbc_correct d) (cbc_constantTime d) (callRd σ₁) (callWr σ₁) ?_
    rintro s₁ s₂ ⟨-, m₁, m₂⟩
    obtain ⟨pre₁, c₁, w₁⟩ := call_pre d σ₁ hp₁ hz s₁ m₁
    obtain ⟨pre₂, c₂, w₂⟩ := call_pre d σ₂ hp₂ hz₂ s₂ m₂
    rw [hrd, hwr] at pre₂ c₂
    rw [hwr] at w₂
    refine ⟨pre₁, pre₂, ?_, c₁, w₁, c₂, w₂, by rw [m₁.rsp, m₂.rsp, hpub .rsp (by decide)]⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [State.withRegions_gpr, State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
        m₁.rdi, m₂.rdi, m₁.rsi, m₂.rsi, m₁.rdx, m₂.rdx, m₁.rcx, m₂.rcx, m₁.r8, m₂.r8, m₁.rsp, m₂.rsp,
        hpub .rdi (by decide), hpub .r8 (by decide), hpub .r9 (by decide), hpub .rsp (by decide), hB]

end VG.Proof.Rc2.X86_64.Stream

end

section

/-! # Streaming RC2-CBC on x86-64: `vg_rc2_cbc_init` is constant time

The length checks and the IV copy are checked by the taint analysis from the
public arguments; the call of key expansion is constant time by its proof,
with the arguments that correctness fixes (`KeyPre`). -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

def InitRelI (s₁ s₂ : State) : Prop := initContract.pre s₁ ∧ initContract.pre s₂ ∧ initContract.pub s₁ s₂

/-- After the checks, from related entry states. -/
def ChecksRel (σ₁ σ₂ s₁ s₂ : State) : Prop :=
  InitRelI σ₁ σ₂ ∧ Keep [.rax, .r10] σ₁ s₁ ∧ Keep [.rax, .r10] σ₂ s₂ ∧
    s₁.zf = some (decide (code (σ₁.gpr .rsi).toNat (σ₁.gpr .rdx).toNat (σ₁.gpr .r8).toNat = 0)) ∧
    s₂.zf = some (decide (code (σ₂.gpr .rsi).toNat (σ₂.gpr .rdx).toNat (σ₂.gpr .r8).toNat = 0))

theorem checksRel_args {σ₁ σ₂ s₁ s₂ : State} (h : ChecksRel σ₁ σ₂ s₁ s₂) : ∀ r ∈ args, s₁.gpr r = s₂.gpr r := by
  intro r hr
  have hr' : r ∉ [Reg.rax, .r10] := by revert hr; revert r; decide
  rw [h.2.1.reg r hr', h.2.2.1.reg r hr']
  exact h.1.2.2.1 r hr

theorem init_constantTime : ConstantTime isa initContract.pre initContract.pub init := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  have chk : RelCT isa InitRelI checks (fun s₁ s₂ => ∃ σ₁ σ₂, ChecksRel σ₁ σ₂ s₁ s₂) := by
    have ct := RelCT.taint (P := InitRelI) (A := taint) (Taint.ofRegs args)
      (fun _ _ h => Taint.agree_ofRegs h.2.2.1) (c := checks) (by taint_decide)
    refine (ct.wpDep (fun s₁ s₂ _ => ⟨checks_ok s₁, checks_ok s₂⟩)).mono (fun _ _ h => h) ?_
    rintro s₁ s₂ ⟨-, σ₁, σ₂, hp, ⟨k₁, z₁, -⟩, ⟨k₂, z₂, -⟩⟩
    exact ⟨σ₁, σ₂, hp, k₁, k₂, z₁, z₂⟩
  change RelCT isa InitRelI (.seq checks (.ite .ne (.block []) (.seq (.block initArgs)
    (.seq keyCall (.block [.mov32 .rax (.imm 0)]))))) (fun _ _ => True)
  refine chk.seq (RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => ?_)
  by_cases hI : InitRelI σ₁ σ₂
  swap
  · exact RelCT.of_false fun _ _ h => hI h.1
  obtain ⟨hp₁, hp₂, hpub, hB⟩ := hI
  have hcode : code (σ₂.gpr .rsi).toNat (σ₂.gpr .rdx).toNat (σ₂.gpr .r8).toNat =
      code (σ₁.gpr .rsi).toNat (σ₁.gpr .rdx).toNat (σ₁.gpr .r8).toNat := by
    rw [hpub .rsi (by decide), hpub .rdx (by decide), hpub .r8 (by decide)]
  refine RelCT.ite (fun s₁ s₂ h => ?_) (RelCT.block_nil fun _ _ _ => trivial) ?_
  · simp only [eval, h.2.2.2.1, h.2.2.2.2, hcode]
  by_cases hz : code (σ₁.gpr .rsi).toNat (σ₁.gpr .rdx).toNat (σ₁.gpr .r8).toNat = 0
  swap
  · refine RelCT.of_false fun s₁ s₂ h => ?_
    have e := h.2; simp only [eval, h.1.2.2.2.1, hz] at e; simp at e
  have hv₁ := valid_of_code hz
  have hv₂ := valid_of_code (σ := σ₂) (by rw [hcode]; exact hz)
  have pre := (RelCT.taint (A := taint) (Taint.ofRegs args)
    (P := fun s₁ s₂ => ChecksRel σ₁ σ₂ s₁ s₂ ∧ isa.eval .ne s₁ = some false)
    (fun _ _ h => Taint.agree_ofRegs (checksRel_args h.1)) (c := .block initArgs)
    (by taint_decide)).wp (F₁ := KeyPre σ₁) (F₂ := KeyPre σ₂) fun s₁ s₂ h =>
      ⟨initArgs_pre σ₁ hp₁ hv₁ s₁ h.1.2.1, initArgs_pre σ₂ hp₂ hv₂ s₂ h.1.2.2.1⟩
  refine RelCT.seq pre (RelCT.seq (R := fun _ _ => True) ?_ (RelCT.taint (A := taint) (Taint.ofRegs [])
    (P := fun _ _ => True) (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)))
  have hrd : keyRd σ₂ = keyRd σ₁ := by simp only [keyRd, hpub .rdi (by decide), hpub .rsi (by decide)]
  have hwr : keyWr σ₂ = keyWr σ₁ := by simp only [keyWr, hpub .r9 (by decide), hB]
  refine RelCT.call key_correct (expandKey_constantTime _) (keyRd σ₁) (keyWr σ₁) ?_
  rintro s₁ s₂ ⟨-, m₁, m₂⟩
  obtain ⟨pre₁, c₁, w₁⟩ := key_pre σ₁ hp₁ hv₁ s₁ m₁
  obtain ⟨pre₂, c₂, w₂⟩ := key_pre σ₂ hp₂ hv₂ s₂ m₂
  rw [hrd, hwr] at pre₂ c₂
  rw [hwr] at w₂
  refine ⟨pre₁, pre₂, ?_, c₁, w₁, c₂, w₂, by rw [m₁.rsp, m₂.rsp, hpub .rsp (by decide)]⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
      m₁.rdi, m₂.rdi, m₁.rsi, m₂.rsi, m₁.rdx, m₂.rdx, m₁.rcx, m₂.rcx, m₁.r8, m₂.r8,
      hpub .rdi (by decide), hpub .rsi (by decide), hpub .rdx (by decide), hpub .r9 (by decide), hB]

end VG.Proof.Rc2.X86_64.Stream

end

/-! # Streaming RC2-CBC on x86-64: verified against the shared contracts -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.Impl.Rc2.X86_64.Stream

theorem init_verified : Verified target init (Proof.Rc2.cbcInitScratchContract abi 8) :=
  Verified.of_correct init_correct init_constantTime init_implies

theorem encryptUpdate_verified :
    Verified target encryptUpdate (Proof.Rc2.cbcEncryptUpdateScratchContract abi 16) :=
  Verified.of_correct (update_correct .encrypt) (update_constantTime .encrypt) (update_implies .encrypt)

theorem decryptUpdate_verified :
    Verified target decryptUpdate (Proof.Rc2.cbcDecryptUpdateScratchContract abi 16) :=
  Verified.of_correct (update_correct .decrypt) (update_constantTime .decrypt) (update_implies .decrypt)

end VG.Proof.Rc2.X86_64.Stream
