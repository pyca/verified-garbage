module

public import VerifiedGarbage.Proof.Rc2.X86.Cbc.Contract
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Rc2.X86.KeyIO
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rc2.X86.Lit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Rc2.X86.Cbc.Contract
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Rc2.X86.KeyIO
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Rc2.X86.Lit
public import VerifiedGarbage.Proof.Rc2.X86.Cbc.Body

/-! ### `Rc2.X86.Cbc.Loop`, which this module and modules that import it used -/

section

@[expose] public section

section

/-! # Frames for successive CBC blocks -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

def loopWrites (s : State) (n : Nat) : List Region := [ivR s, dataR s n, ⟨addr32 (s.gpr .ebp), 264⟩, stackR s]

theorem loopFrame_slice {s s' : State} {n m i : Nat} {a b : Mem}
    (h : Frame (loopWrites s' m) a b) (bound : i + m ≤ n)
    (iv : s'.gpr .ecx = s.gpr .ecx) (buf : s'.gpr .ebp = s.gpr .ebp) (sp : s'.gpr .esp = s.gpr .esp)
    (ptr : addr32 (s'.gpr .esi) = addr32 (s.gpr .esi) + BitVec.ofNat 64 (8 * i)) :
    Frame (loopWrites s n) a b := by
  apply h.sub
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨ivR s, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨addr32 (s'.gpr .ecx), 8⟩ ⟨addr32 (s.gpr .ecx), 8⟩
    rw [iv]; exact fun _ h => h
  · refine ⟨dataR s n, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨addr32 (s'.gpr .esi), 8 * m⟩ ⟨addr32 (s.gpr .esi), 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega_using [bound])
  · refine ⟨⟨addr32 (s.gpr .ebp), 264⟩, by simp [loopWrites], ?_⟩
    rw [buf]; exact fun _ h => h
  · refine ⟨stackR s, by simp [loopWrites], ?_⟩
    change Region.Sub (below (s'.gpr .esp) 16) (below (s.gpr .esp) 16)
    rw [sp]; exact fun _ h => h

theorem BodyPost.frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hn : 1 ≤ n) : Frame (loopWrites s n) s.mem s'.mem :=
  loopFrame_slice (m := 1) (i := 0) h.mem hn rfl rfl rfl (by simp)

theorem BodyPost.schedule {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hp : StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (addr32 (s.gpr .ebx)) = Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx)) := by
  apply scheduleAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData (And.intro
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) hp.stackKey.symm))

theorem BodyPost.tailData {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64) :
    Spec.Rc2.blocksAt s'.mem (addr32 (s.gpr .esi) + 8) n = Spec.Rc2.blocksAt s.mem (addr32 (s.gpr .esi) + 8) n := by
  have sub : Region.Sub ⟨addr32 (s.gpr .esi) + 8, 8 * n⟩ (dataR s (n + 1)) :=
    Offset.sub_base _ (by change 8 + 8 * n ≤ 8 * (n + 1); omega_using [])
  have sep : (Region.mk (addr32 (s.gpr .esi) + 8) (8 * n)).Disjoint (dataR s) :=
    Offset.disjoint_base _ (d := 8) (n := 8 * n) (k := 8) (by decide) (by omega_using [bound])
  apply blocksAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right sub).symm) (And.intro sep (And.intro
      ((hp.dataBuf.sub_left sub).sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) (hp.stackData.sub_right sub).symm))

theorem firstBlock_frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat} {m : Mem}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64)
    (hn : 1 ≤ n)
    (frame : Frame (loopWrites s' n) s'.mem m) :
    Spec.Rc2.blockAt m (addr32 (s.gpr .esi)) = Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .esi)) := by
  have first : Region.Sub (dataR s) (dataR s (n + 1)) := Region.sub_prefix (by change 8 ≤ 8 * (n + 1); omega_using [])
  have sep : (dataR s).Disjoint ⟨addr32 (s.gpr .esi) + 8, 8 * n⟩ :=
    Offset.base_disjoint _ (e := 8) (n := 8 * n) (k := 8) (by decide) (by omega_using [bound])
  have ptr : addr32 (s'.gpr .esi) = addr32 (s.gpr .esi) + 8 := by
    rw [h.ptr]
    exact addr_add (k := 8) (by have := hp.dataFit; omega_using [hn, this])
  apply blockAt_frame frame
  have iv := h.reg .ecx (by decide) (by decide) (by decide)
  have buf := h.reg .ebp (by decide) (by decide) (by decide)
  have sp := h.reg .esp (by decide) (by decide) (by decide)
  simpa only [loopWrites, ivR, dataR, stackR, iv, buf, ptr, sp,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right first).symm) (And.intro sep (And.intro
      ((hp.dataBuf.sub_left first).sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) (hp.stackData.sub_right first).symm))

end VG.Proof.Rc2.X86.Cbc

end

/-! # Correctness of the CBC loop on complete blocks -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

structure LoopPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (8 * n)
  count : s'.gpr .edi = 0
  reg : ∀ r ∈ kept, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (loopWrites s n) s.mem s'.mem
  data : Spec.Rc2.blocksAt s'.mem (addr32 (s.gpr .esi)) n =
    (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blocksAt s.mem (addr32 (s.gpr .esi)) n)).1
  iv : Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .ecx)) =
    (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blocksAt s.mem (addr32 (s.gpr .esi)) n)).2

theorem loop_ok (d : Spec.Rc2.Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → 8 * n ≤ 2 ^ 32 → StepPre s n → s.gpr .edi = BitVec.ofNat 32 n →
      WP isa (.loop (Impl.Rc2.X86.Cbc.body d) .ne) s (LoopPost d s n) := by
  induction n with
  | zero => intro s hn; omega
  | succ n ih =>
    intro s hn bound hp count
    obtain ⟨t₁, s₁, exec₁, h₁⟩ := body_ok d s (n + 1) hn (by omega_using [bound]) count (hp.head hn)
    by_cases hz : n = 0
    · subst n
      refine ⟨_, s₁, Exec.loopExit exec₁ ?_, ?_⟩
      · simp only [eval_nonzeroCount, h₁.flag, decide_true, Option.map_some, Bool.not_true]
      · refine ⟨h₁.ptr, h₁.count, h₁.reg, h₁.callee, h₁.rd, h₁.wr, h₁.frame (by decide), ?_, ?_⟩
        · rw [blocksAt_cons, blocksAt_cons]
          simp only [Spec.Rc2.blocksAt, List.range_zero, List.map_nil, Proof.Rc2.cbcBlocks]
          exact congrArg (· :: []) h₁.data
        · rw [blocksAt_cons]
          simp only [Spec.Rc2.blocksAt, List.range_zero, List.map_nil, Proof.Rc2.cbcBlocks]
          exact h₁.iv
    · have hp₁ := h₁.tail hp (by omega_using [hz])
      obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega_using [hz]) (by omega_using [bound]) hp₁ (by simpa using h₁.count)
      refine ⟨_, s₂, Exec.loopNext exec₁ ?_ exec₂, ?_⟩
      · have he : n + 1 ≠ 1 := by omega_using [hz]
        simp only [eval_nonzeroCount, h₁.flag, he, decide_false, Option.map_some, Bool.not_false]
      · have key := h₁.schedule (hp.head hn)
        have tail := h₁.tailData hp (by omega_using [bound])
        have data := h₂.data
        have iv := h₂.iv
        have ki := h₁.reg .ebx (by decide) (by decide) (by decide)
        have vi := h₁.reg .ecx (by decide) (by decide) (by decide)
        have bi := h₁.reg .ebp (by decide) (by decide) (by decide)
        have ptr : addr32 (s₁.gpr .esi) = addr32 (s.gpr .esi) + 8 := by
          rw [h₁.ptr]; exact addr_add (k := 8) (by have := hp.dataFit; omega_using [hz, this])
        rw [ki, vi, ptr, key, tail, h₁.iv] at data
        rw [ki, vi, ptr, key, tail, h₁.iv] at iv
        refine ⟨?_, h₂.count, ?_, ?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
        · rw [h₂.ptr, h₁.ptr, BitVec.add_assoc]
          exact congrArg (s.gpr .esi + ·) (by
            change BitVec.ofNat 32 8 + BitVec.ofNat 32 (8 * n) = _
            rw [← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 32) (by omega_using []))
        · intro r hr hs hb
          exact (h₂.reg r hr hs hb).trans (h₁.reg r hr hs hb)
        · intro r hr hs hb
          exact (h₂.callee r hr hs hb).trans (h₁.callee r hr hs hb)
        · exact (h₁.frame hn).trans (loopFrame_slice (i := 1) h₂.mem (by omega_using []) vi bi (h₁.reg .esp (by decide) (by decide) (by decide)) ptr)
        · have first := firstBlock_frame h₁ hp (by omega_using [bound]) (by omega_using [hz]) h₂.mem
          rw [blocksAt_cons, first, h₁.data, data, blocksAt_cons]
          rfl
        · rw [blocksAt_cons]
          exact iv

theorem maybeLoop_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 32)
    (hp : StepPre s n) (count : s.gpr .edi = BitVec.ofNat 32 n)
    (flag : zeroCount s = some (s.gpr .edi == 0)) :
    WP isa (.ite .e (.block []) (.loop (Impl.Rc2.X86.Cbc.body d) .ne)) s (LoopPost d s n) := by
  have eqZero := counter_eq n 0 (by omega_using [bound]) (by decide)
  simp only [BitVec.sub_zero] at eqZero
  have flag' : zeroCount s = some (decide (n = 0)) := by
    rw [flag, count]
    exact congrArg some eqZero
  by_cases hz : n = 0
  · subst n
    apply WP.ite true (by simp only [eval_zeroCount, flag', decide_true])
    · intro _
      apply WP.block_nil
      refine ⟨by simp, count, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, ?_, ?_⟩
      · rfl
      · rfl
    · simp
  · apply WP.ite false (by simp only [eval_zeroCount, flag', hz, decide_false])
    · simp
    · intro _
      exact loop_ok d n s (by omega_using [hz]) bound hp count

theorem LoopPost.scratchRead {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : LoopPost d s n s') (hp : StepPre s n) (i : Nat) (lo : 264 ≤ i) (hi : i + 4 ≤ 512) :
    s'.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 32 = s.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 32 := by
  have sub : Region.Sub ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 i, 4⟩ (bufR s) := Offset.sub_base _ hi
  have sep : (Region.mk (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 4).Disjoint ⟨addr32 (s.gpr .ebp), 264⟩ :=
    Offset.disjoint_base _ lo (by omega_using [hi])
  apply h.mem.readW (r := ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 i, 4⟩) (Region.contains_self _ _)
    (hn := by decide)
  simpa only [loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivBuf.sub_right sub).symm) (And.intro ((hp.dataBuf.sub_right sub).symm)
      (And.intro sep (hp.stackBuf.sub_right sub).symm))

end VG.Proof.Rc2.X86.Cbc

end

end

/-! ### `Rc2.X86.Cbc.ConstantTime`, which the modules that import this one used -/

section

@[expose] public section

section

section

/-! # Constant-time CBC steps with public registers restored by the block call -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

def EqKept (s₁ s₂ : State) : Prop := ∀ r ∈ kept, s₁.gpr r = s₂.gpr r

def StepRel (s₁ s₂ : State) : Prop := StepPre s₁ ∧ StepPre s₂ ∧ EqKept s₁ s₂

theorem agreeKept {s₁ s₂ : State} (h : EqKept s₁ s₂) :
    VG.X86.Taint.Agree (τr kept) s₁ s₂ := agree_regs h

theorem before_ok (d : Spec.Rc2.Direction) (s : State) (hp : StepPre s) :
    WP isa (.block (Impl.Rc2.X86.Cbc.before d)) s (fun s' => StepPre s' ∧ ∀ r ∈ kept, s'.gpr r = s.gpr r) := by
  have sep : ∀ r ∈ kept, r ∉ temps := by decide
  cases d
  · apply WP.mono (xor64_ok s .esi .ecx (by decide) (by decide)
      (by simpa using hp.dataFit) hp.ivFit hp.readData hp.readIv hp.writeData)
    intro s' h
    exact ⟨hp.keep h, fun r hr => h.reg r (sep r hr)⟩
  · apply WP.mono (copy64_ok s .esi .ebp 0 256 (by decide) (by decide)
      (by simpa using hp.dataFit) (by have := hp.bufFit; omega_using [this])
      (by simpa using hp.readData) (hp.writeBuf 256 (by decide)))
    intro s' h
    exact ⟨hp.keep h, fun r hr => h.reg r (sep r hr)⟩

theorem kept_ct {c : Prog isa} (h : RelCT isa StepRel c (fun _ _ => True))
    (correct : ∀ s, StepPre s → WP isa c s (fun s' => StepPre s' ∧ ∀ r ∈ kept, s'.gpr r = s.gpr r)) :
    RelCT isa StepRel c StepRel := by
  apply (h.wpDep (fun s₁ s₂ hp => ⟨correct s₁ hp.1, correct s₂ hp.2.1⟩)).mono
    (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  refine ⟨h₁.1, h₂.1, fun r hr => ?_⟩
  rw [h₁.2 r hr, h₂.2 r hr]
  exact hp.2.2 r hr

theorem before_ct (d : Spec.Rc2.Direction) :
    RelCT isa StepRel (.block (Impl.Rc2.X86.Cbc.before d)) StepRel := by
  apply kept_ct _ (before_ok d)
  cases d <;> apply RelCT.taint (A := taint) (τr kept) (fun _ _ h => agreeKept h.2.2)
  all_goals taint_decide

def callRd (s : State) : List Region :=
  [⟨addr32 (s.gpr .ebx), 128⟩, ⟨argAddr (pushed [.ebp, .esi, .ebx] s).callEntry 0, 12⟩]
def callWr (s : State) : List Region := [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 256⟩]

theorem callPre_ok (d : Spec.Rc2.Direction) (s : State) (hp : CallPre s) :
    VG.X86.CallPre (blockContract d) [.ebp, .esi, .ebx] (callRd s) (callWr s) s := by
  let rs : List Reg := [.ebp, .esi, .ebx]
  have hrs : .esp ∉ rs := by decide
  have fit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat := hp.stackLo
  let sE := (pushed rs s).callEntry
  have a0 : arg sE 0 = s.gpr .ebx := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have a1 : arg sE 1 = s.gpr .esi := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have a2 : arg sE 2 = s.gpr .ebp := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have eA : argAddr sE 0 = ((s.gpr .esp) - BitVec.ofNat 32 12).setWidth 64 := by rw [callEntry_argAddr0]; rfl
  have eSp : sE.gpr .esp = s.gpr .esp - BitVec.ofNat 32 16 := by rw [callEntry_esp']; rfl
  have b12 : Region.Sub (below (s.gpr .esp) 12) (below (s.gpr .esp) 16) := below_sub (by decide) hp.stackLo
  have r4 : Region.Sub ⟨((s.gpr .esp) - BitVec.ofNat 32 16).setWidth 64, 4⟩ (below (s.gpr .esp) 16) :=
    Region.sub_prefix (by decide)
  unfold callRd callWr
  refine ⟨?_, ?_, ?_⟩
  · change (blockContract d).pre (sE.withRegions _ _)
    simp only [blockContract, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp]
    refine ⟨?_, trivial, hp.keyScratch, hp.dataScratch, hp.stackData.sub_left b12,
      hp.stackBuf.sub_left b12, hp.stackData.sub_left r4, hp.stackBuf.sub_left r4,
      hp.keyFit, hp.dataFit, hp.bufFit, ?_⟩
    · rw [callEntry_argAddr0]; rfl
    rw [sub_toNat hp.stackLo]
    have := (s.gpr .esp).isLt
    omega_using []
  · intro a n ⟨r, hr, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · apply InRegions_append_cons.mpr
      left
      rw [eA] at hc
      exact hc
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hp.writes a n h
    exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩

theorem call_ct (d : Spec.Rc2.Direction) : RelCT isa StepRel (Impl.Rc2.X86.Cbc.blockCall d) StepRel := by
  apply kept_ct
  · intro s₁ s₂ t₁ t₂ u₁ u₂ hp e₁ e₂
    have sp := hp.2.2 .esp (by decide)
    have key := hp.2.2 .ebx (by decide)
    have data := hp.2.2 .esi (by decide)
    have buf := hp.2.2 .ebp (by decide)
    have rd : callRd s₂ = callRd s₁ := by
      simp only [callRd, callEntry_argAddr0, key, sp]
    have wr : callWr s₂ = callWr s₁ := by simp only [callWr, data, buf]
    have hc : ConstantTime isa (blockContract d).pre (blockContract d).pub (.block (blockCode d)) := by
      cases d
      · exact encryptBlock_constantTime
      · exact decryptBlock_constantTime
    have ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (Impl.Rc2.X86.Cbc.blockCall d) (fun _ _ => True) := by
      rw [blockCall_eq]
      apply RelCT.callWith (block_correct d) hc (callRd s₁) (callWr s₁)
      rintro a b ⟨ha, hb⟩
      subst a b
      refine ⟨callPre_ok d s₁ hp.1.call, ?_, sp, ?_⟩
      · rw [← rd, ← wr]; exact callPre_ok d s₂ hp.2.1.call
      · constructor
        · simp only [State.withRegions_gpr, callEntry_esp', sp]
        · intro i hi
          simp only [arg_withRegions]
          rw [callEntry_arg (by exact hp.1.stackLo) (by decide) (by simpa using hi),
            callEntry_arg (by exact hp.2.1.stackLo) (by decide) (by simpa using hi)]
          have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega_using [hi]
          rcases cases with rfl | rfl | rfl
          · exact key
          · exact data
          · exact buf
    exact ct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  · intro s hp
    apply WP.mono (call_ok d s hp.call)
    intro s' h
    exact ⟨hp.transport h.rd h.wr h.reg, h.reg⟩

theorem after_ct (d : Spec.Rc2.Direction) :
    RelCT isa StepRel (.block (Impl.Rc2.X86.Cbc.after d)) (fun _ _ => True) := by
  cases d <;> apply RelCT.taint (A := taint) (τr kept) (fun _ _ h => agreeKept h.2.2)
  all_goals taint_decide

theorem step_ct (d : Spec.Rc2.Direction) :
    RelCT isa StepRel (Impl.Rc2.X86.Cbc.step d) StepRel := by
  apply kept_ct ((before_ct d).seq ((call_ct d).seq (after_ct d)))
  intro s hp
  apply WP.mono (step_ok d s hp)
  intro s' h
  exact ⟨h.toPinned.pre hp, h.reg⟩

theorem body_ct (d : Spec.Rc2.Direction) :
    RelCT isa StepRel (Impl.Rc2.X86.Cbc.body d) (fun _ _ => True) := by
  apply (step_ct d).seq
  apply RelCT.taint (A := taint) (τr kept) (fun _ _ h => agreeKept h.2.2)
  taint_decide

end VG.Proof.Rc2.X86.Cbc

end

section

/-! # Constant-time CBC loops -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

def LoopRel (n : Nat) (s₁ s₂ : State) : Prop :=
  StepPre s₁ n ∧ StepPre s₂ n ∧ EqKept s₁ s₂ ∧
    s₁.gpr .edi = BitVec.ofNat 32 n ∧ s₂.gpr .edi = BitVec.ofNat 32 n ∧ 1 ≤ n

theorem bodyRel (d : Spec.Rc2.Direction) (n : Nat) :
    RelCT isa (LoopRel n) (Impl.Rc2.X86.Cbc.body d) (fun s₁ s₂ =>
      EqKept s₁ s₂ ∧ eval .ne s₁ = eval .ne s₂ ∧
        (eval .ne s₁ = some true → ∃ m < n, LoopRel m s₁ s₂)) := by
  have ct : RelCT isa (LoopRel n) (Impl.Rc2.X86.Cbc.body d) (fun _ _ => True) :=
    (body_ct d).mono (fun _ _ h => ⟨h.1.head h.2.2.2.2.2, h.2.1.head h.2.2.2.2.2, h.2.2.1⟩)
      (fun _ _ _ => trivial)
  have correct (s₁ s₂ : State) (h : LoopRel n s₁ s₂) :=
    And.intro (body_ok d s₁ n h.2.2.2.2.2 (by have := h.1.dataFit; omega_using [this]) h.2.2.2.1 (h.1.head h.2.2.2.2.2))
      (body_ok d s₂ n h.2.2.2.2.2 (by have := h.2.1.dataFit; omega_using [this]) h.2.2.2.2.1 (h.2.1.head h.2.2.2.2.2))
  apply (ct.wpDep correct).mono (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  have eq : EqKept s₁' s₂' := by
    intro r hr
    by_cases hptr : r = .esi
    · subst r; rw [h₁.ptr, h₂.ptr, hp.2.2.1 .esi (by decide)]
    · by_cases hcount : r = .edi
      · subst r; rw [h₁.count, h₂.count]
      · rw [h₁.reg r hr hptr hcount, h₂.reg r hr hptr hcount]
        exact hp.2.2.1 r hr
  refine ⟨eq, by rw [eval_nonzeroCount, eval_nonzeroCount, h₁.flag, h₂.flag], ?_⟩
  intro hcontinue
  have hn : 1 ≤ n := hp.2.2.2.2.2
  have hm : 1 ≤ n - 1 := by
    rw [eval_nonzeroCount, h₁.flag] at hcontinue
    by_contra h
    have e : n = 1 := by omega_using [hn, h]
    simp only [e, decide_true, Option.map_some, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at hcontinue
  refine ⟨n - 1, by omega_using [hn], ?_, ?_, eq, h₁.count, h₂.count, hm⟩
  · have e : n = (n - 1) + 1 := by omega_using [hn]
    rw [e] at h₁ hp
    exact h₁.tail hp.1 hm
  · have e : n = (n - 1) + 1 := by omega_using [hn]
    rw [e] at h₂ hp
    exact h₂.tail hp.2.1 hm

theorem loop_ct (d : Spec.Rc2.Direction) (n : Nat) :
    RelCT isa (LoopRel n) (.loop (Impl.Rc2.X86.Cbc.body d) .ne) EqKept := by
  refine RelCT.loop (M := isa) (body := Impl.Rc2.X86.Cbc.body d) (c := .ne) (Q := EqKept) LoopRel ?_ n
  intro m
  exact (bodyRel d m).mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, fun _ => h.1, h.2.2⟩)

def MaybeRel (s₁ s₂ : State) : Prop :=
  ∃ n, StepPre s₁ n ∧ StepPre s₂ n ∧ EqKept s₁ s₂ ∧
    s₁.gpr .edi = BitVec.ofNat 32 n ∧ s₂.gpr .edi = BitVec.ofNat 32 n ∧
    zeroCount s₁ = some (decide (n = 0)) ∧ zeroCount s₂ = some (decide (n = 0))

theorem maybeLoop_ct (d : Spec.Rc2.Direction) :
    RelCT isa MaybeRel (.ite .e (.block []) (.loop (Impl.Rc2.X86.Cbc.body d) .ne)) EqKept := by
  apply RelCT.ite
  · rintro s₁ s₂ ⟨n, _, _, _, _, _, h₁, h₂⟩
    change zeroCount s₁ = zeroCount s₂
    rw [h₁, h₂]
  · apply RelCT.nil
    rintro s₁ s₂ ⟨⟨n, _, _, eq, _⟩, _⟩
    exact eq
  · apply RelCT.exists_ (fun n => loop_ct d n) |>.mono
    · rintro s₁ s₂ ⟨⟨n, h₁, h₂, eq, c₁, c₂, z₁, _⟩, branch⟩
      refine ⟨n, h₁, h₂, eq, c₁, c₂, ?_⟩
      change zeroCount s₁ = some false at branch
      rw [z₁] at branch
      have hn : n ≠ 0 := by intro hz; simp [hz] at branch
      omega_using [hn]
    · exact fun _ _ h => h

end VG.Proof.Rc2.X86.Cbc

end

namespace VG.Proof.Rc2.X86.Cbc
open VG VG.X86 VG.Impl.Rc2.X86

def startCode : Prog isa := .seq (.block [.mov .eax (.mem (memOp .esp 20))])
  (.block (Impl.Rc2.X86.Cbc.save ++ Impl.Rc2.X86.Cbc.setup))

structure StartPost (s s' : State) : Prop where
  pre : StepPre s' (arg s 3).toNat
  key : s'.gpr .ebx = arg s 0
  iv : s'.gpr .ecx = arg s 1
  data : s'.gpr .esi = arg s 2
  buf : s'.gpr .ebp = arg s 4
  count : s'.gpr .edi = arg s 3
  flag : zeroCount s' = some (arg s 3 == 0)
  sp : s'.gpr .esp = s.gpr .esp

theorem start_ok (d : Spec.Rc2.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa startCode s (StartPost s) := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    ivArgs, dataArgs, bufArgs, retIv, retData, retBuf, stackKey, stackIv, stackData, stackBuf, keyFit, ivFit, bufFit, spFit, stackLo, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 512) : InRegions s.wr (addr32 (arg s 4) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨addr32 (arg s 4), 512⟩, by simp, Offset.contains_base _ hi (by omega_using [hi])⟩
  rw [startCode]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadArg_ok s .eax 4 (by
    rw [hrd, hwr, argAddr_eq s 4 (by omega_using [spFit])]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit 4 (by decide)⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .eax) := keep₀.reg r (by simpa using hr)
  have writes₀ (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions s₀.wr (addr32 (s₀.gpr .eax) + BitVec.ofNat 64 i) 4 := by
    rw [keep₀.wr, buf₀]; exact writes i hi
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s₀ (by rw [buf₀]; exact bufFit)
    (writes₀ 264 (by decide)) (writes₀ 268 (by decide)) (writes₀ 272 (by decide))
    (writes₀ 276 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  have sp₁ : s₁.gpr .esp = s.gpr .esp := (g₁ .esp).trans (g₀ .esp (by decide))
  have saveFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₁.mem := by
    rw [keep₁.mem, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  have args₁ := args_frame saveFrame sp₁ spFit (by simpa using bufArgs)
  have readArgs₁ (i : Nat) (hi : i < 4) : InRegions (s₁.rd ++ s₁.wr) (argAddr s₁ i) 4 := by
    have ptr : argAddr s₁ i = argAddr s i := by unfold argAddr; rw [sp₁]
    rw [keep₁.rd, keep₁.wr, keep₀.rd, keep₀.wr, hrd, hwr, ptr, argAddr_eq s i (by omega_using [spFit, hi])]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit i (by omega_using [hi])⟩
  obtain ⟨s₂, run₂, key₂, iv₂, data₂, count₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁ readArgs₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [args₁ 0 (by decide)] at key₂
  rw [args₁ 1 (by decide)] at iv₂
  rw [args₁ 2 (by decide)] at data₂
  rw [args₁ 3 (by decide)] at count₂ flag₂
  rw [g₁, buf₀] at buf₂
  have sp₂ := (keep₂.reg .esp (by decide)).trans sp₁
  have rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  have wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  have hp₂ : StepPre s₂ (arg s 3).toNat := by
    constructor
    · rw [key₂]; exact keyFit
    · rw [iv₂]; exact ivFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · simp only [Covers, keyR, ivR, dataR, bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h <;> simp_all only [or_true, true_or], hc⟩
    · simp only [Covers, ivR, dataR, bufR, iv₂, data₂, buf₂, wr₂, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, hr, hc⟩
    · simpa only [keyR, ivR, key₂, iv₂] using keyIv
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [ivR, dataR, iv₂, data₂] using ivData
    · simpa only [ivR, bufR, iv₂, buf₂] using ivBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
    · rw [sp₂]; exact stackLo
    · simpa only [stackR, keyR, sp₂, key₂] using stackKey
    · simpa only [stackR, ivR, sp₂, iv₂] using stackIv
    · simpa only [stackR, dataR, sp₂, data₂] using stackData
    · simpa only [stackR, bufR, sp₂, buf₂] using stackBuf
  exact ⟨hp₂, key₂, iv₂, data₂, buf₂, count₂, flag₂, sp₂⟩

def InitialRel (d : Spec.Rc2.Direction) (s₁ s₂ : State) : Prop :=
  (contract d).pre s₁ ∧ (contract d).pre s₂ ∧ (contract d).pub s₁ s₂

def startTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 24 }

theorem startTaint_wf {d : Spec.Rc2.Direction} {s : State} (h : (contract d).pre s) : VG.X86.Taint.Wf startTaint s := by
  obtain ⟨_, wr, _, _, _, _, _, _, ai, ad, ab, ri, rd, rb, _, _, _, _, _, _, _, spfit, _⟩ := h
  refine Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨spfit, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [startTaint, wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact Taint.frame_disjoint (n := 20) (by omega_using [spfit]) ri ai
  · exact Taint.frame_disjoint (n := 20) (by omega_using [spfit]) rd ad
  · exact Taint.frame_disjoint (n := 20) (by omega_using [spfit]) rb ab

theorem startTaint_agree {d : Spec.Rc2.Direction} {s₁ s₂ : State} (h : InitialRel d s₁ s₂) :
    VG.X86.Taint.Agree startTaint s₁ s₂ := by
  obtain ⟨h₁, h₂, sp, args⟩ := h
  have fit : ∀ s, (contract d).pre s → (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 := by
    intro s hs
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hs
    exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    startTaint_wf h₁, startTaint_wf h₂, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [startTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [startTaint] at hk
    rw [show Taint.depth startTaint.stk = 0 from rfl, Nat.zero_add]
    rw [Taint.argByte_eq (fit _ h₁) h4 hk, Taint.argByte_eq (fit _ h₂) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega_using [hk]))

theorem start_ct (d : Spec.Rc2.Direction) : RelCT isa (InitialRel d) startCode MaybeRel := by
  have ct : RelCT isa (InitialRel d) startCode (fun _ _ => True) := by
    apply RelCT.taint (A := taint) startTaint (fun _ _ h => startTaint_agree h)
    taint_decide
  apply (ct.wpDep (fun s₁ s₂ h => ⟨start_ok d s₁ h.1, start_ok d s₂ h.2.1⟩)).mono (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  obtain ⟨sp, args⟩ := hp.2.2
  have p0 := args 0 (by decide)
  have p1 := args 1 (by decide)
  have p2 := args 2 (by decide)
  have p3 := args 3 (by decide)
  have bp := args 4 (by decide)
  refine ⟨(arg s₁ 3).toNat, h₁.pre, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p3]; exact h₂.pre
  · intro r hr
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₁.key, h₂.key, p0]
    · rw [h₁.iv, h₂.iv, p1]
    · rw [h₁.data, h₂.data, p2]
    · rw [h₁.count, h₂.count, p3]
    · rw [h₁.buf, h₂.buf, bp]
    · rw [h₁.sp, h₂.sp, sp]
  · simpa using h₁.count
  · rw [p3]; simpa using h₂.count
  · rw [h₁.flag]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h
  · rw [h₂.flag, p3]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h

end VG.Proof.Rc2.X86.Cbc

end

/-! # Constant-time CBC callers -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

theorem cbc_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (contract d).pre (contract d).pub (Impl.Rc2.X86.Cbc.cbc d) := by
  apply RelCT.constantTime
  apply RelCT.assoc
  apply (start_ct d).seq
  apply (maybeLoop_ct d).seq
  apply RelCT.taint (A := taint) (τr [.ebp])
    (fun _ _ h => agree_regs (fun r hr => h r (by have e := List.mem_singleton.mp hr; rw [e]; decide)))
  taint_decide

end VG.Proof.Rc2.X86.Cbc

end

end

/-! # Verified RC2-CBC encryption and decryption -/

@[expose] public section

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

theorem cbc_body_correct (d : Spec.Rc2.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.Rc2.X86.Cbc.cbc d) s (fun s' => abiPreserved s s' ∧ (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    ivArgs, dataArgs, bufArgs, retIv, retData, retBuf, stackKey, stackIv, stackData, stackBuf, keyFit, ivFit, bufFit, spFit, stackLo, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 512) : InRegions s.wr (addr32 (arg s 4) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨addr32 (arg s 4), 512⟩, by simp, Offset.contains_base _ hi (by omega_arith)⟩
  rw [Impl.Rc2.X86.Cbc.cbc]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadArg_ok s .eax 4 (by
    rw [hrd, hwr, argAddr_eq s 4 (by omega_arith)]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit 4 (by decide)⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .eax) := keep₀.reg r (by simpa using hr)
  have writes₀ (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions s₀.wr (addr32 (s₀.gpr .eax) + BitVec.ofNat 64 i) 4 := by
    rw [keep₀.wr, buf₀]; exact writes i hi
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s₀ (by rw [buf₀]; exact bufFit)
    (writes₀ 264 (by decide)) (writes₀ 268 (by decide)) (writes₀ 272 (by decide))
    (writes₀ 276 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  obtain sp₁ : s₁.gpr .esp = s.gpr .esp := (g₁ .esp).trans (g₀ .esp (by decide))
  obtain saveFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₁.mem := by
    rw [keep₁.mem, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  obtain args₁ := args_frame saveFrame sp₁ spFit (by simpa using bufArgs)
  have readArgs₁ (i : Nat) (hi : i < 4) : InRegions (s₁.rd ++ s₁.wr) (argAddr s₁ i) 4 := by
    obtain ptr : argAddr s₁ i = argAddr s i := by unfold argAddr; rw [sp₁]
    rw [keep₁.rd, keep₁.wr, keep₀.rd, keep₀.wr, hrd, hwr, ptr, argAddr_eq s i (by omega_arith)]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit i (by omega_arith)⟩
  obtain ⟨s₂, run₂, key₂, iv₂, data₂, count₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁ readArgs₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [args₁ 0 (by decide)] at key₂
  rw [args₁ 1 (by decide)] at iv₂
  rw [args₁ 2 (by decide)] at data₂
  rw [args₁ 3 (by decide)] at count₂ flag₂
  rw [g₁, buf₀] at buf₂
  obtain sp₂ := (keep₂.reg .esp (by decide)).trans sp₁
  obtain rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  obtain wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  obtain mem₂ : s₂.mem = savedMem s₀ := keep₂.mem.trans keep₁.mem
  obtain scratchFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₂.mem := by
    rw [mem₂, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  obtain initialKey := scheduleAt_frame scratchFrame (addr32 (arg s 0)) (by simpa using keyBuf)
  obtain initialIv := blockAt_frame scratchFrame (addr32 (arg s 1)) (by simpa using ivBuf)
  obtain initialData := blocksAt_frame scratchFrame (addr32 (arg s 2)) (arg s 3).toNat (by simpa using dataBuf)
  obtain hp₂ : StepPre s₂ (arg s 3).toNat := by
    constructor
    · rw [key₂]; exact keyFit
    · rw [iv₂]; exact ivFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · simp only [Covers, keyR, ivR, dataR, bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h <;> simp_all only [or_true, true_or], hc⟩
    · simp only [Covers, ivR, dataR, bufR, iv₂, data₂, buf₂, wr₂, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, hr, hc⟩
    · simpa only [keyR, ivR, key₂, iv₂] using keyIv
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [ivR, dataR, iv₂, data₂] using ivData
    · simpa only [ivR, bufR, iv₂, buf₂] using ivBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
    · rw [sp₂]; exact stackLo
    · simpa only [stackR, keyR, sp₂, key₂] using stackKey
    · simpa only [stackR, ivR, sp₂, iv₂] using stackIv
    · simpa only [stackR, dataR, sp₂, data₂] using stackData
    · simpa only [stackR, bufR, sp₂, buf₂] using stackBuf
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (arg s 3).toNat (by omega_arith) hp₂
    (by simpa using count₂) (by rw [count₂]; exact flag₂))
  intro s₃ h₃
  obtain rd₃ := h₃.rd.trans rd₂
  obtain wr₃ := h₃.wr.trans wr₂
  obtain buf₃ := (h₃.reg .ebp (by decide) (by decide) (by decide)).trans buf₂
  have reads (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions (s₃.rd ++ s₃.wr) (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 i) 4 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain v0 : s₃.mem.readW (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 264) 32 = s.gpr .ebp := by
    obtain h := h₃.scratchRead hp₂ 264 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_ebp, g₀ .ebp (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  obtain v1 : s₃.mem.readW (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 268) 32 = s.gpr .ebx := by
    obtain h := h₃.scratchRead hp₂ 268 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_ebx, g₀ .ebx (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  obtain v2 : s₃.mem.readW (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 272) 32 = s.gpr .esi := by
    obtain h := h₃.scratchRead hp₂ 272 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_esi, g₀ .esi (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  obtain v3 : s₃.mem.readW (addr32 (s₃.gpr .ebp) + BitVec.ofNat 64 276) 32 = s.gpr .edi := by
    obtain h := h₃.scratchRead hp₂ 276 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_edi, g₀ .edi (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  obtain ⟨s₄, run₄, saved₄, keep₄⟩ := restore_ok s₃ s.gpr (by rw [buf₃]; exact bufFit)
    (reads 264 (by decide)) v0    (reads 268 (by decide)) v1    (reads 272 (by decide)) v2    (reads 276 (by decide)) v3
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · constructor
    · intro r hr
      by_cases saved : r ∈ callerSaved
      · exact saved₄ r saved
      · have eqSp : r = .esp := by cases r <;> simp_all [calleeSaved, callerSaved]
        subst r
        rw [keep₄.reg .esp (by decide), h₃.reg .esp (by decide) (by decide) (by decide), sp₂]
    · have stackRet : (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint (below (s.gpr .esp) 16) := by
        change (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint ⟨_, 16⟩
        rw [Taint.sub_setWidth stackLo]
        exact Offset.base_disjoint_below _ (by decide)
      have frameLoop := h₃.mem
      obtain retSep : ∀ r ∈ loopWrites s₂ (arg s 3).toNat, (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint r := by
        simpa only [loopWrites, ivR, dataR, stackR, iv₂, data₂, buf₂, sp₂,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
          And.intro retIv (And.intro retData (And.intro (retBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) stackRet))
      change s₄.mem.readW (addr32 (s.gpr .esp)) 32 = s.mem.readW (addr32 (s.gpr .esp)) 32
      rw [keep₄.mem, frameLoop.readW (Region.contains_self _ _) retSep (by decide),
        scratchFrame.readW (Region.contains_self _ _) (by simpa using retBuf) (by decide)]
  · have out := h₃.data
    have iv := h₃.iv
    rw [key₂, iv₂, data₂, initialKey, initialIv, initialData] at out iv
    constructor
    · rw [keep₄.mem]; exact out
    · rw [keep₄.mem]; exact iv

end VG.Proof.Rc2.X86.Cbc
