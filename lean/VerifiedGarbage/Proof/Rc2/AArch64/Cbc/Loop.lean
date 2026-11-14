module

public import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Frame
public import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Steps
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.AArch64.Lit
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Decrypt
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Slice
import VerifiedGarbage.Proof.Rc2.AArch64.KeyLoop
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Rc2.AArch64.Cbc.LoopFrame`, which only this module used -/

section

/-! ### `Rc2.AArch64.Cbc.Body`, which only this module used -/

section

/-! ### `Rc2.AArch64.Cbc.Encrypt`, which only this module used -/

section

/-! # One CBC encryption step -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem encryptStep_ok (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.AArch64.Cbc.step .encrypt) s (StepPost .encrypt s) := by
  rw [Impl.Rc2.AArch64.Cbc.step]
  apply WP.seq
  obtain ⟨s₁, run₁, keep₁⟩ := xor64_ok s .x1 .x23 (by decide) (by decide)
    hp.readData hp.readIv hp.writeData
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have pin₁ := Pinned.of_keep keep₁ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ : Spec.Rc2.blockAt s₁.mem (s.gpr .x1) =
      Proof.Rc2.xorBlock (Spec.Rc2.blockAt s.mem (s.gpr .x1)) (Spec.Rc2.blockAt s.mem (s.gpr .x23)) := by
    rw [keep₁.mem]; exact blockAt_xor _ _ _
  apply WP.seq
  apply WP.mono (call_ok .encrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .x1 (by decide), pin₁.reg .x0 (by decide), key₁, data₁] at output₂
  obtain ⟨s₃, run₃, keep₃⟩ := copy64_ok s₂ .x1 .x23 0 0 (by decide)
    (by simpa using hp₂.readData) (by simpa using hp₂.writeIv)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  simp only [BitVec.add_zero] at keep₃
  have frame₃ : Frame [ivR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  refine ⟨pin₂.trans pin₃, ?_, ?_⟩
  · have same := blockAt_frame frame₃ (s₂.gpr .x1) (by simpa using hp₂.ivData.symm)
    rw [pin₂.reg .x1 (by decide)] at same
    exact same.trans output₂
  · have out : Spec.Rc2.blockAt s₃.mem (s₂.gpr .x23) = Spec.Rc2.blockAt s₂.mem (s₂.gpr .x1) := by
      rw [keep₃.mem]; exact blockAt_copy _ _ _
    rw [pin₂.reg .x23 (by decide), pin₂.reg .x1 (by decide)] at out
    exact out.trans output₂

end VG.Proof.Rc2.AArch64.Cbc

end

end


/-! # A CBC loop iteration and its public counter -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem step_ok (d : Spec.Rc2.Direction) (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.AArch64.Cbc.step d) s (StepPost d s) := by
  cases d
  · exact encryptStep_ok s hp
  · exact decryptStep_ok s hp

structure BodyPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .x1 = s.gpr .x1 + 8
  count : s'.gpr .x24 = BitVec.ofNat 64 (n - 1)
  flag : zeroCount s' = some (decide (n = 1))
  reg : ∀ r ∈ kept, r ≠ .x1 → r ≠ .x24 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, r ≠ .x24 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (stepWrites s) s.mem s'.mem
  data : Spec.Rc2.blockAt s'.mem (s.gpr .x1) =
    (Proof.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blockAt s.mem (s.gpr .x1))).1
  iv : Spec.Rc2.blockAt s'.mem (s.gpr .x23) =
    (Proof.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blockAt s.mem (s.gpr .x1))).2

theorem body_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 64)
    (count : s.gpr .x24 = BitVec.ofNat 64 n) (hp : StepPre s) :
    WP isa (Impl.Rc2.AArch64.Cbc.body d) s (BodyPost d s n) := by
  rw [Impl.Rc2.AArch64.Cbc.body]
  apply WP.seq
  apply WP.mono (step_ok d s hp)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, flag₂, keep₂⟩ := advance_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have count' : s₁.gpr .x24 - 1 = BitVec.ofNat 64 (n - 1) := by
    rw [h₁.reg .x24 (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .x1 (by decide)], count₂.trans count', ?_, ?_, ?_,
    keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
  · rw [flag₂, count']
    have eqZero := counter_eq (n - 1) 0 (by omega_using [bound]) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    change some (BitVec.ofNat 64 (n - 1) == 0#64) = _
    rw [eqZero]
    have he : n - 1 = 0 ↔ n = 1 := by omega_using [hn]
    simp only [he]
  · intro r hr hs hb
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.reg r hr)
  · intro r hr hb
    have hs : r ≠ .x1 := by
      have fact : ∀ r ∈ savedAcrossCall, r ≠ .x1 := by decide
      exact fact r hr
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.callee r hr)
  · rw [keep₂.mem]; exact h₁.mem
  · rw [keep₂.mem]; exact h₁.data
  · rw [keep₂.mem]; exact h₁.iv

theorem BodyPost.tail {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) : StepPre s' n :=
  hp.slice (i := 1) (by omega_using []) h.rd h.wr
    (h.reg .x0 (by decide) (by decide) (by decide))
    (h.reg .x23 (by decide) (by decide) (by decide))
    (h.reg .x2 (by decide) (by decide) (by decide))
    h.ptr

end VG.Proof.Rc2.AArch64.Cbc

end

end


/-! # Frames for successive CBC blocks -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64

def loopWrites (s : State) (n : Nat) : List Region := [ivR s, dataR s n, ⟨s.gpr .x2, 264⟩]

theorem loopFrame_slice {s s' : State} {n m i : Nat} {a b : Mem}
    (h : Frame (loopWrites s' m) a b) (bound : i + m ≤ n)
    (iv : s'.gpr .x23 = s.gpr .x23) (buf : s'.gpr .x2 = s.gpr .x2)
    (ptr : s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * i)) :
    Frame (loopWrites s n) a b := by
  apply h.sub
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨ivR s, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨s'.gpr .x23, 8⟩ ⟨s.gpr .x23, 8⟩
    rw [iv]; exact fun _ h => h
  · refine ⟨dataR s n, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨s'.gpr .x1, 8 * m⟩ ⟨s.gpr .x1, 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega_using [bound])
  · refine ⟨⟨s.gpr .x2, 264⟩, by simp [loopWrites], ?_⟩
    rw [buf]; exact fun _ h => h

theorem BodyPost.frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hn : 1 ≤ n) : Frame (loopWrites s n) s.mem s'.mem :=
  loopFrame_slice (m := 1) (i := 0) h.mem hn rfl rfl (by simp)

theorem BodyPost.schedule {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hp : StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (s.gpr .x0) = Spec.Rc2.scheduleAt s.mem (s.gpr .x0) := by
  apply scheduleAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))))

theorem BodyPost.tailData {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64) :
    Spec.Rc2.blocksAt s'.mem (s.gpr .x1 + 8) n = Spec.Rc2.blocksAt s.mem (s.gpr .x1 + 8) n := by
  have sub : Region.Sub ⟨s.gpr .x1 + 8, 8 * n⟩ (dataR s (n + 1)) :=
    Offset.sub_base _ (by change 8 + 8 * n ≤ 8 * (n + 1); omega_using [])
  have sep : (Region.mk (s.gpr .x1 + 8) (8 * n)).Disjoint (dataR s) :=
    Offset.disjoint_base _ (d := 8) (n := 8 * n) (k := 8) (by decide) (by omega_using [bound])
  apply blocksAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right sub).symm) (And.intro sep
      ((hp.dataBuf.sub_left sub).sub_right (Region.sub_prefix (by decide : 264 ≤ 512))))

theorem firstBlock_frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat} {m : Mem}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64)
    (frame : Frame (loopWrites s' n) s'.mem m) :
    Spec.Rc2.blockAt m (s.gpr .x1) = Spec.Rc2.blockAt s'.mem (s.gpr .x1) := by
  have first : Region.Sub (dataR s) (dataR s (n + 1)) := Region.sub_prefix (by change 8 ≤ 8 * (n + 1); omega_using [])
  have sep : (dataR s).Disjoint ⟨s.gpr .x1 + 8, 8 * n⟩ :=
    Offset.base_disjoint _ (e := 8) (n := 8 * n) (k := 8) (by decide) (by omega_using [bound])
  apply blockAt_frame frame
  have iv := h.reg .x23 (by decide) (by decide) (by decide)
  have buf := h.reg .x2 (by decide) (by decide) (by decide)
  simpa only [loopWrites, ivR, dataR, iv, buf, h.ptr,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right first).symm) (And.intro sep
      ((hp.dataBuf.sub_left first).sub_right (Region.sub_prefix (by decide : 264 ≤ 512))))

end VG.Proof.Rc2.AArch64.Cbc

end

end


/-! # Correctness of the CBC loop on complete blocks -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64

structure LoopPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * n)
  count : s'.gpr .x24 = 0
  reg : ∀ r ∈ kept, r ≠ .x1 → r ≠ .x24 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, r ≠ .x24 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (loopWrites s n) s.mem s'.mem
  data : Spec.Rc2.blocksAt s'.mem (s.gpr .x1) n =
    (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) n)).1
  iv : Spec.Rc2.blockAt s'.mem (s.gpr .x23) =
    (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) n)).2

theorem loop_ok (d : Spec.Rc2.Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → 8 * n ≤ 2 ^ 64 → StepPre s n → s.gpr .x24 = BitVec.ofNat 64 n →
      WP isa (.loop (Impl.Rc2.AArch64.Cbc.body d) (.nonzero .x .x24)) s (LoopPost d s n) := by
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
    · have hp₁ := h₁.tail hp
      obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega_using [hz]) (by omega_using [bound]) hp₁ (by simpa using h₁.count)
      refine ⟨_, s₂, Exec.loopNext exec₁ ?_ exec₂, ?_⟩
      · have he : n + 1 ≠ 1 := by omega_using [hz]
        simp only [eval_nonzeroCount, h₁.flag, he, decide_false, Option.map_some, Bool.not_false]
      · have key := h₁.schedule (hp.head hn)
        have tail := h₁.tailData hp bound
        have data := h₂.data
        have iv := h₂.iv
        have ki := h₁.reg .x0 (by decide) (by decide) (by decide)
        have vi := h₁.reg .x23 (by decide) (by decide) (by decide)
        have bi := h₁.reg .x2 (by decide) (by decide) (by decide)
        rw [ki, vi, h₁.ptr, key, tail, h₁.iv] at data
        rw [ki, vi, h₁.ptr, key, tail, h₁.iv] at iv
        refine ⟨?_, h₂.count, ?_, ?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
        · rw [h₂.ptr, h₁.ptr, BitVec.add_assoc]
          exact congrArg (s.gpr .x1 + ·) (by
            change BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * n) = _
            rw [← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 64) (by omega_using []))
        · intro r hr hs hb
          exact (h₂.reg r hr hs hb).trans (h₁.reg r hr hs hb)
        · intro r hr hb
          exact (h₂.callee r hr hb).trans (h₁.callee r hr hb)
        · exact (h₁.frame hn).trans (loopFrame_slice (i := 1) h₂.mem (by omega_using []) vi bi h₁.ptr)
        · have first := firstBlock_frame h₁ hp bound h₂.mem
          rw [blocksAt_cons, first, h₁.data, data, blocksAt_cons]
          rfl
        · rw [blocksAt_cons]
          exact iv

theorem maybeLoop_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 64)
    (hp : StepPre s n) (count : s.gpr .x24 = BitVec.ofNat 64 n)
    (flag : zeroCount s = some (s.gpr .x24 == 0) := rfl) :
    WP isa (.ite (.zero .x .x24) (.block []) (.loop (Impl.Rc2.AArch64.Cbc.body d) (.nonzero .x .x24))) s (LoopPost d s n) := by
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
      refine ⟨by simp, count, fun _ _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _, ?_, ?_⟩
      · rfl
      · rfl
    · simp
  · apply WP.ite false (by simp only [eval_zeroCount, flag', hz, decide_false])
    · simp
    · intro _
      exact loop_ok d n s (by omega_using [hz]) bound hp count

theorem LoopPost.scratchRead {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : LoopPost d s n s') (hp : StepPre s n) (i : Nat) (lo : 264 ≤ i) (hi : i + 8 ≤ 512) :
    s'.mem.readW (s.gpr .x2 + BitVec.ofNat 64 i) 64 = s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 i) 64 := by
  have sub : Region.Sub ⟨s.gpr .x2 + BitVec.ofNat 64 i, 8⟩ (bufR s) := Offset.sub_base _ hi
  have sep : (Region.mk (s.gpr .x2 + BitVec.ofNat 64 i) 8).Disjoint ⟨s.gpr .x2, 264⟩ :=
    Offset.disjoint_base _ lo (by omega_using [hi])
  apply h.mem.readW (r := ⟨s.gpr .x2 + BitVec.ofNat 64 i, 8⟩) (Region.contains_self _ _)
    (hn := by decide)
  simpa only [loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivBuf.sub_right sub).symm) (And.intro ((hp.dataBuf.sub_right sub).symm)
      sep)

end VG.Proof.Rc2.AArch64.Cbc
