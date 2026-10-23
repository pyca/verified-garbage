module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Ecb.Call
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.TripleDes.EcbMemory
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The ECB loop on PPC64LE: one call of the block function per block -/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Ecb

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction)
open VG.Proof.TripleDes (blocksAt_cons)

abbrev keyR (s : State) : Region := ⟨s.gpr .r3, 384⟩
abbrev dataR (s : State) (n : Nat := 1) : Region := ⟨s.gpr .r4, 8 * n⟩
abbrev bufR (s : State) : Region := ⟨s.gpr .r5, 1024⟩

structure StepPre (s : State) (n : Nat := 1) : Prop where
  reads : Covers [keyR s, dataR s n, bufR s] (s.rd ++ s.wr)
  writes : Covers [dataR s n, bufR s] s.wr
  keyData : (keyR s).Disjoint (dataR s n)
  keyBuf : (keyR s).Disjoint (bufR s)
  dataBuf : (dataR s n).Disjoint (bufR s)
  dataFit : (s.gpr .r4).toNat + 8 * n ≤ 2 ^ 64

theorem StepPre.call {s : State} (hp : StepPre s) : CallPre s := by
  constructor
  · have hc : Covers [⟨s.gpr .r3, 384⟩, ⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩]
        [keyR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp, by simp⟩
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.reads a n (hc a n h)
  · have hc : Covers [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩] [dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.writes a n (hc a n h)
  · exact hp.keyBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.dataBuf.sub_right (Region.sub_prefix (by decide))

theorem StepPre.slice {s s' : State} {n m i : Nat} (hp : StepPre s n) (bound : i + m ≤ n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (key : s'.gpr .r3 = s.gpr .r3) (buf : s'.gpr .r5 = s.gpr .r5)
    (ptr : s'.gpr .r4 = s.gpr .r4 + BitVec.ofNat 64 (8 * i)) : StepPre s' m := by
  have sub : Region.Sub (dataR s' m) (dataR s n) := by
    change Region.Sub ⟨s'.gpr .r4, 8 * m⟩ ⟨s.gpr .r4, 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega)
  constructor
  · have hc : Covers [keyR s', dataR s' m, bufR s'] [keyR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp [key], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [rd, wr]
    exact fun a k h => hp.reads a k (hc a k h)
  · have hc : Covers [dataR s' m, bufR s'] [dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s n, by simp, 8 * i, ptr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [wr]
    exact fun a k h => hp.writes a k (hc a k h)
  · simpa only [keyR, key] using hp.keyData.sub_right sub
  · simpa only [keyR, bufR, key, buf] using hp.keyBuf
  · simpa only [bufR, buf] using hp.dataBuf.sub_left sub
  · rw [ptr]
    have fit : (s.gpr .r4).toNat + 8 * i < 2 ^ 64 ∨ m = 0 := by omega_using [hp.dataFit, bound]
    rcases fit with fit | rfl
    · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega_using [fit] : 8 * i < 2 ^ 64), Nat.mod_eq_of_lt fit]
      omega_using [hp.dataFit, bound]
    · have := (s.gpr .r4 + BitVec.ofNat 64 (8 * i)).isLt
      omega

theorem StepPre.head {s : State} {n : Nat} (hp : StepPre s n) (hn : 1 ≤ n) : StepPre s :=
  hp.slice (i := 0) hn rfl rfl rfl rfl (by simp)

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.TripleDes.PPC64LE.Ecb.advance s = some s' ∧
      s'.gpr .r4 = s.gpr .r4 + 8 ∧ s'.gpr .r31 = s.gpr .r31 - 1 ∧ Kept [.r4, .r31] s s' := by
  let s₁ := s.write .r4 (s.gpr .r4 + BitVec.ofNat 64 8)
  let s₂ := s₁.write .r31 (s₁.gpr .r31 - BitVec.ofNat 64 1)
  refine ⟨s₂, ?_, ?_, ?_, ?_⟩
  · rw [Impl.TripleDes.PPC64LE.Ecb.advance, runBlock_cons, exec_addi (by decide) (by decide),
      runStep_some, runBlock_cons, exec_subi (by decide) (by decide), runStep_some, runBlock_nil]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]; rfl
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [s₂, s₁, gpr_write, hr.1, hr.2, ite_false]

theorem counter_nonzero (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n) != (0 : BitVec 64)) = decide (n ≠ 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · intro h hz; subst hz; exact h rfl
  · intro h he
    have ht := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at ht
    exact h ht

structure BodyPost (d : Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .r4 = s.gpr .r4 + 8
  count : s'.gpr .r31 = BitVec.ofNat 64 (n - 1)
  flag : isa.eval (.nonzero .d .r31) s' = some (decide (n ≠ 1))
  key : s'.gpr .r3 = s.gpr .r3
  buf : s'.gpr .r5 = s.gpr .r5
  callee : ∀ r ∈ preserved, r ≠ .r31 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [dataR s, ⟨s.gpr .r5, 512⟩] s.mem s'.mem
  data : Spec.TripleDes.blockAt s'.mem (s.gpr .r4) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)) d
      (Spec.TripleDes.blockAt s.mem (s.gpr .r4))

theorem body_ok (d : Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 64)
    (count : s.gpr .r31 = BitVec.ofNat 64 n) (hp : StepPre s) :
    WP isa (.seq (Impl.TripleDes.PPC64LE.Ecb.blockCall d) (.block Impl.TripleDes.PPC64LE.Ecb.advance))
      s (BodyPost d s n) := by
  apply WP.seq
  apply WP.mono (call_ok d s hp.call)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, keep₂⟩ := advance_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have count' : s₁.gpr .r31 - 1 = BitVec.ofNat 64 (n - 1) := by
    rw [h₁.callee .r31 (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .r4 (by decide)], count₂.trans count', ?_,
    (keep₂.reg .r3 (by decide)).trans (h₁.reg .r3 (by decide)),
    (keep₂.reg .r5 (by decide)).trans (h₁.reg .r5 (by decide)), ?_,
    keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr, ?_, ?_⟩
  · change VG.PPC64LE.eval (.nonzero .d .r31) s₂ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, count₂, count']
    rw [counter_nonzero (n - 1) (by omega)]
    have he : (n - 1 ≠ 0) ↔ (n ≠ 1) := by omega
    simp only [he]
  · intro r hr h31
    have h4 : r ≠ .r4 := by revert hr; cases r <;> decide
    exact (keep₂.reg r (by simp [h4, h31])).trans (h₁.callee r hr)
  · rw [keep₂.mem]; exact h₁.mem
  · rw [keep₂.mem]; exact h₁.output

theorem BodyPost.tail {d : Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) : StepPre s' n :=
  hp.slice (i := 1) (by omega) h.rd h.wr h.key h.buf h.ptr

def loopWrites (s : State) (n : Nat) : List Region := [dataR s n, ⟨s.gpr .r5, 512⟩]

theorem loopFrame_slice {s s' : State} {n m i : Nat} {a b : Mem}
    (h : Frame (loopWrites s' m) a b) (bound : i + m ≤ n)
    (buf : s'.gpr .r5 = s.gpr .r5)
    (ptr : s'.gpr .r4 = s.gpr .r4 + BitVec.ofNat 64 (8 * i)) :
    Frame (loopWrites s n) a b := by
  apply h.sub
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨dataR s n, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨s'.gpr .r4, 8 * m⟩ ⟨s.gpr .r4, 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega)
  · refine ⟨⟨s.gpr .r5, 512⟩, by simp [loopWrites], ?_⟩
    rw [buf]; exact fun _ h => h

theorem BodyPost.frame {d : Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hn : 1 ≤ n) : Frame (loopWrites s n) s.mem s'.mem :=
  loopFrame_slice (m := 1) (i := 0) h.mem hn rfl (by simp)

theorem BodyPost.schedule {d : Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hp : StepPre s) :
    Spec.TripleDes.scheduleAt s'.mem (s.gpr .r3) = Spec.TripleDes.scheduleAt s.mem (s.gpr .r3) := by
  apply VG.Proof.TripleDes.scheduleAt_eq_of_frame _ h.mem
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyData
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))

theorem BodyPost.tailData {d : Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) :
    Spec.TripleDes.blocksAt s'.mem (s.gpr .r4 + 8) n =
      Spec.TripleDes.blocksAt s.mem (s.gpr .r4 + 8) n := by
  have bound : 8 * (n + 1) ≤ 2 ^ 64 := by omega_using [hp.dataFit]
  have sub : Region.Sub ⟨s.gpr .r4 + 8, 8 * n⟩ (dataR s (n + 1)) :=
    Offset.sub_base _ (by change 8 + 8 * n ≤ 8 * (n + 1); omega)
  have sep : (Region.mk (s.gpr .r4 + 8) (8 * n)).Disjoint (dataR s) :=
    Offset.disjoint_base _ (d := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply VG.Proof.TripleDes.blocksAt_frame h.mem
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro sep
      ((hp.dataBuf.sub_left sub).sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))

theorem firstBlock_frame {d : Direction} {s s' : State} {n : Nat} {m : Mem}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1))
    (frame : Frame (loopWrites s' n) s'.mem m) :
    Spec.TripleDes.blockAt m (s.gpr .r4) = Spec.TripleDes.blockAt s'.mem (s.gpr .r4) := by
  have bound : 8 * (n + 1) ≤ 2 ^ 64 := by omega_using [hp.dataFit]
  have first : Region.Sub (dataR s) (dataR s (n + 1)) :=
    Region.sub_prefix (by change 8 ≤ 8 * (n + 1); omega)
  have sep : (dataR s).Disjoint ⟨s.gpr .r4 + 8, 8 * n⟩ :=
    Offset.base_disjoint _ (e := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply VG.Proof.TripleDes.blockAt_eq_of_frame _ frame
  simpa only [loopWrites, dataR, h.buf, h.ptr,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro sep
      ((hp.dataBuf.sub_left first).sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))

structure LoopPost (d : Direction) (s : State) (n : Nat) (s' : State) : Prop where
  count : s'.gpr .r31 = 0
  key : s'.gpr .r3 = s.gpr .r3
  buf : s'.gpr .r5 = s.gpr .r5
  callee : ∀ r ∈ preserved, r ≠ .r31 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (loopWrites s n) s.mem s'.mem
  data : Spec.TripleDes.blocksAt s'.mem (s.gpr .r4) n =
    Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)) d
      (Spec.TripleDes.blocksAt s.mem (s.gpr .r4) n)

theorem ecb_cons (keys : Spec.TripleDes.Schedule) (d : Direction)
    (b : Spec.TripleDes.Block) (bs : List Spec.TripleDes.Block) :
    Spec.TripleDes.ecb keys d (b :: bs) = blockResult keys d b :: Spec.TripleDes.ecb keys d bs := by
  cases d <;> rfl

theorem loop_ok (d : Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → StepPre s n → s.gpr .r31 = BitVec.ofNat 64 n →
      WP isa (.loop (.seq (Impl.TripleDes.PPC64LE.Ecb.blockCall d)
        (.block Impl.TripleDes.PPC64LE.Ecb.advance)) (.nonzero .d .r31)) s (LoopPost d s n) := by
  induction n with
  | zero => intro s hn; omega
  | succ n ih =>
    intro s hn hp count
    have bound : 8 * (n + 1) ≤ 2 ^ 64 := by omega_using [hp.dataFit]
    obtain ⟨t₁, s₁, exec₁, h₁⟩ := body_ok d s (n + 1) hn (by omega) count (hp.head hn)
    by_cases hz : n = 0
    · subst n
      refine ⟨_, s₁, Exec.loopExit exec₁ ?_, ?_⟩
      · rw [h₁.flag]; rfl
      · refine ⟨h₁.count, h₁.key, h₁.buf, h₁.callee, h₁.rd, h₁.wr, h₁.frame (by decide), ?_⟩
        rw [blocksAt_cons, blocksAt_cons, ecb_cons]
        simp only [Spec.TripleDes.blocksAt, List.range_zero, List.map_nil,
          Spec.TripleDes.ecb, List.map_nil]
        exact congrArg (· :: []) h₁.data
    · have hp₁ := h₁.tail hp
      obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega) hp₁ (by simpa using h₁.count)
      refine ⟨_, s₂, Exec.loopNext exec₁ ?_ exec₂, ?_⟩
      · rw [h₁.flag]
        simp only [ne_eq, Nat.add_eq_right, hz, not_false_eq_true, decide_true]
      · have key := h₁.schedule (hp.head hn)
        have tail := h₁.tailData hp
        have data := h₂.data
        rw [h₁.key, h₁.ptr, key, tail] at data
        refine ⟨h₂.count, h₂.key.trans h₁.key, h₂.buf.trans h₁.buf, ?_,
          h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_, ?_⟩
        · intro r hr h31
          exact (h₂.callee r hr h31).trans (h₁.callee r hr h31)
        · exact (h₁.frame hn).trans
            (loopFrame_slice (i := 1) h₂.mem (by omega) h₁.buf h₁.ptr)
        · have first := firstBlock_frame h₁ hp h₂.mem
          rw [blocksAt_cons, first, h₁.data, data, blocksAt_cons, ecb_cons]

theorem maybeLoop_ok (d : Direction) (s : State) (n : Nat)
    (hp : StepPre s n) (count : s.gpr .r31 = BitVec.ofNat 64 n)
    (initialFlag : isa.eval (.zero .d .r31) s = some (decide (n = 0))) :
    WP isa (.ite (.zero .d .r31) (.block []) (.loop (.seq (Impl.TripleDes.PPC64LE.Ecb.blockCall d)
      (.block Impl.TripleDes.PPC64LE.Ecb.advance)) (.nonzero .d .r31))) s (LoopPost d s n) := by
  by_cases hz : n = 0
  · subst n
    apply WP.ite true (by simpa using initialFlag)
    · intro _
      apply WP.block_nil
      exact ⟨count, rfl, rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl⟩
    · simp
  · apply WP.ite false (by simpa [hz] using initialFlag)
    · simp
    · intro _
      exact loop_ok d n s (by omega) hp count

end VG.Proof.TripleDes.PPC64LE.Ecb
