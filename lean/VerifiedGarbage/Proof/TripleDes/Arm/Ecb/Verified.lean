import VerifiedGarbage.Proof.TripleDes.Arm.VerifiedBlock
import VerifiedGarbage.Impl.TripleDes.Arm.Ecb
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.TripleDes.EcbMemory
import VerifiedGarbage.Proof.Rc2.Arm.KeySteps
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.Proof.TripleDes.Scratch

/-! ## `Call` -/

section

namespace VG.Proof.TripleDes.Arm.Ecb
open VG VG.Arm VG.Impl.TripleDes.Arm

def kept : List Reg := [.r0, .r1, .r2, .r3]
def savedAcrossCall : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

def callContract (d : Spec.TripleDes.Direction) : Contract isa :=
  { blockContract d with
    post := fun s s' => (blockContract d).post s s' ∧ ∀ r ∈ kept, s'.gpr r = s.gpr r }

theorem block_correct' (d : Spec.TripleDes.Direction) (s : State) (hs : (callContract d).pre s) :
    ∃ t s', Exec isa (block d) s t s' ∧ abiPreserved s s' ∧ (callContract d).post s s' := by
  have hp := headPre_of_contract d s hs
  have writes : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    intro t ht
    have fit := hs.2.2.2.2.2.1
    rw [addr_add (by omega_using [fit, ht]), hs.2.1]
    exact ⟨⟨State.addr (s.gpr .r1), 8⟩, by simp,
      Offset.contains_base _ (by omega_using [ht]) (by omega_using [ht])⟩
  obtain ⟨t, s', he, post⟩ := block_ok (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0)))
    (s.gpr .r0) d s hp writes
  refine ⟨t, s', he, ⟨?_, post.sp⟩, post.result, ?_⟩
  · intro r hr
    have covered : ∀ r ∈ preserved, r ∈ savedRegs := by decide
    exact post.saved r (covered r hr)
  · intro r hr
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact post.pointer
    · exact post.regs .r1 (by decide)
    · exact post.regs .r2 (by decide)
    · exact post.regs .r3 (by decide)

theorem blockCall_eq (d : Spec.TripleDes.Direction) : Impl.TripleDes.Arm.Ecb.blockCall d =
    .call (match d with | .encrypt => "vg_triple_des_encrypt_block" | .decrypt => "vg_triple_des_decrypt_block")
      (block d) := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨State.addr (s.gpr .r0), 384⟩, ⟨State.addr (s.gpr .r1), 8⟩,
    ⟨State.addr (s.gpr .r2), 512⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩] s.wr
  keyScratch : (Region.mk (State.addr (s.gpr .r0)) 384).Disjoint ⟨State.addr (s.gpr .r2), 512⟩
  dataScratch : (Region.mk (State.addr (s.gpr .r1)) 8).Disjoint ⟨State.addr (s.gpr .r2), 512⟩
  keyFit : (s.gpr .r0).toNat + 384 ≤ 2 ^ 32
  dataFit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32
  scratchFit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32

structure CallPost (d : Spec.TripleDes.Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩] s.mem s'.mem
  output : Spec.TripleDes.blockAt s'.mem (State.addr (s.gpr .r1)) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1)))

theorem call_ok (d : Spec.TripleDes.Direction) (s : State) (hp : CallPre s) :
    WP isa (Impl.TripleDes.Arm.Ecb.blockCall d) s (CallPost d s) := by
  rw [blockCall_eq]
  refine WP.call (k := callContract d) (block_correct' d)
    (rd := [⟨State.addr (s.gpr .r0), 384⟩])
    (wr := [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩])
    ?_ hp.reads hp.writes ?_ (by cases d <;> rfl)
  · simp only [callContract, blockContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs)]
    exact ⟨trivial, trivial, hp.keyScratch, hp.dataScratch, hp.keyFit, hp.dataFit, hp.scratchFit⟩
  · intro s' rd wr sp frame callee regs out
    have sep : ∀ r ∈ kept, r ∉ linkRegs := by decide
    have saved : ∀ r ∈ savedAcrossCall, r ∈ preserved ∧ r ≠ .lr := by decide
    refine ⟨?_, fun r hr => callee r (saved r hr).1 (saved r hr).2, rd, wr, frame, ?_⟩
    · intro r hr
      have h := out.2 r hr
      simp only [State.withRegions_gpr, State.callEntry_gpr _ (sep r hr)] at h
      exact h
    · have h := out.1
      change Spec.TripleDes.blockAt s'.mem _ = blockResult _ d _ at h
      simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
        State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs)] at h
      exact h

end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `Pre` -/

section

/-! # Permissions and separation for one ECB step -/

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm

abbrev keyR (s : State) : Region := ⟨State.addr (s.gpr .r0), 384⟩
abbrev dataR (s : State) (n : Nat := 1) : Region := ⟨State.addr (s.gpr .r1), 8 * n⟩
abbrev bufR (s : State) : Region := ⟨State.addr (s.gpr .r2), 1024⟩

structure StepPre (s : State) (n : Nat := 1) : Prop where
  reads : Covers [keyR s, dataR s n, bufR s] (s.rd ++ s.wr)
  writes : Covers [dataR s n, bufR s] s.wr
  keyData : (keyR s).Disjoint (dataR s n)
  keyBuf : (keyR s).Disjoint (bufR s)
  dataBuf : (dataR s n).Disjoint (bufR s)
  keyFit : (s.gpr .r0).toNat + 384 ≤ 2 ^ 32
  dataFit : (s.gpr .r1).toNat + 8 * n ≤ 2 ^ 32
  bufFit : (s.gpr .r2).toNat + 1024 ≤ 2 ^ 32

theorem StepPre.transport {s s' : State} {n : Nat} (hp : StepPre s n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (regs : ∀ r ∈ kept, s'.gpr r = s.gpr r) : StepPre s' n := by
  have a := regs .r0 (by decide)
  have c := regs .r1 (by decide)
  have d := regs .r2 (by decide)
  constructor
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.reads
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.writes
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.keyData
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.keyBuf
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.dataBuf
  · simpa only [a] using hp.keyFit
  · simpa only [c] using hp.dataFit
  · simpa only [d] using hp.bufFit

theorem StepPre.call {s : State} (hp : StepPre s) : CallPre s := by
  constructor
  · have hc : Covers [⟨State.addr (s.gpr .r0), 384⟩, ⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩]
        [keyR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp, by simp⟩
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.reads a n (hc a n h)
  · have hc : Covers [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩] [dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.writes a n (hc a n h)
  · exact hp.keyBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.dataBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.keyFit
  · exact hp.dataFit
  · omega_using [hp.bufFit]


end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `Slice` -/

section

/-! # Restricting ECB permissions to a consecutive subrange -/

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm

theorem StepPre.slice {s s' : State} {n m i : Nat} (hp : StepPre s n) (bound : i + m ≤ n) (hm : 1 ≤ m)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (key : s'.gpr .r0 = s.gpr .r0)
    (buf : s'.gpr .r2 = s.gpr .r2)
    (ptr : s'.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (8 * i)) : StepPre s' m := by
  have fit : (s.gpr .r1).toNat + 8 * i < 2 ^ 32 := by omega_using [hp.dataFit, bound, hm]
  have ptrAddr : State.addr (s'.gpr .r1) = State.addr (s.gpr .r1) + BitVec.ofNat 64 (8 * i) := by
    rw [ptr, addr_add fit]
  have sub : Region.Sub (dataR s' m) (dataR s n) := by
    change Region.Sub ⟨State.addr (s'.gpr .r1), 8 * m⟩ ⟨State.addr (s.gpr .r1), 8 * n⟩
    rw [ptrAddr]
    exact Offset.sub_base _ (by omega)
  constructor
  · have hc : Covers [keyR s', dataR s' m, bufR s'] [keyR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp [key], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [rd, wr]
    exact fun a k h => hp.reads a k (hc a k h)
  · have hc : Covers [dataR s' m, bufR s'] [dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [wr]
    exact fun a k h => hp.writes a k (hc a k h)
  · simpa only [keyR, key] using hp.keyData.sub_right sub
  · simpa only [keyR, bufR, key, buf] using hp.keyBuf
  · simpa only [bufR, buf] using hp.dataBuf.sub_left sub
  · rw [key]; exact hp.keyFit
  · rw [ptr]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [fit] : 8 * i < 2 ^ 32), Nat.mod_eq_of_lt fit]
    omega_using [hp.dataFit, bound]
  · rw [buf]; exact hp.bufFit

theorem StepPre.head {s : State} {n : Nat} (hp : StepPre s n) (hn : 1 ≤ n) : StepPre s :=
  hp.slice (i := 0) hn (by decide) rfl rfl rfl rfl (by simp)

end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `Steps` -/

section

namespace VG.Proof.TripleDes.Arm.Ecb
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (Keep gpr_subFlags mem_subFlags rd_subFlags wr_subFlags)

def zeroCount (s : State) : Option Bool := some s.z

theorem eval_zeroCount (s : State) : eval .eq s = zeroCount s := rfl
theorem eval_nonzeroCount (s : State) : eval .ne s = (zeroCount s).map (! ·) := rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.TripleDes.Arm.Ecb.advance s = some s' ∧
      s'.gpr .r1 = s.gpr .r1 + 8 ∧ s'.gpr .r3 = s.gpr .r3 - 1 ∧
      zeroCount s' = some ((s.gpr .r3 - 1) == 0) ∧ Keep [.r1, .r3] s s' := by
  refine ⟨_, by
    simp only [Impl.TripleDes.Arm.Ecb.advance,
      runBlock_cons, exec, Op2.eval, 
      ]
    rfl, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · rfl
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_subFlags, gpr_setReg, hr.1, hr.2, ite_false]
    · simp only [mem_subFlags, mem_setReg]
    · simp only [rd_subFlags, rd_setReg]
    · simp only [wr_subFlags, wr_setReg]

theorem counter_zero (n : Nat) (hn : n < 2 ^ 32) :
    ((BitVec.ofNat 32 n) == (0 : BitVec 32)) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at ht
    exact ht
  · intro h; rw [h]; rfl

end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `Body` -/

section

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm VG.Spec.TripleDes

structure BodyPost (d : Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .r1 = s.gpr .r1 + 8
  count : s'.gpr .r3 = BitVec.ofNat 32 (n - 1)
  flag : zeroCount s' = some (decide (n = 1))
  reg : ∀ r ∈ kept, r ≠ .r1 → r ≠ .r3 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, r ≠ .r3 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame ([dataR s, ⟨State.addr (s.gpr .r2), 512⟩]) s.mem s'.mem
  data : Spec.TripleDes.blockAt s'.mem (State.addr (s.gpr .r1)) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1)))

theorem body_ok (d : Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 32)
    (count : s.gpr .r3 = BitVec.ofNat 32 n) (hp : StepPre s) :
    WP isa (.seq (Impl.TripleDes.Arm.Ecb.blockCall d) (.block Impl.TripleDes.Arm.Ecb.advance)) s (BodyPost d s n) := by
  apply WP.seq
  apply WP.mono (call_ok d s hp.call)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, flag₂, keep₂⟩ := advance_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have count' : s₁.gpr .r3 - 1 = BitVec.ofNat 32 (n - 1) := by
    rw [h₁.reg .r3 (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .r1 (by decide)], count₂.trans count', ?_, ?_, ?_,
    keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr, ?_, ?_⟩
  · rw [flag₂, count']
    rw [counter_zero (n - 1) (by omega)]
    have he : n - 1 = 0 ↔ n = 1 := by omega
    simp only [he]
  · intro r hr hs hb
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.reg r hr)
  · intro r hr hb
    have hs : r ≠ .r1 := by
      have fact : ∀ r ∈ savedAcrossCall, r ≠ .r1 := by decide
      exact fact r hr
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.callee r hr)
  · rw [keep₂.mem]; exact h₁.mem
  · rw [keep₂.mem]; exact h₁.output

theorem BodyPost.tail {d : Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (hn : 1 ≤ n) : StepPre s' n :=
  hp.slice (i := 1) (by omega) hn h.rd h.wr
    (h.reg .r0 (by decide) (by decide) (by decide))
    (h.reg .r2 (by decide) (by decide) (by decide))
    h.ptr

end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `LoopFrame` -/

section

/-! # Frames for successive ECB blocks -/

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm

def stepWrites (s : State) : List Region := [dataR s, ⟨State.addr (s.gpr .r2), 512⟩]

def loopWrites (s : State) (n : Nat) : List Region := [dataR s n, ⟨State.addr (s.gpr .r2), 512⟩]

theorem loopFrame_slice {s s' : State} {n m i : Nat} {a b : Mem}
    (h : Frame (loopWrites s' m) a b) (bound : i + m ≤ n) (fit : (s.gpr .r1).toNat + 8 * i < 2 ^ 32)
    (buf : s'.gpr .r2 = s.gpr .r2)
    (ptr : s'.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (8 * i)) :
    Frame (loopWrites s n) a b := by
  apply h.sub
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨dataR s n, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨State.addr (s'.gpr .r1), 8 * m⟩ ⟨State.addr (s.gpr .r1), 8 * n⟩
    rw [ptr, addr_add fit]
    exact Offset.sub_base _ (by omega)
  · refine ⟨⟨State.addr (s.gpr .r2), 512⟩, by simp [loopWrites], ?_⟩
    rw [buf]; exact fun _ h => h

theorem BodyPost.frame {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hn : 1 ≤ n) : Frame (loopWrites s n) s.mem s'.mem :=
  loopFrame_slice (m := 1) (i := 0) h.mem hn (s.gpr .r1).isLt rfl (by simp)

theorem BodyPost.schedule {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hp : StepPre s) :
    Spec.TripleDes.scheduleAt s'.mem (State.addr (s.gpr .r0)) = Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0)) := by
  apply VG.Proof.TripleDes.scheduleAt_eq_of_frame _ h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyData
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))

theorem BodyPost.tailData {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64) :
    Spec.TripleDes.blocksAt s'.mem (State.addr (s.gpr .r1) + 8) n = Spec.TripleDes.blocksAt s.mem (State.addr (s.gpr .r1) + 8) n := by
  have sub : Region.Sub ⟨State.addr (s.gpr .r1) + 8, 8 * n⟩ (dataR s (n + 1)) :=
    Offset.sub_base _ (by change 8 + 8 * n ≤ 8 * (n + 1); omega)
  have sep : (Region.mk (State.addr (s.gpr .r1) + 8) (8 * n)).Disjoint (dataR s) :=
    Offset.disjoint_base _ (d := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply VG.Proof.TripleDes.blocksAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro sep
      ((hp.dataBuf.sub_left sub).sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))

theorem firstBlock_frame {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat} {m : Mem}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64)
    (frame : Frame (loopWrites s' n) s'.mem m) (hn : 1 ≤ n) :
    Spec.TripleDes.blockAt m (State.addr (s.gpr .r1)) = Spec.TripleDes.blockAt s'.mem (State.addr (s.gpr .r1)) := by
  have first : Region.Sub (dataR s) (dataR s (n + 1)) := Region.sub_prefix (by change 8 ≤ 8 * (n + 1); omega)
  have sep : (dataR s).Disjoint ⟨State.addr (s.gpr .r1) + 8, 8 * n⟩ :=
    Offset.base_disjoint _ (e := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply VG.Proof.TripleDes.blockAt_eq_of_frame _ frame
  have buf := h.reg .r2 (by decide) (by decide) (by decide)
  have ptrAddr : State.addr (s'.gpr .r1) = State.addr (s.gpr .r1) + 8 := by
    rw [h.ptr]
    exact addr_add (k := 8) (by omega_using [hp.dataFit, hn])
  simpa only [loopWrites, dataR, buf, ptrAddr,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro sep
      ((hp.dataBuf.sub_left first).sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))

end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `Loop` -/

section

/-! # Correctness of the ECB loop on complete blocks -/

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm
open VG.Proof.TripleDes (blocksAt_cons)

structure LoopPost (d : Spec.TripleDes.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (8 * n)
  count : s'.gpr .r3 = 0
  reg : ∀ r ∈ kept, r ≠ .r1 → r ≠ .r3 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, r ≠ .r3 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (loopWrites s n) s.mem s'.mem
  data : Spec.TripleDes.blocksAt s'.mem (State.addr (s.gpr .r1)) n =
    Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.TripleDes.blocksAt s.mem (State.addr (s.gpr .r1)) n)

theorem ecb_cons (keys : Spec.TripleDes.Schedule) (d : Spec.TripleDes.Direction)
    (b : Spec.TripleDes.Block) (bs : List Spec.TripleDes.Block) :
    Spec.TripleDes.ecb keys d (b :: bs) = blockResult keys d b :: Spec.TripleDes.ecb keys d bs := by
  cases d <;> rfl

theorem loop_ok (d : Spec.TripleDes.Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → 8 * n ≤ 2 ^ 32 → StepPre s n → s.gpr .r3 = BitVec.ofNat 32 n →
      WP isa (.loop (.seq (Impl.TripleDes.Arm.Ecb.blockCall d) (.block Impl.TripleDes.Arm.Ecb.advance)) .ne) s (LoopPost d s n) := by
  induction n with
  | zero => intro s hn; omega
  | succ n ih =>
    intro s hn bound hp count
    obtain ⟨t₁, s₁, exec₁, h₁⟩ := body_ok d s (n + 1) hn (by omega) count (hp.head hn)
    by_cases hz : n = 0
    · subst n
      refine ⟨_, s₁, Exec.loopExit exec₁ ?_, ?_⟩
      · simp only [eval_nonzeroCount, h₁.flag, decide_true, Option.map_some, Bool.not_true]
      · refine ⟨h₁.ptr, h₁.count, h₁.reg, h₁.callee, h₁.rd, h₁.wr, h₁.frame (by decide), ?_⟩
        · rw [blocksAt_cons, blocksAt_cons, ecb_cons]
          simp only [Spec.TripleDes.blocksAt, List.range_zero, List.map_nil,
            Spec.TripleDes.ecb, List.map_nil]
          exact congrArg (· :: []) h₁.data
    · have hp₁ := h₁.tail hp (by omega)
      obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega) (by omega) hp₁ (by simpa using h₁.count)
      refine ⟨_, s₂, Exec.loopNext exec₁ ?_ exec₂, ?_⟩
      · have he : n + 1 ≠ 1 := by omega
        simp only [eval_nonzeroCount, h₁.flag, he, decide_false, Option.map_some, Bool.not_false]
      · have key := h₁.schedule (hp.head hn)
        have tail := h₁.tailData hp (by omega_using [bound])
        have data := h₂.data
        have ki := h₁.reg .r0 (by decide) (by decide) (by decide)
        have bi := h₁.reg .r2 (by decide) (by decide) (by decide)
        have ptrAddr : State.addr (s₁.gpr .r1) = State.addr (s.gpr .r1) + 8 := by
          rw [h₁.ptr]
          exact addr_add (k := 8) (by omega_using [hp.dataFit, hz])
        rw [ki, ptrAddr, key, tail] at data
        refine ⟨?_, h₂.count, ?_, ?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_, ?_⟩
        · rw [h₂.ptr, h₁.ptr, BitVec.add_assoc]
          exact congrArg (s.gpr .r1 + ·) (by
            change BitVec.ofNat 32 8 + BitVec.ofNat 32 (8 * n) = _
            rw [← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 32) (by omega))
        · intro r hr hs hb
          exact (h₂.reg r hr hs hb).trans (h₁.reg r hr hs hb)
        · intro r hr hb
          exact (h₂.callee r hr hb).trans (h₁.callee r hr hb)
        · exact (h₁.frame hn).trans (loopFrame_slice (i := 1) h₂.mem (by omega) (by omega_using [hp.dataFit, hz]) bi h₁.ptr)
        · have first := firstBlock_frame h₁ hp (by omega_using [bound]) h₂.mem (by omega)
          rw [blocksAt_cons, first, h₁.data, data, blocksAt_cons, ecb_cons]

theorem maybeLoop_ok (d : Spec.TripleDes.Direction) (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 32)
    (hp : StepPre s n) (count : s.gpr .r3 = BitVec.ofNat 32 n)
    (initialFlag : zeroCount s = some (decide (n = 0)))
    :
    WP isa (.ite .eq (.block []) (.loop (.seq (Impl.TripleDes.Arm.Ecb.blockCall d) (.block Impl.TripleDes.Arm.Ecb.advance)) .ne)) s (LoopPost d s n) := by
  have flag' := initialFlag
  by_cases hz : n = 0
  · subst n
    apply WP.ite true (by simp only [eval_zeroCount, flag', decide_true])
    · intro _
      apply WP.block_nil
      refine ⟨by simp, count, fun _ _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _, ?_⟩
      · rfl
    · simp
  · apply WP.ite false (by simp only [eval_zeroCount, flag', hz, decide_false])
    · simp
    · intro _
      exact loop_ok d n s (by omega) bound hp count


end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `IO` -/

section

namespace VG.Proof.TripleDes.Arm.Ecb
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (Keep gpr_subFlags mem_subFlags rd_subFlags wr_subFlags)

def savedMem (s : State) : Mem :=
  s.mem.writeW (State.addr (s.gpr .r3) + BitVec.ofNat 64 512) (s.gpr .lr)

theorem save_ok (s : State) (fit : (s.gpr .r3).toNat + 1024 ≤ 2 ^ 32)
    (hw : InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 512) 4) :
    ∃ s', runBlock isa Impl.TripleDes.Arm.Ecb.save s = some s' ∧ Keep [] {s with mem := savedMem s} s' := by
  refine ⟨_, by
    simp only [Impl.TripleDes.Arm.Ecb.save, runBlock_cons, runStep_some, runBlock_nil,
      exec, show (512 : Nat) < 4096 from by decide, ite_true, State.store32,
      addr_add (a := s.gpr .r3) (k := 512) (by omega_using [fit]), hw]
    rfl, ?_⟩
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem savedMem_frame (s : State) : Frame [⟨State.addr (s.gpr .r3), 1024⟩] s.mem (savedMem s) :=
  (Frame.refl _ _).writeW List.mem_cons_self _
    (Offset.contains_base _ (by decide : 512 + 4 ≤ 1024) (by decide))

theorem savedMem_link (s : State) :
    (savedMem s).readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 512) 32 = s.gpr .lr := by
  rw [savedMem, Mem.readW_writeW_self32]

theorem setup_ok (s : State) :
    ∃ s', runBlock isa Impl.TripleDes.Arm.Ecb.setup s = some s' ∧
      s'.gpr .r3 = s.gpr .r2 ∧ s'.gpr .r2 = s.gpr .r3 ∧
      zeroCount s' = some (s.gpr .r2 == 0) ∧ Keep [.r12, .r3, .r2] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Impl.TripleDes.Arm.Ecb.setup, rr,
      runBlock_cons, runStep_some, exec, Op2.eval, 
      Option.map_some, gpr_setReg]
    rfl, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · change some (s.gpr .r2 - 0 == 0) = _
    exact congrArg (fun v : BitVec 32 => some (v == 0)) (by bv_omega)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_subFlags, gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]
    · simp only [mem_subFlags, mem_setReg]
    · simp only [rd_subFlags, rd_setReg]
    · simp only [wr_subFlags, wr_setReg]

theorem restore_ok (s : State) (lr : BitVec 32)
    (fit : (s.gpr .r2).toNat + 1024 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 512) 4)
    (hv : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 512) 32 = lr) :
    ∃ s', runBlock isa Impl.TripleDes.Arm.Ecb.restore s = some s' ∧
      s'.gpr .lr = lr ∧ Keep [.lr] s s' := by
  refine ⟨_, by
    simp only [Impl.TripleDes.Arm.Ecb.restore, runBlock_cons, runStep_some, runBlock_nil,
      exec, show (512 : Nat) < 4096 from by decide, ite_true, State.load32,
      addr_add (a := s.gpr .r2) (k := 512) (by omega_using [fit]), hr, Option.map_some, hv]
    rfl, gpr_setReg_self _ _ _, ?_⟩
  exact ⟨fun r h => gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using h), rfl, rfl, rfl⟩

theorem LoopPost.scratchRead {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : LoopPost d s n s') (hp : StepPre s n) (i : Nat) (hi : 512 ≤ i ∧ i + 4 ≤ 1024) :
    s'.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 32 =
      s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 32 := by
  have sub : Region.Sub ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 i, 4⟩ (bufR s) :=
    Offset.sub_base _ hi.2
  have sep : (Region.mk (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 4).Disjoint
      ⟨State.addr (s.gpr .r2), 512⟩ := Offset.disjoint_base _ (by omega) (by omega)
  apply h.mem.readW (r := ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 i, 4⟩) (Region.contains_self _ _)
    (hn := by decide)
  simpa only [loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right sub).symm) sep

end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `Contract` -/

section

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm

def contract (d : Spec.TripleDes.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 384⟩
    let data : Region := ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩
    let buf : Region := ⟨State.addr (s.gpr .r3), 1024⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧
      (s.gpr .r1).toNat + 8 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧ (s.gpr .r0).toNat + 384 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 1024 ≤ 2 ^ 32
  post s s' :=
    Spec.TripleDes.blocksAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) d
        (Spec.TripleDes.blocksAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
  pub := PublicRegs [.r0, .r1, .r2, .r3]

end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `Correct` -/

section

namespace VG.Proof.TripleDes.Arm.Ecb
open VG VG.Arm

theorem ecb_correct (d : Spec.TripleDes.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.TripleDes.Arm.Ecb.ecb d) s
      (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit, keyFit, bufFit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 1024) :
      InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨State.addr (s.gpr .r3), 1024⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  rw [Impl.TripleDes.Arm.Ecb.ecb]
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s bufFit (writes 512 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, count₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s.gpr r := keep₁.reg r (by simp)
  rw [g₁] at count₂ buf₂ flag₂
  have key₂ := (keep₂.reg .r0 (by decide)).trans (g₁ .r0)
  have data₂ := (keep₂.reg .r1 (by decide)).trans (g₁ .r1)
  have rd₂ := keep₂.rd.trans keep₁.rd
  have wr₂ := keep₂.wr.trans keep₁.wr
  have mem₂ : s₂.mem = savedMem s := keep₂.mem.trans keep₁.mem
  have scratchFrame : Frame [⟨State.addr (s.gpr .r3), 1024⟩] s.mem s₂.mem := by
    rw [mem₂]; exact savedMem_frame s
  have initialKey := VG.Proof.TripleDes.scheduleAt_eq_of_frame (State.addr (s.gpr .r0)) scratchFrame
    (by simpa using keyBuf)
  have initialData := VG.Proof.TripleDes.blocksAt_frame scratchFrame (State.addr (s.gpr .r1)) (s.gpr .r2).toNat
    (by simpa using dataBuf)
  have hp₂ : StepPre s₂ (s.gpr .r2).toNat := by
    constructor
    · simp only [keyR, dataR, bufR, key₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      exact fun _ _ h => h
    · simp only [dataR, bufR, data₂, buf₂, wr₂, hwr]
      exact fun _ _ h => h
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
    · rw [key₂]; exact keyFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
  have flag : zeroCount s₂ = some (decide ((s.gpr .r2).toNat = 0)) := by
    have hz := counter_zero (s.gpr .r2).toNat (s.gpr .r2).isLt
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hz
    exact flag₂.trans (congrArg some hz)
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (s.gpr .r2).toNat (by omega_using [fit]) hp₂
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using count₂) flag)
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .r2 (by decide) (by decide) (by decide)).trans buf₂
  have readable : InRegions (s₃.rd ++ s₃.wr)
      (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 512) 4 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes 512 (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have link : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 512) 32 = s.gpr .lr := by
    have h := h₃.scratchRead hp₂ 512 (by decide)
    rw [buf₂, mem₂, savedMem_link] at h
    rw [buf₃]; exact h
  obtain ⟨s₄, run₄, link₄, keep₄⟩ := restore_ok s₃ (s.gpr .lr)
    (by rw [buf₃]; exact bufFit) readable link
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · intro r hr
    by_cases hl : r = .lr
    · subst r; exact link₄
    have saved : ∀ r ∈ preserved, r ≠ .lr → r ∈ savedAcrossCall ∧ r ≠ .r3 := by decide
    rw [keep₄.reg r (by simpa only [List.mem_singleton] using hl),
      h₃.callee r (saved r hr hl).1 (saved r hr hl).2]
    have sep : ∀ r ∈ preserved, r ≠ .lr → r ∉ [.r12, .r3, .r2] := by decide
    exact (keep₂.reg r (sep r hr hl)).trans (g₁ r)
  · have out := h₃.data
    rw [key₂, data₂, initialKey, initialData] at out
    change Spec.TripleDes.blocksAt s₄.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat = _
    rw [keep₄.mem]; exact out

end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `Verified` -/

section

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩]

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.Arm.Ecb.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_correct .encrypt s hs
  change Exec isa Impl.TripleDes.Arm.Ecb.encrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.Arm.Ecb.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_correct .decrypt s hs
  change Exec isa Impl.TripleDes.Arm.Ecb.decrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.r0, .r1, .r2, .r3] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
      s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 := by
  simp [PublicRegs]

theorem encrypt_verified : Verified target Impl.TripleDes.Arm.Ecb.encrypt
    (Proof.TripleDes.ecbEncryptScratchContract abi 0) := by
  refine Verified.of_correct encrypt_correct
    (ecbEncrypt_constantTime _) ?_
  sig_implies [Proof.TripleDes.ecbEncryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, contract, publicRegs_four] [satState] using satState

theorem decrypt_verified : Verified target Impl.TripleDes.Arm.Ecb.decrypt
    (Proof.TripleDes.ecbDecryptScratchContract abi 0) := by
  refine Verified.of_correct decrypt_correct
    (ecbDecrypt_constantTime _) ?_
  sig_implies [Proof.TripleDes.ecbDecryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, contract, publicRegs_four] [satState] using satState

end VG.Proof.TripleDes.Arm.Ecb

end
