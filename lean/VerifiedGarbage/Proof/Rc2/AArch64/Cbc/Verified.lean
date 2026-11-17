module

public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.AArch64.ConstantTime
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Rc2.AArch64.Lit
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc2.AArch64.Vec.Loop
import VerifiedGarbage.Proof.Rc2.CbcList
import VerifiedGarbage.Proof.Rc2.AArch64.MemOps
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rc2.AArch64.KeyLoop
public import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Pre
public import VerifiedGarbage.Impl.Rc2.AArch64.Cbc
public import VerifiedGarbage.Proof.Rc2.AArch64.Lookup

/-! ### `Rc2.AArch64.Cbc.Phase`, which this module and modules that import it used -/

section

/-! ### `Rc2.AArch64.Cbc.Loop`, which this module and modules that import it used -/

section

/-! ### `Rc2.AArch64.Cbc.Slice`, which this module and modules that import it used -/

section

/-! # Restricting CBC permissions to a consecutive subrange -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64

theorem StepPre.slice {s s' : State} {n m i : Nat} (hp : StepPre s n) (bound : i + m ≤ n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (key : s'.gpr .x0 = s.gpr .x0) (iv : s'.gpr .x23 = s.gpr .x23)
    (buf : s'.gpr .x2 = s.gpr .x2)
    (ptr : s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * i)) : StepPre s' m := by
  have sub : Region.Sub (dataR s' m) (dataR s n) := by
    change Region.Sub ⟨s'.gpr .x1, 8 * m⟩ ⟨s.gpr .x1, 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega_using [bound])
  constructor
  · have hc : Covers [keyR s', ivR s', dataR s' m, bufR s'] [keyR s, ivR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp [key], by simp⟩
      · exact ⟨ivR s, by simp, 0, by simp [iv], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptr, by change 8 * i + 8 * m ≤ 8 * n; omega_using [bound]⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [rd, wr]
    exact fun a k h => hp.reads a k (hc a k h)
  · have hc : Covers [ivR s', dataR s' m, bufR s'] [ivR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨ivR s, by simp, 0, by simp [iv], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptr, by change 8 * i + 8 * m ≤ 8 * n; omega_using [bound]⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [wr]
    exact fun a k h => hp.writes a k (hc a k h)
  · simpa only [keyR, ivR, key, iv] using hp.keyIv
  · simpa only [keyR, key] using hp.keyData.sub_right sub
  · simpa only [keyR, bufR, key, buf] using hp.keyBuf
  · simpa only [ivR, iv] using hp.ivData.sub_right sub
  · simpa only [ivR, bufR, iv, buf] using hp.ivBuf
  · simpa only [bufR, buf] using hp.dataBuf.sub_left sub

theorem StepPre.head {s : State} {n : Nat} (hp : StepPre s n) (hn : 1 ≤ n) : StepPre s :=
  hp.slice (i := 0) hn rfl rfl rfl rfl rfl (by simp)

end VG.Proof.Rc2.AArch64.Cbc

end

end

/-! ### `Rc2.AArch64.Cbc.Decrypt`, which this module and modules that import it used -/

section

/-! ### `Rc2.AArch64.Cbc.Steps`, which this module and modules that import it used -/

section

/-! # CBC loads, XORs, stores, and public loop counters -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

theorem copy64_ok (s : State) (src dst : Reg) (a b : Nat) (hne : dst ≠ .x8)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 a) 8)
    (writable : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 b) 8)
    (ha : a % 8 = 0 ∧ a < 32768 := by decide)
    (hb : b % 8 = 0 ∧ b < 32768 := by decide) :
    ∃ s', runBlock isa [.ldr .x .x8 src a, .str .x .x8 dst b] s = some s' ∧
      Keep [.x8, .x9] {s with
        mem := s.mem.writeW (s.gpr dst + BitVec.ofNat 64 b) (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)} s' := by
  have hw : InRegions (s.write .x .x8 (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)).wr
      ((s.write .x .x8 (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)).gpr dst + BitVec.ofNat 64 b) 8 := by
    simpa only [wr_write, gpr_write, hne, ite_false] using writable
  refine ⟨_, by
    rw [runBlock_cons, exec_ldr_x s _ _ a ha readable, runStep_some,
      runBlock_cons, exec_str_x _ _ _ b hb hw, runStep_some, runBlock_nil], ?_⟩
  constructor
  · intro r hr
    have hn : r ≠ .x8 := by intro h; subst r; exact hr (by simp)
    exact gpr_write_of_ne _ _ _ hn
  · simp only [gpr_write, hne, ite_false, ite_true, BitVec.setWidth_eq, mem_write]
  · rfl
  · rfl

theorem xor64_ok (s : State) (dst iv : Reg) (hd : dst ≠ .x8) (hi : iv ≠ .x8)
    (readDst : InRegions (s.rd ++ s.wr) (s.gpr dst) 8)
    (readIv : InRegions (s.rd ++ s.wr) (s.gpr iv) 8)
    (writable : InRegions s.wr (s.gpr dst) 8)
    (hd9 : dst ≠ .x9 := by decide) :
    ∃ s', runBlock isa [.ldr .x .x8 dst 0, .ldr .x .x9 iv 0,
      .logic .eor .x .x8 .x8 .x9, .str .x .x8 dst 0] s = some s' ∧
      Keep [.x8, .x9] {s with
        mem := s.mem.writeW (s.gpr dst) (s.mem.readW (s.gpr dst) 64 ^^^ s.mem.readW (s.gpr iv) 64)} s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      Nat.zero_mod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true, Option.bind_some, State.load,
      State.store, State.read, BitVec.setWidth_eq, BitVec.add_zero,
      readDst, readIv, writable, Option.map_some, gpr_write, mem_write, rd_write, wr_write,
      hd, hi, hd9, reduceCtorEq, ite_false]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2, ite_false]
  · rfl
  · rfl
  · rfl

def zeroCount (s : State) : Option Bool := some (s.gpr .x24 == 0)

theorem eval_zeroCount (s : State) : eval (.zero .x .x24) s = zeroCount s := rfl

theorem eval_nonzeroCount (s : State) : eval (.nonzero .x .x24) s = (zeroCount s).map (! ·) := rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.AArch64.Cbc.advance s = some s' ∧
      s'.gpr .x1 = s.gpr .x1 + 8 ∧ s'.gpr .x24 = s.gpr .x24 - 1 ∧
      zeroCount s' = some ((s.gpr .x24 - 1) == 0) ∧ Keep [.x1, .x24] s s' := by
  refine ⟨_, by
    simp only [Impl.Rc2.AArch64.Cbc.advance, runBlock_cons, runStep_some, runBlock_nil,
      exec, State.read, BitVec.setWidth_eq, Nat.reduceLT, ite_true,
      gpr_write, reduceCtorEq, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    rfl
  · exact gpr_write_self _ _ _ _
  · rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, hr.1, hr.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

end VG.Proof.Rc2.AArch64.Cbc

end

end

/-! ### `Rc2.AArch64.Cbc.Frame`, which this module and modules that import it used -/

section

/-! # The frame preserved by a CBC step -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64

def stepWrites (s : State) : List Region := [ivR s, dataR s, ⟨s.gpr .x2, 264⟩]

structure Pinned (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (stepWrites s) s.mem s'.mem

theorem Pinned.of_keep {s s' : State} {m : Mem} (h : Keep [.x8, .x9] {s with mem := m} s')
    (frame : Frame (stepWrites s) s.mem m) : Pinned s s' := by
  have k : ∀ r ∈ kept, r ∉ [.x8, .x9] := by decide
  have c : ∀ r ∈ savedAcrossCall, r ∉ [.x8, .x9] := by decide
  exact ⟨fun r hr => h.reg r (k r hr), fun r hr => h.reg r (c r hr), h.rd, h.wr, by rw [h.mem]; exact frame⟩

theorem Pinned.of_call {d : Spec.Rc2.Direction} {s s' : State} (h : CallPost d s s') : Pinned s s' := by
  refine ⟨h.reg, h.callee, h.rd, h.wr, h.mem.sub ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨dataR s, by simp [stepWrites], fun _ h => h⟩
  · exact ⟨⟨s.gpr .x2, 264⟩, by simp [stepWrites], Region.sub_prefix (by decide)⟩

theorem Pinned.writes_eq {s s' : State} (h : Pinned s s') : stepWrites s' = stepWrites s := by
  simp only [stepWrites, ivR, dataR, h.reg .x23 (by decide), h.reg .x1 (by decide), h.reg .x2 (by decide)]

theorem Pinned.trans {s s' s'' : State} (h : Pinned s s') (h' : Pinned s' s'') : Pinned s s'' := by
  refine ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), fun r hr => (h'.callee r hr).trans (h.callee r hr),
    h'.rd.trans h.rd, h'.wr.trans h.wr, ?_⟩
  have f := h'.mem
  rw [h.writes_eq] at f
  exact h.mem.trans f

theorem Pinned.pre {s s' : State} {n : Nat} (h : Pinned s s') (hp : StepPre s n) : StepPre s' n :=
  hp.transport h.rd h.wr h.reg

theorem Pinned.schedule {s s' : State} (h : Pinned s s') (hp : StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (s.gpr .x0) = Spec.Rc2.scheduleAt s.mem (s.gpr .x0) := by
  apply scheduleAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))))

theorem CallPost.iv {d : Spec.Rc2.Direction} {s s' : State} (h : CallPost d s s') (hp : StepPre s) :
    Spec.Rc2.blockAt s'.mem (s.gpr .x23) = Spec.Rc2.blockAt s.mem (s.gpr .x23) := by
  apply blockAt_frame h.mem
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.ivData
      (hp.ivBuf.sub_right (Region.sub_prefix (by decide : 256 ≤ 512)))

structure StepPost (d : Spec.Rc2.Direction) (s s' : State) : Prop extends Pinned s s' where
  data : Spec.Rc2.blockAt s'.mem (s.gpr .x1) =
    (Proof.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blockAt s.mem (s.gpr .x1))).1
  iv : Spec.Rc2.blockAt s'.mem (s.gpr .x23) =
    (Proof.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blockAt s.mem (s.gpr .x1))).2

end VG.Proof.Rc2.AArch64.Cbc

end

end

/-! # One CBC decryption step, retaining the original ciphertext -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64

abbrev stashR (s : State) : Region := ⟨s.gpr .x2 + BitVec.ofNat 64 256, 8⟩

theorem stash_sub (s : State) : Region.Sub (stashR s) (bufR s) :=
  Offset.sub_base _ (by decide)

theorem call_stash {d : Spec.Rc2.Direction} {s s' : State} (hp : StepPre s) (h : CallPost d s s') :
    Spec.Rc2.blockAt s'.mem (stashR s).base = Spec.Rc2.blockAt s.mem (stashR s).base := by
  apply blockAt_frame h.mem
  have sep : (stashR s).Disjoint ⟨s.gpr .x2, 256⟩ := by
    have h := Offset.disjoint (s.gpr .x2) (d := 256) (n := 8) (e := 0) (k := 256)
      (by omega_using []) (by decide) (by decide)
    simpa using h
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right (stash_sub s)).symm) sep

theorem decryptStep_ok (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.AArch64.Cbc.step .decrypt) s (StepPost .decrypt s) := by
  rw [Impl.Rc2.AArch64.Cbc.step]
  apply WP.seq
  obtain ⟨s₁, run₁, keep₁⟩ := copy64_ok s .x1 .x2 0 256 (by decide)
    (by simpa using hp.readData) (hp.writeBuf 256 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  simp only [BitVec.add_zero] at keep₁
  have frame₁ : Frame [stashR s] s.mem s₁.mem := by
    rw [keep₁.mem]; exact frame_store64 _ _ _
  have pin₁ : Pinned s s₁ := by
    apply Pinned.of_keep keep₁
    apply (frame_store64 _ _ _).sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨s.gpr .x2, 264⟩, by simp [stepWrites], Offset.sub_base _ (by decide)⟩
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ := blockAt_frame frame₁ (s.gpr .x1) (by simpa using hp.dataBuf.sub_right (stash_sub s))
  have iv₁ := blockAt_frame frame₁ (s.gpr .x23) (by simpa using hp.ivBuf.sub_right (stash_sub s))
  have stash₁ : Spec.Rc2.blockAt s₁.mem (stashR s).base = Spec.Rc2.blockAt s.mem (s.gpr .x1) := by
    rw [keep₁.mem]; exact blockAt_copy _ _ _
  apply WP.seq
  apply WP.mono (call_ok .decrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .x1 (by decide), pin₁.reg .x0 (by decide), key₁, data₁] at output₂
  have iv₂ := h₂.iv hp₁
  rw [pin₁.reg .x23 (by decide), iv₁] at iv₂
  have stash₂ := call_stash hp₁ h₂
  simp only [pin₁.reg .x2 (by decide)] at stash₂
  have stash₂' := stash₂.trans stash₁
  change WP isa (.block (([.ldr .x .x8 .x1 0, .ldr .x .x9 .x23 0,
    .logic .eor .x .x8 .x8 .x9, .str .x .x8 .x1 0] : List Instr) ++
    ([.ldr .x .x8 .x2 256, .str .x .x8 .x23 0] : List Instr))) s₂ _
  rw [WP.block_append_iff]
  obtain ⟨s₃, run₃, keep₃⟩ := xor64_ok s₂ .x1 .x23 (by decide) (by decide)
    hp₂.readData hp₂.readIv hp₂.writeData
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have frame₃ : Frame [dataR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  have pin₀₃ := pin₂.trans pin₃
  have hp₃ := pin₀₃.pre hp
  have data₃ : Spec.Rc2.blockAt s₃.mem (s.gpr .x1) =
      Proof.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt s.mem (s.gpr .x0))
        (Spec.Rc2.blockAt s.mem (s.gpr .x1))) (Spec.Rc2.blockAt s.mem (s.gpr .x23)) := by
    have h : Spec.Rc2.blockAt s₃.mem (s₂.gpr .x1) =
        Proof.Rc2.xorBlock (Spec.Rc2.blockAt s₂.mem (s₂.gpr .x1)) (Spec.Rc2.blockAt s₂.mem (s₂.gpr .x23)) := by
      rw [keep₃.mem]; exact blockAt_xor _ _ _
    rw [pin₂.reg .x1 (by decide), pin₂.reg .x23 (by decide), output₂, iv₂] at h
    exact h
  have stash₃ := blockAt_frame frame₃ (stashR s₂).base
    (by simpa using (hp₂.dataBuf.sub_right (stash_sub s₂)).symm)
  simp only [pin₂.reg .x2 (by decide)] at stash₃
  have stash₃' := stash₃.trans stash₂'
  obtain ⟨s₄, run₄, keep₄⟩ := copy64_ok s₃ .x2 .x23 256 0 (by decide)
    (hp₃.readBuf 256 (by decide)) (by simpa using hp₃.writeIv)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  simp only [BitVec.add_zero] at keep₄
  have frame₄ : Frame [ivR s₃] s₃.mem s₄.mem := by
    rw [keep₄.mem]; exact frame_store64 _ _ _
  have pin₄ := Pinned.of_keep keep₄ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  refine ⟨pin₀₃.trans pin₄, ?_, ?_⟩
  · have same := blockAt_frame frame₄ (s₃.gpr .x1) (by simpa using hp₃.ivData.symm)
    rw [pin₀₃.reg .x1 (by decide)] at same
    exact same.trans data₃
  · have out : Spec.Rc2.blockAt s₄.mem (s₃.gpr .x23) = Spec.Rc2.blockAt s₃.mem (stashR s₃).base := by
      rw [keep₄.mem]; exact blockAt_copy _ _ _
    simp only [pin₀₃.reg .x23 (by decide), pin₀₃.reg .x2 (by decide)] at out
    exact out.trans stash₃'

end VG.Proof.Rc2.AArch64.Cbc

end

end

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

end

end

/-!
# Decryption's groups of eight blocks

`phase_ok`: the vector phase decrypts the first `8 ⌊n / 8⌋` of the `n`
blocks, leaves the chaining value updated and `x24` the blocks left.
`phaseLoop_ok`: it and the loop over the blocks left, as the loop alone.
-/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64 VG.Proof.Rc2 VG.Proof.Rc2.AArch64.Vec

theorem contains_prefix {a : Addr} {n k : Nat} (h : n ≤ k) : (⟨a, k⟩ : Region).Contains a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith

/-- A region disjoint from a 128-byte one is shorter than the address space. -/
theorem Region.len_lt_of_disjoint {r r' : Region} (h : r.Disjoint r') (hr : 0 < r.len) :
    r'.len < 2 ^ 64 := by
  apply Nat.lt_of_not_le
  intro hl
  apply h r.base (contains_prefix hr)
  simp only [Region.Contains]
  have := (r.base - r'.base).isLt
  omega_arith

structure PhasePost (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * (n / 8)))
  count : s'.gpr .x24 = BitVec.ofNat 64 (n % 8)
  reg : ∀ r ∈ kept, r ≠ .x1 → r ≠ .x24 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, r ≠ .x24 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [ivR s, dataR s (8 * (n / 8))] s.mem s'.mem
  data : Spec.Rc2.blocksAt s'.mem (s.gpr .x1) (8 * (n / 8)) =
    (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).1
  iv : Spec.Rc2.blockAt s'.mem (s.gpr .x23) =
    (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
      (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).2

theorem exec_lsr (s : State) (d n : Reg) {sh : Nat} (h : sh < 64) :
    exec (.lsr .x d n sh) s = some (s.write .x d (s.gpr n >>> sh)) := by
  simp [exec, Size.bits, h, State.read]

theorem ofNat_shift3 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn]
  rw [Nat.mod_eq_of_lt (by omega_arith)]

theorem ofNat_mask3 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n <<< (64 - 3) >>> (64 - 3) = BitVec.ofNat 64 (n % 8) := by
  rw [maskBits _ 3 (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- The groups, when there are any. -/
theorem groups_ok (s s₁ : State) {n : Nat} (hp : StepPre s n) (bound : 8 * n < 2 ^ 64)
    (hg : 0 < n / 8) (e₁ : s₁ = s.write .x .x10 (BitVec.ofNat 64 (n / 8))) :
    WP isa (.seq (.block Vec.setup) (.seq (.loop (.block Vec.group) (.nonzero .x .x10))
      (.block [.str .x .x11 .x23 0]))) s₁ fun s' =>
        s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * (n / 8))) ∧
        (∀ g, g ≠ .x1 → g ≠ .x6 → g ≠ .x7 → g ≠ .x9 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 →
          s'.gpr g = s.gpr g) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        Frame [ivR s, dataR s (8 * (n / 8))] s.mem s'.mem ∧
        Spec.Rc2.blocksAt s'.mem (s.gpr .x1) (8 * (n / 8)) =
          (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
            (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).1 ∧
        Spec.Rc2.blockAt s'.mem (s.gpr .x23) =
          (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
            (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).2 := by
  subst e₁
  let g := n / 8
  obtain z : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => BitVec.add_zero a
  apply WP.seq
  rw [Vec.setup, WP.block_append_iff]
  obtain rk : InRegions ((s.write .x .x10 (BitVec.ofNat 64 g)).rd ++ (s.write .x .x10 (BitVec.ofNat 64 g)).wr)
      ((s.write .x .x10 (BitVec.ofNat 64 g)).gpr .x0) 128 :=
    hp.reads _ _ ⟨keyR s, by simp, Region.contains_self _ _⟩
  refine WP.mono (loads_ok _ rk 8 (by decide)) fun a ⟨arow, av, ae⟩ => ?_
  let s₁ := s.write .x .x10 (BitVec.ofNat 64 g)
  obtain ag : a.gpr = s₁.gpr := by rw [ae]
  obtain am : a.mem = s.mem := by rw [ae]; rfl
  obtain ard : a.rd = s.rd := by rw [ae]; rfl
  obtain awr : a.wr = s.wr := by rw [ae]; rfl
  obtain asp : a.sp = s.sp := by rw [ae]; rfl
  obtain s₁g : ∀ r, r ≠ .x10 → s₁.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ _ h
  let b₁ := a.write .x .x9 (BitVec.ofNat 64 65535)
  let b₂ := b₁.setV Vec.m16 (ofVWords ((b₁.gpr .x9).setWidth 32) ((b₁.gpr .x9).setWidth 32)
    ((b₁.gpr .x9).setWidth 32) ((b₁.gpr .x9).setWidth 32))
  let b₃ := b₂.write .x .x11 (b₂.mem.readW (b₂.gpr .x23 + BitVec.ofNat 64 0) 64)
  obtain x23 : b₂.gpr .x23 = s.gpr .x23 := by
    simp only [b₂, b₁, gpr_setV, gpr_write_of_ne _ _ _ (by decide : ¬Reg.x23 = .x9), ag]
    exact s₁g _ (by decide)
  obtain e₃ : exec (.ldr .x .x11 .x23 0) b₂ = some b₃ := exec_ldr_x b₂ .x11 .x23 0 ⟨by decide, by decide⟩ (by
    rw [x23, z]
    rw [show b₂.rd = s.rd from ard, show b₂.wr = s.wr from awr]
    exact hp.reads _ _ ⟨ivR s, by simp, Region.contains_self _ _⟩)
  refine WP.of_runBlock ⟨b₃, by
    rw [runBlock_cons, exec_imm _ _ _ (by decide), runStep_some, runBlock_cons, exec_dups,
      runStep_some, runBlock_cons, e₃, runStep_some, runBlock_nil], ?_⟩
  obtain b3g : ∀ r, r ≠ .x9 → r ≠ .x11 → b₃.gpr r = s₁.gpr r := fun r h9 h11 => by
    simp only [b₃, b₂, b₁, gpr_write_of_ne _ _ _ h11, gpr_setV, gpr_write_of_ne _ _ _ h9, ag]
  obtain x1 : b₃.gpr .x1 = s.gpr .x1 := (b3g _ (by decide) (by decide)).trans (s₁g _ (by decide))
  obtain hdata : (dataR s n).Contains (s.gpr .x1) (64 * g) := contains_prefix (by omega_arith)
  obtain big : 64 * g < 2 ^ 64 := by omega_arith
  apply WP.seq
  refine WP.mono (loopV_ok s.mem (s.gpr .x0) g b₃ (by omega_arith) big ?_ ?_ ?_ ?_ ?_) fun c hc => ?_
  · intro r hr
    obtain hne := (treg_ne_kb r hr).2
    simp only [b₃, b₂, b₁, v_write, v_setV_of_ne _ _ hne]
    rw [arow r hr]
    rw [show s₁.mem = s.mem from rfl, show s₁.gpr .x0 = s.gpr .x0 from s₁g _ (by decide)]
  · simp only [b₃, b₂, v_write, v_setV_self, b₁, gpr_write_self, BitVec.setWidth_eq]; rfl
  · rw [b3g _ (by decide) (by decide)]; exact gpr_write_self _ _ _ _
  · rw [x1, show b₃.rd = s.rd from ard, show b₃.wr = s.wr from awr]
    exact hp.reads _ _ ⟨dataR s n, by simp, hdata⟩
  · rw [x1, show b₃.wr = s.wr from awr]
    exact hp.writes _ _ ⟨dataR s n, by simp, hdata⟩
  -- The chaining value: the IV, then the last ciphertext block, stored.
  obtain cx23 : c.gpr .x23 = s.gpr .x23 := by
    rw [hc.reg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      b3g _ (by decide) (by decide), s₁g _ (by decide)]
  obtain b11 : wordBlock (b₃.gpr .x11) = Spec.Rc2.blockAt s.mem (s.gpr .x23) := by
    simp only [b₃, gpr_write_self, BitVec.setWidth_eq]
    rw [x23, z, ← blockAt_read64, show b₂.mem = s.mem from am]
  have data := hc.data
  have chain := hc.chain
  rw [b11, x1, show b₃.mem = s.mem from am] at data chain
  obtain ivw : InRegions c.wr (c.gpr .x23 + BitVec.ofNat 64 0) 8 := by
    rw [cx23, z, hc.wr, show b₃.wr = s.wr from awr]
    exact hp.writes _ _ ⟨ivR s, by simp, Region.contains_self _ _⟩
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons, exec_str_x c .x11 .x23 0 ⟨by decide, by decide⟩ ivw, runStep_some, runBlock_nil], ?_⟩
  simp only [cx23, z]
  obtain ivFrame := frame_store64 c.mem (s.gpr .x23) (c.gpr .x11)
  obtain sub : Region.Sub (dataR s (8 * g)) (dataR s n) := Region.sub_prefix (by omega_arith)
  refine ⟨?_, fun r h1 h6 h7 h9 h10 h11 h12 => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc.ptr, x1, show 64 * g = 8 * (8 * g) by omega_arith]
  · rw [hc.reg r h1 h6 h7 h9 h10 h11 h12, b3g r h9 h11, s₁g r h10]
  · rw [hc.rd]; exact ard
  · rw [hc.wr]; exact awr
  · rw [hc.sp]; exact asp
  · have f₁ : Frame [ivR s, dataR s (8 * g)] s.mem c.mem := by
      have := hc.frame
      rw [x1, show b₃.mem = s.mem from am] at this
      exact this.sub fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        exact ⟨dataR s (8 * g), by simp, Region.sub_prefix (by omega_arith)⟩
    exact f₁.writeW (r := ivR s) (by simp) _ (Region.contains_self _ _)
  · rw [blocksAt_frame ivFrame _ _ (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      exact (hp.ivData.sub_right sub).symm)]
    rw [show 8 * g = 8 * g from rfl] at data
    exact data
  · rw [blockAt_store64, chain]

theorem mask24_ok (s : State) :
    ∃ s', runBlock isa (mask .x24 3) s = some s' ∧
      s'.gpr .x24 = s.gpr .x24 <<< (64 - 3) >>> (64 - 3) ∧
      (∀ r, r ≠ .x24 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .x .x24 (s.gpr .x24 <<< (64 - 3))
  let s₂ := s₁.write .x .x24 (s₁.gpr .x24 >>> (64 - 3))
  refine ⟨s₂, by rw [mask, runBlock_cons, exec_lslx _ _ _ (by decide), runStep_some, runBlock_cons,
      exec_lsrx _ _ _ (by decide), runStep_some, runBlock_nil], ?_, fun r h => ?_, rfl, rfl, rfl⟩
  · simp only [s₂, s₁, gpr_write_self, BitVec.setWidth_eq]
  · simp only [s₂, s₁, gpr_write_of_ne _ _ _ h]

theorem phase_ok (s : State) {n : Nat} (hp : StepPre s n) (bound : 8 * n < 2 ^ 64)
    (count : s.gpr .x24 = BitVec.ofNat 64 n) :
    WP isa Vec.phase s (PhasePost s n) := by
  rw [Vec.phase]
  apply WP.seq
  let s₁ := s.write .x .x10 (s.gpr .x24 >>> 3)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, exec_lsr _ _ _ (by decide), runStep_some,
    runBlock_nil], ?_⟩
  obtain x10 : s.gpr .x24 >>> 3 = BitVec.ofNat 64 (n / 8) := by rw [count, ofNat_shift3 (by omega_arith)]
  obtain s₁g : ∀ r, r ≠ .x10 → s₁.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ _ h
  apply WP.seq
  -- What the masking leaves, from a state with the blocks done.
  obtain finish : ∀ s₂ : State, s₂.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * (n / 8))) →
      (∀ g, g ≠ .x1 → g ≠ .x6 → g ≠ .x7 → g ≠ .x9 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 →
        s₂.gpr g = s.gpr g) → s₂.rd = s.rd → s₂.wr = s.wr →
      Frame [ivR s, dataR s (8 * (n / 8))] s.mem s₂.mem →
      Spec.Rc2.blocksAt s₂.mem (s.gpr .x1) (8 * (n / 8)) =
        (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
          (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).1 →
      Spec.Rc2.blockAt s₂.mem (s.gpr .x23) =
        (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) .decrypt
          (Spec.Rc2.blockAt s.mem (s.gpr .x23)) (Spec.Rc2.blocksAt s.mem (s.gpr .x1) (8 * (n / 8)))).2 →
      WP isa (.block (mask .x24 3)) s₂ (PhasePost s n) := by
    intro s₂ ptr reg rd wr fr data iv
    obtain ⟨s₃, run, c₃, g₃, m₃, rd₃, wr₃⟩ := mask24_ok s₂
    refine WP.of_runBlock ⟨s₃, run, ?_⟩
    obtain keep : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 →
        r ≠ .x24 → s₃.gpr r = s.gpr r := fun r a b c d e f i j => (g₃ r j).trans (reg r a b c d e f i)
    refine ⟨by rw [g₃ _ (by decide), ptr], ?_, fun r hr h1 h24 => ?_, fun r hr h24 => ?_,
      rd₃.trans rd, wr₃.trans wr, by rw [m₃]; exact fr, by rw [m₃]; exact data, by rw [m₃]; exact iv⟩
    · rw [c₃, reg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        count, ofNat_mask3 (by omega_arith)]
    · have : ∀ r ∈ kept, r ≠ .x1 → r ≠ .x24 → r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧
          r ≠ .x12 := by decide
      obtain ⟨a, b, c, d, e, f⟩ := this r hr h1 h24
      exact keep r h1 a b c d e f h24
    · have : ∀ r ∈ savedAcrossCall, r ≠ .x24 → r ≠ .x1 ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧
          r ≠ .x11 ∧ r ≠ .x12 := by decide
      obtain ⟨a, b, c, d, e, f, i⟩ := this r hr h24
      exact keep r a b c d e f i h24
  by_cases hg : n / 8 = 0
  · apply WP.ite true (by simp [eval, State.read, s₁, gpr_write_self, x10, hg])
    · intro _
      apply WP.block_nil
      apply finish s₁ (by rw [s₁g _ (by decide), hg]; exact (BitVec.add_zero _).symm) (fun g _ _ _ _ h _ _ => s₁g g h) rfl rfl
        (by rw [hg]; exact Frame.refl _ _)
      · rw [hg]; rfl
      · rw [hg]; rfl
    · intro h; cases h
  · apply WP.ite false (by
      simp [eval, State.read, s₁, gpr_write_self, x10]
      exact ofNat_ne_zero (by omega_arith) (by omega_arith))
    · intro h; cases h
    · intro _
      refine WP.mono (groups_ok s s₁ hp bound (by omega_arith) (by rw [← x10])) fun s₂ h => ?_
      obtain ⟨ptr, reg, rd, wr, _, fr, data, iv⟩ := h
      exact finish s₂ ptr reg rd wr fr data iv

/-- The groups, then the blocks left one at a time: CBC on all `n`. -/
theorem phaseLoop_ok (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 64) (hp : StepPre s n)
    (count : s.gpr .x24 = BitVec.ofNat 64 n) :
    WP isa (.seq Vec.phase (.ite (.zero .x .x24) (.block [])
      (.loop (Impl.Rc2.AArch64.Cbc.body .decrypt) (.nonzero .x .x24)))) s (LoopPost .decrypt s n) := by
  obtain strict : 8 * n < 2 ^ 64 := Region.len_lt_of_disjoint hp.keyData (show 0 < 128 by decide)
  apply WP.seq
  refine WP.mono (phase_ok s hp strict count) fun s' h' => ?_
  let g := n / 8
  obtain key' := h'.reg .x0 (by decide) (by decide) (by decide)
  obtain iv' := h'.reg .x23 (by decide) (by decide) (by decide)
  obtain buf' := h'.reg .x2 (by decide) (by decide) (by decide)
  obtain hp' : StepPre s' (n % 8) :=
    hp.slice (i := 8 * g) (by omega_arith) h'.rd h'.wr key' iv' buf' h'.ptr
  refine WP.mono (maybeLoop_ok .decrypt s' (n % 8) (by omega_arith) hp' h'.count) fun s'' h'' => ?_
  obtain subG : Region.Sub (dataR s (8 * g)) (dataR s n) := Region.sub_prefix (by omega_arith)
  obtain restSub : Region.Sub ⟨s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * g)), 8 * (n % 8)⟩ (dataR s n) :=
    Offset.sub_base _ (by omega_arith)
  obtain keyFrame : Spec.Rc2.scheduleAt s'.mem (s.gpr .x0) = Spec.Rc2.scheduleAt s.mem (s.gpr .x0) :=
    scheduleAt_frame h'.mem _ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.keyIv
      · exact hp.keyData.sub_right subG)
  obtain restKeep : Spec.Rc2.blocksAt s'.mem (s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * g))) (n % 8) =
      Spec.Rc2.blocksAt s.mem (s.gpr .x1 + BitVec.ofNat 64 (8 * (8 * g))) (n % 8) :=
    blocksAt_frame h'.mem _ _ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.ivData.sub_right restSub).symm
      · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith))
  obtain firstKeep : Spec.Rc2.blocksAt s''.mem (s.gpr .x1) (8 * g) =
      Spec.Rc2.blocksAt s'.mem (s.gpr .x1) (8 * g) :=
    blocksAt_frame h''.mem _ _ (by
      intro r hr
      simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only [ivR, iv']; exact (hp.ivData.sub_right subG).symm
      · simp only [dataR, h'.ptr]; exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)
      · simp only [buf']
        exact (hp.dataBuf.sub_left subG).sub_right (Region.sub_prefix (by decide : 264 ≤ 512)))
  obtain split : ∀ (mm : Mem) (q : Addr), Spec.Rc2.blocksAt mm q n =
      Spec.Rc2.blocksAt mm q (8 * g) ++ Spec.Rc2.blocksAt mm (q + BitVec.ofNat 64 (8 * (8 * g))) (n % 8) :=
    fun mm q => by rw [← blocksAt_add]; exact congrArg _ (by omega_arith)
  have data'' := h''.data
  have ivOut := h''.iv
  rw [h'.ptr, key', iv', keyFrame, h'.iv, restKeep] at data'' ivOut
  refine ⟨?_, h''.count, fun r hr h1 h24 => (h''.reg r hr h1 h24).trans (h'.reg r hr h1 h24),
    fun r hr h24 => (h''.callee r hr h24).trans (h'.callee r hr h24), h''.rd.trans h'.rd,
    h''.wr.trans h'.wr, ?_, ?_, ?_⟩
  · rw [h''.ptr, h'.ptr, Offset.add_add]
    exact congrArg _ (congrArg _ (by omega_arith))
  · refine (h'.mem.sub fun r hr => ?_).trans (loopFrame_slice (i := 8 * g) h''.mem (by omega_arith) iv' buf' h'.ptr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨ivR s, by simp [loopWrites], fun _ h => h⟩
    · exact ⟨dataR s n, by simp [loopWrites], subG⟩
  · rw [split, split, firstKeep, h'.data, cbc_append, data'']
  · rw [ivOut, split, cbc_append]

end VG.Proof.Rc2.AArch64.Cbc

end

end

/-! ### `Rc2.AArch64.Cbc.Contract`, which only this module used -/

section

/-! # CBC's function-level contract -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64

def contract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 128⟩
    let iv : Region := ⟨s.gpr .x1, 8⟩
    let data : Region := ⟨s.gpr .x2, 8 * (s.gpr .x3).toNat⟩
    let buf : Region := ⟨s.gpr .x4, 512⟩
    s.rd = [key] ∧ s.wr = [iv, data, buf] ∧ key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧
      (s.gpr .x2).toNat + 8 * (s.gpr .x3).toNat ≤ 2 ^ 64
  post s s' :=
    let out := Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x1)) (Spec.Rc2.blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    Spec.Rc2.blocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat = out.1 ∧
      Spec.Rc2.blockAt s'.mem (s.gpr .x1) = out.2
  pub := PublicRegs [.x0, .x1, .x2, .x3, .x4]

end VG.Proof.Rc2.AArch64.Cbc

end

end

/-! ### `Rc2.AArch64.Cbc.IO`, which only this module used -/

section

/-! # CBC register saves, setup, and restoration -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

/-- The registers the code saves in `buf`, and where. -/
abbrev saved : List (Reg × Nat) := [(.x23, 264), (.x24, 272), (.x30, 280)]

/-- The memory after the saves. -/
abbrev savedMem (s : State) : Mem := Spill.saveMem s.mem (s.gpr .x4) s.gpr saved

theorem save_eq : Impl.Rc2.AArch64.Cbc.save = Spill.saveCode .x4 saved := rfl

theorem restore_eq : Impl.Rc2.AArch64.Cbc.restore = Spill.restoreCode .x2 saved := rfl

theorem savedMem_frame (s : State) : Frame [⟨s.gpr .x4, 512⟩] s.mem (savedMem s) :=
  Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem setup_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.AArch64.Cbc.setup s = some s' ∧
      s'.gpr .x23 = s.gpr .x1 ∧ s'.gpr .x24 = s.gpr .x3 ∧
      s'.gpr .x1 = s.gpr .x2 ∧ s'.gpr .x2 = s.gpr .x4 ∧
      zeroCount s' = some (s.gpr .x3 == 0) ∧ Keep [.x23, .x24, .x1, .x2] s s' := by
  refine ⟨_, by
    simp only [Impl.Rc2.AArch64.Cbc.setup, rr, runBlock_cons, exec]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · unfold zeroCount
    simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, BitVec.setWidth_eq, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

end VG.Proof.Rc2.AArch64.Cbc

end

end


/-! # Verified RC2-CBC encryption and decryption -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64

/-- The save, the setup, the blocks (`mid`, as the loop over them), and the restore. -/
theorem cbc_body_correct (d : Spec.Rc2.Direction) (mid : Prog isa)
    (hmid : ∀ s n, 8 * n ≤ 2 ^ 64 → StepPre s n → s.gpr .x24 = BitVec.ofNat 64 n →
      WP isa mid s (LoopPost d s n))
    (s : State) (hs : (contract d).pre s) :
    WP isa (.seq (.block (Impl.Rc2.AArch64.Cbc.save ++ Impl.Rc2.AArch64.Cbc.setup))
      (.seq mid (.block Impl.Rc2.AArch64.Cbc.restore))) s
      (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    fit⟩ := hs
  have writes (i : Nat) (hi : i + 8 ≤ 512) : InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 i) 8 := by
    rw [hwr]
    exact ⟨⟨s.gpr .x4, 512⟩, by simp, Offset.contains_base _ hi (by omega_using [hi])⟩
  apply WP.seq
  rw [save_eq]
  refine Spill.save_ok (by decide) (fun p hp => writes p.2 (by revert p; decide)) ?_
  obtain ⟨s₂, run₂, iv₂, count₂, data₂, buf₂, -, keep₂⟩ := setup_ok { s with mem := savedMem s }
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have key₂ : s₂.gpr .x0 = s.gpr .x0 := keep₂.reg .x0 (by decide)
  have rd₂ : s₂.rd = s.rd := keep₂.rd
  have wr₂ : s₂.wr = s.wr := keep₂.wr
  have mem₂ : s₂.mem = savedMem s := keep₂.mem
  have scratchFrame : Frame [⟨s.gpr .x4, 512⟩] s.mem s₂.mem := by
    rw [mem₂]; exact savedMem_frame s
  have initialKey := scheduleAt_frame scratchFrame (s.gpr .x0) (by simpa using keyBuf)
  have initialIv := blockAt_frame scratchFrame (s.gpr .x1) (by simpa using ivBuf)
  have initialData := blocksAt_frame scratchFrame (s.gpr .x2) (s.gpr .x3).toNat (by simpa using dataBuf)
  have hp₂ : StepPre s₂ (s.gpr .x3).toNat := by
    constructor
    · simp only [keyR, ivR, dataR, bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      exact fun _ _ h => h
    · simp only [ivR, dataR, bufR, iv₂, data₂, buf₂, wr₂, hwr]
      exact fun _ _ h => h
    · simpa only [keyR, ivR, key₂, iv₂] using keyIv
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [ivR, dataR, iv₂, data₂] using ivData
    · simpa only [ivR, bufR, iv₂, buf₂] using ivBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
  apply WP.seq
  apply WP.mono (hmid s₂ (s.gpr .x3).toNat (by omega_using [fit]) hp₂ (by simpa using count₂))
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .x2 (by decide) (by decide) (by decide)).trans buf₂
  have reads (i : Nat) (hi : i + 8 ≤ 512) :
      InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .x2 + BitVec.ofNat 64 i) 8 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hsv : Spill.Saved (s₃.gpr .x2) s.gpr saved s₃.mem := fun p hp => by
    have hb : 264 ≤ p.2 ∧ p.2 + 8 ≤ 512 := by revert p; decide
    have h := h₃.scratchRead hp₂ p.2 hb.1 hb.2
    rw [buf₂, mem₂] at h
    rw [buf₃, h]
    exact Spill.saveMem_saved (by decide) _ _ _ p hp
  rw [restore_eq]
  refine WP.mono (Spill.restore_wp rfl (by decide) (by decide)
    (fun p hp => reads p.2 (by revert p; decide)) hsv) fun s₄ h₄ => ?_
  constructor
  · intro r hr
    by_cases hs : r ∈ saved.map Prod.fst
    · exact h₄.gpr_of (.inl hs)
    have hb : r ≠ .x23 ∧ r ≠ .x24 ∧ r ≠ .x30 := by
      simpa only [saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] using hs
    have hsa : ∀ r ∈ preserved, r ≠ .x30 → r ∈ savedAcrossCall := by decide
    have sep : ∀ r ∈ preserved, r ≠ .x23 → r ≠ .x24 → r ∉ [.x23, .x24, .x1, .x2] := by decide
    rw [h₄.other r hs, h₃.callee r (hsa r hr hb.2.2) hb.2.1]
    exact keep₂.reg r (sep r hr hb.1 hb.2.1)
  · have out := h₃.data
    have iv := h₃.iv
    rw [key₂, iv₂, data₂, initialKey, initialIv, initialData] at out iv
    constructor
    · rw [h₄.mem]; exact out
    · rw [h₄.mem]; exact iv

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.AArch64.Cbc.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := cbc_body_correct .encrypt _
    (fun s n bound hp count => maybeLoop_ok .encrypt s n bound hp count) s hs
  change Exec isa Impl.Rc2.AArch64.Cbc.encrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.AArch64.Cbc.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := cbc_body_correct .decrypt _
    (fun s n bound hp count => phaseLoop_ok s n bound hp count) s hs
  change Exec isa Impl.Rc2.AArch64.Cbc.decrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

end VG.Proof.Rc2.AArch64.Cbc
