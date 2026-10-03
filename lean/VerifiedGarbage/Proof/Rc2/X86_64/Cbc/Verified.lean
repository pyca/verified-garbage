import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Rc2.X86_64.KeyLoop
import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Steps
import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.X86_64.ConstantTime

section

/-! # Constant-time CBC callers -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64 VG.Impl.Rc2.X86_64.Cbc

theorem encrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp

theorem decrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp

end VG.Proof.Rc2.X86_64.Cbc

end

section

section

/-! # Permissions and separation for one CBC step -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64

abbrev keyR (s : State) : Region := ⟨s.gpr .rdi, 128⟩
abbrev ivR (s : State) : Region := ⟨s.gpr .rbx, 8⟩
abbrev dataR (s : State) (n : Nat := 1) : Region := ⟨s.gpr .rsi, 8 * n⟩
abbrev bufR (s : State) : Region := ⟨s.gpr .rdx, 512⟩
abbrev stackR (s : State) : Region := below (s.gpr .rsp) 8

structure StepPre (s : State) (n : Nat := 1) : Prop where
  reads : Covers [keyR s, ivR s, dataR s n, bufR s] (s.rd ++ s.wr)
  writes : Covers [ivR s, dataR s n, bufR s] s.wr
  keyIv : (keyR s).Disjoint (ivR s)
  keyData : (keyR s).Disjoint (dataR s n)
  keyBuf : (keyR s).Disjoint (bufR s)
  ivData : (ivR s).Disjoint (dataR s n)
  ivBuf : (ivR s).Disjoint (bufR s)
  dataBuf : (dataR s n).Disjoint (bufR s)
  stackKey : (stackR s).Disjoint (keyR s)
  stackIv : (stackR s).Disjoint (ivR s)
  stackData : (stackR s).Disjoint (dataR s n)
  stackBuf : (stackR s).Disjoint (bufR s)

theorem StepPre.transport {s s' : State} {n : Nat} (hp : StepPre s n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (regs : ∀ r ∈ kept, s'.gpr r = s.gpr r) : StepPre s' n := by
  have a := regs .rdi (by decide)
  have b := regs .rbx (by decide)
  have c := regs .rsi (by decide)
  have d := regs .rdx (by decide)
  have e := regs .rsp (by decide)
  constructor
  · simpa only [keyR, ivR, dataR, bufR, stackR, rd, wr, a, b, c, d, e] using hp.reads
  · simpa only [keyR, ivR, dataR, bufR, stackR, rd, wr, a, b, c, d, e] using hp.writes
  · simpa only [keyR, ivR, dataR, bufR, stackR, rd, wr, a, b, c, d, e] using hp.keyIv
  · simpa only [keyR, ivR, dataR, bufR, stackR, rd, wr, a, b, c, d, e] using hp.keyData
  · simpa only [keyR, ivR, dataR, bufR, stackR, rd, wr, a, b, c, d, e] using hp.keyBuf
  · simpa only [keyR, ivR, dataR, bufR, stackR, rd, wr, a, b, c, d, e] using hp.ivData
  · simpa only [keyR, ivR, dataR, bufR, stackR, rd, wr, a, b, c, d, e] using hp.ivBuf
  · simpa only [keyR, ivR, dataR, bufR, stackR, rd, wr, a, b, c, d, e] using hp.dataBuf
  · simpa only [keyR, ivR, dataR, bufR, stackR, rd, wr, a, b, c, d, e] using hp.stackKey
  · simpa only [keyR, ivR, dataR, bufR, stackR, rd, wr, a, b, c, d, e] using hp.stackIv
  · simpa only [keyR, ivR, dataR, bufR, stackR, rd, wr, a, b, c, d, e] using hp.stackData
  · simpa only [keyR, ivR, dataR, bufR, stackR, rd, wr, a, b, c, d, e] using hp.stackBuf

theorem StepPre.keep {s s' : State} {m : Mem} {n : Nat} (hp : StepPre s n) (h : Keep [.rax] {s with mem := m} s') : StepPre s' n :=
  hp.transport h.rd h.wr fun r hr => h.reg r (by
    have sep : ∀ r ∈ kept, r ∉ [.rax] := by decide
    exact sep r hr)

theorem StepPre.call {s : State} (hp : StepPre s) : CallPre s := by
  constructor
  · have hc : Covers [⟨s.gpr .rdi, 128⟩, ⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 256⟩]
        [keyR s, ivR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp, by simp⟩
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.reads a n (hc a n h)
  · have hc : Covers [⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 256⟩] [ivR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.writes a n (hc a n h)
  · exact hp.keyBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.dataBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.stackKey
  · exact hp.stackData
  · exact hp.stackBuf.sub_right (Region.sub_prefix (by decide))

theorem StepPre.readData {s : State} (hp : StepPre s) : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8 :=
  hp.reads _ _ ⟨dataR s, by simp, Region.contains_self _ _⟩

theorem StepPre.readIv {s : State} (hp : StepPre s) : InRegions (s.rd ++ s.wr) (s.gpr .rbx) 8 :=
  hp.reads _ _ ⟨ivR s, by simp, Region.contains_self _ _⟩

theorem StepPre.writeData {s : State} (hp : StepPre s) : InRegions s.wr (s.gpr .rsi) 8 :=
  hp.writes _ _ ⟨dataR s, by simp, Region.contains_self _ _⟩

theorem StepPre.writeIv {s : State} (hp : StepPre s) : InRegions s.wr (s.gpr .rbx) 8 :=
  hp.writes _ _ ⟨ivR s, by simp, Region.contains_self _ _⟩

theorem StepPre.readBuf {s : State} (hp : StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 i) 8 :=
  hp.reads _ _ ⟨bufR s, by simp, Offset.contains_base _ hi (by omega)⟩

theorem StepPre.writeBuf {s : State} (hp : StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 i) 8 :=
  hp.writes _ _ ⟨bufR s, by simp, Offset.contains_base _ hi (by omega)⟩

end VG.Proof.Rc2.X86_64.Cbc

end

/-! # The frame preserved by a CBC step -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64

def stepWrites (s : State) : List Region := [ivR s, dataR s, ⟨s.gpr .rdx, 264⟩, stackR s]

structure Pinned (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (stepWrites s) s.mem s'.mem

theorem Pinned.of_keep {s s' : State} {m : Mem} (h : Keep [.rax] {s with mem := m} s')
    (frame : Frame (stepWrites s) s.mem m) : Pinned s s' := by
  have k : ∀ r ∈ kept, r ∉ [.rax] := by decide
  have c : ∀ r ∈ calleeSaved, r ∉ [.rax] := by decide
  exact ⟨fun r hr => h.reg r (k r hr), fun r hr => h.reg r (c r hr), h.rd, h.wr, by rw [h.mem]; exact frame⟩

theorem Pinned.of_call {d : Spec.Rc2.Direction} {s s' : State} (h : CallPost d s s') : Pinned s s' := by
  refine ⟨h.reg, h.callee, h.rd, h.wr, h.mem.sub ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨dataR s, by simp [stepWrites], fun _ h => h⟩
  · exact ⟨⟨s.gpr .rdx, 264⟩, by simp [stepWrites], Region.sub_prefix (by decide)⟩
  · exact ⟨stackR s, by simp [stepWrites], fun _ h => h⟩

theorem Pinned.writes_eq {s s' : State} (h : Pinned s s') : stepWrites s' = stepWrites s := by
  simp only [stepWrites, ivR, dataR, stackR, h.reg .rbx (by decide), h.reg .rsi (by decide),
    h.reg .rdx (by decide), h.reg .rsp (by decide)]

theorem Pinned.trans {s s' s'' : State} (h : Pinned s s') (h' : Pinned s' s'') : Pinned s s'' := by
  refine ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), fun r hr => (h'.callee r hr).trans (h.callee r hr),
    h'.rd.trans h.rd, h'.wr.trans h.wr, ?_⟩
  have f := h'.mem
  rw [h.writes_eq] at f
  exact h.mem.trans f

theorem Pinned.pre {s s' : State} {n : Nat} (h : Pinned s s') (hp : StepPre s n) : StepPre s' n :=
  hp.transport h.rd h.wr h.reg

theorem Pinned.schedule {s s' : State} (h : Pinned s s') (hp : StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (s.gpr .rdi) = Spec.Rc2.scheduleAt s.mem (s.gpr .rdi) := by
  apply scheduleAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData (And.intro
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) hp.stackKey.symm))

theorem CallPost.iv {d : Spec.Rc2.Direction} {s s' : State} (h : CallPost d s s') (hp : StepPre s) :
    Spec.Rc2.blockAt s'.mem (s.gpr .rbx) = Spec.Rc2.blockAt s.mem (s.gpr .rbx) := by
  apply blockAt_frame h.mem
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.ivData (And.intro
      (hp.ivBuf.sub_right (Region.sub_prefix (by decide : 256 ≤ 512))) hp.stackIv.symm)

structure StepPost (d : Spec.Rc2.Direction) (s s' : State) : Prop extends Pinned s s' where
  data : Spec.Rc2.blockAt s'.mem (s.gpr .rsi) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .rbx)) (Spec.Rc2.blockAt s.mem (s.gpr .rsi))).1
  iv : Spec.Rc2.blockAt s'.mem (s.gpr .rbx) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .rbx)) (Spec.Rc2.blockAt s.mem (s.gpr .rsi))).2

end VG.Proof.Rc2.X86_64.Cbc

end

section

section

section

/-! # One CBC decryption step, retaining the original ciphertext -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64 VG.Impl.Rc2.X86_64

abbrev stashR (s : State) : Region := ⟨s.gpr .rdx + BitVec.ofNat 64 256, 8⟩

theorem stash_sub (s : State) : Region.Sub (stashR s) (bufR s) :=
  Offset.sub_base _ (by decide)

theorem call_stash {d : Spec.Rc2.Direction} {s s' : State} (hp : StepPre s) (h : CallPost d s s') :
    Spec.Rc2.blockAt s'.mem (stashR s).base = Spec.Rc2.blockAt s.mem (stashR s).base := by
  apply blockAt_frame h.mem
  have sep : (stashR s).Disjoint ⟨s.gpr .rdx, 256⟩ := by
    have h := Offset.disjoint (s.gpr .rdx) (d := 256) (n := 8) (e := 0) (k := 256)
      (by omega) (by decide) (by decide)
    simpa using h
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right (stash_sub s)).symm) (And.intro sep
      ((hp.stackBuf.sub_right (stash_sub s)).symm))

theorem decryptStep_ok (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.X86_64.Cbc.step .decrypt) s (StepPost .decrypt s) := by
  rw [Impl.Rc2.X86_64.Cbc.step]
  apply WP.seq
  obtain ⟨s₁, run₁, keep₁⟩ := copy64_ok s .rsi .rdx 0 256 (by decide)
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
    exact ⟨⟨s.gpr .rdx, 264⟩, by simp [stepWrites], Offset.sub_base _ (by decide)⟩
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ := blockAt_frame frame₁ (s.gpr .rsi) (by simpa using hp.dataBuf.sub_right (stash_sub s))
  have iv₁ := blockAt_frame frame₁ (s.gpr .rbx) (by simpa using hp.ivBuf.sub_right (stash_sub s))
  have stash₁ : Spec.Rc2.blockAt s₁.mem (stashR s).base = Spec.Rc2.blockAt s.mem (s.gpr .rsi) := by
    rw [keep₁.mem]; exact blockAt_copy _ _ _
  apply WP.seq
  apply WP.mono (call_ok .decrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .rsi (by decide), pin₁.reg .rdi (by decide), key₁, data₁] at output₂
  have iv₂ := h₂.iv hp₁
  rw [pin₁.reg .rbx (by decide), iv₁] at iv₂
  have stash₂ := call_stash hp₁ h₂
  simp only [pin₁.reg .rdx (by decide)] at stash₂
  have stash₂' := stash₂.trans stash₁
  change WP isa (.block (([.mov .rax (.mem (memOp .rsi 0)), .alu .xor .rax (.mem (memOp .rbx 0)),
    .store (memOp .rsi 0) .rax] : List Instr) ++
    ([.mov .rax (.mem (memOp .rdx 256)), .store (memOp .rbx 0) .rax] : List Instr))) s₂ _
  rw [WP.block_append_iff]
  obtain ⟨s₃, run₃, keep₃⟩ := xor64_ok s₂ .rsi .rbx (by decide) (by decide)
    hp₂.readData hp₂.readIv hp₂.writeData
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have frame₃ : Frame [dataR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  have pin₀₃ := pin₂.trans pin₃
  have hp₃ := pin₀₃.pre hp
  have data₃ : Spec.Rc2.blockAt s₃.mem (s.gpr .rsi) =
      Spec.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi))
        (Spec.Rc2.blockAt s.mem (s.gpr .rsi))) (Spec.Rc2.blockAt s.mem (s.gpr .rbx)) := by
    have h : Spec.Rc2.blockAt s₃.mem (s₂.gpr .rsi) =
        Spec.Rc2.xorBlock (Spec.Rc2.blockAt s₂.mem (s₂.gpr .rsi)) (Spec.Rc2.blockAt s₂.mem (s₂.gpr .rbx)) := by
      rw [keep₃.mem]; exact blockAt_xor _ _ _
    rw [pin₂.reg .rsi (by decide), pin₂.reg .rbx (by decide), output₂, iv₂] at h
    exact h
  have stash₃ := blockAt_frame frame₃ (stashR s₂).base
    (by simpa using (hp₂.dataBuf.sub_right (stash_sub s₂)).symm)
  simp only [pin₂.reg .rdx (by decide)] at stash₃
  have stash₃' := stash₃.trans stash₂'
  obtain ⟨s₄, run₄, keep₄⟩ := copy64_ok s₃ .rdx .rbx 256 0 (by decide)
    (hp₃.readBuf 256 (by decide)) (by simpa using hp₃.writeIv)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  simp only [BitVec.add_zero] at keep₄
  have frame₄ : Frame [ivR s₃] s₃.mem s₄.mem := by
    rw [keep₄.mem]; exact frame_store64 _ _ _
  have pin₄ := Pinned.of_keep keep₄ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  refine ⟨pin₀₃.trans pin₄, ?_, ?_⟩
  · have same := blockAt_frame frame₄ (s₃.gpr .rsi) (by simpa using hp₃.ivData.symm)
    rw [pin₀₃.reg .rsi (by decide)] at same
    exact same.trans data₃
  · have out : Spec.Rc2.blockAt s₄.mem (s₃.gpr .rbx) = Spec.Rc2.blockAt s₃.mem (stashR s₃).base := by
      rw [keep₄.mem]; exact blockAt_copy _ _ _
    simp only [pin₀₃.reg .rbx (by decide), pin₀₃.reg .rdx (by decide)] at out
    exact out.trans stash₃'

end VG.Proof.Rc2.X86_64.Cbc

end

section

/-! # Restricting CBC permissions to a consecutive subrange -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64

theorem StepPre.slice {s s' : State} {n m i : Nat} (hp : StepPre s n) (bound : i + m ≤ n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (key : s'.gpr .rdi = s.gpr .rdi) (iv : s'.gpr .rbx = s.gpr .rbx)
    (buf : s'.gpr .rdx = s.gpr .rdx) (sp : s'.gpr .rsp = s.gpr .rsp)
    (ptr : s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 (8 * i)) : StepPre s' m := by
  have sub : Region.Sub (dataR s' m) (dataR s n) := by
    change Region.Sub ⟨s'.gpr .rsi, 8 * m⟩ ⟨s.gpr .rsi, 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega)
  constructor
  · have hc : Covers [keyR s', ivR s', dataR s' m, bufR s'] [keyR s, ivR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp [key], by simp⟩
      · exact ⟨ivR s, by simp, 0, by simp [iv], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [rd, wr]
    exact fun a k h => hp.reads a k (hc a k h)
  · have hc : Covers [ivR s', dataR s' m, bufR s'] [ivR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨ivR s, by simp, 0, by simp [iv], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [wr]
    exact fun a k h => hp.writes a k (hc a k h)
  · simpa only [keyR, ivR, key, iv] using hp.keyIv
  · simpa only [keyR, key] using hp.keyData.sub_right sub
  · simpa only [keyR, bufR, key, buf] using hp.keyBuf
  · simpa only [ivR, iv] using hp.ivData.sub_right sub
  · simpa only [ivR, bufR, iv, buf] using hp.ivBuf
  · simpa only [bufR, buf] using hp.dataBuf.sub_left sub
  · simpa only [stackR, keyR, sp, key] using hp.stackKey
  · simpa only [stackR, ivR, sp, iv] using hp.stackIv
  · simpa only [stackR, sp] using hp.stackData.sub_right sub
  · simpa only [stackR, bufR, sp, buf] using hp.stackBuf

theorem StepPre.head {s : State} {n : Nat} (hp : StepPre s n) (hn : 1 ≤ n) : StepPre s :=
  hp.slice (i := 0) hn rfl rfl rfl rfl rfl rfl (by simp)

end VG.Proof.Rc2.X86_64.Cbc

end

section

section

/-! # One CBC encryption step -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem encryptStep_ok (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.X86_64.Cbc.step .encrypt) s (StepPost .encrypt s) := by
  rw [Impl.Rc2.X86_64.Cbc.step]
  apply WP.seq
  obtain ⟨s₁, run₁, keep₁⟩ := xor64_ok s .rsi .rbx (by decide) (by decide)
    hp.readData hp.readIv hp.writeData
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have pin₁ := Pinned.of_keep keep₁ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ : Spec.Rc2.blockAt s₁.mem (s.gpr .rsi) =
      Spec.Rc2.xorBlock (Spec.Rc2.blockAt s.mem (s.gpr .rsi)) (Spec.Rc2.blockAt s.mem (s.gpr .rbx)) := by
    rw [keep₁.mem]; exact blockAt_xor _ _ _
  apply WP.seq
  apply WP.mono (call_ok .encrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .rsi (by decide), pin₁.reg .rdi (by decide), key₁, data₁] at output₂
  obtain ⟨s₃, run₃, keep₃⟩ := copy64_ok s₂ .rsi .rbx 0 0 (by decide)
    (by simpa using hp₂.readData) (by simpa using hp₂.writeIv)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  simp only [BitVec.add_zero] at keep₃
  have frame₃ : Frame [ivR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  refine ⟨pin₂.trans pin₃, ?_, ?_⟩
  · have same := blockAt_frame frame₃ (s₂.gpr .rsi) (by simpa using hp₂.ivData.symm)
    rw [pin₂.reg .rsi (by decide)] at same
    exact same.trans output₂
  · have out : Spec.Rc2.blockAt s₃.mem (s₂.gpr .rbx) = Spec.Rc2.blockAt s₂.mem (s₂.gpr .rsi) := by
      rw [keep₃.mem]; exact blockAt_copy _ _ _
    rw [pin₂.reg .rbx (by decide), pin₂.reg .rsi (by decide)] at out
    exact out.trans output₂

end VG.Proof.Rc2.X86_64.Cbc

end

/-! # A CBC loop iteration and its public counter -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem step_ok (d : Spec.Rc2.Direction) (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.X86_64.Cbc.step d) s (StepPost d s) := by
  cases d
  · exact encryptStep_ok s hp
  · exact decryptStep_ok s hp

structure BodyPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .rsi = s.gpr .rsi + 8
  count : s'.gpr .rbp = BitVec.ofNat 64 (n - 1)
  flag : s'.zf = some (decide (n = 1))
  reg : ∀ r ∈ kept, r ≠ .rsi → r ≠ .rbp → s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, r ≠ .rbp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (stepWrites s) s.mem s'.mem
  data : Spec.Rc2.blockAt s'.mem (s.gpr .rsi) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .rbx)) (Spec.Rc2.blockAt s.mem (s.gpr .rsi))).1
  iv : Spec.Rc2.blockAt s'.mem (s.gpr .rbx) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .rbx)) (Spec.Rc2.blockAt s.mem (s.gpr .rsi))).2

theorem body_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 64)
    (count : s.gpr .rbp = BitVec.ofNat 64 n) (hp : StepPre s) :
    WP isa (Impl.Rc2.X86_64.Cbc.body d) s (BodyPost d s n) := by
  rw [Impl.Rc2.X86_64.Cbc.body]
  apply WP.seq
  apply WP.mono (step_ok d s hp)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, flag₂, keep₂⟩ := advance_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have count' : s₁.gpr .rbp - 1 = BitVec.ofNat 64 (n - 1) := by
    rw [h₁.reg .rbp (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .rsi (by decide)], count₂.trans count', ?_, ?_, ?_,
    keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
  · rw [flag₂, count']
    have eqZero := counter_eq (n - 1) 0 (by omega) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    change some (BitVec.ofNat 64 (n - 1) == 0#64) = _
    rw [eqZero]
    have he : n - 1 = 0 ↔ n = 1 := by omega
    simp only [he]
  · intro r hr hs hb
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.reg r hr)
  · intro r hr hb
    have hs : r ≠ .rsi := by
      have fact : ∀ r ∈ calleeSaved, r ≠ .rsi := by decide
      exact fact r hr
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.callee r hr)
  · rw [keep₂.mem]; exact h₁.mem
  · rw [keep₂.mem]; exact h₁.data
  · rw [keep₂.mem]; exact h₁.iv

theorem BodyPost.tail {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) : StepPre s' n :=
  hp.slice (i := 1) (by omega) h.rd h.wr
    (h.reg .rdi (by decide) (by decide) (by decide))
    (h.reg .rbx (by decide) (by decide) (by decide))
    (h.reg .rdx (by decide) (by decide) (by decide))
    (h.reg .rsp (by decide) (by decide) (by decide)) h.ptr

end VG.Proof.Rc2.X86_64.Cbc

end

/-! # Frames for successive CBC blocks -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64

def loopWrites (s : State) (n : Nat) : List Region := [ivR s, dataR s n, ⟨s.gpr .rdx, 264⟩, stackR s]

theorem loopFrame_slice {s s' : State} {n m i : Nat} {a b : Mem}
    (h : Frame (loopWrites s' m) a b) (bound : i + m ≤ n)
    (iv : s'.gpr .rbx = s.gpr .rbx) (buf : s'.gpr .rdx = s.gpr .rdx)
    (sp : s'.gpr .rsp = s.gpr .rsp) (ptr : s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 (8 * i)) :
    Frame (loopWrites s n) a b := by
  apply h.sub
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨ivR s, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨s'.gpr .rbx, 8⟩ ⟨s.gpr .rbx, 8⟩
    rw [iv]; exact fun _ h => h
  · refine ⟨dataR s n, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨s'.gpr .rsi, 8 * m⟩ ⟨s.gpr .rsi, 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega)
  · refine ⟨⟨s.gpr .rdx, 264⟩, by simp [loopWrites], ?_⟩
    rw [buf]; exact fun _ h => h
  · refine ⟨stackR s, by simp [loopWrites], ?_⟩
    change Region.Sub (below (s'.gpr .rsp) 8) (below (s.gpr .rsp) 8)
    rw [sp]; exact fun _ h => h

theorem BodyPost.frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hn : 1 ≤ n) : Frame (loopWrites s n) s.mem s'.mem :=
  loopFrame_slice (m := 1) (i := 0) h.mem hn rfl rfl rfl (by simp)

theorem BodyPost.schedule {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hp : StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (s.gpr .rdi) = Spec.Rc2.scheduleAt s.mem (s.gpr .rdi) := by
  apply scheduleAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData (And.intro
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) hp.stackKey.symm))

theorem BodyPost.tailData {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64) :
    Spec.Rc2.blocksAt s'.mem (s.gpr .rsi + 8) n = Spec.Rc2.blocksAt s.mem (s.gpr .rsi + 8) n := by
  have sub : Region.Sub ⟨s.gpr .rsi + 8, 8 * n⟩ (dataR s (n + 1)) :=
    Offset.sub_base _ (by change 8 + 8 * n ≤ 8 * (n + 1); omega)
  have sep : (Region.mk (s.gpr .rsi + 8) (8 * n)).Disjoint (dataR s) :=
    Offset.disjoint_base _ (d := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply blocksAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right sub).symm) (And.intro sep (And.intro
      ((hp.dataBuf.sub_left sub).sub_right (Region.sub_prefix (by decide : 264 ≤ 512)))
      ((hp.stackData.sub_right sub).symm)))

theorem firstBlock_frame {d : Spec.Rc2.Direction} {s s' : State} {n : Nat} {m : Mem}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64)
    (frame : Frame (loopWrites s' n) s'.mem m) :
    Spec.Rc2.blockAt m (s.gpr .rsi) = Spec.Rc2.blockAt s'.mem (s.gpr .rsi) := by
  have first : Region.Sub (dataR s) (dataR s (n + 1)) := Region.sub_prefix (by change 8 ≤ 8 * (n + 1); omega)
  have sep : (dataR s).Disjoint ⟨s.gpr .rsi + 8, 8 * n⟩ :=
    Offset.base_disjoint _ (e := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply blockAt_frame frame
  have iv := h.reg .rbx (by decide) (by decide) (by decide)
  have buf := h.reg .rdx (by decide) (by decide) (by decide)
  have sp := h.reg .rsp (by decide) (by decide) (by decide)
  simpa only [loopWrites, ivR, dataR, stackR, iv, buf, sp, h.ptr,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivData.sub_right first).symm) (And.intro sep (And.intro
      ((hp.dataBuf.sub_left first).sub_right (Region.sub_prefix (by decide : 264 ≤ 512)))
      ((hp.stackData.sub_right first).symm)))

end VG.Proof.Rc2.X86_64.Cbc

end

/-! # Correctness of the CBC loop on complete blocks -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64

structure LoopPost (d : Spec.Rc2.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 (8 * n)
  count : s'.gpr .rbp = 0
  reg : ∀ r ∈ kept, r ≠ .rsi → r ≠ .rbp → s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, r ≠ .rbp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (loopWrites s n) s.mem s'.mem
  data : Spec.Rc2.blocksAt s'.mem (s.gpr .rsi) n =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .rbx)) (Spec.Rc2.blocksAt s.mem (s.gpr .rsi) n)).1
  iv : Spec.Rc2.blockAt s'.mem (s.gpr .rbx) =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .rbx)) (Spec.Rc2.blocksAt s.mem (s.gpr .rsi) n)).2

theorem loop_ok (d : Spec.Rc2.Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → 8 * n ≤ 2 ^ 64 → StepPre s n → s.gpr .rbp = BitVec.ofNat 64 n →
      WP isa (.loop (Impl.Rc2.X86_64.Cbc.body d) .ne) s (LoopPost d s n) := by
  induction n with
  | zero => intro s hn; omega
  | succ n ih =>
    intro s hn bound hp count
    obtain ⟨t₁, s₁, exec₁, h₁⟩ := body_ok d s (n + 1) hn (by omega) count (hp.head hn)
    by_cases hz : n = 0
    · subst n
      refine ⟨_, s₁, Exec.loopExit exec₁ ?_, ?_⟩
      · simp only [eval, h₁.flag, decide_true, Option.map_some, Bool.not_true]
      · refine ⟨h₁.ptr, h₁.count, h₁.reg, h₁.callee, h₁.rd, h₁.wr, h₁.frame (by decide), ?_, ?_⟩
        · rw [blocksAt_cons, blocksAt_cons]
          simp only [Spec.Rc2.blocksAt, List.range_zero, List.map_nil, Spec.Rc2.cbc]
          exact congrArg (· :: []) h₁.data
        · rw [blocksAt_cons]
          simp only [Spec.Rc2.blocksAt, List.range_zero, List.map_nil, Spec.Rc2.cbc]
          exact h₁.iv
    · have hp₁ := h₁.tail hp
      obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega) (by omega) hp₁ (by simpa using h₁.count)
      refine ⟨_, s₂, Exec.loopNext exec₁ ?_ exec₂, ?_⟩
      · have he : n + 1 ≠ 1 := by omega
        simp only [eval, h₁.flag, he, decide_false, Option.map_some, Bool.not_false]
      · have key := h₁.schedule (hp.head hn)
        have tail := h₁.tailData hp bound
        have data := h₂.data
        have iv := h₂.iv
        have ki := h₁.reg .rdi (by decide) (by decide) (by decide)
        have vi := h₁.reg .rbx (by decide) (by decide) (by decide)
        have bi := h₁.reg .rdx (by decide) (by decide) (by decide)
        have sp := h₁.reg .rsp (by decide) (by decide) (by decide)
        rw [ki, vi, h₁.ptr, key, tail, h₁.iv] at data
        rw [ki, vi, h₁.ptr, key, tail, h₁.iv] at iv
        refine ⟨?_, h₂.count, ?_, ?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_, ?_, ?_⟩
        · rw [h₂.ptr, h₁.ptr, BitVec.add_assoc]
          exact congrArg (s.gpr .rsi + ·) (by
            change BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * n) = _
            rw [← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 64) (by omega))
        · intro r hr hs hb
          exact (h₂.reg r hr hs hb).trans (h₁.reg r hr hs hb)
        · intro r hr hb
          exact (h₂.callee r hr hb).trans (h₁.callee r hr hb)
        · exact (h₁.frame hn).trans (loopFrame_slice (i := 1) h₂.mem (by omega) vi bi sp h₁.ptr)
        · have first := firstBlock_frame h₁ hp bound h₂.mem
          rw [blocksAt_cons, first, h₁.data, data, blocksAt_cons]
          rfl
        · rw [blocksAt_cons]
          exact iv

theorem maybeLoop_ok (d : Spec.Rc2.Direction) (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 64)
    (hp : StepPre s n) (count : s.gpr .rbp = BitVec.ofNat 64 n)
    (flag : s.zf = some (s.gpr .rbp == 0)) :
    WP isa (.ite .e (.block []) (.loop (Impl.Rc2.X86_64.Cbc.body d) .ne)) s (LoopPost d s n) := by
  have eqZero := counter_eq n 0 (by omega) (by decide)
  simp only [BitVec.sub_zero] at eqZero
  have flag' : s.zf = some (decide (n = 0)) := by
    rw [flag, count]
    exact congrArg some eqZero
  by_cases hz : n = 0
  · subst n
    apply WP.ite true (by simp only [eval, flag', decide_true])
    · intro _
      apply WP.block_nil
      refine ⟨by simp, count, fun _ _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _, ?_, ?_⟩
      · rfl
      · rfl
    · simp
  · apply WP.ite false (by simp only [eval, flag', hz, decide_false])
    · simp
    · intro _
      exact loop_ok d n s (by omega) bound hp count

theorem LoopPost.scratchRead {d : Spec.Rc2.Direction} {s s' : State} {n : Nat}
    (h : LoopPost d s n s') (hp : StepPre s n) (i : Nat) (lo : 264 ≤ i) (hi : i + 8 ≤ 512) :
    s'.mem.readW (s.gpr .rdx + BitVec.ofNat 64 i) 64 = s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 i) 64 := by
  have sub : Region.Sub ⟨s.gpr .rdx + BitVec.ofNat 64 i, 8⟩ (bufR s) := Offset.sub_base _ hi
  have sep : (Region.mk (s.gpr .rdx + BitVec.ofNat 64 i) 8).Disjoint ⟨s.gpr .rdx, 264⟩ :=
    Offset.disjoint_base _ lo (by omega)
  apply h.mem.readW (r := ⟨s.gpr .rdx + BitVec.ofNat 64 i, 8⟩) (Region.contains_self _ _)
    (hn := by decide)
  simpa only [loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.ivBuf.sub_right sub).symm) (And.intro ((hp.dataBuf.sub_right sub).symm)
      (And.intro sep ((hp.stackBuf.sub_right sub).symm)))

end VG.Proof.Rc2.X86_64.Cbc

end

section

/-! # CBC register saves, setup, and restoration -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

def savedMem (s : State) : Mem :=
  (s.mem.writeW (s.gpr .r8 + BitVec.ofNat 64 264) (s.gpr .rbx)).writeW
    (s.gpr .r8 + BitVec.ofNat 64 272) (s.gpr .rbp)

theorem save_ok (s : State)
    (w₁ : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 264) 8)
    (w₂ : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 272) 8) :
    ∃ s', runBlock isa Impl.Rc2.X86_64.Cbc.save s = some s' ∧ Keep [] {s with mem := savedMem s} s' := by
  refine ⟨_, by
    simp only [Impl.Rc2.X86_64.Cbc.save, runBlock_cons, runStep_some, runBlock_nil,
      memOp, exec, State.store64, State.ea, offset_nat, w₁, w₂, ite_true]
    rfl, ?_⟩
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem savedMem_frame (s : State) : Frame [⟨s.gpr .r8, 512⟩] s.mem (savedMem s) := by
  exact ((Frame.refl _ _).writeW List.mem_cons_self _
    (Offset.contains_base _ (by decide : 264 + 8 ≤ 512) (by decide))).writeW List.mem_cons_self _
      (Offset.contains_base _ (by decide : 272 + 8 ≤ 512) (by decide))

theorem savedMem_rbx (s : State) : (savedMem s).readW (s.gpr .r8 + BitVec.ofNat 64 264) 64 = s.gpr .rbx := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 8 ≤ 272 ∨ 272 + 8 ≤ 264)
    (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]

theorem savedMem_rbp (s : State) : (savedMem s).readW (s.gpr .r8 + BitVec.ofNat 64 272) 64 = s.gpr .rbp := by
  rw [savedMem, Mem.readW_writeW_self64]

theorem setup_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.X86_64.Cbc.setup s = some s' ∧
      s'.gpr .rbx = s.gpr .rsi ∧ s'.gpr .rbp = s.gpr .rcx ∧
      s'.gpr .rsi = s.gpr .rdx ∧ s'.gpr .rdx = s.gpr .r8 ∧
      s'.zf = some (s.gpr .rcx == 0) ∧ Keep [.rbx, .rbp, .rsi, .rdx] s s' := by
  refine ⟨_, by
    simp only [Impl.Rc2.X86_64.Cbc.setup, rr, runBlock_cons, exec, readSrc]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · rw [zf_arithFlags]
    simp [gpr_setReg]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem restore_ok (s : State) (b p : BitVec 64)
    (r₁ : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 264) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 272) 8)
    (v₁ : s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 264) 64 = b)
    (v₂ : s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 272) 64 = p) :
    ∃ s', runBlock isa Impl.Rc2.X86_64.Cbc.restore s = some s' ∧
      s'.gpr .rbx = b ∧ s'.gpr .rbp = p ∧ Keep [.rbx, .rbp] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Impl.Rc2.X86_64.Cbc.restore, runBlock_cons, runStep_some,
      runBlock_nil, memOp, exec, readSrc, State.load64, State.ea, offset_nat, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, r₁, r₂, Option.map_some,
      v₁, v₂]
    rfl, ?_⟩
  refine ⟨?_, gpr_setReg_self _ _ _, ?_⟩
  · simp [gpr_setReg]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2, ite_false]
    · simp only [mem_setReg]
    · simp only [rd_setReg]
    · simp only [wr_setReg]

end VG.Proof.Rc2.X86_64.Cbc

end

section

/-! # CBC's function-level contract -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64

def contract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 128⟩
    let iv : Region := ⟨s.gpr .rsi, 8⟩
    let data : Region := ⟨s.gpr .rdx, 8 * (s.gpr .rcx).toNat⟩
    let buf : Region := ⟨s.gpr .r8, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    s.rd = [key] ∧ s.wr = [iv, data, buf] ∧ key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧
      ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
      stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
      (s.gpr .rdx).toNat + 8 * (s.gpr .rcx).toNat ≤ 2 ^ 64
  post s s' :=
    let out := Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .rsi)) (Spec.Rc2.blocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    Spec.Rc2.blocksAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat = out.1 ∧
      Spec.Rc2.blockAt s'.mem (s.gpr .rsi) = out.2
  pub := PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]

end VG.Proof.Rc2.X86_64.Cbc

end

/-! # Verified RC2-CBC encryption and decryption -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem cbc_body_correct (d : Spec.Rc2.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.Rc2.X86_64.Cbc.cbc d) s (fun s' => gprPreserved s s' ∧ (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    retIv, retData, retBuf, stackKey, stackIv, stackData, stackBuf, fit⟩ := hs
  have writes (i : Nat) (hi : i + 8 ≤ 512) : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 i) 8 := by
    rw [hwr]
    exact ⟨⟨s.gpr .r8, 512⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  rw [Impl.Rc2.X86_64.Cbc.cbc]
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s (writes 264 (by decide)) (writes 272 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, iv₂, count₂, data₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s.gpr r := keep₁.reg r (by simp)
  rw [g₁] at iv₂ count₂ data₂ buf₂ flag₂
  have key₂ := (keep₂.reg .rdi (by decide)).trans (g₁ .rdi)
  have sp₂ := (keep₂.reg .rsp (by decide)).trans (g₁ .rsp)
  have rd₂ := keep₂.rd.trans keep₁.rd
  have wr₂ := keep₂.wr.trans keep₁.wr
  have mem₂ : s₂.mem = savedMem s := keep₂.mem.trans keep₁.mem
  have scratchFrame : Frame [⟨s.gpr .r8, 512⟩] s.mem s₂.mem := by
    rw [mem₂]; exact savedMem_frame s
  have initialKey := scheduleAt_frame scratchFrame (s.gpr .rdi) (by simpa using keyBuf)
  have initialIv := blockAt_frame scratchFrame (s.gpr .rsi) (by simpa using ivBuf)
  have initialData := blocksAt_frame scratchFrame (s.gpr .rdx) (s.gpr .rcx).toNat (by simpa using dataBuf)
  have hp₂ : StepPre s₂ (s.gpr .rcx).toNat := by
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
    · simpa only [stackR, keyR, sp₂, key₂] using stackKey
    · simpa only [stackR, ivR, sp₂, iv₂] using stackIv
    · simpa only [stackR, dataR, sp₂, data₂] using stackData
    · simpa only [stackR, bufR, sp₂, buf₂] using stackBuf
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (s.gpr .rcx).toNat (by omega) hp₂
    (by simpa using count₂) (by rw [count₂]; exact flag₂))
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .rdx (by decide) (by decide) (by decide)).trans buf₂
  have reads (i : Nat) (hi : i + 8 ≤ 512) :
      InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .rdx + BitVec.ofNat 64 i) 8 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have v₁ : s₃.mem.readW (s₃.gpr .rdx + BitVec.ofNat 64 264) 64 = s.gpr .rbx := by
    have h := h₃.scratchRead hp₂ 264 (by decide) (by decide)
    rw [buf₂, mem₂, savedMem_rbx] at h
    rw [buf₃]; exact h
  have v₂ : s₃.mem.readW (s₃.gpr .rdx + BitVec.ofNat 64 272) 64 = s.gpr .rbp := by
    have h := h₃.scratchRead hp₂ 272 (by decide) (by decide)
    rw [buf₂, mem₂, savedMem_rbp] at h
    rw [buf₃]; exact h
  obtain ⟨s₄, run₄, rbx₄, rbp₄, keep₄⟩ := restore_ok s₃ (s.gpr .rbx) (s.gpr .rbp)
    (reads 264 (by decide)) (reads 272 (by decide)) v₁ v₂
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · constructor
    · intro r hr
      by_cases hb : r = .rbx
      · subst r; exact rbx₄
      · by_cases hp : r = .rbp
        · subst r; exact rbp₄
        · rw [keep₄.reg r (by simp [hb, hp]), h₃.callee r hr hp]
          have sep : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .rbp → r ∉ [.rbx, .rbp, .rsi, .rdx] := by decide
          exact (keep₂.reg r (sep r hr hb hp)).trans (g₁ r)
    · let rs : List Region := [⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 8 * (s.gpr .rcx).toNat⟩,
        ⟨s.gpr .r8, 512⟩, below (s.gpr .rsp) 8]
      have loopFrame : Frame rs s₂.mem s₃.mem := by
        have h := h₃.mem
        simp only [loopWrites, ivR, dataR, stackR, iv₂, data₂, buf₂, sp₂] at h
        apply h.sub
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨⟨s.gpr .rsi, 8⟩, by simp [rs], fun _ h => h⟩
        · exact ⟨⟨s.gpr .rdx, 8 * (s.gpr .rcx).toNat⟩, by simp [rs], fun _ h => h⟩
        · exact ⟨⟨s.gpr .r8, 512⟩, by simp [rs], Region.sub_prefix (by decide)⟩
        · exact ⟨below (s.gpr .rsp) 8, by simp [rs], fun _ h => h⟩
      have frame : Frame rs s.mem s₄.mem := by
        rw [keep₄.mem]
        exact (scratchFrame.mono (by simp [rs])).trans loopFrame
      apply frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (hn := by decide)
      have stackSep : (Region.mk (s.gpr .rsp) 8).Disjoint (below (s.gpr .rsp) 8) :=
        Offset.base_disjoint_below _ (by decide : 8 + 8 ≤ 2 ^ 64)
      simpa only [rs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
        And.intro retIv (And.intro retData (And.intro retBuf stackSep))
  · have out := h₃.data
    have iv := h₃.iv
    rw [key₂, iv₂, data₂, initialKey, initialIv, initialData] at out iv
    constructor
    · rw [keep₄.mem]; exact out
    · rw [keep₄.mem]; exact iv

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .r8 => 0x4000 | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 512⟩]

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.X86_64.Cbc.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := cbc_body_correct .encrypt s hs
  change Exec isa Impl.Rc2.X86_64.Cbc.encrypt s t s' at he
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.X86_64.Cbc.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := cbc_body_correct .decrypt s hs
  change Exec isa Impl.Rc2.X86_64.Cbc.decrypt s t s' at he
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem publicRegs_six (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp := by
  simp [PublicRegs]

theorem encrypt_verified : Verified target Impl.Rc2.X86_64.Cbc.encrypt (Spec.Rc2.cbcEncryptContract abi 8) := by
  refine Verified.of_correct encrypt_correct (encrypt_constantTime _) ?_
  sig_implies [Spec.Rc2.cbcEncryptContract, Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argRegs,
    contract, publicRegs_six] [satState] using satState

theorem decrypt_verified : Verified target Impl.Rc2.X86_64.Cbc.decrypt (Spec.Rc2.cbcDecryptContract abi 8) := by
  refine Verified.of_correct decrypt_correct (decrypt_constantTime _) ?_
  sig_implies [Spec.Rc2.cbcDecryptContract, Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argRegs,
    contract, publicRegs_six] [satState] using satState

end VG.Proof.Rc2.X86_64.Cbc
