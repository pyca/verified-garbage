import VerifiedGarbage.Impl.Rc2.X86_64.ExpandKey
import VerifiedGarbage.Proof.Rc2.X86_64.Save
import VerifiedGarbage.Proof.Rc2.Expansion
import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Finish
import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Vector

section

section

/-! # Initialization of SSE2 RC2 lookup state -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

theorem start_ok (s : State) (scratch : Reg)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr scratch + BitVec.ofNat 64 64) 16) :
    ∃ s', runBlock isa (Sse2.start scratch 255) s = some s' ∧
      s'.xmm .xmm0 = broadcast ((s.gpr .rax).setWidth 8) ∧
      s'.xmm .xmm1 = 0#128 ∧ s'.xmm .xmm2 = Sse2.indices 0 ∧
      s'.xmm .xmm6 = Sse2.ones ∧ s'.xmm .xmm7 = Sse2.eights ∧
      s'.xmm .xmm8 = s.mem.readW (s.gpr scratch + BitVec.ofNat 64 64) 128 ∧
      Keep [.rax, .r10] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [Sse2.start, Sse2.loadConst,
      List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, XOp.exec,
      State.load128, State.ea, memOp, offset_nat, hread, ite_true, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_setXmm, gpr_arithFlags,
      xmm_setReg, xmm_setXmm_self, xmm_setXmm_of_ne]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg]
    rw [show (255#32).signExtend 64 = (255 : BitVec 64) by decide, maskByte]
    apply ext_word
    intro i hi
    rw [broadcast, word_ofWords _ hi]
    exact broadcast_word _ i hi
  · simp (config := {decide := true}) only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg,
      XBinOp.eval, BitVec.xor_self]
  · simp (config := {decide := true}) only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg]
  · simp (config := {decide := true}) only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg]
  · simp only [xmm_setXmm_self]
    exact movq_const _
  · simp (config := {decide := true}) only [xmm_setXmm_of_ne, xmm_setReg,
      xmm_arithFlags, xmm_setXmm_self]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setXmm, gpr_setReg_of_ne _ _ hr.1, gpr_setReg_of_ne _ _ hr.2, gpr_arithFlags]
    · simp only [mem_setXmm, mem_setReg, mem_arithFlags]
    · simp only [rd_setXmm, rd_setReg, rd_arithFlags]
    · simp only [wr_setXmm, wr_setReg, wr_arithFlags]

end VG.Proof.Rc2.X86_64.Sse2

end

section

/-! # Composing eight-candidate PITABLE scans -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.Impl.Rc2.X86_64

def piWord (i : Nat) : BitVec 16 := (Spec.Rc2.piTable.getD i 0).setWidth 16

structure ScanInv (x : Byte) (n : Nat) (s : State) : Prop where
  input : s.xmm .xmm0 = broadcast x
  acc : s.xmm .xmm1 = Sse2.acc piWord x.toNat n
  indices : s.xmm .xmm2 = Impl.Rc2.X86_64.Sse2.indices n
  ones : s.xmm .xmm6 = Impl.Rc2.X86_64.Sse2.ones
  eights : s.xmm .xmm7 = Impl.Rc2.X86_64.Sse2.eights

theorem piStep_ok (s : State) (x : Byte) (n : Nat) (hn : n < 32) (hinv : ScanInv x n s) :
    WP isa (.block (Impl.Rc2.X86_64.Sse2.piStep n)) s (fun s' =>
      ScanInv x (n + 1) s' ∧ Keep [.r10] s s' ∧ s'.xmm .xmm8 = s.xmm .xmm8) := by
  rw [Impl.Rc2.X86_64.Sse2.piStep, WP.block_append_iff]
  obtain ⟨s₁, run₁, val₁, keep₁⟩ := loadConst_ok s .xmm4 (by decide)
    (Impl.Rc2.X86_64.Sse2.piValues n)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, val₂, idx₂, keep₂⟩ := select_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  refine ⟨?_, keep₁.keep.trans (keep₂.keep.weaken (by simp)), ?_⟩
  · constructor
    · rw [keep₂.xmm .xmm0 (by decide), keep₁.xmm .xmm0 (by decide)]
      exact hinv.input
    · rw [val₂, keep₁.xmm .xmm1 (by decide), keep₁.xmm .xmm0 (by decide),
        keep₁.xmm .xmm2 (by decide), keep₁.xmm .xmm6 (by decide), val₁,
        hinv.acc, hinv.input, hinv.indices, hinv.ones]
      apply acc_step piWord x n hn
      intro j hj
      exact word_ofWords _ hj
    · rw [idx₂, keep₁.xmm .xmm2 (by decide), keep₁.xmm .xmm7 (by decide),
        hinv.indices, hinv.eights]
      exact indices_next n
    · rw [keep₂.xmm .xmm6 (by decide), keep₁.xmm .xmm6 (by decide)]
      exact hinv.ones
    · rw [keep₂.xmm .xmm7 (by decide), keep₁.xmm .xmm7 (by decide)]
      exact hinv.eights
  · rw [keep₂.xmm .xmm8 (by decide), keep₁.xmm .xmm8 (by decide)]

theorem piSteps_ok (count n : Nat) (hbound : n + count ≤ 32)
    (s : State) (x : Byte) (hinv : ScanInv x n s) :
    WP isa (.block ((List.range' n count).flatMap Impl.Rc2.X86_64.Sse2.piStep)) s
      (fun s' => ScanInv x (n + count) s' ∧ Keep [.r10] s s' ∧
        s'.xmm .xmm8 = s.xmm .xmm8) := by
  induction count generalizing n s with
  | zero =>
    apply WP.block_nil
    exact ⟨hinv, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl⟩
  | succ count ih =>
    rw [List.range'_succ, List.flatMap_cons, WP.block_append_iff]
    apply WP.mono (piStep_ok s x n (by omega) hinv)
    intro s₁ h₁
    apply WP.mono (ih (n + 1) (by omega) s₁ h₁.1)
    intro s₂ h₂
    refine ⟨?_, h₁.2.1.trans h₂.2.1, h₂.2.2.trans h₁.2.2⟩
    have he : n + 1 + count = n + (count + 1) := by omega
    exact he ▸ h₂.1

end VG.Proof.Rc2.X86_64.Sse2

end

section

/-! # Verified constant-time SSE2 PITABLE lookup -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem piLookup_ok (s : State)
    (hwrite : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16) :
    WP isa (.block Impl.Rc2.X86_64.Sse2.piLookup) s (fun s' =>
      s'.gpr .rax = (Spec.Rc2.pi ((s.gpr .rax).setWidth 8)).setWidth 64 ∧
      Keep [.rax, .rcx, .r10, .r11] s s') := by
  have hread : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 64) 16 := by
    obtain ⟨r, hr, hc⟩ := hwrite
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [Impl.Rc2.X86_64.Sse2.piLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, idx₁, ones₁, eights₁, saved₁, keep₁⟩ := start_ok s .r8 hread
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff, List.range_eq_range']
  have inv₁ : ScanInv ((s.gpr .rax).setWidth 8) 0 s₁ :=
    ⟨input₁, zero₁.trans (acc_zero _ _).symm, idx₁, ones₁, eights₁⟩
  apply WP.mono (piSteps_ok 32 0 (by decide) s₁ _ inv₁)
  intro s₂ h₂
  rw [Impl.Rc2.X86_64.Sse2.finish, WP.block_append_iff]
  obtain ⟨s₃, run₃, reduced₃, keep₃⟩ := reduceOr_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have keep₂ : Keep [.rax, .r10] s₁ s₂ := h₂.2.1.weaken (by simp)
  have keep₃' : Keep [.rax, .r10] s₂ s₃ := keep₃.keep.weaken (by simp)
  have kept : Keep [.rax, .r10] s s₃ := (keep₁.trans keep₂).trans keep₃'
  have ptr : s₃.gpr .r8 = s.gpr .r8 := kept.reg .r8 (by decide)
  have wr₃ : InRegions s₃.wr (s₃.gpr .r8 + BitVec.ofNat 64 64) 16 := by
    rw [kept.wr, ptr]; exact hwrite
  have rd₃ : InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .r8 + BitVec.ofNat 64 64) 8 := by
    rw [kept.rd, kept.wr, ptr]
    obtain ⟨r, hr, hc⟩ := hread
    exact ⟨r, hr, by unfold Region.Contains at hc ⊢; omega⟩
  have saved₃ : s₃.xmm .xmm8 = s₃.mem.readW (s₃.gpr .r8 + BitVec.ofNat 64 64) 128 := by
    rw [keep₃.xmm .xmm8 (by decide), h₂.2.2, saved₁, kept.mem, ptr]
  obtain ⟨s₄, run₄, out₄, keep₄⟩ := finishTail_ok s₃ .r8 (by decide) rd₃ wr₃ saved₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · rw [out₄, reduced₃, h₂.1.acc, reduce_acc, ite_eq_left ((s.gpr .rax).setWidth 8).isLt]
    simp [piWord, Spec.Rc2.pi]
  · exact (kept.trans (keep₄.weaken (by simp))).weaken (by simp)

end VG.Proof.Rc2.X86_64.Sse2

end

/-! # Individual steps of RC2 key expansion -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

def keyTemps : List Reg := [.rax, .rbx, .rcx, .r9, .r10, .r11]

theorem copyKey_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .r12 + s.gpr .rbx) 1)
    (writable : InRegions s.wr (s.gpr .r14 + s.gpr .rbx) 1) :
    ∃ s', runBlock isa copyKey s = some s' ∧
      s'.gpr .rbx = s.gpr .rbx + 1 ∧
      s'.zf = some ((s.gpr .rbx + 1 - s.gpr .r13) == 0) ∧
      Keep keyTemps
        {s with mem := s.mem.writeW (s.gpr .r14 + s.gpr .rbx) (s.mem (s.gpr .r12 + s.gpr .rbx))} s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [copyKey, indexed, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, State.load8, State.store8, State.ea,
      BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat, BitVec.mul_one, BitVec.add_zero,
      Option.map_some, Option.bind_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg,
      wr_setReg, readable, writable, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_arithFlags, gpr_setReg_self]
    rfl
  · exact zf_arithFlags _ _ _ _
  · constructor
    · intro r hr
      simp only [keyTemps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_arithFlags, gpr_setReg, hr.1, hr.2.1, ite_false]
    · simp only [mem_arithFlags, mem_setReg, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
        BitVec.setWidth_eq]
    · simp only [rd_arithFlags, rd_setReg]
    · simp only [wr_arithFlags, wr_setReg]

theorem add_minus_one (a : BitVec 64) : a + BitVec.ofInt 64 (-1) = a - 1 := by
  rw [BitVec.sub_eq_add_neg]
  rfl

theorem fillInput_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (s.gpr .r14 + s.gpr .rbx - 1#64) 1)
    (readHi : InRegions (s.rd ++ s.wr) (s.gpr .r14 + (s.gpr .rbx - s.gpr .r13)) 1) :
    ∃ s', runBlock isa
      [.movzx8 .rax (indexed .r14 .rbx (-1)), rr .r9 .rbx, .alu .sub .r9 (.reg .r13),
       .movzx8 .rcx (indexed .r14 .r9), .alu .add .rax (.reg .rcx)] s = some s' ∧
      s'.gpr .rax = (s.mem (s.gpr .r14 + s.gpr .rbx - 1#64)).setWidth 64 +
        (s.mem (s.gpr .r14 + (s.gpr .rbx - s.gpr .r13))).setWidth 64 ∧
      Keep [.rax, .rcx, .r9] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [indexed, rr, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, State.load8, State.ea,
      BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat, BitVec.mul_one, BitVec.add_zero,
      Option.map_some, Option.bind_some, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      add_minus_one, readLo, readHi, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem fillOutput_ok (s : State)
    (writable : InRegions s.wr (s.gpr .r14 + s.gpr .rbx) 1) :
    ∃ s', runBlock isa [.store8 (indexed .r14 .rbx) .rax,
      .alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 128)] s = some s' ∧
      s'.gpr .rbx = s.gpr .rbx + 1 ∧
      s'.zf = some ((s.gpr .rbx + 1 - 128) == 0) ∧
      Keep keyTemps {s with mem := s.mem.writeW (s.gpr .r14 + s.gpr .rbx) ((s.gpr .rax).setWidth 8)} s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [indexed, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, State.store8, State.ea,
      BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat, BitVec.mul_one, BitVec.add_zero,
      Option.bind_some, gpr_setReg, writable, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_arithFlags, gpr_setReg_self]
    rfl
  · exact zf_arithFlags _ _ _ _
  · constructor
    · intro r hr
      simp only [keyTemps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_arithFlags, gpr_setReg, hr.2.1, ite_false]
    · simp only [mem_arithFlags, mem_setReg]
    · simp only [rd_arithFlags, rd_setReg]
    · simp only [wr_arithFlags, wr_setReg]

theorem fillKey_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16)
    (readLo : InRegions (s.rd ++ s.wr) (s.gpr .r14 + s.gpr .rbx - 1#64) 1)
    (readHi : InRegions (s.rd ++ s.wr) (s.gpr .r14 + (s.gpr .rbx - s.gpr .r13)) 1)
    (writable : InRegions s.wr (s.gpr .r14 + s.gpr .rbx) 1) :
    WP isa (.block fillKey) s (fun s' =>
      s'.gpr .rbx = s.gpr .rbx + 1 ∧
      s'.zf = some ((s.gpr .rbx + 1 - 128) == 0) ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (s.gpr .r14 + s.gpr .rbx)
          (Spec.Rc2.pi (s.mem (s.gpr .r14 + s.gpr .rbx - 1#64) +
          s.mem (s.gpr .r14 + (s.gpr .rbx - s.gpr .r13))))} s') := by
  rw [fillKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := fillInput_ok s readLo readHi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  apply WP.mono (Sse2.piLookup_ok s₁ (by
    rw [keep₁.wr, keep₁.reg .r8 (by decide)]; exact hlookup))
  intro s₂ h₂
  have k₁ : Keep keyTemps s s₁ := keep₁.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h <;> subst r <;> decide)
  have k₂ : Keep keyTemps s₁ s₂ := h₂.2.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h <;> subst r <;> decide)
  have keep := k₁.trans k₂
  have ptr := keep.reg .r14 (by decide)
  have index := (keep₁.reg .rbx (by decide)).trans rfl
  have index₂ : s₂.gpr .rbx = s.gpr .rbx := (h₂.2.reg .rbx (by decide)).trans index
  have write₂ : InRegions s₂.wr (s₂.gpr .r14 + s₂.gpr .rbx) 1 := by
    rw [keep.wr, ptr, index₂]; exact writable
  obtain ⟨s₃, run₃, out₃, flag₃, keep₃⟩ := fillOutput_ok s₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨by rw [out₃, index₂], by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact (keep₃.reg r hr).trans (keep.reg r hr)
  · rw [keep₃.mem, keep.mem, ptr, index₂, h₂.1, out₁]
    simp [BitVec.setWidth_add]
  · exact keep₃.rd.trans keep.rd
  · exact keep₃.wr.trans keep.wr

theorem reduceInput_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .r14 + s.gpr .rbx) 1) :
    ∃ s', runBlock isa [.movzx8 .rax (indexed .r14 .rbx), .alu .and .rax (.reg .rdx)] s = some s' ∧
      s'.gpr .rax = (s.mem (s.gpr .r14 + s.gpr .rbx)).setWidth 64 &&& s.gpr .rdx ∧
      Keep [.rax] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [indexed, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.load8, State.ea, BitVec.ofInt_ofNat,
      BitVec.mul_one, BitVec.add_zero, Option.map_some, Option.bind_some, gpr_setReg,
      readable, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_singleton] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem storeByte_ok (s : State)
    (writable : InRegions s.wr (s.gpr .r14 + s.gpr .rbx) 1) :
    runBlock isa [.store8 (indexed .r14 .rbx) .rax] s =
      some {s with mem := s.mem.writeW (s.gpr .r14 + s.gpr .rbx) ((s.gpr .rax).setWidth 8)} := by
  simp only [indexed, runBlock_cons, runStep_some, runBlock_nil, exec, State.store8, State.ea,
    BitVec.ofInt_ofNat, BitVec.mul_one, BitVec.add_zero, writable, ite_true]

theorem descendInput_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (s.gpr .r14 + (s.gpr .rbx - 1#64) + 1#64) 1)
    (readHi : InRegions (s.rd ++ s.wr) (s.gpr .r14 + (s.gpr .rbx - 1#64 + s.gpr .rbp)) 1) :
    ∃ s', runBlock isa
      [.alu .sub .rbx (.imm 1), .movzx8 .rax (indexed .r14 .rbx 1), rr .r9 .rbx,
       .alu .add .r9 (.reg .rbp), .movzx8 .rcx (indexed .r14 .r9), .alu .xor .rax (.reg .rcx)] s = some s' ∧
      s'.gpr .rbx = s.gpr .rbx - 1 ∧
      s'.gpr .rax = (s.mem (s.gpr .r14 + (s.gpr .rbx - 1#64) + 1#64)).setWidth 64 ^^^
        (s.mem (s.gpr .r14 + (s.gpr .rbx - 1#64 + s.gpr .rbp))).setWidth 64 ∧
      Keep [.rax, .rbx, .rcx, .r9] s s' := by
  have one : (1#32).signExtend 64 = 1#64 := by decide
  refine ⟨_, by
    simp (config := {decide := true}) only [indexed, rr, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, State.load8, State.ea,
      BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat, BitVec.mul_one, BitVec.add_zero, one,
      Option.map_some, Option.bind_some, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      readLo, readHi, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rfl
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem piStore_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16) (writable : InRegions s.wr (s.gpr .r14 + s.gpr .rbx) 1) :
    WP isa (.block (Sse2.piLookup ++ ([.store8 (indexed .r14 .rbx) .rax] : List Instr))) s (fun s' =>
      s'.gpr .rbx = s.gpr .rbx ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (s.gpr .r14 + s.gpr .rbx) (Spec.Rc2.pi ((s.gpr .rax).setWidth 8))} s') := by
  rw [WP.block_append_iff]
  apply WP.mono (Sse2.piLookup_ok s hlookup)
  intro s₁ h₁
  have ptr := h₁.2.reg .r14 (by decide)
  have index := h₁.2.reg .rbx (by decide)
  have valid : InRegions s₁.wr (s₁.gpr .r14 + s₁.gpr .rbx) 1 := by
    rw [h₁.2.wr, ptr, index]; exact writable
  refine WP.of_runBlock ⟨_, storeByte_ok s₁ valid, ?_⟩
  refine ⟨index, ?_⟩
  constructor
  · intro r hr
    exact h₁.2.reg r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h <;> subst r <;> decide))
  · change s₁.mem.writeW _ _ = _
    rw [h₁.2.mem, ptr, index, h₁.1]
    simp
  · exact h₁.2.rd
  · exact h₁.2.wr

theorem reduceKey_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .r14 + s.gpr .rbx) 1)
    (writable : InRegions s.wr (s.gpr .r14 + s.gpr .rbx) 1) :
    WP isa (.block reduceKey) s (fun s' => s'.gpr .rbx = s.gpr .rbx ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (s.gpr .r14 + s.gpr .rbx)
          (Spec.Rc2.pi (s.mem (s.gpr .r14 + s.gpr .rbx) &&& (s.gpr .rdx).setWidth 8))} s') := by
  rw [reduceKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := reduceInput_ok s readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg .r14 (by decide)
  have index := keep₁.reg .rbx (by decide)
  have valid : InRegions s₁.wr (s₁.gpr .r14 + s₁.gpr .rbx) 1 := by
    rw [keep₁.wr, ptr, index]; exact writable
  apply WP.mono (piStore_ok s₁ (by
    rw [keep₁.wr, keep₁.reg .r8 (by decide)]; exact hlookup) valid)
  intro s₂ h₂
  refine ⟨h₂.1.trans index, ?_⟩
  constructor
  · intro r hr
    exact (h₂.2.reg r hr).trans (keep₁.reg r (by
      simp only [List.mem_singleton]
      exact fun he => hr (he ▸ List.mem_cons_self)))
  · rw [h₂.2.mem, keep₁.mem, ptr, index, out₁]
    simp
  · exact h₂.2.rd.trans keep₁.rd
  · exact h₂.2.wr.trans keep₁.wr

theorem cmpZero_ok (s : State) :
    ∃ s', runBlock isa [.alu .cmp .rbx (.imm 0)] s = some s' ∧
      s'.zf = some (s.gpr .rbx == 0) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
    rfl, ?_⟩
  constructor
  · rw [zf_arithFlags]
    change some ((s.gpr .rbx - 0#64) == 0#64) = some (s.gpr .rbx == 0#64)
    rw [BitVec.sub_zero]
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem descendKey_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16)
    (readLo : InRegions (s.rd ++ s.wr) (s.gpr .r14 + (s.gpr .rbx - 1#64) + 1#64) 1)
    (readHi : InRegions (s.rd ++ s.wr) (s.gpr .r14 + (s.gpr .rbx - 1#64 + s.gpr .rbp)) 1)
    (writable : InRegions s.wr (s.gpr .r14 + (s.gpr .rbx - 1#64)) 1) :
    WP isa (.block descendKey) s (fun s' =>
      s'.gpr .rbx = s.gpr .rbx - 1 ∧ s'.zf = some ((s.gpr .rbx - 1) == 0) ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (s.gpr .r14 + (s.gpr .rbx - 1#64))
          (Spec.Rc2.pi (s.mem (s.gpr .r14 + (s.gpr .rbx - 1#64) + 1#64) ^^^
            s.mem (s.gpr .r14 + (s.gpr .rbx - 1#64 + s.gpr .rbp))))} s') := by
  rw [descendKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, index₁, out₁, keep₁⟩ := descendInput_ok s readLo readHi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg .r14 (by decide)
  have valid : InRegions s₁.wr (s₁.gpr .r14 + s₁.gpr .rbx) 1 := by
    rw [keep₁.wr, ptr, index₁]; exact writable
  have split : Sse2.piLookup ++ [.store8 (indexed .r14 .rbx) .rax, .alu .cmp .rbx (.imm 0)] =
      (Sse2.piLookup ++ ([.store8 (indexed .r14 .rbx) .rax] : List Instr)) ++ [.alu .cmp .rbx (.imm 0)] := by
    rw [List.append_assoc]; rfl
  rw [split, WP.block_append_iff]
  apply WP.mono (piStore_ok s₁ (by
    rw [keep₁.wr, keep₁.reg .r8 (by decide)]; exact hlookup) valid)
  intro s₂ h₂
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := cmpZero_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have index₂ := h₂.1.trans index₁
  refine ⟨(keep₃.reg .rbx (by decide)).trans index₂, by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact ((keep₃.reg r (by simp)).trans (h₂.2.reg r hr)).trans (keep₁.reg r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h <;> subst r <;> decide)))
  · rw [keep₃.mem, h₂.2.mem, keep₁.mem, ptr, index₁, out₁]
    simp
  · exact keep₃.rd.trans (h₂.2.rd.trans keep₁.rd)
  · exact keep₃.wr.trans (h₂.2.wr.trans keep₁.wr)

end VG.Proof.Rc2.X86_64

end

/-! # A bounded loop rule and frame invariant for key expansion -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem forwardLoop (body : Prog isa) (I : Nat → State → Prop) (stop : Nat)
    (step : ∀ i < stop, ∀ s, I i s → WP isa body s (fun s' =>
      I (i + 1) s' ∧ s'.zf = some (decide (i + 1 = stop))))
    (i : Nat) (hi : i < stop) (s : State) (hs : I i s) :
    WP isa (.loop body .ne) s (I stop) := by
  let Inv (n : Nat) (s : State) := ∃ i, i < stop ∧ stop - i = n ∧ I i s
  refine WP.loop (M := isa) Inv ?_ (stop - i) s ⟨i, hi, rfl, hs⟩
  intro n s ⟨j, hj, hn, hI⟩
  apply WP.mono (step j hj s hI)
  intro s' h'
  by_cases he : j + 1 = stop
  · left
    constructor
    · simp only [eval, h'.2, he, decide_true, Option.map_some, Bool.not_true]
    · rw [he] at h'
      exact h'.1
  · right
    constructor
    · simp only [eval, h'.2, he, decide_false, Option.map_some, Bool.not_false]
    · exact ⟨stop - (j + 1), by omega, j + 1, by omega, rfl, h'.1⟩

/-- Across a key-expansion loop only the six temporaries and the schedule
buffer change. The key, scratch saves, and return address are separate. -/
structure KeyFrame (s₀ s : State) : Prop where
  reg : ∀ r, r ∉ keyTemps → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨s₀.gpr .r14, 128⟩] s₀.mem s.mem

theorem KeyFrame.refl (s : State) : KeyFrame s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩

theorem KeyFrame.trans {s₀ s₁ s₂ : State} (h₁ : KeyFrame s₀ s₁) (h₂ : KeyFrame s₁ s₂) :
    KeyFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_⟩
  have frame₂ := h₂.mem
  rw [h₁.reg .r14 (by decide)] at frame₂
  exact h₁.mem.trans frame₂

theorem KeyFrame.step {s₀ s s' : State} (h : KeyFrame s₀ s) (i : Nat) (hi : i < 128)
    (b : Byte) (keep : Keep keyTemps {s with mem := s.mem.writeW (s₀.gpr .r14 + BitVec.ofNat 64 i) b} s') : KeyFrame s₀ s' := by
  refine ⟨fun r hr => (keep.reg r hr).trans (h.reg r hr), keep.rd.trans h.rd,
    keep.wr.trans h.wr, ?_⟩
  rw [keep.mem]
  exact h.mem.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))

theorem KeyFrame.keep {s₀ s s' : State} (h : KeyFrame s₀ s) (keep : Keep keyTemps s s') :
    KeyFrame s₀ s' := by
  refine ⟨fun r hr => (keep.reg r hr).trans (h.reg r hr), keep.rd.trans h.rd,
    keep.wr.trans h.wr, ?_⟩
  rw [keep.mem]; exact h.mem

theorem counter_add (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.ofNat_add]
  rfl

theorem counter_eq (i n : Nat) (hi : i < 2 ^ 64) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 i - BitVec.ofNat 64 n) == 0#64) = decide (i = n) := by
  have he : (BitVec.ofNat 64 i - BitVec.ofNat 64 n = 0#64) ↔ i = n := by bv_omega
  apply Bool.eq_iff_iff.mpr
  simpa only [beq_iff_eq, decide_eq_true_eq] using he

end VG.Proof.Rc2.X86_64
