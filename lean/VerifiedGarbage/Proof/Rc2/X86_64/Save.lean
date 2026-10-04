import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Impl.Rc2.X86_64.Block
import VerifiedGarbage.Proof.Rc2.X86_64.Lookup
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Finish
import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Vector
import VerifiedGarbage.Impl.Rc2.X86_64.Sse2KeyLookup

section

section

section

section

/-! # Initialization of SSE2 RC2 schedule lookup state -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

theorem keyStart_ok (s : State) (scratch : Reg)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr scratch + BitVec.ofNat 64 64) 16) :
    ∃ s', runBlock isa (Sse2.start scratch 63) s = some s' ∧
      s'.xmm .xmm0 = broadcast (((s.gpr .rax).setWidth 6).setWidth 8) ∧
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
    rw [show (63#32).signExtend 64 = (63 : BitVec 64) by decide, maskIndex]
    apply ext_word
    intro i hi
    rw [broadcast, word_ofWords _ hi]
    simpa using broadcast_word (((s.gpr .rax).setWidth 6).setWidth 8) i hi
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

/-! # Composing eight-candidate schedule scans -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

structure KeyScanInv (f : Nat → BitVec 16) (x : Byte) (n : Nat) (s : State) : Prop where
  input : s.xmm .xmm0 = broadcast x
  acc : s.xmm .xmm1 = Sse2.acc f x.toNat n
  indices : s.xmm .xmm2 = Impl.Rc2.X86_64.Sse2.indices n
  ones : s.xmm .xmm6 = Impl.Rc2.X86_64.Sse2.ones
  eights : s.xmm .xmm7 = Impl.Rc2.X86_64.Sse2.eights

theorem keyLoad_ok (s : State) (n : Nat)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * n)) 16) :
    ∃ s', runBlock isa [.movdquLoad .xmm4 (memOp .rdi (16 * n))] s = some s' ∧
      s'.xmm .xmm4 = s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * n)) 128 ∧
      KeepX [] [.xmm4] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128,
      State.ea, memOp, offset_nat, hread, ite_true, Option.map_some]
    rfl, ?_⟩
  constructor
  · exact xmm_setXmm_self _ _ _
  · constructor
    · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      exact xmm_setXmm_of_ne _ _ hr

theorem keyStep_ok (s : State) (f : Nat → BitVec 16) (x : Byte) (n : Nat) (hn : n < 8)
    (hinv : KeyScanInv f x n s)
    (hf : ∀ i < 64, f i = s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (2 * i)) 16)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * n)) 16) :
    WP isa (.block (Impl.Rc2.X86_64.Sse2.keyStep n)) s (fun s' =>
      KeyScanInv f x (n + 1) s' ∧ Keep [] s s' ∧ s'.xmm .xmm8 = s.xmm .xmm8) := by
  rw [Impl.Rc2.X86_64.Sse2.keyStep, WP.block_append_iff]
  obtain ⟨s₁, run₁, val₁, keep₁⟩ := keyLoad_ok s n hread
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, val₂, idx₂, keep₂⟩ := select_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  refine ⟨?_, keep₁.keep.trans keep₂.keep, ?_⟩
  · constructor
    · rw [keep₂.xmm .xmm0 (by decide), keep₁.xmm .xmm0 (by decide)]
      exact hinv.input
    · rw [val₂, keep₁.xmm .xmm1 (by decide), keep₁.xmm .xmm0 (by decide),
        keep₁.xmm .xmm2 (by decide), keep₁.xmm .xmm6 (by decide), val₁,
        hinv.acc, hinv.input, hinv.indices, hinv.ones]
      apply acc_step f x n (by omega)
      intro j hj
      rw [word_readW _ _ hj, hf (8 * n + j) (by omega)]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact congrArg (fun d => s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 d) 16) (by omega)
    · rw [idx₂, keep₁.xmm .xmm2 (by decide), keep₁.xmm .xmm7 (by decide),
        hinv.indices, hinv.eights]
      exact indices_next n
    · rw [keep₂.xmm .xmm6 (by decide), keep₁.xmm .xmm6 (by decide)]
      exact hinv.ones
    · rw [keep₂.xmm .xmm7 (by decide), keep₁.xmm .xmm7 (by decide)]
      exact hinv.eights
  · rw [keep₂.xmm .xmm8 (by decide), keep₁.xmm .xmm8 (by decide)]

theorem keySteps_ok (count n : Nat) (hbound : n + count ≤ 8)
    (s : State) (f : Nat → BitVec 16) (x : Byte) (hinv : KeyScanInv f x n s)
    (hf : ∀ i < 64, f i = s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (2 * i)) 16)
    (hread : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block ((List.range' n count).flatMap Impl.Rc2.X86_64.Sse2.keyStep)) s
      (fun s' => KeyScanInv f x (n + count) s' ∧ Keep [] s s' ∧
        s'.xmm .xmm8 = s.xmm .xmm8) := by
  induction count generalizing n s with
  | zero =>
    apply WP.block_nil
    exact ⟨hinv, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl⟩
  | succ count ih =>
    rw [List.range'_succ, List.flatMap_cons, WP.block_append_iff]
    apply WP.mono (keyStep_ok s f x n (by omega) hinv hf (hread n (by omega)))
    intro s₁ h₁
    have hf₁ : ∀ i < 64, f i = s₁.mem.readW (s₁.gpr .rdi + BitVec.ofNat 64 (2 * i)) 16 := by
      rw [h₁.2.1.mem, h₁.2.1.reg .rdi (by simp)]; exact hf
    have hr₁ : ∀ i < 8, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 (16 * i)) 16 := by
      rw [h₁.2.1.rd, h₁.2.1.wr, h₁.2.1.reg .rdi (by simp)]; exact hread
    apply WP.mono (ih (n + 1) (by omega) s₁ h₁.1 hf₁ hr₁)
    intro s₂ h₂
    refine ⟨?_, h₁.2.1.trans h₂.2.1, h₂.2.2.trans h₁.2.2⟩
    have he : n + 1 + count = n + (count + 1) := by omega
    exact he ▸ h₂.1

end VG.Proof.Rc2.X86_64.Sse2

end

/-! # Verified constant-time SSE2 schedule lookup -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem schedule_readWord (m : Mem) (p : Addr) (i : Nat) (hi : i < 64) :
    m.readW (p + BitVec.ofNat 64 (2 * i)) 16 = (Spec.Rc2.scheduleAt m p).getD i 0 := by
  rw [scheduleAt_getD _ _ _ hi]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Mem.readW, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, decide_eq_true hj, Bool.true_and]
  rw [getLsbD_read _ _ (by omega)]
  by_cases h : j < 8
  · simp only [h, decide_true, Bool.not_true, Bool.false_and, Bool.or_false,
      Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, BitVec.add_zero]
  · have hj' : j - 8 < 8 := by omega
    simp only [h, decide_false, Bool.not_false]
    have hdiv : j / 8 = 1 := by omega
    have hmod : j % 8 = j - 8 := by omega
    rw [hdiv, hmod]
    have hp : p + BitVec.ofNat 64 (2 * i) + BitVec.ofNat 64 1 =
        p + BitVec.ofNat 64 (2 * i + 1) := by rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [hp]
    simp (disch := omega) only [BitVec.getLsbD_of_ge, decide_eq_true,
      Bool.true_and, Bool.false_or]

theorem keyLookup_ok (s : State)
    (hread : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * i)) 16)
    (hwrite : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 64) 16) :
    WP isa (.block Impl.Rc2.X86_64.Sse2.keyLookup) s (fun s' =>
      s'.gpr .rax = ((Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)).getD
        ((s.gpr .rax).setWidth 6).toNat 0).setWidth 64 ∧
      Keep [.rax, .rcx, .r8, .r9, .r10, .r11] s s') := by
  have hsread : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 64) 16 := by
    obtain ⟨r, hr, hc⟩ := hwrite
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [Impl.Rc2.X86_64.Sse2.keyLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, idx₁, ones₁, eights₁, saved₁, keep₁⟩ := keyStart_ok s .rdx hsread
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff, List.range_eq_range']
  let x : Byte := ((s.gpr .rax).setWidth 6).setWidth 8
  let f (i : Nat) := s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (2 * i)) 16
  have inv₁ : KeyScanInv f x 0 s₁ :=
    ⟨input₁, zero₁.trans (acc_zero _ _).symm, idx₁, ones₁, eights₁⟩
  have hf₁ : ∀ i < 64, f i = s₁.mem.readW (s₁.gpr .rdi + BitVec.ofNat 64 (2 * i)) 16 := by
    rw [keep₁.mem, keep₁.reg .rdi (by decide)]
    intro _ _; rfl
  have hr₁ : ∀ i < 8, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [keep₁.rd, keep₁.wr, keep₁.reg .rdi (by decide)]; exact hread
  apply WP.mono (keySteps_ok 8 0 (by decide) s₁ f x inv₁ hf₁ hr₁)
  intro s₂ h₂
  rw [Impl.Rc2.X86_64.Sse2.finish, WP.block_append_iff]
  obtain ⟨s₃, run₃, reduced₃, keep₃⟩ := reduceOr_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have keep₂ : Keep [.rax, .r10] s₁ s₂ := h₂.2.1.weaken (by simp)
  have keep₃' : Keep [.rax, .r10] s₂ s₃ := keep₃.keep.weaken (by simp)
  have kept : Keep [.rax, .r10] s s₃ := (keep₁.trans keep₂).trans keep₃'
  have ptr : s₃.gpr .rdx = s.gpr .rdx := kept.reg .rdx (by decide)
  have wr₃ : InRegions s₃.wr (s₃.gpr .rdx + BitVec.ofNat 64 64) 16 := by
    rw [kept.wr, ptr]; exact hwrite
  have rd₃ : InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .rdx + BitVec.ofNat 64 64) 8 := by
    rw [kept.rd, kept.wr, ptr]
    obtain ⟨r, hr, hc⟩ := hsread
    exact ⟨r, hr, by unfold Region.Contains at hc ⊢; omega⟩
  have saved₃ : s₃.xmm .xmm8 = s₃.mem.readW (s₃.gpr .rdx + BitVec.ofNat 64 64) 128 := by
    rw [keep₃.xmm .xmm8 (by decide), h₂.2.2, saved₁, kept.mem, ptr]
  obtain ⟨s₄, run₄, out₄, keep₄⟩ := finishTail_ok s₃ .rdx (by decide) rd₃ wr₃ saved₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · have xb : x.toNat < 64 := by
      simp only [x, BitVec.toNat_setWidth]
      have h := ((s.gpr .rax).setWidth 6).isLt
      simp only [BitVec.toNat_setWidth] at h
      omega
    have xe : x.toNat = ((s.gpr .rax).setWidth 6).toNat := by
      simp only [x, BitVec.toNat_setWidth]
      have h := ((s.gpr .rax).setWidth 6).isLt
      simp only [BitVec.toNat_setWidth] at h
      omega
    rw [out₄, reduced₃, h₂.1.acc, reduce_acc, ite_eq_left xb]
    dsimp only [f]
    rw [schedule_readWord _ _ _ xb, xe]
  · exact (kept.trans (keep₄.weaken (by simp))).weaken (by simp)

end VG.Proof.Rc2.X86_64.Sse2

end

section

/-! # Existing contract permissions used by vector schedule scans -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64

structure ScanMemory (s : State) : Prop where
  bytes : ∀ i < 128, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 i) 1
  vectors : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * i)) 16
  scratch : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 64) 16

instance (s : State) : CoeFun (ScanMemory s)
    (fun _ => ∀ i, i < 128 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 i) 1) where
  coe := fun h => h.bytes

theorem ScanMemory.keep {s s' : State} {rs : List Reg} (h : ScanMemory s)
    (keep : Keep rs s s') (hk : .rdi ∉ rs) (hs : .rdx ∉ rs) : ScanMemory s' := by
  constructor
  · rw [keep.rd, keep.wr, keep.reg .rdi hk]
    exact h.bytes
  · rw [keep.rd, keep.wr, keep.reg .rdi hk]
    exact h.vectors
  · rw [keep.wr, keep.reg .rdx hs]
    exact h.scratch

end VG.Proof.Rc2.X86_64

end

/-! # RC2 mixing and mashing in x86-64 registers -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

/-- State words never alias the temporaries or argument registers. -/
theorem wordReg_separate (i : Nat) :
    wordReg i ≠ .rax ∧ wordReg i ≠ .rcx ∧ wordReg i ≠ .rdx ∧ wordReg i ≠ .rdi ∧
    wordReg i ≠ .rsi ∧ wordReg i ≠ .r8 ∧ wordReg i ≠ .r9 ∧
    wordReg i ≠ .r10 ∧ wordReg i ≠ .r11 := by
  have h : ∀ j < 4,
      wordReg j ≠ .rax ∧ wordReg j ≠ .rcx ∧ wordReg j ≠ .rdx ∧ wordReg j ≠ .rdi ∧
      wordReg j ≠ .rsi ∧ wordReg j ≠ .r8 ∧ wordReg j ≠ .r9 ∧
      wordReg j ≠ .r10 ∧ wordReg j ≠ .r11 := by decide
  simpa only [wordReg, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem wordReg_injective : ∀ i < 4, ∀ j < 4, wordReg i = wordReg j ↔ i = j := by decide

theorem rotation_bounds (i : Nat) : 1 ≤ Spec.Rc2.rotation i ∧ Spec.Rc2.rotation i < 16 := by
  have h : ∀ j < 4, 1 ≤ Spec.Rc2.rotation j ∧ Spec.Rc2.rotation j < 16 := by decide
  simpa only [Spec.Rc2.rotation, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem rotate16_ok (s : State) (r : Reg) (hr : r ≠ .rax)
    (x : BitVec 16) (hx : s.gpr r = x.setWidth 64)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    ∃ s', runBlock isa (rotate16 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 64 ∧ Keep [r, .rax] s s' := by
  have hleft : 1 ≤ 64 - n ∧ 64 - n ≤ 63 := by omega
  have hright : 1 ≤ 16 - n ∧ 16 - n ≤ 63 := by omega
  refine ⟨_, by
    simp only [rotate16, rr, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, execShift, readSrc, hleft, hright, and_self, ite_true, hr, Ne.symm hr,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_setFlags, gpr_arithFlags,
      ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      hr, ite_false]
    rw [hx]
    exact rotateWord x n hn hn'
  · constructor
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr'.1, hr'.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem mixInputs_ok (s : State) (i j : Nat) (hj : j < 64)
    (readable : ∀ k < 128,
      InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 k) 1) :
    ∃ s', runBlock isa (mixInputs j i) s = some s' ∧
      s'.gpr .r10 = (s.gpr (wordReg (i + 3)) &&& s.gpr (wordReg (i + 2))) +
        (~~~(s.gpr (wordReg (i + 3))) &&& s.gpr (wordReg (i + 1))) ∧
      s'.gpr .r8 = ((Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)).getD j 0).setWidth 64 ∧
      Keep [.r8, .r9, .r10, .r11] s s' := by
  have h₁ := wordReg_separate (i + 1)
  have h₂ := wordReg_separate (i + 2)
  have h₃ := wordReg_separate (i + 3)
  have lo := readable (2 * j) (by omega)
  have hi := readable (2 * j + 1) (by omega)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reducePow, and_self, mixInputs, loadKey, rr, memOp,
      List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, execShift, readSrc, State.load8, State.ea, offset_nat,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, gpr_setFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags,
      wr_setReg, wr_arithFlags, lo, hi, 
      h₁.2.2.2.2.2.2.2.1, h₁.2.2.2.2.2.2.2.2,
      h₂.2.2.2.2.2.2.2.1, h₃.2.2.2.2.2.2.2.1]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true,
      ite_false]
    change _ + ((_ ^^^ BitVec.allOnes 64) &&& _) = _
    rw [BitVec.xor_allOnes]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    rw [joinBytes, scheduleAt_getD _ _ _ hj]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

/-- Current RC2 words in the four dedicated registers. -/
def Words (s : State) (v : Spec.Rc2.State) : Prop :=
  ∀ i < 4, s.gpr (wordReg i) = (v.getD i 0).setWidth 64

def temps : List Reg := [.rax, .rcx, .r8, .r9, .r10, .r11]
def roundWrites : List Reg := temps ++ [.r12, .r13, .r14, .r15]

theorem wordReg_not_temps (i : Nat) : wordReg i ∉ temps := by
  have h := wordReg_separate i
  simp only [temps, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h.1, h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem wordReg_mem_roundWrites (i : Nat) : wordReg i ∈ roundWrites := by
  have h : ∀ j < 4, wordReg j ∈ roundWrites := by decide
  simpa only [wordReg, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem vector_getD {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) (d : α) :
    v.getD i d = v[i] := by
  simp [Vector.getD, hi]

theorem Words.update {s s' : State} {v : Spec.Rc2.State} (h : Words s v)
    (i : Nat) (hi : i < 4) (x : BitVec 16)
    (out : s'.gpr (wordReg i) = x.setWidth 64)
    (keep : Keep (wordReg i :: temps) s s') : Words s' (v.set! i x) := by
  intro j hj
  by_cases he : j = i
  · subst j
    simpa [Vector.getD, hi] using out
  · have hr : wordReg j ∉ wordReg i :: temps := by
      simp only [List.mem_cons, not_or]
      exact ⟨fun e => he ((wordReg_injective j hj i hi).mp e), wordReg_not_temps j⟩
    rw [keep.reg _ hr, h j hj]
    rw [vector_getD _ j hj, vector_getD _ j hj, Vector.getElem_set!_ne hj (Ne.symm he)]

theorem Words.preserve {s s' : State} {v : Spec.Rc2.State} (h : Words s v)
    (keep : Keep temps s s') : Words s' v := by
  intro i hi
  exact (keep.reg _ (wordReg_not_temps i)).trans (h i hi)

theorem Keep.round {s s' : State} {i : Nat}
    (h : Keep (wordReg i :: temps) s s') : Keep roundWrites s s' :=
  h.weaken (by
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with he | hm
    · subst r; exact wordReg_mem_roundWrites i
    · exact List.mem_append_left _ hm)

theorem addInputs_ok (s : State) (r : Reg) (h10 : r ≠ .r10) :
    ∃ s', runBlock isa [.alu .add r (.reg .r8), .alu .add r (.reg .r10),
      .alu .and r (.imm 65535)] s = some s' ∧
      s'.gpr r = (s.gpr r + s.gpr .r8 + s.gpr .r10) &&& 65535 ∧ Keep [r] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some, gpr_setReg, gpr_arithFlags,
      Ne.symm h10, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r' hr
      simp only [List.mem_singleton] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem subInputs_ok (s : State) (r : Reg) (h10 : r ≠ .r10) :
    ∃ s', runBlock isa [.alu .sub r (.reg .r8), .alu .sub r (.reg .r10),
      .alu .and r (.imm 65535)] s = some s' ∧
      s'.gpr r = (s.gpr r - s.gpr .r8 - s.gpr .r10) &&& 65535 ∧ Keep [r] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some, gpr_setReg, gpr_arithFlags,
      Ne.symm h10, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r' hr
      simp only [List.mem_singleton] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem mix_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (readable : ∀ k < 128,
      InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 k) 1) :
    WP isa (.block (mix j i)) s (fun s' =>
      Words s' (Spec.Rc2.mix (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j i v) ∧
      Keep (wordReg i :: temps) s s') := by
  rw [mix, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, composite₁, key₁, keep₁⟩ := mixInputs_ok s i j hj readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have sep := wordReg_separate i
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := addInputs_ok s₁ (wordReg i)
    sep.2.2.2.2.2.2.2.1
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  let x := v.getD i 0 + (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)).getD j 0 +
    (v.getD ((i + 3) % 4) 0 &&& v.getD ((i + 2) % 4) 0) +
    (~~~(v.getD ((i + 3) % 4) 0) &&& v.getD ((i + 1) % 4) 0)
  have wordmod (j : Nat) : wordReg j = wordReg (j % 4) := by simp [wordReg]
  have value₂ : s₂.gpr (wordReg i) = x.setWidth 64 := by
    rw [out₂, key₁, composite₁, keep₁.reg (wordReg i) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨sep.2.2.2.2.2.1, sep.2.2.2.2.2.2.1,
        sep.2.2.2.2.2.2.2.1, sep.2.2.2.2.2.2.2.2⟩), hv i hi,
      wordmod (i + 3), wordmod (i + 2), wordmod (i + 1),
      hv _ (Nat.mod_lt _ (by decide)), hv _ (Nat.mod_lt _ (by decide)),
      hv _ (Nat.mod_lt _ (by decide))]
    exact mixWord _ _ _ _ _
  have hn := rotation_bounds i
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := rotate16_ok s₂ (wordReg i) sep.1 x value₂ _ hn.1 hn.2
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have k₁ : Keep (wordReg i :: temps) s s₁ := keep₁.weaken (by
    intro r hr
    apply List.mem_cons_of_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h <;> subst r <;> decide)
  have k₂ : Keep (wordReg i :: temps) s₁ s₂ := keep₂.weaken (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r; exact List.mem_cons_self)
  have k₃ : Keep (wordReg i :: temps) s₂ s₃ := keep₃.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h
    · subst r; exact List.mem_cons_self
    · subst r; exact List.mem_cons_of_mem _ (by decide))
  have keep := (k₁.trans k₂).trans k₃
  exact ⟨hv.update i hi (x.rotateLeft _) out₃ keep, keep⟩

theorem wordReg_mod (i : Nat) : wordReg i = wordReg (i % 4) := by simp [wordReg]

theorem wordReg_offset_ne (i : Nat) (hi : i < 4) (d : Nat) (hd : 1 ≤ d) (hd' : d < 4) :
    wordReg (i + d) ≠ wordReg i := by
  rw [wordReg_mod (i + d)]
  intro he
  have := (wordReg_injective _ (Nat.mod_lt _ (by decide)) i hi).mp he
  omega

theorem keep_inputs {s s' : State} (h : Keep [.r8, .r9, .r10, .r11] s s') (i : Nat) :
    Keep (wordReg i :: temps) s s' := h.weaken (by
  intro r hr
  apply List.mem_cons_of_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h <;> subst r <;> decide)

theorem keep_rotate {i : Nat} {s s' : State} (h : Keep [wordReg i, .rax] s s') :
    Keep (wordReg i :: temps) s s' := h.weaken (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h
  · subst r; exact List.mem_cons_self
  · subst r; exact List.mem_cons_of_mem _ (by decide))

theorem keep_word {i : Nat} {s s' : State} (h : Keep [wordReg i] s s') :
    Keep (wordReg i :: temps) s s' := h.weaken (by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r; exact List.mem_cons_self)

theorem reverseMix_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (readable : ∀ k < 128,
      InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 k) 1) :
    WP isa (.block (reverseMix j i)) s (fun s' =>
      Words s' (Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j i v) ∧
      Keep (wordReg i :: temps) s s') := by
  rw [reverseMix, List.append_assoc, WP.block_append_iff]
  have sep := wordReg_separate i
  have hn := rotation_bounds i
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := rotate16_ok s (wordReg i) sep.1 (v.getD i 0)
    (hv i hi) (16 - Spec.Rc2.rotation i) (by omega) (by omega)
  rw [rotateLeft_reverse _ _ hn.1 hn.2] at out₁
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have ptr₁ : s₁.gpr .rdi = s.gpr .rdi := keep₁.reg _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm sep.2.2.2.1, by decide⟩)
  have read₁ : ∀ k < 128,
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 k) 1 := by
    rw [keep₁.rd, keep₁.wr, ptr₁]; exact readable
  obtain ⟨s₂, run₂, composite₂, key₂, keep₂⟩ := mixInputs_ok s₁ i j hj read₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := subInputs_ok s₂ (wordReg i) sep.2.2.2.2.2.2.2.1
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have other (d : Nat) (hd : 1 ≤ d) (hd' : d < 4) :
      s₁.gpr (wordReg (i + d)) = (v.getD ((i + d) % 4) 0).setWidth 64 := by
    rw [keep₁.reg _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨wordReg_offset_ne i hi d hd hd', (wordReg_separate _).1⟩),
      wordReg_mod (i + d)]
    exact hv _ (Nat.mod_lt _ (by decide))
  have keptWord := keep₂.reg (wordReg i) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨sep.2.2.2.2.2.1, sep.2.2.2.2.2.2.1,
      sep.2.2.2.2.2.2.2.1, sep.2.2.2.2.2.2.2.2⟩)
  have value₃ : s₃.gpr (wordReg i) =
      ((v.getD i 0).rotateRight (Spec.Rc2.rotation i) -
        (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)).getD j 0 -
        (v.getD ((i + 3) % 4) 0 &&& v.getD ((i + 2) % 4) 0) -
        (~~~(v.getD ((i + 3) % 4) 0) &&& v.getD ((i + 1) % 4) 0)).setWidth 64 := by
    rw [out₃, keptWord, out₁, key₂, composite₂, keep₁.mem, ptr₁,
      other 3 (by decide) (by decide), other 2 (by decide) (by decide),
      other 1 (by decide) (by decide)]
    exact reverseMixWord _ _ _ _ _
  have keep := ((keep_rotate keep₁).trans (keep_inputs keep₂ i)).trans (keep_word keep₃)
  exact ⟨hv.update i hi _ value₃ keep, keep⟩

theorem adjust_ok (s : State) (r : Reg) (subtract : Bool) :
    ∃ s', runBlock isa [.alu (if subtract then .sub else .add) r (.reg .rax),
      .alu .and r (.imm 65535)] s = some s' ∧
      s'.gpr r = (if subtract then s.gpr r - s.gpr .rax else s.gpr r + s.gpr .rax) &&& 65535 ∧
      Keep [r] s s' := by
  cases subtract <;>
    refine ⟨_, by
      simp only [Bool.false_eq_true, runBlock_cons, runStep_some,
        runBlock_nil, exec, execAlu, readSrc, Option.bind_some, gpr_setReg,
        ↓reduceIte]
      rfl, ?_⟩
  all_goals
    constructor
    · exact gpr_setReg_self _ _ _
    · constructor
      · intro r' hr
        simp only [List.mem_singleton] at hr
        simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]
      · simp only [mem_setReg, mem_arithFlags]
      · simp only [rd_setReg, rd_arithFlags]
      · simp only [wr_setReg, wr_arithFlags]

theorem indexWord (x : BitVec 16) :
    ((x.setWidth 64).setWidth 6).toNat = (x &&& 63).toNat := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  change x.toNat % 18446744073709551616 % 64 = x.toNat &&& (2 ^ 6 - 1)
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (show x.toNat < 18446744073709551616 by have := x.isLt; omega)]

def mashSpec (direction : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule)
    (i : Nat) (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match direction with
  | .encrypt => Spec.Rc2.mash k i v
  | .decrypt => Spec.Rc2.reverseMash k i v

theorem mash_ok (direction : Spec.Rc2.Direction) (s : State)
    (v : Spec.Rc2.State) (hv : Words s v) (i : Nat) (hi : i < 4)
    (readable : ScanMemory s) :
    WP isa (.block (mash direction i)) s (fun s' =>
      Words s' (mashSpec direction (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) i v) ∧
      Keep (wordReg i :: temps) s s') := by
  rw [mash, List.append_assoc, WP.block_append_iff]
  let s₁ := s.setReg .rax (s.gpr (wordReg (i + 3)))
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
    rfl
  rw [WP.block_append_iff]
  have keep₁ : Keep temps s s₁ := by
    constructor
    · intro r hr
      exact gpr_setReg_of_ne _ _ (fun he => hr (he ▸ List.mem_cons_self))
    · exact mem_setReg _ _ _
    · exact rd_setReg _ _ _
    · exact wr_setReg _ _ _
  have ptr₁ := keep₁.reg .rdi (by decide)
  have read₁ : ScanMemory s₁ := readable.keep keep₁ (by decide) (by decide)
  apply WP.mono (Sse2.keyLookup_ok s₁ read₁.vectors read₁.scratch)
  intro s₂ h₂
  let k := Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)
  let key := k.getD ((v.getD ((i + 3) % 4) 0 &&& 63).toNat) 0
  have out₂ : s₂.gpr .rax = key.setWidth 64 := by
    rw [h₂.1, keep₁.mem, ptr₁]
    change (k.getD (((s.gpr (wordReg (i + 3))).setWidth 6).toNat) 0).setWidth 64 = _
    rw [wordReg_mod (i + 3), hv _ (Nat.mod_lt _ (by decide)), indexWord]
  have keep₂ : Keep temps s₁ s₂ := h₂.2
  have value₂ := ((hv.preserve keep₁).preserve keep₂) i hi
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := adjust_ok s₂ (wordReg i) (direction == .decrypt)
  have code_eq : (if (direction == .decrypt) = true then AluOp.sub else .add) =
      (if direction = .encrypt then .add else .sub) := by cases direction <;> rfl
  rw [code_eq] at run₃
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have keep : Keep (wordReg i :: temps) s s₃ :=
    ((keep₁.trans keep₂).weaken (fun _ hr => List.mem_cons_of_mem _ hr)).trans (keep_word keep₃)
  have out₃' : s₃.gpr (wordReg i) =
      (if direction == .decrypt then v.getD i 0 - key else v.getD i 0 + key).setWidth 64 := by
    rw [out₃, value₂, out₂]
    cases direction <;>
      simp [maskWord_lit, BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le]
  constructor
  · cases direction <;> exact hv.update i hi _ out₃' keep
  · exact keep

end VG.Proof.Rc2.X86_64

end

section

section

/-! # Composition of RC2's sixteen rounds -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem foldWords_ok (code : Nat → List Instr)
    (step : Spec.Rc2.Schedule → Nat → Spec.Rc2.State → Spec.Rc2.State) (is : List Nat)
    (correct : ∀ i ∈ is, ∀ (s : State) (v : Spec.Rc2.State), Words s v →
      (ScanMemory s) →
      WP isa (.block (code i)) s (fun s' =>
        Words s' (step (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) i v) ∧ Keep roundWrites s s'))
    (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (readable : ScanMemory s) :
    WP isa (.block (is.flatMap code)) s (fun s' =>
      Words s' (is.foldl (fun v i => step (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) i v) v) ∧
      Keep roundWrites s s') := by
  induction is generalizing s v with
  | nil =>
    apply WP.block_nil
    exact ⟨hv, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    apply WP.mono (correct i (by simp) s v hv readable)
    intro s₁ h₁
    have ptr₁ := h₁.2.reg .rdi (by decide)
    have read₁ : ScanMemory s₁ := readable.keep h₁.2 (by decide) (by decide)
    apply WP.mono (ih (fun j hj => correct j (List.mem_cons_of_mem _ hj)) s₁ _ h₁.1 read₁)
    intro s₂ h₂
    refine ⟨?_, h₁.2.trans h₂.2⟩
    rw [h₁.2.mem, ptr₁] at h₂
    exact h₂.1

theorem mixRound_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (j : Nat) (hj : j < 16)
    (readable : ScanMemory s) :
    WP isa (.block ((List.range 4).flatMap (fun i => mix (4 * j + i) i))) s (fun s' =>
      Words s' (Spec.Rc2.mixRound (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j v) ∧
      Keep roundWrites s s') := by
  apply foldWords_ok (step := fun k i v => Spec.Rc2.mix k (4 * j + i) i v) _ _ _ s v hv readable
  intro i hi s v hv readable
  have bound := List.mem_range.mp hi
  apply WP.mono (mix_ok s v hv i (4 * j + i) bound (by omega) readable.bytes)
  exact fun _ h => ⟨h.1, h.2.round⟩

theorem reverseMixRound_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (j : Nat) (hj : j < 16)
    (readable : ScanMemory s) :
    WP isa (.block ([3, 2, 1, 0].flatMap (fun i => reverseMix (4 * j + i) i))) s (fun s' =>
      Words s' (Spec.Rc2.reverseMixRound (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j v) ∧
      Keep roundWrites s s') := by
  apply foldWords_ok (step := fun k i v => Spec.Rc2.reverseMix k (4 * j + i) i v) _ _ _ s v hv readable
  intro i hi s v hv readable
  have bound : i < 4 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  apply WP.mono (reverseMix_ok s v hv i (4 * j + i) bound (by omega) readable.bytes)
  exact fun _ h => ⟨h.1, h.2.round⟩

def mashRoundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mashRound k v
  | .decrypt => Spec.Rc2.reverseMashRound k v

def order (d : Spec.Rc2.Direction) : List Nat :=
  match d with
  | .encrypt => List.range 4
  | .decrypt => [3, 2, 1, 0]

theorem mashRound_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (readable : ScanMemory s) :
    WP isa (.block ((order d).flatMap (mash d))) s (fun s' =>
      Words s' (mashRoundSpec d (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) v) ∧
      Keep roundWrites s s') := by
  have he (k : Spec.Rc2.Schedule) : mashRoundSpec d k v =
      (order d).foldl (fun v i => mashSpec d k i v) v := by cases d <;> rfl
  simp only [he]
  apply foldWords_ok (step := fun k i v => mashSpec d k i v) _ _ _ s v hv readable
  intro i hi s v hv readable
  have bound : i < 4 := by
    cases d with
    | encrypt => exact List.mem_range.mp hi
    | decrypt =>
      simp only [order, List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
  apply WP.mono (mash_ok d s v hv i bound readable)
  exact fun _ h => ⟨h.1, h.2.round⟩

def roundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j : Nat)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  let v := match d with
    | .encrypt => Spec.Rc2.mixRound k j v
    | .decrypt => Spec.Rc2.reverseMixRound k (15 - j) v
  if j = 4 ∨ j = 10 then mashRoundSpec d k v else v

theorem round_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (j : Nat) (hj : j < 16)
    (readable : ScanMemory s) :
    WP isa (.block (round d j)) s (fun s' =>
      Words s' (roundSpec d (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j v) ∧
      Keep roundWrites s s') := by
  have finish (s₁ : State) (v₁ : Spec.Rc2.State) (h₁ : Words s₁ v₁ ∧ Keep roundWrites s s₁) :
      WP isa (.block (if j = 4 ∨ j = 10 then (order d).flatMap (mash d) else [])) s₁ (fun s₂ =>
        Words s₂ (if j = 4 ∨ j = 10 then mashRoundSpec d (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) v₁
          else v₁) ∧ Keep roundWrites s s₂) := by
    by_cases h : j = 4 ∨ j = 10
    · rw [ite_eq_left h]
      have ptr₁ := h₁.2.reg .rdi (by decide)
      have read₁ : ScanMemory s₁ := readable.keep h₁.2 (by decide) (by decide)
      apply WP.mono (mashRound_ok d s₁ v₁ h₁.1 read₁)
      intro s₂ h₂
      rw [h₁.2.mem, ptr₁] at h₂
      exact ⟨by simpa only [ite_eq_left h] using h₂.1, h₁.2.trans h₂.2⟩
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by simpa only [ite_eq_right h] using h₁.1, h₁.2⟩
  cases d with
  | encrypt =>
    rw [round, WP.block_append_iff]
    apply WP.mono (mixRound_ok s v hv j hj readable)
    intro s₁ h₁
    exact finish s₁ _ h₁
  | decrypt =>
    rw [round, WP.block_append_iff]
    apply WP.mono (reverseMixRound_ok s v hv (15 - j) (by omega) readable)
    intro s₁ h₁
    exact finish s₁ _ h₁

theorem rounds_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (readable : ScanMemory s) :
    WP isa (.block ((List.range 16).flatMap (round d))) s (fun s' =>
      Words s' ((List.range 16).foldl (fun v j => roundSpec d
        (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) j v) v) ∧ Keep roundWrites s s') := by
  apply foldWords_ok (step := fun k j v => roundSpec d k j v) _ _ _ s v hv readable
  intro j hj s v hv readable
  exact round_ok d s v hv j (List.mem_range.mp hj) readable

end VG.Proof.Rc2.X86_64

end

/-! # Loading and storing RC2 blocks -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

theorem unpackWord_ok (s : State) (i : Nat) (hi : i < 4) :
    ∃ s', runBlock isa (unpackWord i) s = some s' ∧
      s'.gpr (wordReg i) = (((s.gpr .rax) >>> (16 * i)).setWidth 16).setWidth 64 ∧
      Keep [wordReg i] s s' := by
  by_cases hz : i = 0
  · subst i
    refine ⟨_, by
      simp only [unpackWord, rr, ite_true, List.append_nil, List.cons_append, List.nil_append,
        runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
        Option.map_some, Option.bind_some, gpr_setReg, ite_true]
      rfl, ?_⟩
    constructor
    · simp only [gpr_setReg_self, Nat.mul_zero, BitVec.ushiftRight_zero]
      exact maskWord _
    · constructor
      · intro r hr
        simp only [List.mem_singleton] at hr
        simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]
      · simp only [mem_setReg, mem_arithFlags]
      · simp only [rd_setReg, rd_arithFlags]
      · simp only [wr_setReg, wr_arithFlags]
  · have hn : 1 ≤ 16 * i ∧ 16 * i ≤ 63 := by omega
    refine ⟨_, by
      simp only [unpackWord, rr, hz, ite_false, List.cons_append, List.nil_append,
        runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, readSrc,
        Option.map_some, Option.bind_some, gpr_setReg, gpr_setFlags, hn, and_self, ite_true]
      rfl, ?_⟩
    constructor
    · rw [gpr_setReg_self]
      exact maskWord _
    · constructor
      · intro r hr
        simp only [List.mem_singleton] at hr
        simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr, ite_false]
      · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
      · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
      · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem unpackWords_ok (is : List Nat) (hi : ∀ i ∈ is, i < 4) (s : State) :
    WP isa (.block (is.flatMap unpackWord)) s (fun s' =>
      (∀ i ∈ is, s'.gpr (wordReg i) = (((s.gpr .rax) >>> (16 * i)).setWidth 16).setWidth 64) ∧
      Keep (is.map wordReg) s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := unpackWord_ok s i (hi i (by simp))
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁)
    intro s₂ h₂
    have input₁ := keep₁.reg .rax (by
      simp only [List.mem_singleton]
      exact Ne.symm (wordReg_separate i).1)
    constructor
    · intro j hj
      rw [List.mem_cons] at hj
      by_cases hm : j ∈ is
      · rw [h₂.1 j hm, input₁]
      · have he : j = i := hj.resolve_right hm
        subst j
        rw [h₂.2.reg _ (by
          intro hm'
          obtain ⟨j, hj, he⟩ := List.mem_map.mp hm'
          have je := (wordReg_injective j (hi j (List.mem_cons_of_mem _ hj)) i (hi i (by simp))).mp he
          exact hm (je ▸ hj)), out₁]
    · apply (keep₁.weaken (fun r hr => ?_)).trans (h₂.2.weaken (fun r hr => ?_))
      · simp only [List.mem_singleton] at hr
        subst r; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hr

theorem blockLoad_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8) :
    WP isa (.block blockLoad) s (fun s' =>
      Words s' (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (s.gpr .rsi))) ∧
      Keep roundWrites s s') := by
  rw [blockLoad, WP.block_append_iff]
  let s₁ := s.setReg .rax (s.mem.readW (s.gpr .rsi) 64)
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · simp only [memOp, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load64, State.ea, offset_nat, BitVec.add_zero, readable, ite_true,
      Option.map_some]
    rfl
  apply WP.mono (unpackWords_ok (List.range 4) (fun i hi => List.mem_range.mp hi) s₁)
  intro s₂ h₂
  constructor
  · intro i hi
    rw [h₂.1 i (List.mem_range.mpr hi), decode_read64 _ _ i hi]
    rfl
  · have keep₁ : Keep roundWrites s s₁ := by
      constructor
      · intro r hr
        exact gpr_setReg_of_ne _ _ (fun he => hr (he ▸ (by decide)))
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _
    apply keep₁.trans
    exact h₂.2.weaken (by
      intro r hr
      obtain ⟨i, _, he⟩ := List.mem_map.mp hr
      subst r; exact wordReg_mem_roundWrites i)

theorem packWord_ok (s : State) (i : Nat) (hi : 1 ≤ i) (hi' : i < 4) :
    ∃ s', runBlock isa (packWord i) s = some s' ∧
      s'.gpr .rax = s.gpr .rax ||| (s.gpr (wordReg i)).rotateRight (64 - 16 * i) ∧
      Keep [.rax, .rcx] s s' := by
  have hn : 1 ≤ 64 - 16 * i ∧ 64 - 16 * i ≤ 63 := by omega
  refine ⟨_, by
    simp only [packWord, rr, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      execShift, readSrc, Option.map_some, Option.bind_some, gpr_setReg, gpr_setFlags,
      hn, and_self, reduceCtorEq, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem packWords_ok (is : List Nat) (hi : ∀ i ∈ is, 1 ≤ i ∧ i < 4)
    (s : State) (v : Spec.Rc2.State) (hv : Words s v) :
    WP isa (.block (is.flatMap packWord)) s (fun s' =>
      s'.gpr .rax = is.foldl (fun acc i => acc |||
        ((v.getD i 0).setWidth 64).rotateRight (64 - 16 * i)) (s.gpr .rax) ∧
      Keep [.rax, .rcx] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    have bound := hi i (by simp)
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := packWord_ok s i bound.1 bound.2
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have keepTemps : Keep temps s s₁ := keep₁.weaken (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h <;> subst r <;> decide)
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ (hv.preserve keepTemps))
    intro s₂ h₂
    refine ⟨?_, keep₁.trans h₂.2⟩
    rw [h₂.1, out₁, hv i bound.2]
    rfl

/-- The block store changes exactly the data word, plus two caller-saved
registers; it leaves all memory-access permissions unchanged. -/
theorem blockStore_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (writable : InRegions s.wr (s.gpr .rsi) 8) :
    WP isa (.block blockStore) s (fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rsi) (pack v) ∧
      (∀ r, r ∉ [.rax, .rcx] → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr) := by
  rw [blockStore, List.append_assoc, WP.block_append_iff]
  let s₁ := s.setReg .rax (s.gpr (wordReg 0))
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
    rfl
  rw [WP.block_append_iff]
  have keep₁ : Keep [.rax, .rcx] s s₁ := by
    constructor
    · intro r hr
      exact gpr_setReg_of_ne _ _ (fun he => hr (he ▸ List.mem_cons_self))
    · exact mem_setReg _ _ _
    · exact rd_setReg _ _ _
    · exact wr_setReg _ _ _
  have keepTemps : Keep temps s s₁ := keep₁.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h <;> subst r <;> decide)
  apply WP.mono (packWords_ok [1, 2, 3] (by decide) s₁ v (hv.preserve keepTemps))
  intro s₂ h₂
  have keep := keep₁.trans h₂.2
  have ptr₂ := keep.reg .rsi (by decide)
  have out₂ : s₂.gpr .rax = pack v := by
    rw [h₂.1]
    change ((s.gpr (wordReg 0) ||| ((v.getD 1 0).setWidth 64).rotateRight 48) |||
      ((v.getD 2 0).setWidth 64).rotateRight 32) |||
      ((v.getD 3 0).setWidth 64).rotateRight 16 = _
    rw [hv 0 (by decide)]
    exact (pack_eq v).symm
  refine WP.of_runBlock ⟨{s₂ with mem := s₂.mem.writeW (s₂.gpr .rsi) (s₂.gpr .rax)}, ?_, ?_⟩
  · have valid : InRegions s₂.wr (s₂.gpr .rsi) 8 := by rw [keep.wr, ptr₂]; exact writable
    simp only [memOp, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
      State.ea, offset_nat, BitVec.add_zero, valid, ite_true]
  · exact ⟨by rw [keep.mem, ptr₂, out₂], keep.reg, keep.rd, keep.wr⟩

end VG.Proof.Rc2.X86_64

end

/-! # Saving and restoring RC2's callee-saved registers in scratch -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

def saveMem (m : Mem) (p : Addr) (v : Nat → BitVec 64) (n : Nat) : Mem :=
  (List.range n).foldl (fun m i => m.writeW (p + BitVec.ofNat 64 (8 * i)) (v i)) m

theorem saveMem_succ (m : Mem) (p : Addr) (v : Nat → BitVec 64) (n : Nat) :
    saveMem m p v (n + 1) = (saveMem m p v n).writeW (p + BitVec.ofNat 64 (8 * n)) (v n) := by
  simp only [saveMem, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem saveMem_read (m : Mem) (p : Addr) (v : Nat → BitVec 64) (n : Nat) (hn : n ≤ 64)
    (i : Nat) (hi : i < n) : (saveMem m p v n).readW (p + BitVec.ofNat 64 (8 * i)) 64 = v i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [saveMem_succ]
    by_cases he : i = n
    · subst i; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)]
      exact ih (by omega) (by omega)

theorem saveMem_frame (m : Mem) (p : Addr) (v : Nat → BitVec 64) (n : Nat) (hn : n ≤ 64) :
    Frame [⟨p, 8 * n⟩] m (saveMem m p v n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    rw [saveMem_succ]
    have prev : Frame [⟨p, 8 * (n + 1)⟩] m (saveMem m p v n) := by
      apply (ih (by omega)).sub
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      refine ⟨⟨p, 8 * (n + 1)⟩, List.mem_cons_self, ?_⟩
      intro x hx
      change (x - p).toNat + 1 ≤ 8 * n at hx
      change (x - p).toNat + 1 ≤ 8 * (n + 1)
      omega
    exact prev.writeW List.mem_cons_self _ (Offset.contains_base p (by omega) (by omega))

def saveCode (base : Reg) (regs : Nat → Reg) (n : Nat) : List Instr :=
  (List.range n).map fun i => .store (memOp base (8 * i)) (regs i)

theorem saveCode_ok (s : State) (base : Reg) (regs : Nat → Reg) (n : Nat)
    (writable : ∀ i < n, InRegions s.wr (s.gpr base + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block (saveCode base regs n)) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = saveMem s.mem (s.gpr base) (fun i => s.gpr (regs i)) n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [saveCode, List.range_succ, List.map_append, List.map_cons, List.map_nil, WP.block_append_iff]
    apply WP.mono (ih (fun i hi => writable i (by omega)))
    intro s₁ h₁
    have valid := writable n (by omega)
    have valid₁ : InRegions s₁.wr (s₁.gpr base + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [h₁.1, h₁.2.2.1]; exact valid
    refine WP.of_runBlock ⟨{s₁ with mem := s₁.mem.writeW (s₁.gpr base + BitVec.ofNat 64 (8 * n)) (s₁.gpr (regs n))}, ?_, ?_⟩
    · simp only [memOp, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
        State.ea, offset_nat, valid₁, ite_true]
    · exact ⟨h₁.1, h₁.2.1, h₁.2.2.1, by rw [h₁.2.2.2, h₁.1, saveMem_succ]⟩

def restoreCode (base : Reg) (regs : Nat → Reg) (is : List Nat) : List Instr :=
  is.map fun i => .mov (regs i) (.mem (memOp base (8 * i)))

theorem restoreCode_ok (s : State) (base : Reg) (regs : Nat → Reg) (is : List Nat)
    (values : Reg → BitVec 64)
    (separate : ∀ i ∈ is, regs i ≠ base)
    (readable : ∀ i ∈ is, InRegions (s.rd ++ s.wr) (s.gpr base + BitVec.ofNat 64 (8 * i)) 8)
    (stored : ∀ i ∈ is, s.mem.readW (s.gpr base + BitVec.ofNat 64 (8 * i)) 64 = values (regs i)) :
    WP isa (.block (restoreCode base regs is)) s (fun s' =>
      (∀ r ∈ is.map regs, s'.gpr r = values r) ∧ Keep (is.map regs) s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    change WP isa (.block (([.mov (regs i) (.mem (memOp base (8 * i)))] : List Instr) ++ restoreCode base regs is)) s _
    rw [WP.block_append_iff]
    let s₁ := s.setReg (regs i) (values (regs i))
    have hi : i ∈ i :: is := List.mem_cons_self
    refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
    · simp only [memOp, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
        State.ea, offset_nat, readable i hi, ite_true, Option.map_some, stored i hi]
      rfl
    have keep₁ : Keep [regs i] s s₁ := by
      constructor
      · intro r hr
        simp only [List.mem_singleton] at hr
        exact gpr_setReg_of_ne _ _ hr
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _
    have ptr₁ := keep₁.reg base (by
      simp only [List.mem_singleton]; exact Ne.symm (separate i hi))
    have read₁ : ∀ j ∈ is,
        InRegions (s₁.rd ++ s₁.wr) (s₁.gpr base + BitVec.ofNat 64 (8 * j)) 8 := by
      rw [keep₁.rd, keep₁.wr, ptr₁]
      exact fun j hj => readable j (List.mem_cons_of_mem _ hj)
    have stored₁ : ∀ j ∈ is,
        s₁.mem.readW (s₁.gpr base + BitVec.ofNat 64 (8 * j)) 64 = values (regs j) := by
      rw [keep₁.mem, ptr₁]
      exact fun j hj => stored j (List.mem_cons_of_mem _ hj)
    apply WP.mono (ih s₁ (fun j hj => separate j (List.mem_cons_of_mem _ hj)) read₁ stored₁)
    intro s₂ h₂
    constructor
    · intro r hr
      simp only [List.map_cons, List.mem_cons] at hr
      by_cases hm : r ∈ is.map regs
      · exact h₂.1 r hm
      · have he := hr.resolve_right hm
        subst r
        rw [h₂.2.reg _ hm]
        exact gpr_setReg_self _ _ _
    · apply (keep₁.weaken (fun r hr => ?_)).trans (h₂.2.weaken (fun r hr => ?_))
      · simp only [List.mem_singleton] at hr
        subst r; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hr

theorem saveMem_frame_le (m : Mem) (p : Addr) (v : Nat → BitVec 64)
    (n capacity : Nat) (hn : n ≤ capacity) (hc : capacity ≤ 64) :
    Frame [⟨p, 8 * capacity⟩] m (saveMem m p v n) := by
  apply (saveMem_frame m p v n (by omega)).sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  refine ⟨⟨p, 8 * capacity⟩, List.mem_cons_self, ?_⟩
  intro x hx
  change (x - p).toNat + 1 ≤ 8 * n at hx
  change (x - p).toNat + 1 ≤ 8 * capacity
  omega

end VG.Proof.Rc2.X86_64
