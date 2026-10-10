import VerifiedGarbage.Proof.TripleDes.X86.Key.Permutation
import VerifiedGarbage.Proof.TripleDes.X86.Bytes
import VerifiedGarbage.Proof.TripleDes.X86.RoundStep
import VerifiedGarbage.Proof.Rc2.X86.RoundSteps
import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
import VerifiedGarbage.Proof.TripleDes.X86.WordStore
import VerifiedGarbage.Proof.TripleDes.X86.Word
import VerifiedGarbage.Proof.TripleDes.X86.Key.Compare
import VerifiedGarbage.Proof.TripleDes.Schedule

/-! ## `Load` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep)

def keyArg (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esp) 1) 32

def scheduleArg (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esp) 3) 32

def keyAddr (s : State) (offset : Nat) : BitVec 64 :=
  (keyArg s + BitVec.ofNat 32 offset).setWidth 64

theorem readKey_ok (s : State) (offset : Nat)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 1) 4)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr) (keyAddr s (offset + 4 * t)) 4) :
    ∃ s', runBlock isa (Impl.TripleDes.X86.Key.loadHead offset) s = some s' ∧
      s'.gpr .edi = bswap (s.mem.readW (keyAddr s offset) 32) ∧
      s'.gpr .esi = bswap (s.mem.readW (keyAddr s (offset + 4)) 32) ∧
      Keep [.edi, .esi, .edx] s s' := by
  have h0 := hr 0 (by decide)
  have h1 := hr 1 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, keyAddr, keyArg, wordAddr, addr] at h0
  simp only [Nat.mul_one, keyAddr, keyArg, wordAddr, addr] at h1
  simp only [wordAddr, addr] at harg
  refine ⟨_, by
    simp only [Impl.TripleDes.X86.Key.loadHead, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, State.load32, State.ea, memOp, harg, h0, h1, ite_true,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg,
      wr_setReg, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]

def loadMem (s : State) (component : Nat) : Mem :=
  (s.mem.writeW (wordAddr (s.gpr .ebp) 5) (0 : BitVec 32)).writeW
    (wordAddr (s.gpr .ebp) 4) (scheduleArg s + BitVec.ofNat 32 (128 * component))

theorem loadTail_ok (s : State) (component : Nat) (hok : Ok sboxCfg s)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 3) 4) :
    ∃ s', runBlock isa (Impl.TripleDes.X86.Key.loadTail component) s = some s' ∧
      s'.gpr .esi = s.gpr .ebx ∧ s'.gpr .edi = s.gpr .eax ∧
      s'.mem = loadMem s component ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → r ≠ .edx → r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r) := by
  have hw4 := hok.slotIn 4 (by decide)
  have hw5 := hok.slotIn 5 (by decide)
  simp only [wordAddr, addr, sboxCfg] at hw4 hw5
  simp only [wordAddr, addr] at hr
  refine ⟨_, by
    simp only [Impl.TripleDes.X86.Key.loadTail, rr, imm, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, State.load32, State.store32, State.ea,
      memOp, hw4, hw5, hr, ite_true, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags,
      wr_setReg, wr_arithFlags, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r ha hd hs hi
    simp only [gpr_setReg, gpr_arithFlags, ha, hd, hs, hi, ite_false]

structure LoadPost (x : BitVec 56) (component : Nat) (s s' : State) : Prop where
  c : s'.gpr .esi = ((x >>> 28).setWidth 28).setWidth 32
  d : s'.gpr .edi = (x.setWidth 28).setWidth 32
  counter : roundCount s' = 0
  ptr : roundKeyPtr s' = scheduleArg s + BitVec.ofNat 32 (128 * component)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  base : s'.gpr .ebp = s.gpr .ebp
  sp : s'.gpr .esp = s.gpr .esp
  frame : Frame [workRegion s] s.mem s'.mem

theorem loadMem_frame (s : State) (component : Nat)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) :
    Frame [workRegion s] s.mem (loadMem s component) := by
  have h4 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 4) 4 := by
    change (workRegion s).Contains (addr (s.gpr .ebp) 16) 4
    rw [addr_eq (by omega)]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  have h5 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 5) 4 := by
    change (workRegion s).Contains (addr (s.gpr .ebp) 20) 4
    rw [addr_eq (by omega)]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  exact ((Frame.refl [workRegion s] s.mem).writeW (List.mem_singleton_self _) _ h5).writeW
    (List.mem_singleton_self _) _ h4

theorem load_ok (s : State) (offset component : Nat) (hok : Ok sboxCfg s)
    (fit : (keyArg s).toNat + offset + 8 ≤ 2 ^ 32)
    (harg : ∀ i ∈ [1, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr) (keyAddr s (offset + 4 * t)) 4) :
    WP isa (.block (Impl.TripleDes.X86.Key.load offset component)) s
      (LoadPost (Spec.TripleDes.permute Spec.TripleDes.pc1 (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (keyAddr s offset)))) component s) := by
  rw [Impl.TripleDes.X86.Key.load, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, hi₁, lo₁, keep₁⟩ := readKey_ok s offset (harg 1 (by decide)) hr
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, lo₂, hi₂, rd₂, wr₂, sp₂, mem₂, reg₂⟩ := pc1_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have key₁ : packedInput 64 32 (s₁.gpr .esi) (s₁.gpr .edi) =
      Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (keyAddr s offset)) := by
    rw [packedInput, lo₁, hi₁, decodeBlock_readW]
    simp only [BitVec.setWidth_eq]
    have ha : keyAddr s (offset + 4) = keyAddr s offset + 4 := by
      change VG.Proof.Rc2.X86.addr32 (keyArg s + BitVec.ofNat 32 (offset + 4)) =
        VG.Proof.Rc2.X86.addr32 (keyArg s + BitVec.ofNat 32 offset) + 4
      rw [VG.Proof.Rc2.X86.addr_add (by omega), VG.Proof.Rc2.X86.addr_add (by omega)]
      rw [← VG.Offset.add_ofNat_add_ofNat]
      rfl
    rw [ha]
  rw [key₁] at lo₂ hi₂
  have base₂ : s₂.gpr .ebp = s.gpr .ebp :=
    (reg₂ .ebp (by decide +kernel)).trans (keep₁.reg .ebp (by decide))
  have sp₂' : s₂.gpr .esp = s.gpr .esp := sp₂.trans (keep₁.reg .esp (by decide))
  have hok₂ : Ok sboxCfg s₂ := hok.congr base₂ base₂ (rd₂.trans keep₁.rd) (wr₂.trans keep₁.wr)
  have hr₂ : InRegions (s₂.rd ++ s₂.wr) (wordAddr (s₂.gpr .esp) 3) 4 := by
    rw [sp₂', rd₂, wr₂, keep₁.rd, keep₁.wr]
    exact harg 3 (by decide)
  obtain ⟨s₃, run₃, c₃, d₃, mem₃, rd₃, wr₃, reg₃⟩ := loadTail_ok s₂ component hok₂ hr₂
  have base₃ : s₃.gpr .ebp = s.gpr .ebp := (reg₃ .ebp (by decide) (by decide)
    (by decide) (by decide)).trans base₂
  have sp₃ : s₃.gpr .esp = s.gpr .esp := (reg₃ .esp (by decide) (by decide)
    (by decide) (by decide)).trans sp₂'
  have sched₂ : scheduleArg s₂ = scheduleArg s := by
    unfold scheduleArg
    rw [sp₂', mem₂, keep₁.mem]
  have hm : s₃.mem = loadMem s component := by
    rw [mem₃, loadMem, base₂, sched₂, mem₂, keep₁.mem]
    rfl
  refine WP.of_runBlock ⟨s₃, run₃, ⟨c₃.trans hi₂, d₃.trans lo₂, ?_, ?_,
    rd₃.trans (rd₂.trans keep₁.rd), wr₃.trans (wr₂.trans keep₁.wr), base₃, sp₃, ?_⟩⟩
  · unfold roundCount
    rw [base₃, hm, loadMem, Mem.readW_writeW_sep (counter_ptr_sep s hok.fit) (by decide),
      Mem.readW_writeW_self32]
  · unfold roundKeyPtr
    rw [base₃, hm, loadMem, Mem.readW_writeW_self32]
  · rw [hm]
    exact loadMem_frame s component hok.fit

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Store` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86

def storeMem (s : State) : Mem :=
  (((s.mem.writeW (wordAddr (roundKeyPtr s) 0) (s.gpr .eax)).writeW
    (wordAddr (roundKeyPtr s) 1) (s.gpr .ebx)).writeW
    (wordAddr (s.gpr .ebp) 4) (roundKeyPtr s + 8)).writeW
    (wordAddr (s.gpr .ebp) 5) (roundCount s + 1)

theorem nextRound_values : ∀ j < 16,
    BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) ∧
    (!(BitVec.ofNat 32 j + 1 - (16 : BitVec 32) == 0)) = decide (j ≠ 15) := by decide

theorem tail_ok (s : State) (hok : Ok sboxCfg s)
    (hw : ∀ t < 2, InRegions s.wr (wordAddr (roundKeyPtr s) t) 4)
    :
    ∃ s', runBlock isa Impl.TripleDes.X86.Key.storeTail s = some s' ∧
      s'.mem = storeMem s ∧ s'.zf = some ((roundCount s + 1 - 16) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) := by
  have hw4 := hok.slotIn 4 (by decide)
  have hw5 := hok.slotIn 5 (by decide)
  have hr4 : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 4) 4 := by
    obtain ⟨r, h, hc⟩ := hw4; exact ⟨r, List.mem_append_right _ h, hc⟩
  have hr5 : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 5) 4 := by
    obtain ⟨r, h, hc⟩ := hw5; exact ⟨r, List.mem_append_right _ h, hc⟩
  have hw0 := hw 0 (by decide)
  have hw1 := hw 1 (by decide)
  simp only [wordAddr, addr, sboxCfg, roundKeyPtr] at hw4 hw5 hr4 hr5 hw0 hw1
  refine ⟨_, by
    simp only [Impl.TripleDes.X86.Key.storeTail, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.load32, State.store32, State.ea, memOp,
      hw4, hw5, hr4, hr5, hw0, hw1, ite_true, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only [mem_setReg, mem_arithFlags, storeMem, roundKeyPtr, roundCount,
    wordAddr, addr, gpr_setReg, gpr_arithFlags, rd_setReg, wr_setReg,
    rd_arithFlags, wr_arithFlags, zf_setReg, zf_arithFlags]
  all_goals try rfl
  all_goals
    intro r hc hd
    simp only [hc, hd, ite_false]

def keyStoreMem (s : State) (k : BitVec 64) : Mem :=
  ((s.mem.writeW (wordAddr (roundKeyPtr s) 0) k).writeW
    (wordAddr (s.gpr .ebp) 4) (roundKeyPtr s + 8)).writeW
    (wordAddr (s.gpr .ebp) 5) (roundCount s + 1)

structure StorePost (c d : BitVec 28) (j : Nat) (s s' : State) : Prop where
  mem : s'.mem = keyStoreMem s ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64)
  ptr : roundKeyPtr s' = roundKeyPtr s + 8
  counter : roundCount s' = BitVec.ofNat 32 (j + 1)
  flag : isa.eval .ne s' = some (decide (j ≠ 15))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp], s'.gpr r = s.gpr r

theorem storeRound_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .esi = c.setWidth 32) (hd : s.gpr .edi = d.setWidth 32)
    (hcount : roundCount s = BitVec.ofNat 32 j) (hok : Ok sboxCfg s)
    (fit : (roundKeyPtr s).toNat + 8 ≤ 2 ^ 32)
    (hw : ∀ t < 2, InRegions s.wr (wordAddr (roundKeyPtr s) t) 4)
    :
    WP isa (.block Impl.TripleDes.X86.Key.storeRound) s (StorePost c d j s) := by
  rw [Impl.TripleDes.X86.Key.storeRound, WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, rd₁, wr₁, sp₁, mem₁, reg₁⟩ := pc2_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have input : packedInput 56 28 (s.gpr .edi) (s.gpr .esi) = c ++ d := by
    rw [hd, hc]; exact packed28 c d
  rw [input] at lo₁ hi₁
  have checks : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp],
      ((instrs keyPermutation2.lit).all fun op => op.dst != some r) = true := by decide +kernel
  have keep₁ : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp], s₁.gpr r = s.gpr r :=
    fun r hr => reg₁ r (checks r hr)
  have base₁ := keep₁ .ebp (by decide)
  have ptr₁ : roundKeyPtr s₁ = roundKeyPtr s := by unfold roundKeyPtr; rw [base₁, mem₁]
  have count₁ : roundCount s₁ = roundCount s := by unfold roundCount; rw [base₁, mem₁]
  have hok₁ : Ok sboxCfg s₁ := hok.congr base₁ base₁ rd₁ wr₁
  have hw₁ : ∀ t < 2, InRegions s₁.wr (wordAddr (roundKeyPtr s₁) t) 4 := by
    rw [wr₁, ptr₁]; exact hw
  obtain ⟨s₂, run₂, mem₂, flag₂, rd₂, wr₂, reg₂⟩ := tail_ok s₁ hok₁ hw₁
  have regs : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp], s₂.gpr r = s.gpr r := by
    intro r hr
    have diffs : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp], r ≠ .ecx ∧ r ≠ .edx := by decide
    exact (reg₂ r (diffs r hr).1 (diffs r hr).2).trans (keep₁ r hr)
  have hm : s₂.mem = keyStoreMem s ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64) := by
    rw [mem₂, storeMem, ptr₁, count₁, base₁, mem₁, lo₁, hi₁, BitVec.setWidth_eq]
    have ha : wordAddr (roundKeyPtr s) 1 = wordAddr (roundKeyPtr s) 0 + 4 := by
      rw [show wordAddr (roundKeyPtr s) 0 = (roundKeyPtr s).setWidth 64 from by
        simp [wordAddr, addr]]
      exact VG.X86.addr_eq (x := roundKeyPtr s) (k := 4) (by omega)
    rw [ha, writeW_pair, packed48]
    rfl
  refine WP.of_runBlock ⟨s₂, run₂, ⟨hm, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, regs⟩⟩
  · unfold roundKeyPtr
    rw [regs .ebp (by decide), hm, keyStoreMem,
      Mem.readW_writeW_sep (fun a h4 h5 => counter_ptr_sep s hok.fit a h5 h4) (by decide),
      Mem.readW_writeW_self32]
    rfl
  · unfold roundCount
    rw [regs .ebp (by decide), hm, keyStoreMem, Mem.readW_writeW_self32, hcount]
    exact (nextRound_values j hj).1
  · change s₂.zf.map (!·) = _
    rw [flag₂, count₁, hcount, Option.map_some]
    exact congrArg some (nextRound_values j hj).2

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Memory` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight
open VG.Proof.Rc2.X86 (addr32)

def scheduleRegion (base : BitVec 32) : Region := ⟨addr32 base, 128⟩

theorem pointer_fit (base : BitVec 32) (fit : base.toNat + 128 ≤ 2 ^ 32)
    (j : Nat) (hj : j < 16) : (base + BitVec.ofNat 32 (8 * j)).toNat + 8 ≤ 2 ^ 32 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 8 * j < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : base.toNat + 8 * j < 2 ^ 32)]
  omega

theorem schedule_contains (base : BitVec 32) (j : Nat) (hj : j < 16) :
    (scheduleRegion base).Contains (addr32 base + BitVec.ofNat 64 (8 * j)) 8 :=
  Offset.contains_base _ (by omega) (by omega)

theorem work_slot (s : State) (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (k : Nat) (hk : k = 4 ∨ k = 5) :
    (workRegion s).Contains (wordAddr (s.gpr .ebp) k) 4 := by
  change (workRegion s).Contains (addr (s.gpr .ebp) (4 * k)) 4
  rw [addr_eq (by omega)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem keyStore_read (s : State) (k : BitVec 64) (p : Addr)
    (hsep : ∀ j ∈ [4, 5], Mem.Sep p 8 (wordAddr (s.gpr .ebp) j) 4) :
    (keyStoreMem s k).readW p 64 = (s.mem.writeW (wordAddr (roundKeyPtr s) 0) k).readW p 64 := by
  rw [keyStoreMem, Mem.readW_writeW_sep (hsep 5 (by decide)) (by decide),
    Mem.readW_writeW_sep (hsep 4 (by decide)) (by decide)]

theorem keyStore_frame (s : State) (base : BitVec 32) (j : Nat) (hj : j < 16)
    (fit : base.toNat + 128 ≤ 2 ^ 32) (scratchFit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (ptr : roundKeyPtr s = base + BitVec.ofNat 32 (8 * j)) (k : BitVec 64) :
    Frame [scheduleRegion base, workRegion s] s.mem (keyStoreMem s k) := by
  have hc : (scheduleRegion base).Contains (wordAddr (roundKeyPtr s) 0) 8 := by
    rw [ptr]
    have ha : wordAddr (base + BitVec.ofNat 32 (8 * j)) 0 =
        addr32 base + BitVec.ofNat 64 (8 * j) := by
      simpa [wordAddr, addr, addr32] using
        (VG.Proof.Rc2.X86.addr_add (x := base) (k := 8 * j) (by omega))
    rw [ha]
    exact schedule_contains base j hj
  exact (((Frame.refl _ _).writeW (by simp) k hc).writeW (by simp) _
    (work_slot s scratchFit 4 (Or.inl rfl))).writeW (by simp) _
    (work_slot s scratchFit 5 (Or.inr rfl))

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Loop` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)
open VG.Proof.TripleDes (keyPrefix keyInitial keyStep keyPrefix_succ)

structure LoopState (key : BitVec 64) (base : BitVec 32) (origin : State) (j : Nat) (s : State) : Prop where
  c : s.gpr .esi = (keyPrefix key j).1.setWidth 32
  d : s.gpr .edi = (keyPrefix key j).2.1.setWidth 32
  counter : roundCount s = BitVec.ofNat 32 j
  pointer : roundKeyPtr s = base + BitVec.ofNat 32 (8 * j)
  keys : ∀ i < j, ∀ hi : i < 16, s.mem.readW (addr32 base + BitVec.ofNat 64 (8 * i)) 64 =
    ((keyPrefix key j).2.2[i]'hi).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  bp : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  frame : Frame [scheduleRegion base, workRegion origin] origin.mem s.mem

def LoopInv (key : BitVec 64) (base : BitVec 32) (origin : State) (n : Nat) (s : State) : Prop :=
  1 ≤ n ∧ n ≤ 16 ∧ LoopState key base origin (16 - n) s

theorem keyWordAddr (base : BitVec 32) (fit : base.toNat + 128 ≤ 2 ^ 32)
    (j t : Nat) (hj : j < 16) (ht : t < 2) :
    wordAddr (base + BitVec.ofNat 32 (8 * j)) t =
      addr32 base + BitVec.ofNat 64 (8 * j + 4 * t) := by
  change addr (base + BitVec.ofNat 32 (8 * j)) (4 * t) = _
  rw [addr_eq (by have h := pointer_fit base fit j hj; omega)]
  change addr32 (base + BitVec.ofNat 32 (8 * j)) + BitVec.ofNat 64 (4 * t) = _
  rw [VG.Proof.Rc2.X86.addr_add (x := base) (k := 8 * j) (by omega), Offset.add_ofNat_add_ofNat]

theorem loopBody_ok (key : BitVec 64) (base : BitVec 32) (origin : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32) (hok : Ok sboxCfg origin)
    (hw : ∀ j < 16, ∀ t < 2, InRegions origin.wr
      (addr32 base + BitVec.ofNat 64 (8 * j + 4 * t)) 4)
    (hdis : (scheduleRegion base).Disjoint (workRegion origin))
    (j : Nat) (hj : j < 16) (s : State) (hs : LoopState key base origin j s) :
    WP isa (.seq Impl.TripleDes.X86.Key.rotation (.block Impl.TripleDes.X86.Key.storeRound)) s
      (fun s' => isa.eval .ne s' = some (decide (j ≠ 15)) ∧ LoopState key base origin (j + 1) s') := by
  have hoks : Ok sboxCfg s := hok.congr hs.bp hs.bp hs.rd hs.wr
  apply WP.seq
  apply WP.mono (rotation_ok s _ _ j hj hs.c hs.d hs.counter hoks)
  intro s₁ h₁
  have bp₁ : s₁.gpr .ebp = origin.gpr .ebp := (h₁.keep.reg .ebp (by decide)).trans hs.bp
  have sp₁ : s₁.gpr .esp = origin.gpr .esp := (h₁.keep.reg .esp (by decide)).trans hs.sp
  have ptr₁ : roundKeyPtr s₁ = roundKeyPtr s := by
    unfold roundKeyPtr
    rw [h₁.keep.reg .ebp (by decide), h₁.keep.mem]
  have count₁ : roundCount s₁ = roundCount s := by
    unfold roundCount
    rw [h₁.keep.reg .ebp (by decide), h₁.keep.mem]
  have hok₁ : Ok sboxCfg s₁ := hok.congr bp₁ bp₁ (h₁.keep.rd.trans hs.rd) (h₁.keep.wr.trans hs.wr)
  have fit₁ : (roundKeyPtr s₁).toNat + 8 ≤ 2 ^ 32 := by
    rw [ptr₁, hs.pointer]; exact pointer_fit base fit j hj
  have write₁ : ∀ t < 2, InRegions s₁.wr (wordAddr (roundKeyPtr s₁) t) 4 := by
    intro t ht
    rw [h₁.keep.wr, hs.wr, ptr₁, hs.pointer, keyWordAddr base fit j t hj ht]
    exact hw j hj t ht
  apply WP.mono (storeRound_ok s₁ _ _ j hj h₁.c h₁.d (count₁.trans hs.counter) hok₁ fit₁ write₁)
  intro s₂ h₂
  let k := (Spec.TripleDes.permute Spec.TripleDes.pc2
    ((keyPrefix key j).1.rotateLeft (Spec.TripleDes.rotations.getD j 0) ++
      (keyPrefix key j).2.1.rotateLeft (Spec.TripleDes.rotations.getD j 0))).setWidth 64
  have addr₁ : wordAddr (roundKeyPtr s₁) 0 = addr32 base + BitVec.ofNat 64 (8 * j) := by
    rw [ptr₁, hs.pointer, keyWordAddr base fit j 0 hj (by decide)]
    simp only [Nat.mul_zero, Nat.add_zero]
  have hm : s₂.mem = ((s.mem.writeW (addr32 base + BitVec.ofNat 64 (8 * j)) k).writeW
      (wordAddr (origin.gpr .ebp) 4) (base + BitVec.ofNat 32 (8 * j) + 8)).writeW
      (wordAddr (origin.gpr .ebp) 5) (BitVec.ofNat 32 j + 1) := by
    rw [h₂.mem, keyStoreMem, addr₁, ptr₁, hs.pointer, count₁, hs.counter, bp₁, h₁.keep.mem]
  refine ⟨h₂.flag, ⟨?_, ?_, h₂.counter, ?_, ?_, h₂.rd.trans (h₁.keep.rd.trans hs.rd),
    h₂.wr.trans (h₁.keep.wr.trans hs.wr), (h₂.reg .ebp (by decide)).trans bp₁,
    (h₂.reg .esp (by decide)).trans sp₁, ?_⟩⟩
  · rw [keyPrefix_succ]
    exact (h₂.reg .esi (by decide)).trans h₁.c
  · rw [keyPrefix_succ]
    exact (h₂.reg .edi (by decide)).trans h₁.d
  · rw [h₂.ptr, ptr₁, hs.pointer]
    change base + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 8 = _
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega)
  · intro i hi hi16
    have hsep (t : Nat) (ht : t = 4 ∨ t = 5) :
        Mem.Sep (addr32 base + BitVec.ofNat 64 (8 * i)) 8 (wordAddr (origin.gpr .ebp) t) 4 :=
      hdis.sep (schedule_contains base i hi16) (work_slot origin hok.fit t ht)
    rw [hm, Mem.readW_writeW_sep (hsep 5 (Or.inr rfl)) (by decide),
      Mem.readW_writeW_sep (hsep 4 (Or.inl rfl)) (by decide), keyPrefix_succ]
    by_cases he : i = j
    · subst i
      rw [Mem.readW_writeW_self64]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_self hj).symm
    · rw [Mem.readW_writeW_sep (Offset.sep (addr32 base) (by omega) (by omega)
        (by omega)) (by decide), hs.keys i (by omega) hi16]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_ne hi16 (Ne.symm he)).symm
  · have fr := keyStore_frame s₁ base j hj fit hok₁.fit (ptr₁.trans hs.pointer) k
    rw [← h₂.mem] at fr
    have hreg : workRegion s₁ = workRegion origin := by unfold workRegion; rw [bp₁]
    rw [hreg, h₁.keep.mem] at fr
    exact hs.frame.trans fr

theorem loopStep (key : BitVec 64) (base : BitVec 32) (origin : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32) (hok : Ok sboxCfg origin)
    (hw : ∀ j < 16, ∀ t < 2, InRegions origin.wr
      (addr32 base + BitVec.ofNat 64 (8 * j + 4 * t)) 4)
    (hdis : (scheduleRegion base).Disjoint (workRegion origin))
    (n : Nat) (s : State) (hs : LoopInv key base origin n s) :
    WP isa (.seq Impl.TripleDes.X86.Key.rotation (.block Impl.TripleDes.X86.Key.storeRound)) s
      (fun s' => (isa.eval .ne s' = some false ∧ LoopState key base origin 16 s') ∨
        (isa.eval .ne s' = some true ∧ ∃ m < n, LoopInv key base origin m s')) := by
  apply WP.mono (loopBody_ok key base origin fit hok hw hdis (16 - n) (by omega_using [hs.1]) s hs.2.2)
  intro s' h
  by_cases last : n = 1
  · left
    have idx : 16 - n = 15 := by omega_using [last]
    refine ⟨?_, ?_⟩
    · simpa only [idx, ne_eq, not_true_eq_false, decide_false] using h.1
    · simpa only [idx] using h.2
  · right
    have idx : ¬16 - n = 15 := by omega_using [hs.1, hs.2.1, last]
    refine ⟨?_, n - 1, by omega_using [hs.1], ?_⟩
    · simpa only [idx, ne_eq, not_false_eq_true, decide_true] using h.1
    · refine ⟨by omega_using [hs.1, last], by omega_using [hs.2.1], ?_⟩
      have eq : 16 - n + 1 = 16 - (n - 1) := by omega_using [hs.1, hs.2.1]
      rw [← eq]
      exact h.2

theorem loop_ok (key : BitVec 64) (base : BitVec 32) (s : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32) (hok : Ok sboxCfg s)
    (hw : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (addr32 base + BitVec.ofNat 64 (8 * j + 4 * t)) 4)
    (hdis : (scheduleRegion base).Disjoint (workRegion s))
    (hc : s.gpr .esi = (keyInitial key).1.setWidth 32)
    (hd : s.gpr .edi = (keyInitial key).2.1.setWidth 32)
    (hcount : roundCount s = 0) (hptr : roundKeyPtr s = base) :
    WP isa (.loop (.seq Impl.TripleDes.X86.Key.rotation
      (.block Impl.TripleDes.X86.Key.storeRound)) .ne) s (LoopState key base s 16) := by
  apply WP.loop (M := isa) (body := .seq Impl.TripleDes.X86.Key.rotation
      (.block Impl.TripleDes.X86.Key.storeRound)) (c := .ne)
    (Q := LoopState key base s 16) (LoopInv key base s) (loopStep key base s fit hok hw hdis) 16 s
  refine ⟨by decide, by decide, hc, hd, hcount, ?_, ?_, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  · exact hptr.trans (BitVec.add_zero base).symm
  · intro i hi
    omega

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Component` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight
open VG.Proof.Rc2.X86 (addr32)

structure ComponentPost (keys : Spec.TripleDes.DesSchedule) (base : BitVec 32) (s s' : State) : Prop where
  keys : ∀ i < 16, s'.mem.readW (addr32 base + BitVec.ofNat 64 (8 * i)) 64 = (keys.getD i 0).setWidth 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bp : s'.gpr .ebp = s.gpr .ebp
  sp : s'.gpr .esp = s.gpr .esp
  frame : Frame [scheduleRegion base, workRegion s] s.mem s'.mem

theorem component_ok (s : State) (offset component : Nat) (hok : Ok sboxCfg s)
    (keyFit : (keyArg s).toNat + offset + 8 ≤ 2 ^ 32)
    (scheduleFit : (scheduleArg s + BitVec.ofNat 32 (128 * component)).toNat + 128 ≤ 2 ^ 32)
    (harg : ∀ i ∈ [1, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr) (keyAddr s (offset + 4 * t)) 4)
    (hw : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (addr32 (scheduleArg s + BitVec.ofNat 32 (128 * component)) + BitVec.ofNat 64 (8 * j + 4 * t)) 4)
    (hdis : (scheduleRegion (scheduleArg s + BitVec.ofNat 32 (128 * component))).Disjoint (workRegion s)) :
    WP isa (Impl.TripleDes.X86.Key.component offset component) s
      (ComponentPost (Spec.TripleDes.expandDesKey (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (keyAddr s offset))))
        (scheduleArg s + BitVec.ofNat 32 (128 * component)) s) := by
  rw [Impl.TripleDes.X86.Key.component]
  apply WP.seq
  apply WP.mono (load_ok s offset component hok keyFit harg hr)
  intro s₁ h₁
  have hok₁ : Ok sboxCfg s₁ := hok.congr h₁.base h₁.base h₁.rd h₁.wr
  have writes : ∀ j < 16, ∀ t < 2, InRegions s₁.wr
      (addr32 (scheduleArg s + BitVec.ofNat 32 (128 * component)) + BitVec.ofNat 64 (8 * j + 4 * t)) 4 := by
    rw [h₁.wr]; exact hw
  have work₁ : workRegion s₁ = workRegion s := by unfold workRegion; rw [h₁.base]
  have dis₁ : (scheduleRegion (scheduleArg s + BitVec.ofNat 32 (128 * component))).Disjoint (workRegion s₁) := by
    rw [work₁]; exact hdis
  apply WP.mono (loop_ok _ _ s₁ scheduleFit hok₁ writes dis₁ h₁.c h₁.d h₁.counter h₁.ptr)
  intro s₂ h₂
  refine ⟨?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.bp.trans h₁.base,
    h₂.sp.trans h₁.sp, ?_⟩
  · intro i hi
    rw [VG.Proof.TripleDes.expandDesKey_prefix, VG.Proof.TripleDes.vector_getD _ i hi 0]
    exact h₂.keys i hi hi
  · have hf := h₂.frame
    rw [work₁] at hf
    exact (h₁.frame.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp)).trans hf

end VG.Proof.TripleDes.X86.Key

end
