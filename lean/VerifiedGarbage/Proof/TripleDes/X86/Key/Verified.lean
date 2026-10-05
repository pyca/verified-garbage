import Batteries.Logic
import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
import VerifiedGarbage.Proof.TripleDes.X86.Word
import VerifiedGarbage.Proof.Rc2.X86.Block
import VerifiedGarbage.Proof.TripleDes.X86.VerifiedBlock
import VerifiedGarbage.Proof.TripleDes.KeySchedule
import VerifiedGarbage.Proof.TripleDes.KeyMemory
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.TripleDes.Scratch

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.Rotation`. -/
section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Impl.TripleDes.X86.Key
open VG.Proof.Rc2.X86 (Keep)

theorem rotate28_ok (s : State) (r : Reg) (hr : r ≠ .eax)
    (x : BitVec 28) (hx : s.gpr r = x.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    ∃ s', runBlock isa (rotate28 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 32 ∧ Keep [r, .eax] s s' := by
  have hleft : 1 ≤ 32 - n ∧ 32 - n ≤ 31 := by omega
  have hright : 1 ≤ 28 - n ∧ 28 - n ≤ 31 := by omega
  refine ⟨_, by
    simp only [hleft, hright, and_self, rotate28, rr, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, execShift, VG.X86.readSrc, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, gpr_setFlags, hr, Ne.symm hr, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      hr, ite_false]
    rw [hx]
    exact VG.Proof.TripleDes.X86.rotate28_word x n hn hn'
  · constructor
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr'.1, hr'.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

structure RotatePost (c d : BitVec 28) (n : Nat) (s s' : State) : Prop where
  c : s'.gpr .esi = (c.rotateLeft n).setWidth 32
  d : s'.gpr .edi = (d.rotateLeft n).setWidth 32
  keep : Keep [.esi, .edi, .eax] s s'

theorem rotate_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .esi = c.setWidth 32) (hd : s.gpr .edi = d.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    WP isa (rotate n) s (VG.Proof.TripleDes.X86.Key.RotatePost c d n s) := by
  rw [rotate, WP.block_append_iff]
  obtain ⟨s₁, run₁, c₁, keep₁⟩ := VG.Proof.TripleDes.X86.Key.rotate28_ok s .esi (by decide) c hc n hn hn'
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have d₁ : s₁.gpr .edi = d.setWidth 32 := (keep₁.reg .edi (by decide)).trans hd
  obtain ⟨s₂, run₂, d₂, keep₂⟩ := VG.Proof.TripleDes.X86.Key.rotate28_ok s₁ .edi (by decide) d d₁ n hn hn'
  refine WP.of_runBlock ⟨s₂, run₂, ⟨(keep₂.reg .esi (by decide)).trans c₁, d₂, ?_⟩⟩
  refine ⟨?_, keep₂.mem.trans keep₁.mem, keep₂.rd.trans keep₁.rd, keep₂.wr.trans keep₁.wr⟩
  intro r hr
  simp only [List.mem_cons, not_or] at hr
  exact (keep₂.reg r (by simp only [List.mem_cons, hr.2.1,
    hr.2.2, or_self, not_false_eq_true])).trans
    (keep₁.reg r (by simp only [List.mem_cons, hr.1,
      hr.2.2, or_self, not_false_eq_true]))

end VG.Proof.TripleDes.X86.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.Compare`. -/
section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep)

theorem comparison_values : ∀ j < 16, ∀ k < 16,
    decide ((BitVec.ofNat 32 j).toNat < (BitVec.ofNat 32 2).toNat) = decide (j < 2) ∧
    ((BitVec.ofNat 32 j - BitVec.ofNat 32 k) == (0 : BitVec 32)) = decide (j = k) := by
  decide

theorem lowTest_ok (s : State) (j : Nat) (hj : j < 16)
    (hv : roundCount s = BitVec.ofNat 32 j) (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa [.mov .eax (.mem (memOp .ebp 20)), .alu .cmp .eax (.imm 2)] s = some s' ∧
      isa.eval .b s' = some (decide (j < 2)) ∧
      s'.gpr .eax = BitVec.ofNat 32 j ∧ Keep [.eax] s s' := by
  have hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 5) 4 := by
    obtain ⟨r, h, hc⟩ := hok.slotIn 5 (by decide)
    exact ⟨r, List.mem_append_right _ h, hc⟩
  simp only [wordAddr, addr] at hr
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      State.load32, State.ea, memOp, hr, ite_true, Option.bind_some, Option.map_some,
      gpr_setReg, ite_true]
    rfl, ?_, ?_, ?_⟩
  · change some (decide ((roundCount s).toNat < (BitVec.ofNat 32 2).toNat)) = _
    rw [hv]
    exact congrArg some (VG.Proof.TripleDes.X86.Key.comparison_values j hj 0 (by decide)).1
  · exact hv
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [gpr_arithFlags, gpr_setReg, hr, ite_false]
    · rfl
    · rfl
    · rfl

theorem eqTest_ok (s : State) (j k : Nat) (hj : j < 16) (hk : k < 16)
    (hv : s.gpr .eax = BitVec.ofNat 32 j) :
    ∃ s', runBlock isa [.alu .cmp .eax (.imm (BitVec.ofNat 32 k))] s = some s' ∧
      isa.eval .e s' = some (decide (j = k)) ∧ s'.gpr .eax = BitVec.ofNat 32 j ∧ Keep [.eax] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some]
    rfl, ?_, ?_, ?_⟩
  · change some ((s.gpr .eax - BitVec.ofNat 32 k) == 0) = _
    rw [hv]
    exact congrArg some (VG.Proof.TripleDes.X86.Key.comparison_values j hj k hk).2
  · exact hv
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem rotation_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .esi = c.setWidth 32) (hd : s.gpr .edi = d.setWidth 32)
    (hjreg : roundCount s = BitVec.ofNat 32 j) (hok : Ok sboxCfg s) :
    WP isa Impl.TripleDes.X86.Key.rotation s
      (VG.Proof.TripleDes.X86.Key.RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
  rw [Impl.TripleDes.X86.Key.rotation]
  apply WP.seq
  obtain ⟨s₁, run₁, cond₁, eax₁, keep₁⟩ := VG.Proof.TripleDes.X86.Key.lowTest_ok s j hj hjreg hok
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hrot (s' : State) (h : Keep [.eax] s s') (n : Nat) (hn : 1 ≤ n) (hn' : n < 5)
      (hv : Spec.TripleDes.rotations.getD j 0 = n) :
      WP isa (Impl.TripleDes.X86.Key.rotate n) s' (VG.Proof.TripleDes.X86.Key.RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
    apply WP.mono (VG.Proof.TripleDes.X86.Key.rotate_ok s' c d ((h.reg .esi (by simp)).trans hc)
      ((h.reg .edi (by simp)).trans hd) n hn hn')
    intro t ht
    rw [hv]
    refine ⟨ht.c, ht.d, ⟨?_, ht.keep.mem.trans h.mem, ht.keep.rd.trans h.rd,
      ht.keep.wr.trans h.wr⟩⟩
    intro r hr
    have ha : r ∉ ([.eax] : List Reg) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
      exact hr.2.2
    exact (ht.keep.reg r hr).trans (h.reg r ha)
  have combine {a b : State} (ha : Keep [.eax] s a) (hb : Keep [.eax] a b) : Keep [.eax] s b :=
    ⟨fun r hr => (hb.reg r hr).trans (ha.reg r hr), hb.mem.trans ha.mem,
      hb.rd.trans ha.rd, hb.wr.trans ha.wr⟩
  by_cases h2 : j < 2
  · apply WP.ite true (by simpa only [h2, decide_true] using cond₁)
    · intro _
      exact hrot s₁ keep₁ 1 (by decide) (by decide)
        (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inl h2)])
    · simp
  · apply WP.ite false (by simpa only [h2, decide_false] using cond₁)
    · simp
    · intro _
      apply WP.seq
      obtain ⟨s₂, run₂, cond₂, eax₂, keep₂⟩ := VG.Proof.TripleDes.X86.Key.eqTest_ok s₁ j 8 hj (by decide)
        eax₁
      refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
      have keep₂' := combine keep₁ keep₂
      by_cases h8 : j = 8
      · apply WP.ite true (by simpa only [h8, decide_true] using cond₂)
        · intro _
          exact hrot s₂ keep₂' 1 (by decide) (by decide)
            (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inl h8))])
        · simp
      · apply WP.ite false (by simpa only [h8, decide_false] using cond₂)
        · simp
        · intro _
          apply WP.seq
          obtain ⟨s₃, run₃, cond₃, _, keep₃⟩ := VG.Proof.TripleDes.X86.Key.eqTest_ok s₂ j 15 hj (by decide)
            eax₂
          refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
          have keep₃' := combine keep₂' keep₃
          by_cases h15 : j = 15
          · apply WP.ite true (by simpa only [h15, decide_true] using cond₃)
            · intro _
              exact hrot s₃ keep₃' 1 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inr h15))])
            · simp
          · apply WP.ite false (by simpa only [h15, decide_false] using cond₃)
            · simp
            · intro _
              exact hrot s₃ keep₃' 2 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_right (by simp only [h2, h8, h15, or_self, not_false_eq_true])])

end VG.Proof.TripleDes.X86.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.Permutation`. -/
section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.Impl.TripleDes.X86

theorem pc1_ok (s : VG.X86.State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc1 64 32 28 .eax .ebx .esi .edi .ecx) s = some s' ∧
      s'.gpr .eax = ((Spec.TripleDes.permute Spec.TripleDes.pc1 (packedInput 64 32 (s.gpr .esi) (s.gpr .edi))).setWidth 28).setWidth 32 ∧
      s'.gpr .ebx = (((Spec.TripleDes.permute Spec.TripleDes.pc1 (packedInput 64 32 (s.gpr .esi) (s.gpr .edi))) >>> 28).setWidth 28).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation1.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc1 (by decide) 32 28
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .esi .edi .eax .ebx (instrs keyPermutation1.lit) keyPermutation1_check (by decide +kernel) s
  have hcode : permuteCode Spec.TripleDes.pc1 64 32 28 .eax .ebx .esi .edi .ecx = instrs keyPermutation1.lit :=
    congrArg instrs keyPermutation1.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run,
    lo, hi, rd, wr, sp, mem, regs⟩


theorem pc2_ok (s : VG.X86.State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc2 56 28 32 .eax .ebx .edi .esi .ecx) s = some s' ∧
      s'.gpr .eax = ((Spec.TripleDes.permute Spec.TripleDes.pc2 (packedInput 56 28 (s.gpr .edi) (s.gpr .esi))).setWidth 32).setWidth 32 ∧
      s'.gpr .ebx = (((Spec.TripleDes.permute Spec.TripleDes.pc2 (packedInput 56 28 (s.gpr .edi) (s.gpr .esi))) >>> 32).setWidth 16).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation2.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc2 (by decide) 28 32
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .edi .esi .eax .ebx (instrs keyPermutation2.lit) keyPermutation2_check (by decide +kernel) s
  have hcode : permuteCode Spec.TripleDes.pc2 56 28 32 .eax .ebx .edi .esi .ecx = instrs keyPermutation2.lit :=
    congrArg instrs keyPermutation2.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run,
    lo, hi, rd, wr, sp, mem, regs⟩

end VG.Proof.TripleDes.X86.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.Load`. -/
section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep)

def keyArg (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esp) 1) 32

def scheduleArg (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esp) 3) 32

def keyAddr (s : State) (offset : Nat) : BitVec 64 :=
  (VG.Proof.TripleDes.X86.Key.keyArg s + BitVec.ofNat 32 offset).setWidth 64

theorem readKey_ok (s : State) (offset : Nat)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 1) 4)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86.Key.keyAddr s (offset + 4 * t)) 4) :
    ∃ s', runBlock isa (Impl.TripleDes.X86.Key.loadHead offset) s = some s' ∧
      s'.gpr .edi = bswap (s.mem.readW (VG.Proof.TripleDes.X86.Key.keyAddr s offset) 32) ∧
      s'.gpr .esi = bswap (s.mem.readW (VG.Proof.TripleDes.X86.Key.keyAddr s (offset + 4)) 32) ∧
      Keep [.edi, .esi, .edx] s s' := by
  have h0 := hr 0 (by decide)
  have h1 := hr 1 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, VG.Proof.TripleDes.X86.Key.keyAddr, VG.Proof.TripleDes.X86.Key.keyArg, wordAddr, addr] at h0
  simp only [Nat.mul_one, VG.Proof.TripleDes.X86.Key.keyAddr, VG.Proof.TripleDes.X86.Key.keyArg, wordAddr, addr] at h1
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
    (wordAddr (s.gpr .ebp) 4) (VG.Proof.TripleDes.X86.Key.scheduleArg s + BitVec.ofNat 32 (128 * component))

theorem loadTail_ok (s : State) (component : Nat) (hok : Ok sboxCfg s)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 3) 4) :
    ∃ s', runBlock isa (Impl.TripleDes.X86.Key.loadTail component) s = some s' ∧
      s'.gpr .esi = s.gpr .ebx ∧ s'.gpr .edi = s.gpr .eax ∧
      s'.mem = VG.Proof.TripleDes.X86.Key.loadMem s component ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
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
  ptr : roundKeyPtr s' = VG.Proof.TripleDes.X86.Key.scheduleArg s + BitVec.ofNat 32 (128 * component)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  base : s'.gpr .ebp = s.gpr .ebp
  sp : s'.gpr .esp = s.gpr .esp
  frame : VG.Frame [workRegion s] s.mem s'.mem

theorem loadMem_frame (s : State) (component : Nat)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) :
    VG.Frame [workRegion s] s.mem (VG.Proof.TripleDes.X86.Key.loadMem s component) := by
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
    (fit : (VG.Proof.TripleDes.X86.Key.keyArg s).toNat + offset + 8 ≤ 2 ^ 32)
    (harg : ∀ i ∈ [1, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86.Key.keyAddr s (offset + 4 * t)) 4) :
    WP isa (.block (Impl.TripleDes.X86.Key.load offset component)) s
      (VG.Proof.TripleDes.X86.Key.LoadPost (Spec.TripleDes.permute Spec.TripleDes.pc1 (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86.Key.keyAddr s offset)))) component s) := by
  rw [Impl.TripleDes.X86.Key.load, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, hi₁, lo₁, keep₁⟩ := VG.Proof.TripleDes.X86.Key.readKey_ok s offset (harg 1 (by decide)) hr
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, lo₂, hi₂, rd₂, wr₂, sp₂, mem₂, reg₂⟩ := VG.Proof.TripleDes.X86.Key.pc1_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have key₁ : packedInput 64 32 (s₁.gpr .esi) (s₁.gpr .edi) =
      Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86.Key.keyAddr s offset)) := by
    rw [packedInput, lo₁, hi₁, decodeBlock_readW]
    simp only [BitVec.setWidth_eq]
    have ha : VG.Proof.TripleDes.X86.Key.keyAddr s (offset + 4) = VG.Proof.TripleDes.X86.Key.keyAddr s offset + 4 := by
      change VG.Proof.Rc2.X86.addr32 (VG.Proof.TripleDes.X86.Key.keyArg s + BitVec.ofNat 32 (offset + 4)) =
        VG.Proof.Rc2.X86.addr32 (VG.Proof.TripleDes.X86.Key.keyArg s + BitVec.ofNat 32 offset) + 4
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
  obtain ⟨s₃, run₃, c₃, d₃, mem₃, rd₃, wr₃, reg₃⟩ := VG.Proof.TripleDes.X86.Key.loadTail_ok s₂ component hok₂ hr₂
  have base₃ : s₃.gpr .ebp = s.gpr .ebp := (reg₃ .ebp (by decide) (by decide)
    (by decide) (by decide)).trans base₂
  have sp₃ : s₃.gpr .esp = s.gpr .esp := (reg₃ .esp (by decide) (by decide)
    (by decide) (by decide)).trans sp₂'
  have sched₂ : VG.Proof.TripleDes.X86.Key.scheduleArg s₂ = VG.Proof.TripleDes.X86.Key.scheduleArg s := by
    unfold VG.Proof.TripleDes.X86.Key.scheduleArg
    rw [sp₂', mem₂, keep₁.mem]
  have hm : s₃.mem = VG.Proof.TripleDes.X86.Key.loadMem s component := by
    rw [mem₃, VG.Proof.TripleDes.X86.Key.loadMem, base₂, sched₂, mem₂, keep₁.mem]
    rfl
  refine WP.of_runBlock ⟨s₃, run₃, ⟨c₃.trans hi₂, d₃.trans lo₂, ?_, ?_,
    rd₃.trans (rd₂.trans keep₁.rd), wr₃.trans (wr₂.trans keep₁.wr), base₃, sp₃, ?_⟩⟩
  · unfold roundCount
    rw [base₃, hm, VG.Proof.TripleDes.X86.Key.loadMem, Mem.readW_writeW_sep (counter_ptr_sep s hok.fit) (by decide),
      Mem.readW_writeW_self32]
  · unfold roundKeyPtr
    rw [base₃, hm, VG.Proof.TripleDes.X86.Key.loadMem, Mem.readW_writeW_self32]
  · rw [hm]
    exact VG.Proof.TripleDes.X86.Key.loadMem_frame s component hok.fit

end VG.Proof.TripleDes.X86.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.Store`. -/
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
      s'.mem = VG.Proof.TripleDes.X86.Key.storeMem s ∧ s'.zf = some ((roundCount s + 1 - 16) == 0) ∧
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
  all_goals dsimp only [mem_setReg, mem_arithFlags, VG.Proof.TripleDes.X86.Key.storeMem, roundKeyPtr, roundCount,
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
  mem : s'.mem = VG.Proof.TripleDes.X86.Key.keyStoreMem s ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64)
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
    WP isa (.block Impl.TripleDes.X86.Key.storeRound) s (VG.Proof.TripleDes.X86.Key.StorePost c d j s) := by
  rw [Impl.TripleDes.X86.Key.storeRound, WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, rd₁, wr₁, sp₁, mem₁, reg₁⟩ := VG.Proof.TripleDes.X86.Key.pc2_ok s
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
  obtain ⟨s₂, run₂, mem₂, flag₂, rd₂, wr₂, reg₂⟩ := VG.Proof.TripleDes.X86.Key.tail_ok s₁ hok₁ hw₁
  have regs : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp], s₂.gpr r = s.gpr r := by
    intro r hr
    have diffs : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp], r ≠ .ecx ∧ r ≠ .edx := by decide
    exact (reg₂ r (diffs r hr).1 (diffs r hr).2).trans (keep₁ r hr)
  have hm : s₂.mem = VG.Proof.TripleDes.X86.Key.keyStoreMem s ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64) := by
    rw [mem₂, VG.Proof.TripleDes.X86.Key.storeMem, ptr₁, count₁, base₁, mem₁, lo₁, hi₁, BitVec.setWidth_eq]
    have ha : wordAddr (roundKeyPtr s) 1 = wordAddr (roundKeyPtr s) 0 + 4 := by
      rw [show wordAddr (roundKeyPtr s) 0 = (roundKeyPtr s).setWidth 64 from by
        simp [wordAddr, addr]]
      exact VG.X86.addr_eq (x := roundKeyPtr s) (k := 4) (by omega)
    rw [ha, writeW_pair, packed48]
    rfl
  refine WP.of_runBlock ⟨s₂, run₂, ⟨hm, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, regs⟩⟩
  · unfold roundKeyPtr
    rw [regs .ebp (by decide), hm, VG.Proof.TripleDes.X86.Key.keyStoreMem,
      Mem.readW_writeW_sep (fun a h4 h5 => counter_ptr_sep s hok.fit a h5 h4) (by decide),
      Mem.readW_writeW_self32]
    rfl
  · unfold roundCount
    rw [regs .ebp (by decide), hm, VG.Proof.TripleDes.X86.Key.keyStoreMem, Mem.readW_writeW_self32, hcount]
    exact (VG.Proof.TripleDes.X86.Key.nextRound_values j hj).1
  · change s₂.zf.map (!·) = _
    rw [flag₂, count₁, hcount, Option.map_some]
    exact congrArg some (VG.Proof.TripleDes.X86.Key.nextRound_values j hj).2

end VG.Proof.TripleDes.X86.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.Memory`. -/
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
    (VG.Proof.TripleDes.X86.Key.scheduleRegion base).Contains (addr32 base + BitVec.ofNat 64 (8 * j)) 8 :=
  Offset.contains_base _ (by omega) (by omega)

theorem work_slot (s : State) (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (k : Nat) (hk : k = 4 ∨ k = 5) :
    (workRegion s).Contains (wordAddr (s.gpr .ebp) k) 4 := by
  change (workRegion s).Contains (addr (s.gpr .ebp) (4 * k)) 4
  rw [addr_eq (by omega)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem keyStore_read (s : State) (k : BitVec 64) (p : Addr)
    (hsep : ∀ j ∈ [4, 5], Mem.Sep p 8 (wordAddr (s.gpr .ebp) j) 4) :
    (VG.Proof.TripleDes.X86.Key.keyStoreMem s k).readW p 64 = (s.mem.writeW (wordAddr (roundKeyPtr s) 0) k).readW p 64 := by
  rw [VG.Proof.TripleDes.X86.Key.keyStoreMem, Mem.readW_writeW_sep (hsep 5 (by decide)) (by decide),
    Mem.readW_writeW_sep (hsep 4 (by decide)) (by decide)]

theorem keyStore_frame (s : State) (base : BitVec 32) (j : Nat) (hj : j < 16)
    (fit : base.toNat + 128 ≤ 2 ^ 32) (scratchFit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (ptr : roundKeyPtr s = base + BitVec.ofNat 32 (8 * j)) (k : BitVec 64) :
    VG.Frame [VG.Proof.TripleDes.X86.Key.scheduleRegion base, workRegion s] s.mem (VG.Proof.TripleDes.X86.Key.keyStoreMem s k) := by
  have hc : (VG.Proof.TripleDes.X86.Key.scheduleRegion base).Contains (wordAddr (roundKeyPtr s) 0) 8 := by
    rw [ptr]
    have ha : wordAddr (base + BitVec.ofNat 32 (8 * j)) 0 =
        addr32 base + BitVec.ofNat 64 (8 * j) := by
      simpa [wordAddr, addr, addr32] using
        (VG.Proof.Rc2.X86.addr_add (x := base) (k := 8 * j) (by omega))
    rw [ha]
    exact VG.Proof.TripleDes.X86.Key.schedule_contains base j hj
  exact (((Frame.refl _ _).writeW (by simp) k hc).writeW (by simp) _
    (VG.Proof.TripleDes.X86.Key.work_slot s scratchFit 4 (Or.inl rfl))).writeW (by simp) _
    (VG.Proof.TripleDes.X86.Key.work_slot s scratchFit 5 (Or.inr rfl))

end VG.Proof.TripleDes.X86.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.Loop`. -/
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
  frame : VG.Frame [VG.Proof.TripleDes.X86.Key.scheduleRegion base, workRegion origin] origin.mem s.mem

def LoopInv (key : BitVec 64) (base : BitVec 32) (origin : State) (n : Nat) (s : State) : Prop :=
  1 ≤ n ∧ n ≤ 16 ∧ VG.Proof.TripleDes.X86.Key.LoopState key base origin (16 - n) s

theorem keyWordAddr (base : BitVec 32) (fit : base.toNat + 128 ≤ 2 ^ 32)
    (j t : Nat) (hj : j < 16) (ht : t < 2) :
    wordAddr (base + BitVec.ofNat 32 (8 * j)) t =
      addr32 base + BitVec.ofNat 64 (8 * j + 4 * t) := by
  change addr (base + BitVec.ofNat 32 (8 * j)) (4 * t) = _
  rw [addr_eq (by have h := VG.Proof.TripleDes.X86.Key.pointer_fit base fit j hj; omega)]
  change addr32 (base + BitVec.ofNat 32 (8 * j)) + BitVec.ofNat 64 (4 * t) = _
  rw [VG.Proof.Rc2.X86.addr_add (x := base) (k := 8 * j) (by omega), Offset.add_ofNat_add_ofNat]

theorem loopBody_ok (key : BitVec 64) (base : BitVec 32) (origin : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32) (hok : Ok sboxCfg origin)
    (hw : ∀ j < 16, ∀ t < 2, InRegions origin.wr
      (addr32 base + BitVec.ofNat 64 (8 * j + 4 * t)) 4)
    (hdis : (VG.Proof.TripleDes.X86.Key.scheduleRegion base).Disjoint (workRegion origin))
    (j : Nat) (hj : j < 16) (s : State) (hs : VG.Proof.TripleDes.X86.Key.LoopState key base origin j s) :
    WP isa (.seq Impl.TripleDes.X86.Key.rotation (.block Impl.TripleDes.X86.Key.storeRound)) s
      (fun s' => isa.eval .ne s' = some (decide (j ≠ 15)) ∧ VG.Proof.TripleDes.X86.Key.LoopState key base origin (j + 1) s') := by
  have hoks : Ok sboxCfg s := hok.congr hs.bp hs.bp hs.rd hs.wr
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86.Key.rotation_ok s _ _ j hj hs.c hs.d hs.counter hoks)
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
    rw [ptr₁, hs.pointer]; exact VG.Proof.TripleDes.X86.Key.pointer_fit base fit j hj
  have write₁ : ∀ t < 2, InRegions s₁.wr (wordAddr (roundKeyPtr s₁) t) 4 := by
    intro t ht
    rw [h₁.keep.wr, hs.wr, ptr₁, hs.pointer, VG.Proof.TripleDes.X86.Key.keyWordAddr base fit j t hj ht]
    exact hw j hj t ht
  apply WP.mono (VG.Proof.TripleDes.X86.Key.storeRound_ok s₁ _ _ j hj h₁.c h₁.d (count₁.trans hs.counter) hok₁ fit₁ write₁)
  intro s₂ h₂
  let k := (Spec.TripleDes.permute Spec.TripleDes.pc2
    ((keyPrefix key j).1.rotateLeft (Spec.TripleDes.rotations.getD j 0) ++
      (keyPrefix key j).2.1.rotateLeft (Spec.TripleDes.rotations.getD j 0))).setWidth 64
  have addr₁ : wordAddr (roundKeyPtr s₁) 0 = addr32 base + BitVec.ofNat 64 (8 * j) := by
    rw [ptr₁, hs.pointer, VG.Proof.TripleDes.X86.Key.keyWordAddr base fit j 0 hj (by decide)]
    simp only [Nat.mul_zero, Nat.add_zero]
  have hm : s₂.mem = ((s.mem.writeW (addr32 base + BitVec.ofNat 64 (8 * j)) k).writeW
      (wordAddr (origin.gpr .ebp) 4) (base + BitVec.ofNat 32 (8 * j) + 8)).writeW
      (wordAddr (origin.gpr .ebp) 5) (BitVec.ofNat 32 j + 1) := by
    rw [h₂.mem, VG.Proof.TripleDes.X86.Key.keyStoreMem, addr₁, ptr₁, hs.pointer, count₁, hs.counter, bp₁, h₁.keep.mem]
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
      hdis.sep (VG.Proof.TripleDes.X86.Key.schedule_contains base i hi16) (VG.Proof.TripleDes.X86.Key.work_slot origin hok.fit t ht)
    rw [hm, Mem.readW_writeW_sep (hsep 5 (Or.inr rfl)) (by decide),
      Mem.readW_writeW_sep (hsep 4 (Or.inl rfl)) (by decide), keyPrefix_succ]
    by_cases he : i = j
    · subst i
      rw [Mem.readW_writeW_self64]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_self hj).symm
    · rw [Mem.readW_writeW_sep (Offset.sep (addr32 base) (by omega) (by omega)
        (by omega)) (by decide), hs.keys i (by omega) hi16]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_ne hi16 (Ne.symm he)).symm
  · have fr := VG.Proof.TripleDes.X86.Key.keyStore_frame s₁ base j hj fit hok₁.fit (ptr₁.trans hs.pointer) k
    rw [← h₂.mem] at fr
    have hreg : workRegion s₁ = workRegion origin := by unfold workRegion; rw [bp₁]
    rw [hreg, h₁.keep.mem] at fr
    exact hs.frame.trans fr

theorem loopStep (key : BitVec 64) (base : BitVec 32) (origin : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32) (hok : Ok sboxCfg origin)
    (hw : ∀ j < 16, ∀ t < 2, InRegions origin.wr
      (addr32 base + BitVec.ofNat 64 (8 * j + 4 * t)) 4)
    (hdis : (VG.Proof.TripleDes.X86.Key.scheduleRegion base).Disjoint (workRegion origin))
    (n : Nat) (s : State) (hs : VG.Proof.TripleDes.X86.Key.LoopInv key base origin n s) :
    WP isa (.seq Impl.TripleDes.X86.Key.rotation (.block Impl.TripleDes.X86.Key.storeRound)) s
      (fun s' => (isa.eval .ne s' = some false ∧ VG.Proof.TripleDes.X86.Key.LoopState key base origin 16 s') ∨
        (isa.eval .ne s' = some true ∧ ∃ m < n, VG.Proof.TripleDes.X86.Key.LoopInv key base origin m s')) := by
  apply WP.mono (VG.Proof.TripleDes.X86.Key.loopBody_ok key base origin fit hok hw hdis (16 - n) (by omega_using [hs.1]) s hs.2.2)
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
    (hdis : (VG.Proof.TripleDes.X86.Key.scheduleRegion base).Disjoint (workRegion s))
    (hc : s.gpr .esi = (keyInitial key).1.setWidth 32)
    (hd : s.gpr .edi = (keyInitial key).2.1.setWidth 32)
    (hcount : roundCount s = 0) (hptr : roundKeyPtr s = base) :
    WP isa (.loop (.seq Impl.TripleDes.X86.Key.rotation
      (.block Impl.TripleDes.X86.Key.storeRound)) .ne) s (VG.Proof.TripleDes.X86.Key.LoopState key base s 16) := by
  apply WP.loop (M := isa) (body := .seq Impl.TripleDes.X86.Key.rotation
      (.block Impl.TripleDes.X86.Key.storeRound)) (c := .ne)
    (Q := VG.Proof.TripleDes.X86.Key.LoopState key base s 16) (VG.Proof.TripleDes.X86.Key.LoopInv key base s) (VG.Proof.TripleDes.X86.Key.loopStep key base s fit hok hw hdis) 16 s
  refine ⟨by decide, by decide, hc, hd, hcount, ?_, ?_, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  · exact hptr.trans (BitVec.add_zero base).symm
  · intro i hi
    omega

end VG.Proof.TripleDes.X86.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.Component`. -/
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
  frame : VG.Frame [VG.Proof.TripleDes.X86.Key.scheduleRegion base, workRegion s] s.mem s'.mem

theorem component_ok (s : State) (offset component : Nat) (hok : Ok sboxCfg s)
    (keyFit : (VG.Proof.TripleDes.X86.Key.keyArg s).toNat + offset + 8 ≤ 2 ^ 32)
    (scheduleFit : (VG.Proof.TripleDes.X86.Key.scheduleArg s + BitVec.ofNat 32 (128 * component)).toNat + 128 ≤ 2 ^ 32)
    (harg : ∀ i ∈ [1, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86.Key.keyAddr s (offset + 4 * t)) 4)
    (hw : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (addr32 (VG.Proof.TripleDes.X86.Key.scheduleArg s + BitVec.ofNat 32 (128 * component)) + BitVec.ofNat 64 (8 * j + 4 * t)) 4)
    (hdis : (VG.Proof.TripleDes.X86.Key.scheduleRegion (VG.Proof.TripleDes.X86.Key.scheduleArg s + BitVec.ofNat 32 (128 * component))).Disjoint (workRegion s)) :
    WP isa (Impl.TripleDes.X86.Key.component offset component) s
      (VG.Proof.TripleDes.X86.Key.ComponentPost (Spec.TripleDes.expandDesKey (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86.Key.keyAddr s offset))))
        (VG.Proof.TripleDes.X86.Key.scheduleArg s + BitVec.ofNat 32 (128 * component)) s) := by
  rw [Impl.TripleDes.X86.Key.component]
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86.Key.load_ok s offset component hok keyFit harg hr)
  intro s₁ h₁
  have hok₁ : Ok sboxCfg s₁ := hok.congr h₁.base h₁.base h₁.rd h₁.wr
  have writes : ∀ j < 16, ∀ t < 2, InRegions s₁.wr
      (addr32 (VG.Proof.TripleDes.X86.Key.scheduleArg s + BitVec.ofNat 32 (128 * component)) + BitVec.ofNat 64 (8 * j + 4 * t)) 4 := by
    rw [h₁.wr]; exact hw
  have work₁ : workRegion s₁ = workRegion s := by unfold workRegion; rw [h₁.base]
  have dis₁ : (VG.Proof.TripleDes.X86.Key.scheduleRegion (VG.Proof.TripleDes.X86.Key.scheduleArg s + BitVec.ofNat 32 (128 * component))).Disjoint (workRegion s₁) := by
    rw [work₁]; exact hdis
  apply WP.mono (VG.Proof.TripleDes.X86.Key.loop_ok _ _ s₁ scheduleFit hok₁ writes dis₁ h₁.c h₁.d h₁.counter h₁.ptr)
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

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.Copy`. -/
section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep addr32)

def copyWord (a b : Nat) : List Instr :=
  [.mov .eax (.mem (memOp .edx a)), .store (memOp .edx b) .eax]

theorem copyWord_ok (s : State) (a b : Nat)
    (hr : InRegions (s.rd ++ s.wr) (addr (s.gpr .edx) a) 4)
    (hw : InRegions s.wr (addr (s.gpr .edx) b) 4) :
    ∃ s', runBlock isa (VG.Proof.TripleDes.X86.Key.copyWord a b) s = some s' ∧
      Keep [.eax] {s with
        mem := (s.mem.writeW (addr (s.gpr .edx) b)
          (s.mem.readW (addr (s.gpr .edx) a) 32))} s' := by
  simp only [addr] at hr hw
  refine ⟨_, by
    simp only [VG.Proof.TripleDes.X86.Key.copyWord, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.store32, State.ea, memOp, hr, hw, ite_true,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, ite_false]
    rfl, ?_⟩
  refine ⟨?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [gpr_setReg, hr, ite_false]

structure CopyPost (base : Addr) (s : State) (n : Nat) (s' : State) : Prop where
  words : ∀ i < n, s'.mem.readW (base + BitVec.ofNat 64 (256 + 4 * i)) 32 =
    s.mem.readW (base + BitVec.ofNat 64 (4 * i)) 32
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  frame : VG.Frame [⟨base + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copy_ok (s : State) (n : Nat) (hn : n ≤ 32)
    (fit : (s.gpr .edx).toNat + 384 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (addr (s.gpr .edx) (4 * i)) 4)
    (hw : ∀ i < 32, InRegions s.wr (addr (s.gpr .edx) (256 + 4 * i)) 4) :
    WP isa (.block (Impl.TripleDes.X86.Key.copyWords n)) s (VG.Proof.TripleDes.X86.Key.CopyPost (addr32 (s.gpr .edx)) s n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ hi => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [Impl.TripleDes.X86.Key.copyWords, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, WP.block_append_iff]
    apply WP.mono (ih (by omega))
    intro s₁ h₁
    have base₁ : s₁.gpr .edx = s.gpr .edx := h₁.reg .edx (by decide)
    have readable : InRegions (s₁.rd ++ s₁.wr) (addr (s₁.gpr .edx) (4 * n)) 4 := by
      rw [h₁.rd, h₁.wr, base₁]; exact hr n (by omega)
    have writable : InRegions s₁.wr (addr (s₁.gpr .edx) (256 + 4 * n)) 4 := by
      rw [h₁.wr, base₁]; exact hw n (by omega)
    obtain ⟨s₂, run₂, keep₂⟩ := VG.Proof.TripleDes.X86.Key.copyWord_ok s₁ (4 * n) (256 + 4 * n) readable writable
    have source : s₁.mem.readW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n)) 32 =
        s.mem.readW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n)) 32 := by
      apply h₁.frame.readW (r := ⟨addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n), 4⟩)
        (Region.contains_self _ _) _ (by decide)
      intro r h
      obtain rfl := List.mem_singleton.mp h
      exact Offset.disjoint (addr32 (s.gpr .edx)) (by omega) (by omega) (by decide)
    have mem₂ : s₂.mem = s₁.mem.writeW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (256 + 4 * n))
        (s.mem.readW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n)) 32) := by
      have hm := keep₂.mem
      rw [base₁, addr_eq (by omega : (s.gpr .edx).toNat + (256 + 4 * n) < 2 ^ 32),
        addr_eq (by omega : (s.gpr .edx).toNat + 4 * n < 2 ^ 32)] at hm
      change s₂.mem = s₁.mem.writeW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (256 + 4 * n))
        (s₁.mem.readW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n)) 32) at hm
      rw [source] at hm
      exact hm
    refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr,
      fun r hr => (keep₂.reg r (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr)).trans
        (h₁.reg r hr), ?_⟩⟩
    · intro i hi
      rw [mem₂]
      by_cases he : i = n
      · subst i; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep (addr32 (s.gpr .edx)) (by omega) (by omega)
          (by omega)) (by decide)]
        exact h₁.words i (by omega)
    · rw [mem₂]
      apply h₁.frame.writeW (List.mem_singleton_self _) _
      have hc := Offset.contains_base (addr32 (s.gpr .edx) + BitVec.ofNat 64 256)
        (d := 4 * n) (n := 4) (k := 128) (by omega) (by omega)
      rw [Offset.add_ofNat_add_ofNat] at hc
      exact hc

structure CopySchedulePost (s s' : State) : Prop where
  keys : ∀ i < 16, s'.mem.readW (addr32 (VG.Proof.TripleDes.X86.Key.scheduleArg s) + BitVec.ofNat 64 (256 + 8 * i)) 64 =
    s.mem.readW (addr32 (VG.Proof.TripleDes.X86.Key.scheduleArg s) + BitVec.ofNat 64 (8 * i)) 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .eax → r ≠ .edx → s'.gpr r = s.gpr r
  frame : VG.Frame [⟨addr32 (VG.Proof.TripleDes.X86.Key.scheduleArg s) + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copyThird_ok (s : State) (fit : (VG.Proof.TripleDes.X86.Key.scheduleArg s).toNat + 384 ≤ 2 ^ 32)
    (harg : InRegions (s.rd ++ s.wr) (VG.X86.Straight.wordAddr (s.gpr .esp) 3) 4)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (addr (VG.Proof.TripleDes.X86.Key.scheduleArg s) (4 * i)) 4)
    (hw : ∀ i < 32, InRegions s.wr (addr (VG.Proof.TripleDes.X86.Key.scheduleArg s) (256 + 4 * i)) 4) :
    WP isa (.block Impl.TripleDes.X86.Key.copyThird) s (VG.Proof.TripleDes.X86.Key.CopySchedulePost s) := by
  rw [Impl.TripleDes.X86.Key.copyThird, WP.block_append_iff]
  let s₀ := s.setReg .edx (VG.Proof.TripleDes.X86.Key.scheduleArg s)
  have he : exec (.mov .edx (.mem (memOp .esp 12))) s = some s₀ := by
    simp only [exec, readSrc, State.load32, State.ea, memOp]
    change (if InRegions (s.rd ++ s.wr) (VG.X86.Straight.wordAddr (s.gpr .esp) 3) 4 then
      some (VG.Proof.TripleDes.X86.Key.scheduleArg s) else none).map (s.setReg .edx) = some s₀
    rw [ite_eq_left harg, Option.map_some]
  refine WP.of_runBlock ⟨s₀, by simp only [runBlock_cons, he, runStep_some, runBlock_nil], ?_⟩
  have ptr₀ : s₀.gpr .edx = VG.Proof.TripleDes.X86.Key.scheduleArg s := gpr_setReg_self _ _ _
  apply WP.mono (VG.Proof.TripleDes.X86.Key.copy_ok s₀ 32 (by decide) (by rw [ptr₀]; exact fit)
    (by rw [ptr₀]; exact hr) (by rw [ptr₀]; exact hw))
  intro s₁ h₁
  refine ⟨?_, h₁.rd, h₁.wr, ?_, ?_⟩
  · intro i hi
    let p := addr32 (VG.Proof.TripleDes.X86.Key.scheduleArg s)
    have h0 := h₁.words (2 * i) (by omega)
    have h1 := h₁.words (2 * i + 1) (by omega)
    rw [ptr₀] at h0 h1
    change s₁.mem.readW (p + BitVec.ofNat 64 (256 + 8 * i)) 64 =
      s.mem.readW (p + BitVec.ofNat 64 (8 * i)) 64
    rw [← readW_pair, ← readW_pair]
    have d0 : 256 + 4 * (2 * i) = 256 + 8 * i := by omega
    have d1 : 256 + 4 * (2 * i + 1) = 256 + 8 * i + 4 := by omega
    have a0 : 4 * (2 * i) = 8 * i := by omega
    have a1 : 4 * (2 * i + 1) = 8 * i + 4 := by omega
    rw [d0, a0] at h0
    rw [d1, a1, ← Offset.add_ofNat_add_ofNat (addr32 (VG.Proof.TripleDes.X86.Key.scheduleArg s)) (256 + 8 * i) 4,
      ← Offset.add_ofNat_add_ofNat (addr32 (VG.Proof.TripleDes.X86.Key.scheduleArg s)) (8 * i) 4] at h1
    change s₁.mem.readW ((p + BitVec.ofNat 64 (256 + 8 * i)) + 4) 32 =
      s.mem.readW ((p + BitVec.ofNat 64 (8 * i)) + 4) 32 at h1
    change s₁.mem.readW (p + BitVec.ofNat 64 (256 + 8 * i)) 32 =
      s.mem.readW (p + BitVec.ofNat 64 (8 * i)) 32 at h0
    exact congrArg₂ (fun (hi lo : BitVec 32) => hi ++ lo) h1 h0
  · intro r ha hd
    exact (h₁.reg r ha).trans (gpr_setReg_of_ne s _ hd)
  · have hf := h₁.frame
    rw [ptr₀] at hf
    exact hf

end VG.Proof.TripleDes.X86.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.Composition`. -/
section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight
open VG.Proof.Rc2.X86 (addr32)
open VG.Proof.TripleDes (componentKeys componentOffset)

def keyLength (s : State) : Nat := (arg s 1).toNat
abbrev keyR (s : State) : Region := ⟨addr32 (VG.Proof.TripleDes.X86.Key.keyArg s), VG.Proof.TripleDes.X86.Key.keyLength s⟩
abbrev outputR (s : State) : Region := ⟨addr32 (VG.Proof.TripleDes.X86.Key.scheduleArg s), 384⟩
def slot (base : Addr) (c j : Nat) : Addr := base + BitVec.ofNat 64 (128 * c + 8 * j)

structure Components (origin s : State) (done : Nat) : Prop where
  keys : ∀ c < done, ∀ j < 16, s.mem.readW (VG.Proof.TripleDes.X86.Key.slot (addr32 (VG.Proof.TripleDes.X86.Key.scheduleArg origin)) c j) 64 =
    ((componentKeys origin.mem (addr32 (VG.Proof.TripleDes.X86.Key.keyArg origin)) (VG.Proof.TripleDes.X86.Key.keyLength origin) c).getD j 0).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  bp : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  args : ∀ i < 4, arg s i = arg origin i
  frame : VG.Frame [VG.Proof.TripleDes.X86.Key.outputR origin, workRegion origin] origin.mem s.mem

structure Permissions (s : State) : Prop where
  ok : Ok sboxCfg s
  reads : ∀ offset, offset + 4 ≤ VG.Proof.TripleDes.X86.Key.keyLength s →
    InRegions (s.rd ++ s.wr) (addr32 (VG.Proof.TripleDes.X86.Key.keyArg s) + BitVec.ofNat 64 offset) 4
  writes : ∀ offset, offset + 4 ≤ 384 →
    InRegions s.wr (addr32 (VG.Proof.TripleDes.X86.Key.scheduleArg s) + BitVec.ofNat 64 offset) 4
  argRead : ∀ i ∈ [1, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4
  argOutput : (⟨argAddr s 0, 16⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.Key.outputR s)
  argWork : (⟨argAddr s 0, 16⟩ : Region).Disjoint (workRegion s)
  keyOutput : (VG.Proof.TripleDes.X86.Key.keyR s).Disjoint (VG.Proof.TripleDes.X86.Key.outputR s)
  keyWork : (VG.Proof.TripleDes.X86.Key.keyR s).Disjoint (workRegion s)
  outputWork : (VG.Proof.TripleDes.X86.Key.outputR s).Disjoint (workRegion s)
  valid : Spec.TripleDes.validKey (VG.Proof.TripleDes.X86.Key.keyLength s)
  keyFit : (VG.Proof.TripleDes.X86.Key.keyArg s).toNat + VG.Proof.TripleDes.X86.Key.keyLength s ≤ 2 ^ 32
  outputFit : (VG.Proof.TripleDes.X86.Key.scheduleArg s).toNat + 384 ≤ 2 ^ 32
  spFit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32

theorem Components.keyArg {origin s : State} {done : Nat} (h : VG.Proof.TripleDes.X86.Key.Components origin s done) :
    VG.Proof.TripleDes.X86.Key.keyArg s = VG.Proof.TripleDes.X86.Key.keyArg origin := by
  change s.mem.readW (wordAddr (s.gpr .esp) 1) 32 = _
  rw [← argument_word s 0, h.args 0 (by decide), argument_word origin 0]
  rfl

theorem Components.scheduleArg {origin s : State} {done : Nat} (h : VG.Proof.TripleDes.X86.Key.Components origin s done) :
    VG.Proof.TripleDes.X86.Key.scheduleArg s = Key.scheduleArg origin := by
  change s.mem.readW (wordAddr (s.gpr .esp) 3) 32 = _
  rw [← argument_word s 2, h.args 2 (by decide), argument_word origin 2]
  rfl

theorem Permissions.congr {s t : State} (hp : VG.Proof.TripleDes.X86.Key.Permissions s)
    (args : ∀ i < 4, arg t i = arg s i) (bp : t.gpr .ebp = s.gpr .ebp)
    (sp : t.gpr .esp = s.gpr .esp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : VG.Proof.TripleDes.X86.Key.Permissions t := by
  have key : VG.Proof.TripleDes.X86.Key.keyArg t = VG.Proof.TripleDes.X86.Key.keyArg s := by
    change t.mem.readW (wordAddr (t.gpr .esp) 1) 32 = _
    rw [← argument_word t 0, args 0 (by decide), argument_word s 0]
    rfl
  have output : VG.Proof.TripleDes.X86.Key.scheduleArg t = VG.Proof.TripleDes.X86.Key.scheduleArg s := by
    change t.mem.readW (wordAddr (t.gpr .esp) 3) 32 = _
    rw [← argument_word t 2, args 2 (by decide), argument_word s 2]
    rfl
  have len : VG.Proof.TripleDes.X86.Key.keyLength t = VG.Proof.TripleDes.X86.Key.keyLength s := by unfold VG.Proof.TripleDes.X86.Key.keyLength; rw [args 1 (by decide)]
  have work : workRegion t = workRegion s := by unfold workRegion; rw [bp]
  have argBase : argAddr t 0 = argAddr s 0 := by unfold argAddr; rw [sp]
  refine ⟨hp.ok.congr bp bp rd wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro off ho; rw [rd, wr, key]; exact hp.reads off (by rwa [len] at ho)
  · intro off ho; rw [wr, output]; exact hp.writes off ho
  · intro i hi; rw [rd, wr, sp]; exact hp.argRead i hi
  · rw [argBase, VG.Proof.TripleDes.X86.Key.outputR, output]; exact hp.argOutput
  · rw [argBase, work]; exact hp.argWork
  · rw [VG.Proof.TripleDes.X86.Key.keyR, key, len, VG.Proof.TripleDes.X86.Key.outputR, output]; exact hp.keyOutput
  · rw [VG.Proof.TripleDes.X86.Key.keyR, key, len, work]; exact hp.keyWork
  · rw [VG.Proof.TripleDes.X86.Key.outputR, output, work]; exact hp.outputWork
  · rw [len]; exact hp.valid
  · rw [key, len]; exact hp.keyFit
  · rw [output]; exact hp.outputFit
  · rw [sp]; exact hp.spFit

theorem componentStep_ok (origin s : State) (c : Nat) (hc : c < 3)
    (hp : VG.Proof.TripleDes.X86.Key.Permissions origin) (hs : VG.Proof.TripleDes.X86.Key.Components origin s c)
    (hoff : componentOffset (VG.Proof.TripleDes.X86.Key.keyLength origin) c = 8 * c) :
    WP isa (Impl.TripleDes.X86.Key.component (8 * c) c) s (VG.Proof.TripleDes.X86.Key.Components origin · (c + 1)) := by
  have offBound := VG.Proof.TripleDes.componentOffset_bound _ c hp.valid hc
  rw [hoff] at offBound
  have hok : Ok sboxCfg s := hp.ok.congr hs.bp hs.bp hs.rd hs.wr
  have kfit : (VG.Proof.TripleDes.X86.Key.keyArg s).toNat + 8 * c + 8 ≤ 2 ^ 32 := by
    rw [hs.keyArg]; omega_using [hp.keyFit, offBound]
  have sfit : (VG.Proof.TripleDes.X86.Key.scheduleArg s + BitVec.ofNat 32 (128 * c)).toNat + 128 ≤ 2 ^ 32 := by
    rw [hs.scheduleArg, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hc] : 128 * c < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [hp.outputFit, hc] : (Key.scheduleArg origin).toNat + 128 * c < 2 ^ 32)]
    omega_using [hp.outputFit, hc]
  have args : ∀ i ∈ [1, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4 := by
    rw [hs.rd, hs.wr, hs.sp]; exact hp.argRead
  have reads : ∀ t < 2, InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86.Key.keyAddr s (8 * c + 4 * t)) 4 := by
    intro t ht
    change InRegions (s.rd ++ s.wr) (addr32 (VG.Proof.TripleDes.X86.Key.keyArg s + BitVec.ofNat 32 (8 * c + 4 * t))) 4
    rw [hs.keyArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.keyFit, offBound, ht]), hs.rd, hs.wr]
    exact hp.reads _ (by omega_using [offBound, ht])
  have writes : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (addr32 (VG.Proof.TripleDes.X86.Key.scheduleArg s + BitVec.ofNat 32 (128 * c)) + BitVec.ofNat 64 (8 * j + 4 * t)) 4 := by
    intro j hj t ht
    rw [hs.scheduleArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.outputFit, hc]),
      Offset.add_ofNat_add_ofNat, hs.wr]
    exact hp.writes _ (by omega_using [hc, hj, ht])
  have componentSub : Region.Sub
      (VG.Proof.TripleDes.X86.Key.scheduleRegion (VG.Proof.TripleDes.X86.Key.scheduleArg s + BitVec.ofNat 32 (128 * c))) (VG.Proof.TripleDes.X86.Key.outputR origin) := by
    rw [VG.Proof.TripleDes.X86.Key.scheduleRegion, hs.scheduleArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.outputFit, hc])]
    exact Offset.sub_base _ (by omega_using [hc])
  have work : workRegion s = workRegion origin := by unfold workRegion; rw [hs.bp]
  have dis : (VG.Proof.TripleDes.X86.Key.scheduleRegion (VG.Proof.TripleDes.X86.Key.scheduleArg s + BitVec.ofNat 32 (128 * c))).Disjoint (workRegion s) := by
    rw [work]; exact hp.outputWork.sub_left componentSub
  apply WP.mono (VG.Proof.TripleDes.X86.Key.component_ok s (8 * c) c hok kfit sfit args reads writes dis)
  intro t ht
  have frame : VG.Frame [⟨addr32 (Key.scheduleArg origin) + BitVec.ofNat 64 (128 * c), 128⟩,
      workRegion origin] s.mem t.mem := by
    have h := ht.frame
    rw [work, VG.Proof.TripleDes.X86.Key.scheduleRegion, hs.scheduleArg,
      VG.Proof.Rc2.X86.addr_add (by omega_using [hp.outputFit, hc])] at h
    exact h
  have targs := VG.Proof.Rc2.X86.arguments_frame 4 ht.frame ht.sp
    (by rw [hs.sp]; exact hp.spFit) (by
      intro r hr
      rw [List.mem_cons, List.mem_singleton] at hr
      have a : argAddr s 0 = argAddr origin 0 := by unfold argAddr; rw [hs.sp]
      rw [a]
      rcases hr with rfl | rfl
      · exact hp.argOutput.sub_right componentSub
      · rw [work]; exact hp.argWork)
  have key : Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86.Key.keyAddr s (8 * c)) =
      Spec.TripleDes.blockAt origin.mem (addr32 (Key.keyArg origin) + BitVec.ofNat 64 (8 * c)) := by
    change Spec.TripleDes.blockAt s.mem (addr32 (VG.Proof.TripleDes.X86.Key.keyArg s + BitVec.ofNat 32 (8 * c))) = _
    rw [hs.keyArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.keyFit, offBound])]
    apply VG.Proof.TripleDes.blockAt_eq_of_frame _ hs.frame
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hp.keyOutput.sub_left (Offset.sub_base _ offBound)
    · obtain rfl := List.mem_singleton.mp hr
      exact hp.keyWork.sub_left (Offset.sub_base _ offBound)
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.bp.trans hs.bp, ht.sp.trans hs.sp,
    fun i hi => (targs i hi).trans (hs.args i hi), hs.frame.trans (ht.frame.sub ?_)⟩
  · intro k hk j hj
    by_cases he : k = c
    · subst k
      have h := ht.keys j hj
      rw [hs.scheduleArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.outputFit, hc]),
        Offset.add_ofNat_add_ofNat, key] at h
      unfold componentKeys
      rw [hoff]
      exact h
    · have before : k < c := by omega_using [hk, he]
      have keySub : Region.Sub ⟨VG.Proof.TripleDes.X86.Key.slot (addr32 (Key.scheduleArg origin)) k j, 8⟩ (VG.Proof.TripleDes.X86.Key.outputR origin) :=
        Offset.sub_base _ (by omega_using [before, hc, hj])
      have hmem := frame.readW (a := VG.Proof.TripleDes.X86.Key.slot (addr32 (Key.scheduleArg origin)) k j) (w := 64)
        (r := ⟨VG.Proof.TripleDes.X86.Key.slot (addr32 (Key.scheduleArg origin)) k j, 8⟩) (Region.contains_self _ _) (by
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact Offset.disjoint _ (by omega_using [before, hj])
              (by omega_using [before, hc, hj]) (by omega_using [hc])
          · obtain rfl := List.mem_singleton.mp hr
            exact hp.outputWork.sub_left keySub) (by decide)
      exact hmem.trans (hs.keys k before j hj)
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨VG.Proof.TripleDes.X86.Key.outputR origin, by simp, componentSub⟩
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨workRegion origin, by simp, by rw [work]; exact fun _ h => h⟩

theorem copyThirdStep_ok (origin s : State) (hp : VG.Proof.TripleDes.X86.Key.Permissions origin)
    (hs : VG.Proof.TripleDes.X86.Key.Components origin s 2) (hn : VG.Proof.TripleDes.X86.Key.keyLength origin = 16) :
    WP isa (.block Impl.TripleDes.X86.Key.copyThird) s (VG.Proof.TripleDes.X86.Key.Components origin · 3) := by
  have fit : (VG.Proof.TripleDes.X86.Key.scheduleArg s).toNat + 384 ≤ 2 ^ 32 := by rw [hs.scheduleArg]; exact hp.outputFit
  have reads : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.X86.addr (VG.Proof.TripleDes.X86.Key.scheduleArg s) (4 * i)) 4 := by
    intro i hi
    rw [hs.scheduleArg, addr_eq (by omega_using [hp.outputFit, hi]), hs.rd, hs.wr]
    obtain ⟨r, hr, hc⟩ := hp.writes (4 * i) (by omega_using [hi])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writes : ∀ i < 32, InRegions s.wr (VG.X86.addr (VG.Proof.TripleDes.X86.Key.scheduleArg s) (256 + 4 * i)) 4 := by
    intro i hi
    rw [hs.scheduleArg, addr_eq (by omega_using [hp.outputFit, hi]), hs.wr]
    exact hp.writes _ (by omega_using [hi])
  have ar : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 3) 4 := by
    rw [hs.rd, hs.wr, hs.sp]; exact hp.argRead 3 (by decide)
  apply WP.mono (VG.Proof.TripleDes.X86.Key.copyThird_ok s fit ar reads writes)
  intro t ht
  have frame : VG.Frame [⟨addr32 (Key.scheduleArg origin) + BitVec.ofNat 64 256, 128⟩] s.mem t.mem := by
    have h := ht.frame; rw [hs.scheduleArg] at h; exact h
  have sub : Region.Sub ⟨addr32 (Key.scheduleArg origin) + BitVec.ofNat 64 256, 128⟩ (VG.Proof.TripleDes.X86.Key.outputR origin) :=
    Offset.sub_base _ (by decide)
  have sp : t.gpr .esp = s.gpr .esp := ht.reg .esp (by decide) (by decide)
  have targs := VG.Proof.Rc2.X86.arguments_frame 4 frame sp
    (by rw [hs.sp]; exact hp.spFit) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      have a : argAddr s 0 = argAddr origin 0 := by unfold argAddr; rw [hs.sp]
      rw [a]; exact hp.argOutput.sub_right sub)
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    (ht.reg .ebp (by decide) (by decide)).trans hs.bp, sp.trans hs.sp,
    fun i hi => (targs i hi).trans (hs.args i hi), hs.frame.trans (frame.sub ?_)⟩
  · intro c hc j hj
    by_cases he : c = 2
    · subst c
      have hRepeat : componentKeys origin.mem (addr32 (Key.keyArg origin)) (VG.Proof.TripleDes.X86.Key.keyLength origin) 2 =
          componentKeys origin.mem (addr32 (Key.keyArg origin)) (VG.Proof.TripleDes.X86.Key.keyLength origin) 0 := by rw [hn]; rfl
      have h := ht.keys j hj
      rw [hs.scheduleArg] at h
      change t.mem.readW (addr32 (Key.scheduleArg origin) + BitVec.ofNat 64 (256 + 8 * j)) 64 = _
      rw [hRepeat]
      have first := hs.keys 0 (by decide) j hj
      simp only [VG.Proof.TripleDes.X86.Key.slot, Nat.mul_zero, Nat.zero_add] at first
      exact h.trans first
    · have before : c < 2 := by omega_using [hc, he]
      have hm := frame.readW (a := VG.Proof.TripleDes.X86.Key.slot (addr32 (Key.scheduleArg origin)) c j) (w := 64)
        (r := ⟨VG.Proof.TripleDes.X86.Key.slot (addr32 (Key.scheduleArg origin)) c j, 8⟩) (Region.contains_self _ _) (by
          intro r hr; obtain rfl := List.mem_singleton.mp hr
          exact Offset.disjoint _ (by omega_using [before, hj])
            (by omega_using [before, hj]) (by decide)) (by decide)
      exact hm.trans (hs.keys c before j hj)
  · intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨VG.Proof.TripleDes.X86.Key.outputR origin, by simp, sub⟩

def componentIndex (i : Nat) : Nat := if i < 16 then 0 else if i < 32 then 1 else 2

theorem index_partition : ∀ i < 48, VG.Proof.TripleDes.X86.Key.componentIndex i < 3 ∧ i % 16 < 16 ∧
    8 * i = 128 * VG.Proof.TripleDes.X86.Key.componentIndex i + 8 * (i % 16) := by decide

theorem Components.schedule {origin s : State} (h : VG.Proof.TripleDes.X86.Key.Components origin s 3) :
    Spec.TripleDes.scheduleAt s.mem (addr32 (Key.scheduleArg origin)) =
      VG.Proof.TripleDes.expandedMemory origin.mem (addr32 (Key.keyArg origin)) (VG.Proof.TripleDes.X86.Key.keyLength origin) := by
  apply Vector.ext
  intro i hi
  have fact := VG.Proof.TripleDes.X86.Key.index_partition i hi
  have keys := h.keys (VG.Proof.TripleDes.X86.Key.componentIndex i) fact.1 (i % 16) fact.2.1
  rw [VG.Proof.TripleDes.X86.Key.slot, ← fact.2.2] at keys
  rw [VG.Proof.TripleDes.scheduleAt_readW s.mem (addr32 (Key.scheduleArg origin)) i hi]
  simp only [VG.Proof.TripleDes.expandedMemory, Vector.getElem_ofFn]
  by_cases h16 : i < 16
  · simpa only [VG.Proof.TripleDes.X86.Key.componentIndex, h16, ite_true] using keys
  · by_cases h32 : i < 32
    · simpa only [VG.Proof.TripleDes.X86.Key.componentIndex, h16, h32, ite_false, ite_true] using keys
    · simpa only [VG.Proof.TripleDes.X86.Key.componentIndex, h16, h32, ite_false] using keys

end VG.Proof.TripleDes.X86.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.Body`. -/
section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep)

theorem lengthCompare (x : BitVec 32) : ((x - 16) == 0) = decide (x.toNat = 16) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have h' : x = 16 := by bv_omega_using [h]
    rw [h']; rfl
  · intro h
    have h' : x = 16 := BitVec.eq_of_toNat_eq h
    rw [h']; rfl

theorem cmpLength_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (memOp .esp 8)), .alu .cmp .eax (.imm 16)] s = some s' ∧
      isa.eval .e s' = some (decide (VG.Proof.TripleDes.X86.Key.keyLength s = 16)) ∧ Keep [.eax] s s' := by
  simp only [wordAddr, addr] at hr
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      State.load32, State.ea, memOp, hr, ite_true, Option.bind_some, Option.map_some,
      gpr_setReg, ite_true]
    rfl, ?_, ?_⟩
  · change some ((s.mem.readW (wordAddr (s.gpr .esp) 2) 32 - 16) == 0) = _
    rw [← argument_word s 1]
    exact congrArg some (VG.Proof.TripleDes.X86.Key.lengthCompare (arg s 1))
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [gpr_arithFlags, gpr_setReg, hr, ite_false]

theorem Components.keep {origin s t : State} {n : Nat} (hs : VG.Proof.TripleDes.X86.Key.Components origin s n)
    (ht : Keep [.eax] s t) : VG.Proof.TripleDes.X86.Key.Components origin t n := by
  have sp : t.gpr .esp = s.gpr .esp := ht.reg .esp (by decide)
  refine ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    (ht.reg .ebp (by decide)).trans hs.bp, sp.trans hs.sp, ?_, ?_⟩
  · intro i hi
    unfold arg argAddr
    rw [sp, ht.mem]
    exact hs.args i hi
  · rw [ht.mem]; exact hs.frame

theorem body_ok (origin s : State) (hp : VG.Proof.TripleDes.X86.Key.Permissions origin) (hs : VG.Proof.TripleDes.X86.Key.Components origin s 0)
    (lenRead : InRegions (origin.rd ++ origin.wr) (wordAddr (origin.gpr .esp) 2) 4)
    (Q : State → Prop)
    (finish : ∀ t, VG.Proof.TripleDes.X86.Key.Components origin t 3 → WP isa (.block Impl.TripleDes.X86.Key.restore) t Q) :
    WP isa (.seq (Impl.TripleDes.X86.Key.component 0 0)
      (.seq (Impl.TripleDes.X86.Key.component 8 1)
        (.seq (.block [.mov .eax (.mem (memOp .esp 8)), .alu .cmp .eax (.imm 16)])
          (.seq (.ite .e (.block Impl.TripleDes.X86.Key.copyThird)
            (Impl.TripleDes.X86.Key.component 16 2)) (.block Impl.TripleDes.X86.Key.restore))))) s Q := by
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86.Key.componentStep_ok origin s 0 (by decide) hp hs (by rfl))
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86.Key.componentStep_ok origin s₁ 1 (by decide) hp hs₁ (by rfl))
  intro s₂ hs₂
  apply WP.seq
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := VG.Proof.TripleDes.X86.Key.cmpLength_ok s₂
    (by rw [hs₂.rd, hs₂.wr, hs₂.sp]; exact lenRead)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have hs₃ := hs₂.keep keep₃
  apply WP.seq
  apply WP.mono (Q := (VG.Proof.TripleDes.X86.Key.Components origin · 3)) ?_
  · intro t ht; exact finish t ht
  have flag : isa.eval .e s₃ = some (decide (VG.Proof.TripleDes.X86.Key.keyLength origin = 16)) := by
    rw [flag₃, VG.Proof.TripleDes.X86.Key.keyLength, hs₂.args 1 (by decide)]
    rfl
  by_cases h16 : VG.Proof.TripleDes.X86.Key.keyLength origin = 16
  · apply WP.ite true (by simpa only [h16, decide_true] using flag)
    · intro _; exact VG.Proof.TripleDes.X86.Key.copyThirdStep_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simpa only [h16, decide_false] using flag)
    · simp
    · intro _
      exact VG.Proof.TripleDes.X86.Key.componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

end VG.Proof.TripleDes.X86.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.Entry`. -/
section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd
open VG.Proof.Rc2.X86 (addr32)

def preparedKey (s : State) : State := s.setReg .ebp (scratchArg s 4)
abbrev scratchR (s : State) : Region := ⟨addr32 (scratchArg s 4), 512⟩
abbrev savedR (s : State) : Region := ⟨addr32 (scratchArg s 4), 16⟩

structure HeadPre (s : State) : Prop where
  permissions : VG.Proof.TripleDes.X86.Key.Permissions (VG.Proof.TripleDes.X86.Key.preparedKey s)
  scratchFit : (scratchArg s 4).toNat + 512 ≤ 2 ^ 32
  argRead : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 4) 4
  lenRead : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4
  saveWrites : ∀ i < 4, InRegions s.wr (addr32 (scratchArg s 4) + BitVec.ofNat 64 (4 * i)) 4
  argsSave : (⟨argAddr s 0, 16⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.Key.savedR s)
  keyScratch : (VG.Proof.TripleDes.X86.Key.keyR s).Disjoint (VG.Proof.TripleDes.X86.Key.scratchR s)
  outputScratch : (VG.Proof.TripleDes.X86.Key.outputR s).Disjoint (VG.Proof.TripleDes.X86.Key.scratchR s)

structure ExpandPost (original s : State) : Prop where
  result : Spec.TripleDes.scheduleAt s.mem (addr32 (VG.Proof.TripleDes.X86.Key.scheduleArg original)) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt original.mem (addr32 (VG.Proof.TripleDes.X86.Key.keyArg original)) (VG.Proof.TripleDes.X86.Key.keyLength original))
  saved : ∀ r ∈ VG.Impl.TripleDes.X86.savedRegs, s.gpr r = original.gpr r
  sp : s.gpr .esp = original.gpr .esp
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  frame : VG.Frame [VG.Proof.TripleDes.X86.Key.outputR original, VG.Proof.TripleDes.X86.Key.scratchR original] original.mem s.mem

theorem expandKey_ok (s : State) (hp : VG.Proof.TripleDes.X86.Key.HeadPre s) :
    WP isa Impl.TripleDes.X86.Key.expandKey s (VG.Proof.TripleDes.X86.Key.ExpandPost s) := by
  rw [Impl.TripleDes.X86.Key.expandKey]
  apply WP.seq
  apply WP.mono (saveWithArg_ok s 4 hp.argRead hp.scratchFit hp.saveWrites)
  intro s₁ h₁
  have sp₁ : s₁.gpr .esp = s.gpr .esp := h₁.reg .esp (by decide) (by decide)
  have ghostSP : (VG.Proof.TripleDes.X86.Key.preparedKey s).gpr .esp = s.gpr .esp := gpr_setReg_of_ne s _ (by decide)
  have args₁ := VG.Proof.Rc2.X86.arguments_frame 4 h₁.frame sp₁
    (by have h := hp.permissions.spFit; rw [ghostSP] at h; exact h)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hp.argsSave)
  have ghostArgs : ∀ i, arg (VG.Proof.TripleDes.X86.Key.preparedKey s) i = arg s i := by
    intro i; unfold arg argAddr; rw [ghostSP]; rfl
  have permissions₁ : VG.Proof.TripleDes.X86.Key.Permissions s₁ := hp.permissions.congr
    (fun i hi => (args₁ i hi).trans (ghostArgs i).symm)
    (by rw [VG.Proof.TripleDes.X86.Key.preparedKey, gpr_setReg_self]; exact h₁.bp)
    (sp₁.trans ghostSP.symm) h₁.rd h₁.wr
  have init : VG.Proof.TripleDes.X86.Key.Components s₁ s₁ 0 :=
    ⟨fun _ h => by omega, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  apply VG.Proof.TripleDes.X86.Key.body_ok s₁ s₁ permissions₁ init
    (by rw [h₁.rd, h₁.wr, sp₁]; exact hp.lenRead)
  intro s₂ h₂
  have bp₂ : s₂.gpr .ebp = scratchArg s 4 := h₂.bp.trans h₁.bp
  have args₂ (i : Nat) (hi : i < 4) : arg s₂ i = arg s i :=
    (h₂.args i hi).trans (args₁ i hi)
  have output₁ : VG.Proof.TripleDes.X86.Key.outputR s₁ = VG.Proof.TripleDes.X86.Key.outputR s := by
    unfold VG.Proof.TripleDes.X86.Key.outputR
    change Region.mk (addr32 (s₁.mem.readW (wordAddr (s₁.gpr .esp) 3) 32)) 384 = _
    rw [← argument_word s₁ 2, args₁ 2 (by decide), argument_word s 2]; rfl
  have outputArg₁ : VG.Proof.TripleDes.X86.Key.scheduleArg s₁ = VG.Proof.TripleDes.X86.Key.scheduleArg s := by
    change s₁.mem.readW (wordAddr (s₁.gpr .esp) 3) 32 = _
    rw [← argument_word s₁ 2, args₁ 2 (by decide), argument_word s 2]; rfl
  have keyArg₁ : VG.Proof.TripleDes.X86.Key.keyArg s₁ = VG.Proof.TripleDes.X86.Key.keyArg s := by
    change s₁.mem.readW (wordAddr (s₁.gpr .esp) 1) 32 = _
    rw [← argument_word s₁ 0, args₁ 0 (by decide), argument_word s 0]; rfl
  have len₁ : VG.Proof.TripleDes.X86.Key.keyLength s₁ = VG.Proof.TripleDes.X86.Key.keyLength s := by unfold VG.Proof.TripleDes.X86.Key.keyLength; rw [args₁ 1 (by decide)]
  have scratchSub (i : Nat) (hi : i < 4) :
      Region.Sub ⟨addr32 (scratchArg s 4) + BitVec.ofNat 64 (4 * i), 4⟩ (VG.Proof.TripleDes.X86.Key.scratchR s) :=
    Offset.sub_base _ (by omega_using [hi])
  have saved₂ : Saved s s₂ := by
    intro i hi
    rw [bp₂]
    have hm := h₂.frame.readW (a := addr32 (scratchArg s 4) + BitVec.ofNat 64 (4 * i)) (w := 32)
      (r := ⟨addr32 (scratchArg s 4) + BitVec.ofNat 64 (4 * i), 4⟩)
      (Region.contains_self _ _) (by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [output₁]; exact (hp.outputScratch.sub_right (scratchSub i hi)).symm
        · obtain rfl := List.mem_singleton.mp hr
          have sep := savedSlot_work_disjoint s₁ i hi
          rw [h₁.bp] at sep
          exact sep) (by decide)
    have saved₁ := h₁.saved i hi
    rw [h₁.bp] at saved₁
    exact hm.trans saved₁
  have reads₂ : ∀ i < 4, InRegions (s₂.rd ++ s₂.wr)
      (addr32 (s₂.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, bp₂]
    obtain ⟨r, hr, hc⟩ := hp.saveWrites i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.mono (blockRestore_ok s s₂ saved₂ (by rw [bp₂]; exact hp.scratchFit) reads₂)
  intro s₃ h₃
  have initialBytes := VG.Proof.TripleDes.bytesAt_eq_of_frame (addr32 (VG.Proof.TripleDes.X86.Key.keyArg s)) (VG.Proof.TripleDes.X86.Key.keyLength s)
    h₁.frame (by
      have fit := permissions₁.keyFit
      rw [keyArg₁, len₁] at fit
      have bound := (VG.Proof.TripleDes.X86.Key.keyArg s).isLt
      omega_using [fit, bound]) (by
        intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact hp.keyScratch.sub_right (Region.sub_prefix (by decide)))
  have result := h₂.schedule
  rw [outputArg₁, keyArg₁, len₁] at result
  rw [← VG.Proof.TripleDes.expandKey_memory s₁.mem (addr32 (VG.Proof.TripleDes.X86.Key.keyArg s)) (VG.Proof.TripleDes.X86.Key.keyLength s)
    (by have valid := permissions₁.valid; rw [len₁] at valid; exact valid), initialBytes] at result
  refine ⟨?_, h₃.saved, h₃.sp.trans (h₂.sp.trans sp₁), h₃.rd.trans (h₂.rd.trans h₁.rd),
    h₃.wr.trans (h₂.wr.trans h₁.wr), ?_⟩
  · rw [h₃.mem]; exact result
  · rw [h₃.mem]
    have first : VG.Frame [VG.Proof.TripleDes.X86.Key.outputR s, VG.Proof.TripleDes.X86.Key.scratchR s] s.mem s₁.mem := h₁.frame.sub (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨VG.Proof.TripleDes.X86.Key.scratchR s, by simp, Region.sub_prefix (by decide)⟩)
    exact first.trans (h₂.frame.sub (by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [output₁]; exact ⟨VG.Proof.TripleDes.X86.Key.outputR s, by simp, fun _ h => h⟩
      · obtain rfl := List.mem_singleton.mp hr
        refine ⟨VG.Proof.TripleDes.X86.Key.scratchR s, by simp, ?_⟩
        rw [workRegion, h₁.bp]
        exact Offset.sub_base _ (by decide)))

end VG.Proof.TripleDes.X86.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.Contract`. -/
section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

def contract : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (arg s 0), (arg s 1).toNat⟩
    let output : Region := ⟨addr32 (arg s 2), 384⟩
    let scratch : Region := ⟨addr32 (arg s 3), 512⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    s.rd = [key, args] ∧ s.wr = [output, scratch] ∧ key.Disjoint output ∧
      key.Disjoint scratch ∧ output.Disjoint scratch ∧ args.Disjoint output ∧
      args.Disjoint scratch ∧ ret.Disjoint output ∧ ret.Disjoint scratch ∧
      Spec.TripleDes.validKey (arg s 1).toNat ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 384 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 512 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' := Spec.TripleDes.scheduleAt s'.mem (addr32 (arg s 2)) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat)
  pub s t := s.gpr .esp = t.gpr .esp ∧ ∀ i < 4, arg s i = arg t i

end VG.Proof.TripleDes.X86.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.ConstantTime`. -/
section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

theorem keyTaint_wf {s : State} (hs : contract.pre s) : VG.X86.Taint.Wf VG.Proof.TripleDes.X86.keyTaint s := by
  obtain ⟨_, hwr, _, _, dataSep, argsData, argsScratch, retData, retScratch, _, _, dataFit, scratchFit, spFit⟩ := hs
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spFit, ?_⟩, ?_⟩
  · rw [hwr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨dataSep, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr32, BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) retData argsData
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) retScratch argsScratch
  · intro p hp
    simp only [VG.Proof.TripleDes.X86.keyTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, addr32, arg, argAddr]

theorem keyTaint_agree {s t : State} (hs : contract.pre s)
    (ht : contract.pre t) (hp : contract.pub s t) :
    VG.X86.Taint.Agree VG.Proof.TripleDes.X86.keyTaint s t := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, contract.pre s → (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := by
    intro s hs; obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hs; exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.TripleDes.X86.Key.keyTaint_wf hs,
    VG.Proof.TripleDes.X86.Key.keyTaint_wf ht, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [VG.Proof.TripleDes.X86.keyTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.2.1, ht.2.1, args 2 (by decide), args 3 (by decide)]
  · simp only [VG.Proof.TripleDes.X86.keyTaint] at hk
    rw [show VG.X86.Taint.depth keyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

end VG.Proof.TripleDes.X86.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.Pre`. -/
section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd
open VG.Proof.Rc2.X86 (addr32 argContainsCount)

theorem key_argument (s : State) : VG.Proof.TripleDes.X86.Key.keyArg s = arg s 0 := (argument_word s 0).symm
 theorem output_argument (s : State) : VG.Proof.TripleDes.X86.Key.scheduleArg s = arg s 2 := (argument_word s 2).symm
 theorem scratch_argument (s : State) : scratchArg s 4 = arg s 3 := (argument_word s 3).symm

theorem headPre_of_contract (s : State) (hs : contract.pre s) : VG.Proof.TripleDes.X86.Key.HeadPre s := by
  obtain ⟨rd, wr, keyOut, keyScratch, outScratch, argsOut, argsScratch, _, _,
    valid, keyFit, outputFit, scratchFit, spFit⟩ := hs
  have bp : (VG.Proof.TripleDes.X86.Key.preparedKey s).gpr .ebp = arg s 3 := by rw [VG.Proof.TripleDes.X86.Key.preparedKey, gpr_setReg_self, VG.Proof.TripleDes.X86.Key.scratch_argument]
  have sp : (VG.Proof.TripleDes.X86.Key.preparedKey s).gpr .esp = s.gpr .esp := gpr_setReg_of_ne s _ (by decide)
  have args (i : Nat) : arg (VG.Proof.TripleDes.X86.Key.preparedKey s) i = arg s i := by unfold arg argAddr; rw [sp]; rfl
  have key : VG.Proof.TripleDes.X86.Key.keyArg (VG.Proof.TripleDes.X86.Key.preparedKey s) = arg s 0 := by rw [VG.Proof.TripleDes.X86.Key.key_argument, args]
  have output : VG.Proof.TripleDes.X86.Key.scheduleArg (VG.Proof.TripleDes.X86.Key.preparedKey s) = arg s 2 := by rw [VG.Proof.TripleDes.X86.Key.output_argument, args]
  have len : VG.Proof.TripleDes.X86.Key.keyLength (VG.Proof.TripleDes.X86.Key.preparedKey s) = (arg s 1).toNat := by unfold VG.Proof.TripleDes.X86.Key.keyLength; rw [args]
  have argBase : argAddr (VG.Proof.TripleDes.X86.Key.preparedKey s) 0 = argAddr s 0 := by unfold argAddr; rw [sp]
  have workSub : Region.Sub (workRegion (VG.Proof.TripleDes.X86.Key.preparedKey s)) ⟨addr32 (arg s 3), 512⟩ := by
    rw [workRegion, bp]; exact Offset.sub_base _ (by decide)
  have saveSub : Region.Sub (VG.Proof.TripleDes.X86.Key.savedR s) ⟨addr32 (arg s 3), 512⟩ := by
    rw [VG.Proof.TripleDes.X86.Key.savedR, VG.Proof.TripleDes.X86.Key.scratch_argument]; exact Region.sub_prefix (by decide)
  have contains : ∀ i, 1 ≤ i → i ≤ 4 → (⟨argAddr s 0, 16⟩ : Region).Contains
      (wordAddr (s.gpr .esp) i) 4 := by
    intro i hlo hhi
    rw [wordAddr, addr_eq (by omega_using [spFit, hhi])]
    have h := argContainsCount s 4 spFit (i - 1) (by omega_using [hlo, hhi])
    rw [show 4 + 4 * (i - 1) = 4 * i by omega_using [hlo]] at h
    exact h
  have readArg : ∀ i, 1 ≤ i → i ≤ 4 → InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4 := by
    intro i hlo hhi
    rw [rd, wr]
    exact ⟨⟨argAddr s 0, 16⟩, by simp, contains i hlo hhi⟩
  have slots : ∀ i < 128, InRegions (VG.Proof.TripleDes.X86.Key.preparedKey s).wr (wordAddr ((VG.Proof.TripleDes.X86.Key.preparedKey s).gpr .ebp) i) 4 := by
    intro i hi
    rw [bp, wordAddr, addr_eq (by omega_using [scratchFit, hi])]
    change InRegions s.wr _ 4
    rw [wr]
    exact ⟨⟨addr32 (arg s 3), 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  have ok : Ok sboxCfg (VG.Proof.TripleDes.X86.Key.preparedKey s) := by
    refine ⟨slots, ?_, ?_, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · change ((VG.Proof.TripleDes.X86.Key.preparedKey s).gpr .ebp).toNat + 512 ≤ 2 ^ 32; rw [bp]; exact scratchFit
    · intro k hk j hj; change j < 0 at hj; omega
  refine ⟨?_, ?_, readArg 4 (by decide) (by decide), readArg 2 (by decide) (by decide), ?_,
    argsScratch.sub_right saveSub, ?_, ?_⟩
  · refine ⟨ok, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro off ho
      rw [len] at ho
      rw [key]
      change InRegions (s.rd ++ s.wr) _ 4
      rw [rd, wr]
      exact ⟨⟨addr32 (arg s 0), (arg s 1).toNat⟩, by simp,
        Offset.contains_base _ ho (by omega_using [ho, keyFit])⟩
    · intro off ho
      rw [output]
      change InRegions s.wr _ 4
      rw [wr]
      exact ⟨⟨addr32 (arg s 2), 384⟩, by simp, Offset.contains_base _ ho (by omega_using [ho])⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      change InRegions (s.rd ++ s.wr) (wordAddr ((VG.Proof.TripleDes.X86.Key.preparedKey s).gpr .esp) i) 4
      rw [sp]
      rcases hi with rfl | rfl
      · exact readArg 1 (by decide) (by decide)
      · exact readArg 3 (by decide) (by decide)
    · rw [argBase, VG.Proof.TripleDes.X86.Key.outputR, output]; exact argsOut
    · rw [argBase]; exact argsScratch.sub_right workSub
    · rw [VG.Proof.TripleDes.X86.Key.keyR, key, len, VG.Proof.TripleDes.X86.Key.outputR, output]; exact keyOut
    · rw [VG.Proof.TripleDes.X86.Key.keyR, key, len]; exact keyScratch.sub_right workSub
    · rw [VG.Proof.TripleDes.X86.Key.outputR, output]; exact outScratch.sub_right workSub
    · rw [len]; exact valid
    · rw [key, len]; exact keyFit
    · rw [output]; exact outputFit
    · rw [sp]; exact spFit
  · rw [VG.Proof.TripleDes.X86.Key.scratch_argument]; exact scratchFit
  · intro i hi
    rw [VG.Proof.TripleDes.X86.Key.scratch_argument, wr]
    exact ⟨⟨addr32 (arg s 3), 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [VG.Proof.TripleDes.X86.Key.keyR, VG.Proof.TripleDes.X86.Key.key_argument, VG.Proof.TripleDes.X86.Key.keyLength, VG.Proof.TripleDes.X86.Key.scratchR, VG.Proof.TripleDes.X86.Key.scratch_argument]; exact keyScratch
  · rw [VG.Proof.TripleDes.X86.Key.outputR, VG.Proof.TripleDes.X86.Key.output_argument, VG.Proof.TripleDes.X86.Key.scratchR, VG.Proof.TripleDes.X86.Key.scratch_argument]; exact outScratch

end VG.Proof.TripleDes.X86.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.Correct`. -/
section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

theorem expand_correct (s : State) (hs : contract.pre s) :
    WP isa Impl.TripleDes.X86.Key.expandKey s (fun s' => abiPreserved s s' ∧ contract.post s s') := by
  have hp := VG.Proof.TripleDes.X86.Key.headPre_of_contract s hs
  obtain ⟨_, _, _, _, _, _, _, retOutput, retScratch, _⟩ := hs
  apply WP.mono (VG.Proof.TripleDes.X86.Key.expandKey_ok s hp)
  intro s' hpost
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    have regs : ∀ r ∈ calleeSaved, r ∈ Impl.TripleDes.X86.savedRegs ∨ r = .esp := by decide
    rcases regs r hr with saved | rfl
    · exact hpost.saved r saved
    · exact hpost.sp
  · apply hpost.frame.readW (r := ⟨addr32 (s.gpr .esp), 4⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [VG.Proof.TripleDes.X86.Key.outputR, VG.Proof.TripleDes.X86.Key.output_argument]; exact retOutput
    · obtain rfl := List.mem_singleton.mp hr
      rw [VG.Proof.TripleDes.X86.Key.scratchR, VG.Proof.TripleDes.X86.Key.scratch_argument]; exact retScratch
  · have result := hpost.result
    rw [VG.Proof.TripleDes.X86.Key.output_argument, VG.Proof.TripleDes.X86.Key.key_argument, VG.Proof.TripleDes.X86.Key.keyLength] at result
    exact result

end VG.Proof.TripleDes.X86.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Key.Verified`. -/
section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

def satState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4008 then 16 else
    if a = 0x400d then 0x20 else if a = 0x4011 then 0x30 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x4004, 16⟩]
  wr := [⟨0x2000, 384⟩, ⟨0x3000, 512⟩]

theorem verified : Verified target Impl.TripleDes.X86.Key.expandKey
    (Proof.TripleDes.expandKeyScratchContract abi) := by
  refine Verified.of_correct VG.Proof.TripleDes.X86.Key.expand_correct
    (VG.Proof.TripleDes.X86.expandKey_constantTime _ _ (fun _ _ h₁ h₂ hp => VG.Proof.TripleDes.X86.Key.keyTaint_agree h₁ h₂ hp)) ?_
  sig_implies [Proof.TripleDes.expandKeyScratchContract, Proof.TripleDes.expandKeyScratchSig, Spec.TripleDes.expandKeyPre, Spec.TripleDes.expandKeyPost, abi, argSlots, argVal,
    argBytes, addr32, VG.Proof.TripleDes.X86.Key.contract]
    [satState, arg, argAddr, Mem.readW, Mem.read] using VG.Proof.TripleDes.X86.Key.satState

end VG.Proof.TripleDes.X86.Key

end
