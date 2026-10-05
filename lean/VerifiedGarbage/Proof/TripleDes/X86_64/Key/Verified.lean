import VerifiedGarbage.Proof.TripleDes.X86_64.KeySteps
import VerifiedGarbage.Proof.TripleDes.KeySchedule
import VerifiedGarbage.Proof.Rc2.X86_64.Block
import VerifiedGarbage.Proof.TripleDes.X86_64.VerifiedBlock
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.KeyMemory
import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Verified
import VerifiedGarbage.Proof.Rc2.X86_64.Block
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.TripleDes.Scratch

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Key.Rotation`. -/
section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64
open VG.Proof.Rc2.X86_64 (Keep)

structure RotatePost (c d : BitVec 28) (n : Nat) (s s' : State) : Prop where
  c : s'.gpr .r12 = (c.rotateLeft n).setWidth 64
  d : s'.gpr .r13 = (d.rotateLeft n).setWidth 64
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .rax → r ≠ .r12 → r ≠ .r13 → s'.gpr r = s.gpr r

theorem rotate_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .r12 = c.setWidth 64) (hd : s.gpr .r13 = d.setWidth 64)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 28) :
    WP isa (Impl.TripleDes.X86_64.Key.rotate n) s (VG.Proof.TripleDes.X86_64.Key.RotatePost c d n s) := by
  rw [Impl.TripleDes.X86_64.Key.rotate, WP.block_append_iff]
  obtain ⟨s₁, run₁, c₁, mem₁, rd₁, wr₁, reg₁⟩ := rotate28_ok s .r12 (by decide) c hc n hn hn'
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have d₁ : s₁.gpr .r13 = d.setWidth 64 := (reg₁ .r13 (by decide) (by decide)).trans hd
  obtain ⟨s₂, run₂, d₂, mem₂, rd₂, wr₂, reg₂⟩ := rotate28_ok s₁ .r13 (by decide) d d₁ n hn hn'
  refine WP.of_runBlock ⟨s₂, run₂, ⟨(reg₂ .r12 (by decide) (by decide)).trans c₁, d₂,
    mem₂.trans mem₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩⟩
  intro r ha hc hd
  exact (reg₂ r hd ha).trans (reg₁ r hc ha)

theorem comparison_values : ∀ j < 16, ∀ k < 16,
    decide ((BitVec.ofNat 64 j).toNat < ((BitVec.ofNat 32 k).signExtend 64).toNat) = decide (j < k) ∧
    ((BitVec.ofNat 64 j - (BitVec.ofNat 32 k).signExtend 64) == (0 : BitVec 64)) = decide (j = k) := by
  decide

theorem cmp_ok (s : State) (j k : Nat) (hj : j < 16) (hk : k < 16)
    (hv : s.gpr .r14 = BitVec.ofNat 64 j) :
    ∃ s', runBlock isa [.alu .cmp .r14 (.imm (BitVec.ofNat 32 k))] s = some s' ∧
      s'.cf = some (decide (j < k)) ∧ s'.zf = some (decide (j = k)) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86_64.readSrc, Option.bind_some]
    rfl, ?_, ?_, ?_⟩
  · rw [cf_arithFlags, hv]
    exact congrArg some (VG.Proof.TripleDes.X86_64.Key.comparison_values j hj k hk).1
  · rw [zf_arithFlags, hv]
    exact congrArg some (VG.Proof.TripleDes.X86_64.Key.comparison_values j hj k hk).2
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem rotation_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r12 = c.setWidth 64) (hd : s.gpr .r13 = d.setWidth 64)
    (hjreg : s.gpr .r14 = BitVec.ofNat 64 j) :
    WP isa Impl.TripleDes.X86_64.Key.rotation s
      (VG.Proof.TripleDes.X86_64.Key.RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
  rw [Impl.TripleDes.X86_64.Key.rotation]
  apply WP.seq
  obtain ⟨s₁, run₁, cf₁, zf₁, keep₁⟩ := VG.Proof.TripleDes.X86_64.Key.cmp_ok s j 2 hj (by decide) hjreg
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hrot (s' : State) (h : Keep [] s s') (n : Nat) (hn : 1 ≤ n) (hn' : n < 28)
      (hv : Spec.TripleDes.rotations.getD j 0 = n) :
      WP isa (Impl.TripleDes.X86_64.Key.rotate n) s' (VG.Proof.TripleDes.X86_64.Key.RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
    apply WP.mono (VG.Proof.TripleDes.X86_64.Key.rotate_ok s' c d ((h.reg .r12 (by simp)).trans hc)
      ((h.reg .r13 (by simp)).trans hd) n hn hn')
    intro t ht
    rw [hv]
    exact ⟨ht.c, ht.d, ht.mem.trans h.mem, ht.rd.trans h.rd, ht.wr.trans h.wr,
      fun r ha hc hd => (ht.reg r ha hc hd).trans (h.reg r (by simp))⟩
  have combine {a b : State} (ha : Keep [] s a) (hb : Keep [] a b) : Keep [] s b :=
    ⟨fun r hr => (hb.reg r hr).trans (ha.reg r hr), hb.mem.trans ha.mem,
      hb.rd.trans ha.rd, hb.wr.trans ha.wr⟩
  by_cases h2 : j < 2
  · apply WP.ite true (by simp only [VG.X86_64.eval, cf₁, h2, decide_true])
    · intro _
      exact hrot s₁ keep₁ 1 (by decide) (by decide)
        (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inl h2)])
    · simp
  · apply WP.ite false (by simp only [VG.X86_64.eval, cf₁, h2, decide_false])
    · simp
    · intro _
      apply WP.seq
      obtain ⟨s₂, run₂, cf₂, zf₂, keep₂⟩ := VG.Proof.TripleDes.X86_64.Key.cmp_ok s₁ j 8 hj (by decide)
        ((keep₁.reg .r14 (by simp)).trans hjreg)
      refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
      have keep₂' := combine keep₁ keep₂
      by_cases h8 : j = 8
      · apply WP.ite true (by simp only [VG.X86_64.eval, zf₂, h8, decide_true])
        · intro _
          exact hrot s₂ keep₂' 1 (by decide) (by decide)
            (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inl h8))])
        · simp
      · apply WP.ite false (by simp only [VG.X86_64.eval, zf₂, h8, decide_false])
        · simp
        · intro _
          apply WP.seq
          obtain ⟨s₃, run₃, cf₃, zf₃, keep₃⟩ := VG.Proof.TripleDes.X86_64.Key.cmp_ok s₂ j 15 hj (by decide)
            ((keep₂'.reg .r14 (by simp)).trans hjreg)
          refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
          have keep₃' := combine keep₂' keep₃
          by_cases h15 : j = 15
          · apply WP.ite true (by simp only [VG.X86_64.eval, zf₃, h15, decide_true])
            · intro _
              exact hrot s₃ keep₃' 1 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inr h15))])
            · simp
          · apply WP.ite false (by simp only [VG.X86_64.eval, zf₃, h15, decide_false])
            · simp
            · intro _
              exact hrot s₃ keep₃' 2 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_right (by simp only [h2, h8, h15, or_self, not_false_eq_true])])

end VG.Proof.TripleDes.X86_64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Key.Permutation`. -/
section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

 theorem pc1_ok (s : VG.X86_64.State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc1 64 .rbx .rax .rbp) s = some s' ∧
      s'.gpr .rbx = (Spec.TripleDes.permute Spec.TripleDes.pc1 (s.gpr .rax)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation1.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc1 (by decide) (by decide) (by decide)
      (instrs keyPermutation1.lit) keyPermutation1_check s
  have hcode : permuteCode Spec.TripleDes.pc1 64 .rbx .rax .rbp = instrs keyPermutation1.lit :=
    congrArg instrs keyPermutation1.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, mem, regs⟩
  exact word.trans (congrArg (fun x => (Spec.TripleDes.permute Spec.TripleDes.pc1 x).setWidth 64)
    (BitVec.setWidth_eq _))

theorem pc2_ok (s : VG.X86_64.State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc2 56 .rbx .rax .rbp) s = some s' ∧
      s'.gpr .rbx = (Spec.TripleDes.permute Spec.TripleDes.pc2 ((s.gpr .rax).setWidth 56)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation2.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc2 (by decide) (by decide) (by decide)
      (instrs keyPermutation2.lit) keyPermutation2_check s
  have hcode : permuteCode Spec.TripleDes.pc2 56 .rbx .rax .rbp = instrs keyPermutation2.lit :=
    congrArg instrs keyPermutation2.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, word, rd, wr, mem, regs⟩

end VG.Proof.TripleDes.X86_64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Key.Load`. -/
section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64
open VG.Proof.Rc2.X86_64 (offset_nat)

theorem readKey_ok (s : State) (offset : Nat)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 offset) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (memOp .rdi offset)), .bswap .rax] s = some s' ∧
      s'.gpr .rax = Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .rdi + BitVec.ofNat 64 offset)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load64, State.ea, memOp, offset_nat, hr, ite_true, Option.map_some,
      gpr_setReg_self]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg_self]
    exact (decodeBlock_readW s.mem _).symm
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · intro r hr
    simp only [gpr_setReg, hr, ite_false]

def loadTail (component : Nat) : List Instr :=
  [rr .r12 .rbx, .shift .shr .r12 28, rr .r13 .rbx,
    .alu .and .r13 (.imm 0x0fffffff), imm .r14 0, rr .r15 .rdx,
    .alu .add .r15 (.imm (BitVec.ofNat 32 (128 * component)))]

theorem componentOffset_word : ∀ c < 3,
    (BitVec.ofNat 32 (128 * c)).signExtend 64 = BitVec.ofNat 64 (128 * c) := by decide

theorem loadTail_ok (s : State) (component : Nat) (hc : component < 3) (x : BitVec 56)
    (hx : s.gpr .rbx = x.setWidth 64) :
    ∃ s', runBlock isa (VG.Proof.TripleDes.X86_64.Key.loadTail component) s = some s' ∧
      s'.gpr .r12 = ((x >>> 28).setWidth 28).setWidth 64 ∧
      s'.gpr .r13 = (x.setWidth 28).setWidth 64 ∧ s'.gpr .r14 = 0 ∧
      s'.gpr .r15 = s.gpr .rdx + BitVec.ofNat 64 (128 * component) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ [Reg.r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [VG.Proof.TripleDes.X86_64.Key.loadTail, rr, imm, runBlock_cons, runStep_some, exec,
      execShift, readSrc, Option.map_some, gpr_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    rw [hx]
    exact VG.Proof.TripleDes.split28_upper x
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    rw [hx]
    change x.setWidth 64 &&& 0x0fffffff = _
    rw [VG.Proof.TripleDes.mask28]
    exact congrArg (BitVec.setWidth 64) (by simp only [BitVec.setWidth_setWidth_of_le x (by decide : 28 ≤ 64)])
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    rw [VG.Proof.TripleDes.X86_64.Key.componentOffset_word component hc]
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
  · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
  · simp only [wr_setReg, wr_arithFlags, wr_setFlags]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

structure LoadPost (x : BitVec 56) (component : Nat) (s s' : State) : Prop where
  c : s'.gpr .r12 = ((x >>> 28).setWidth 28).setWidth 64
  d : s'.gpr .r13 = (x.setWidth 28).setWidth 64
  counter : s'.gpr .r14 = 0
  ptr : s'.gpr .r15 = s.gpr .rdx + BitVec.ofNat 64 (128 * component)
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp], s'.gpr r = s.gpr r

theorem load_ok (s : State) (offset component : Nat) (hc : component < 3)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 offset) 8) :
    WP isa (.block (Impl.TripleDes.X86_64.Key.load offset component)) s
      (VG.Proof.TripleDes.X86_64.Key.LoadPost (Spec.TripleDes.permute Spec.TripleDes.pc1 (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .rdi + BitVec.ofNat 64 offset)))) component s) := by
  have code : Impl.TripleDes.X86_64.Key.load offset component =
      (([.mov .rax (.mem (memOp .rdi offset)), .bswap .rax] : List Instr) ++
        permuteCode Spec.TripleDes.pc1 64 .rbx .rax .rbp) ++ VG.Proof.TripleDes.X86_64.Key.loadTail component := rfl
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, key₁, mem₁, rd₁, wr₁, reg₁⟩ := VG.Proof.TripleDes.X86_64.Key.readKey_ok s offset hr
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, reg₂⟩ := VG.Proof.TripleDes.X86_64.Key.pc1_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [key₁] at word₂
  obtain ⟨s₃, run₃, c₃, d₃, counter₃, ptr₃, mem₃, rd₃, wr₃, reg₃⟩ := VG.Proof.TripleDes.X86_64.Key.loadTail_ok s₂ component hc _ word₂
  refine WP.of_runBlock ⟨s₃, run₃, ⟨c₃, d₃, counter₃, ?_, mem₃.trans (mem₂.trans mem₁),
    rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_⟩⟩
  · have rdx₂ : s₂.gpr .rdx = s.gpr .rdx :=
      (reg₂ .rdx (by decide +kernel)).trans (reg₁ .rdx (by decide))
    rw [rdx₂] at ptr₃
    exact ptr₃
  · intro r hr
    have unused : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp],
        r ∉ [Reg.r12, .r13, .r14, .r15] ∧ r ≠ .rax := by decide
    have hcheck : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp],
        ((instrs keyPermutation1.lit).all fun op => op.dst != some r) = true := by decide +kernel
    exact (reg₃ r (unused r hr).1).trans ((reg₂ r (hcheck r hr)).trans (reg₁ r (unused r hr).2))

end VG.Proof.TripleDes.X86_64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Key.Store`. -/
section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64
open VG.Proof.Rc2.X86_64 (offset_nat)

def pack : List Instr := [rr .rax .r12, .shift .ror .rax 36, .alu .xor .rax (.reg .r13)]

def tail : List Instr := [.store (memOp .r15 0) .rbx, .alu .add .r15 (.imm 8),
  .alu .add .r14 (.imm 1), .alu .cmp .r14 (.imm 16)]

theorem pack_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .r12 = c.setWidth 64) (hd : s.gpr .r13 = d.setWidth 64) :
    ∃ s', runBlock isa VG.Proof.TripleDes.X86_64.Key.pack s = some s' ∧
      (s'.gpr .rax).setWidth 56 = c ++ d ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [VG.Proof.TripleDes.X86_64.Key.pack, rr, runBlock_cons, runStep_some, exec, execShift,
      readSrc, Option.map_some, gpr_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rw [hc, hd]
    exact VG.Proof.TripleDes.pack28_word c d
  · simp only [mem_setReg, mem_setFlags, mem_arithFlags]
  · simp only [rd_setReg, rd_setFlags, rd_arithFlags]
  · simp only [wr_setReg, wr_setFlags, wr_arithFlags]
  · intro r hr
    simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, hr, ite_false]

theorem nextRound_values : ∀ j < 16,
    BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) ∧
    ((BitVec.ofNat 64 j + 1 - (16 : BitVec 64)) == 0) = decide (j = 15) := by decide

theorem tail_ok (s : State) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r14 = BitVec.ofNat 64 j)
    (hw : InRegions s.wr (s.gpr .r15) 8) :
    ∃ s', runBlock isa VG.Proof.TripleDes.X86_64.Key.tail s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r15) (s.gpr .rbx) ∧
      s'.gpr .r15 = s.gpr .r15 + 8 ∧ s'.gpr .r14 = BitVec.ofNat 64 (j + 1) ∧
      s'.zf = some (decide (j = 15)) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) := by
  have hoff : s.gpr .r15 + BitVec.ofInt 64 (Int.ofNat 0) = s.gpr .r15 := BitVec.add_zero _
  refine ⟨_, by
    simp only [VG.Proof.TripleDes.X86_64.Key.tail, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.store64, State.ea, memOp, hoff, hw, ite_true, Option.bind_some,
      gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rw [hc]
    exact (VG.Proof.TripleDes.X86_64.Key.nextRound_values j hj).1
  · rw [zf_arithFlags, hc]
    exact congrArg some (VG.Proof.TripleDes.X86_64.Key.nextRound_values j hj).2
  · simp only [rd_setReg, rd_arithFlags]
  · simp only [wr_setReg, wr_arithFlags]
  · intro r h14 h15
    simp only [gpr_setReg, gpr_arithFlags, h14, h15, ite_false]

structure StorePost (c d : BitVec 28) (j : Nat) (s s' : State) : Prop where
  mem : s'.mem = s.mem.writeW (s.gpr .r15) ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64)
  ptr : s'.gpr .r15 = s.gpr .r15 + 8
  counter : s'.gpr .r14 = BitVec.ofNat 64 (j + 1)
  flag : s'.zf = some (decide (j = 15))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13], s'.gpr r = s.gpr r

theorem storeRound_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r12 = c.setWidth 64) (hd : s.gpr .r13 = d.setWidth 64)
    (hjreg : s.gpr .r14 = BitVec.ofNat 64 j) (hw : InRegions s.wr (s.gpr .r15) 8) :
    WP isa (.block Impl.TripleDes.X86_64.Key.storeRound) s (VG.Proof.TripleDes.X86_64.Key.StorePost c d j s) := by
  have code : Impl.TripleDes.X86_64.Key.storeRound =
      (VG.Proof.TripleDes.X86_64.Key.pack ++ permuteCode Spec.TripleDes.pc2 56 .rbx .rax .rbp) ++ VG.Proof.TripleDes.X86_64.Key.tail := rfl
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, reg₁⟩ := VG.Proof.TripleDes.X86_64.Key.pack_ok s c d hc hd
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, reg₂⟩ := VG.Proof.TripleDes.X86_64.Key.pc2_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [word₁] at word₂
  have checks : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13, .r14, .r15],
      ((instrs keyPermutation2.lit).all fun op => op.dst != some r) = true := by decide +kernel
  have keep₂ : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13, .r14, .r15], s₂.gpr r = s.gpr r := by
    intro r hr
    have unused : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13, .r14, .r15], r ≠ .rax := by decide
    exact (reg₂ r (checks r hr)).trans (reg₁ r (unused r hr))
  have counter₂ := (keep₂ .r14 (by decide)).trans hjreg
  have write₂ : InRegions s₂.wr (s₂.gpr .r15) 8 := by
    rw [wr₂, wr₁, keep₂ .r15 (by decide)]; exact hw
  obtain ⟨s₃, run₃, mem₃, ptr₃, counter₃, flag₃, rd₃, wr₃, reg₃⟩ := VG.Proof.TripleDes.X86_64.Key.tail_ok s₂ j hj counter₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ⟨?_, ?_, counter₃, flag₃, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), ?_⟩⟩
  · rw [mem₃, mem₂, mem₁, keep₂ .r15 (by decide), word₂]
  · rw [ptr₃, keep₂ .r15 (by decide)]
  · intro r hr
    have incl : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13],
        r ≠ .r14 ∧ r ≠ .r15 ∧ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13, .r14, .r15] := by decide
    exact (reg₃ r (incl r hr).1 (incl r hr).2.1).trans (keep₂ r (incl r hr).2.2)

end VG.Proof.TripleDes.X86_64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Key.Loop`. -/
section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64
open VG.Proof.TripleDes (keyPrefix keyInitial keyStep keyPrefix_succ)

structure LoopState (key : BitVec 64) (base : Addr) (origin : State) (j : Nat) (s : State) : Prop where
  c : s.gpr .r12 = (keyPrefix key j).1.setWidth 64
  d : s.gpr .r13 = (keyPrefix key j).2.1.setWidth 64
  counter : s.gpr .r14 = BitVec.ofNat 64 j
  pointer : s.gpr .r15 = base + BitVec.ofNat 64 (8 * j)
  keys : ∀ i < j, ∀ hi : i < 16, s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 =
    ((keyPrefix key j).2.2[i]'hi).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp], s.gpr r = origin.gpr r
  frame : VG.Frame [⟨base, 128⟩] origin.mem s.mem

def LoopInv (key : BitVec 64) (base : Addr) (origin : State) (n : Nat) (s : State) : Prop :=
  1 ≤ n ∧ n ≤ 16 ∧ VG.Proof.TripleDes.X86_64.Key.LoopState key base origin (16 - n) s

theorem loopBody_ok (key : BitVec 64) (base : Addr) (origin : State)
    (hw : ∀ j < 16, InRegions origin.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (j : Nat) (hj : j < 16) (s : State) (hs : VG.Proof.TripleDes.X86_64.Key.LoopState key base origin j s) :
    WP isa (.seq Impl.TripleDes.X86_64.Key.rotation (.block Impl.TripleDes.X86_64.Key.storeRound)) s
      (fun s' => s'.zf = some (decide (j = 15)) ∧ VG.Proof.TripleDes.X86_64.Key.LoopState key base origin (j + 1) s') := by
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86_64.Key.rotation_ok s _ _ j hj hs.c hs.d hs.counter)
  intro s₁ h₁
  have unused : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r14, .r15],
      r ≠ .rax ∧ r ≠ .r12 ∧ r ≠ .r13 := by decide
  have reg₁ : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r14, .r15], s₁.gpr r = s.gpr r := by
    intro r hr
    exact h₁.reg r (unused r hr).1 (unused r hr).2.1 (unused r hr).2.2
  have write₁ : InRegions s₁.wr (s₁.gpr .r15) 8 := by
    rw [h₁.wr, hs.wr, reg₁ .r15 (by decide), hs.pointer]
    exact hw j hj
  apply WP.mono (VG.Proof.TripleDes.X86_64.Key.storeRound_ok s₁ _ _ j hj h₁.c h₁.d
    ((reg₁ .r14 (by decide)).trans hs.counter) write₁)
  intro s₂ h₂
  have hmem : s₂.mem = s.mem.writeW (base + BitVec.ofNat 64 (8 * j))
      ((Spec.TripleDes.permute Spec.TripleDes.pc2
        ((keyPrefix key j).1.rotateLeft (Spec.TripleDes.rotations.getD j 0) ++
          (keyPrefix key j).2.1.rotateLeft (Spec.TripleDes.rotations.getD j 0))).setWidth 64) := by
    rw [h₂.mem, h₁.mem, reg₁ .r15 (by decide), hs.pointer]
  refine ⟨h₂.flag, ⟨?_, ?_, h₂.counter, ?_, ?_, h₂.rd.trans (h₁.rd.trans hs.rd),
    h₂.wr.trans (h₁.wr.trans hs.wr), ?_, ?_⟩⟩
  · rw [keyPrefix_succ]
    exact (h₂.reg .r12 (by decide)).trans h₁.c
  · rw [keyPrefix_succ]
    exact (h₂.reg .r13 (by decide)).trans h₁.d
  · rw [h₂.ptr, reg₁ .r15 (by decide), hs.pointer]
    change base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 8 = _
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega)
  · intro i hi hi16
    rw [hmem, keyPrefix_succ]
    by_cases he : i = j
    · subst i
      rw [Mem.readW_writeW_self64]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_self hj).symm
    · rw [Mem.readW_writeW_sep (Offset.sep base (by omega_using [hi, he])
        (by omega_using [hi16]) (by omega_using [hj])) (by decide), hs.keys i (by omega_using [hi, he]) hi16]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_ne hi16 (Ne.symm he)).symm
  · intro r hr
    have incl : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp],
        r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13] ∧
        r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r14, .r15] := by decide
    exact (h₂.reg r (incl r hr).1).trans ((reg₁ r (incl r hr).2).trans (hs.reg r hr))
  · rw [hmem]
    exact hs.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base base (by omega_using [hj]) (by omega_using [hj]))

theorem loopStep (key : BitVec 64) (base : Addr) (origin : State)
    (hw : ∀ j < 16, InRegions origin.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (n : Nat) (s : State) (hs : VG.Proof.TripleDes.X86_64.Key.LoopInv key base origin n s) :
    WP isa (.seq Impl.TripleDes.X86_64.Key.rotation (.block Impl.TripleDes.X86_64.Key.storeRound)) s
      (fun s' => (isa.eval .ne s' = some false ∧ VG.Proof.TripleDes.X86_64.Key.LoopState key base origin 16 s') ∨
        (isa.eval .ne s' = some true ∧ ∃ m < n, VG.Proof.TripleDes.X86_64.Key.LoopInv key base origin m s')) := by
  apply WP.mono (VG.Proof.TripleDes.X86_64.Key.loopBody_ok key base origin hw (16 - n) (by omega_using [hs.1]) s hs.2.2)
  intro s' h
  by_cases last : n = 1
  · left
    have idx : 16 - n = 15 := by omega_using [last]
    refine ⟨?_, ?_⟩
    · simp only [eval, h.1, idx, decide_true, Option.map_some, Bool.not_true]
    · simpa only [idx] using h.2
  · right
    have idx : ¬16 - n = 15 := by omega_using [hs.1, hs.2.1, last]
    refine ⟨?_, n - 1, by omega_using [hs.1], ?_⟩
    · simp only [eval, h.1, idx, decide_false, Option.map_some, Bool.not_false]
    · refine ⟨by omega_using [hs.1, last], by omega_using [hs.2.1], ?_⟩
      have eq : 16 - n + 1 = 16 - (n - 1) := by omega_using [hs.1, hs.2.1]
      rw [← eq]
      exact h.2

theorem loop_ok (key : BitVec 64) (base : Addr) (s : State)
    (hw : ∀ j < 16, InRegions s.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (hc : s.gpr .r12 = (keyInitial key).1.setWidth 64)
    (hd : s.gpr .r13 = (keyInitial key).2.1.setWidth 64)
    (hcount : s.gpr .r14 = 0) (hptr : s.gpr .r15 = base) :
    WP isa (.loop (.seq Impl.TripleDes.X86_64.Key.rotation
      (.block Impl.TripleDes.X86_64.Key.storeRound)) .ne) s (VG.Proof.TripleDes.X86_64.Key.LoopState key base s 16) := by
  apply WP.loop (M := isa) (body := .seq Impl.TripleDes.X86_64.Key.rotation
      (.block Impl.TripleDes.X86_64.Key.storeRound)) (c := .ne)
    (Q := VG.Proof.TripleDes.X86_64.Key.LoopState key base s 16) (VG.Proof.TripleDes.X86_64.Key.LoopInv key base s) (VG.Proof.TripleDes.X86_64.Key.loopStep key base s hw) 16 s
  refine ⟨by decide, by decide, hc, hd, hcount, ?_, ?_, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  · exact hptr.trans (BitVec.add_zero base).symm
  · intro i hi
    omega

end VG.Proof.TripleDes.X86_64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Key.Component`. -/
section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64

structure ComponentPost (keys : Spec.TripleDes.DesSchedule) (base : Addr) (s s' : State) : Prop where
  keys : ∀ i < 16, s'.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 = (keys.getD i 0).setWidth 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp], s'.gpr r = s.gpr r
  frame : VG.Frame [⟨base, 128⟩] s.mem s'.mem

theorem component_ok (s : State) (offset component : Nat) (hc : component < 3)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 offset) 8)
    (hw : ∀ j < 16, InRegions s.wr
      (s.gpr .rdx + BitVec.ofNat 64 (128 * component) + BitVec.ofNat 64 (8 * j)) 8) :
    WP isa (Impl.TripleDes.X86_64.Key.component offset component) s
      (VG.Proof.TripleDes.X86_64.Key.ComponentPost (Spec.TripleDes.expandDesKey (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .rdi + BitVec.ofNat 64 offset))))
        (s.gpr .rdx + BitVec.ofNat 64 (128 * component)) s) := by
  rw [Impl.TripleDes.X86_64.Key.component]
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86_64.Key.load_ok s offset component hc hr)
  intro s₁ h₁
  have writes : ∀ j < 16, InRegions s₁.wr
      (s.gpr .rdx + BitVec.ofNat 64 (128 * component) + BitVec.ofNat 64 (8 * j)) 8 := by
    rw [h₁.wr]; exact hw
  apply WP.mono (VG.Proof.TripleDes.X86_64.Key.loop_ok _ _ s₁ writes h₁.c h₁.d h₁.counter h₁.ptr)
  intro s₂ h₂
  refine ⟨?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), ?_⟩
  · intro i hi
    rw [VG.Proof.TripleDes.expandDesKey_prefix, VG.Proof.TripleDes.vector_getD _ i hi 0]
    exact h₂.keys i hi hi
  · rw [← h₁.mem]
    exact h₂.frame

end VG.Proof.TripleDes.X86_64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Key.Copy`. -/
section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

 def copyCode (n : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    [.mov .rax (.mem (memOp .rdx (8 * j))), .store (memOp .rdx (256 + 8 * j)) .rax]

structure CopyPost (base : Addr) (s : State) (n : Nat) (s' : State) : Prop where
  keys : ∀ i < n, s'.mem.readW (base + BitVec.ofNat 64 (256 + 8 * i)) 64 =
    s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  frame : VG.Frame [⟨base + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copy_ok (s : State) (n : Nat) (hn : n ≤ 16)
    (hr : ∀ i < 16, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8)
    (hw : ∀ i < 16, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (256 + 8 * i)) 8) :
    WP isa (.block (VG.Proof.TripleDes.X86_64.Key.copyCode n)) s (VG.Proof.TripleDes.X86_64.Key.CopyPost (s.gpr .rdx) s n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ hi => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [VG.Proof.TripleDes.X86_64.Key.copyCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    apply WP.mono (ih (by omega))
    intro s₁ h₁
    have hbase : s₁.gpr .rdx = s.gpr .rdx := h₁.reg .rdx (by decide)
    have readable : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdx + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [h₁.rd, h₁.wr, hbase]; exact hr n (by omega)
    have writable : InRegions s₁.wr (s₁.gpr .rdx + BitVec.ofNat 64 (256 + 8 * n)) 8 := by
      rw [h₁.wr, hbase]; exact hw n (by omega)
    obtain ⟨s₂, run₂, keep₂⟩ := VG.Proof.Rc2.X86_64.Cbc.copy64_ok s₁ .rdx .rdx
      (8 * n) (256 + 8 * n) (by decide) readable writable
    have source : s₁.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (8 * n)) 64 =
        s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (8 * n)) 64 := by
      apply h₁.frame.readW (r := ⟨s.gpr .rdx + BitVec.ofNat 64 (8 * n), 8⟩)
        (Region.contains_self _ _) _ (by decide)
      intro r h
      obtain rfl := List.mem_singleton.mp h
      exact Offset.disjoint (s.gpr .rdx) (by omega) (by omega) (by decide)
    have mem₂ : s₂.mem = s₁.mem.writeW (s.gpr .rdx + BitVec.ofNat 64 (256 + 8 * n))
        (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (8 * n)) 64) := by
      have hm := keep₂.mem
      rw [hbase, source] at hm
      exact hm
    refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr,
      fun r hr => (keep₂.reg r (by simpa only [List.mem_singleton] using hr)).trans (h₁.reg r hr), ?_⟩⟩
    · intro i hi
      rw [mem₂]
      by_cases he : i = n
      · subst i; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep (s.gpr .rdx) (by omega) (by omega) (by omega)) (by decide)]
        exact h₁.keys i (by omega)
    · rw [mem₂]
      apply h₁.frame.writeW (List.mem_singleton_self _) _
      have hc := Offset.contains_base (s.gpr .rdx + BitVec.ofNat 64 256)
        (d := 8 * n) (n := 8) (k := 128) (by omega) (by omega)
      rw [Offset.add_ofNat_add_ofNat] at hc
      exact hc

end VG.Proof.TripleDes.X86_64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Key.Composition`. -/
section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64
open VG.Proof.TripleDes (componentKeys componentOffset)

abbrev keyR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
abbrev outputR (s : State) : Region := ⟨s.gpr .rdx, 384⟩

def slot (base : Addr) (c j : Nat) : Addr := base + BitVec.ofNat 64 (128 * c + 8 * j)

structure Components (origin s : State) (done : Nat) : Prop where
  keys : ∀ c < done, ∀ j < 16, s.mem.readW (VG.Proof.TripleDes.X86_64.Key.slot (origin.gpr .rdx) c j) 64 =
    ((componentKeys origin.mem (origin.gpr .rdi) (origin.gpr .rsi).toNat c).getD j 0).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp], s.gpr r = origin.gpr r
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.Key.outputR origin] origin.mem s.mem

structure Permissions (s : State) : Prop where
  reads : ∀ offset, offset + 8 ≤ (s.gpr .rsi).toNat →
    InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 offset) 8
  writes : ∀ offset, offset + 8 ≤ 384 → InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 offset) 8
  keyOutput : (VG.Proof.TripleDes.X86_64.Key.keyR s).Disjoint (VG.Proof.TripleDes.X86_64.Key.outputR s)
  valid : Spec.TripleDes.validKey (s.gpr .rsi).toNat

theorem componentStep_ok (origin s : State) (c : Nat) (hc : c < 3)
    (hp : VG.Proof.TripleDes.X86_64.Key.Permissions origin) (hs : VG.Proof.TripleDes.X86_64.Key.Components origin s c)
    (hoff : componentOffset (origin.gpr .rsi).toNat c = 8 * c) :
    WP isa (Impl.TripleDes.X86_64.Key.component (8 * c) c) s
      (VG.Proof.TripleDes.X86_64.Key.Components origin · (c + 1)) := by
  have offsetBound := VG.Proof.TripleDes.componentOffset_bound _ c hp.valid hc
  rw [hoff] at offsetBound
  have read : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (8 * c)) 8 := by
    rw [hs.rd, hs.wr, hs.reg .rdi (by decide)]
    exact hp.reads _ offsetBound
  have write : ∀ j < 16, InRegions s.wr
      (s.gpr .rdx + BitVec.ofNat 64 (128 * c) + BitVec.ofNat 64 (8 * j)) 8 := by
    intro j hj
    rw [hs.wr, hs.reg .rdx (by decide), Offset.add_ofNat_add_ofNat]
    exact hp.writes _ (by omega_using [hc, hj])
  apply WP.mono (VG.Proof.TripleDes.X86_64.Key.component_ok s (8 * c) c hc read write)
  intro t ht
  have frame : VG.Frame [⟨origin.gpr .rdx + BitVec.ofNat 64 (128 * c), 128⟩] s.mem t.mem := by
    have hf := ht.frame
    rw [hs.reg .rdx (by decide)] at hf
    exact hf
  have key : Spec.TripleDes.blockAt s.mem (s.gpr .rdi + BitVec.ofNat 64 (8 * c)) =
      Spec.TripleDes.blockAt origin.mem (origin.gpr .rdi + BitVec.ofNat 64 (8 * c)) := by
    rw [hs.reg .rdi (by decide)]
    apply VG.Proof.TripleDes.blockAt_eq_of_frame _ hs.frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hp.keyOutput.sub_left (Offset.sub_base _ offsetBound)
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r hr => (ht.reg r hr).trans (hs.reg r hr), hs.frame.trans (frame.sub ?_)⟩
  · intro k hk j hj
    by_cases he : k = c
    · subst k
      have h := ht.keys j hj
      rw [key, hs.reg .rdx (by decide), Offset.add_ofNat_add_ofNat] at h
      unfold componentKeys
      rw [hoff]
      exact h
    · have before : k < c := by omega_using [hk, he]
      have sep : (Region.mk (VG.Proof.TripleDes.X86_64.Key.slot (origin.gpr .rdx) k j) 8).Disjoint
          ⟨origin.gpr .rdx + BitVec.ofNat 64 (128 * c), 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [hk, hc, hj]) (by omega_using [hc])
      have hmem := frame.readW (a := VG.Proof.TripleDes.X86_64.Key.slot (origin.gpr .rdx) k j) (w := 64) (r := ⟨VG.Proof.TripleDes.X86_64.Key.slot (origin.gpr .rdx) k j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys k before j hj)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨VG.Proof.TripleDes.X86_64.Key.outputR origin, by simp, Offset.sub_base _ (by omega_using [hc])⟩

theorem copyThird_ok (origin s : State) (hp : VG.Proof.TripleDes.X86_64.Key.Permissions origin)
    (hs : VG.Proof.TripleDes.X86_64.Key.Components origin s 2) (hn : (origin.gpr .rsi).toNat = 16) :
    WP isa (.block Impl.TripleDes.X86_64.Key.copyThird) s (VG.Proof.TripleDes.X86_64.Key.Components origin · 3) := by
  have reads : ∀ i < 16, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hs.rd, hs.wr, hs.reg .rdx (by decide)]
    obtain ⟨r, hr, hc⟩ := hp.writes (8 * i) (by omega_using [hi])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writes : ∀ i < 16, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (256 + 8 * i)) 8 := by
    intro i hi
    rw [hs.wr, hs.reg .rdx (by decide)]
    exact hp.writes _ (by omega_using [hi])
  apply WP.mono (VG.Proof.TripleDes.X86_64.Key.copy_ok s 16 (by decide) reads writes)
  intro t ht
  have frame : VG.Frame [⟨origin.gpr .rdx + BitVec.ofNat 64 256, 128⟩] s.mem t.mem := by
    have h := ht.frame
    rw [hs.reg .rdx (by decide)] at h
    exact h
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr, ?_, hs.frame.trans (frame.sub ?_)⟩
  · intro c hc j hj
    by_cases he : c = 2
    · subst c
      have hRepeat : componentKeys origin.mem (origin.gpr .rdi) (origin.gpr .rsi).toNat 2 =
          componentKeys origin.mem (origin.gpr .rdi) (origin.gpr .rsi).toNat 0 := by
        rw [hn]; rfl
      have h := ht.keys j hj
      rw [hs.reg .rdx (by decide)] at h
      change t.mem.readW (origin.gpr .rdx + BitVec.ofNat 64 (256 + 8 * j)) 64 = _
      rw [hRepeat]
      have first := hs.keys 0 (by decide) j hj
      simp only [VG.Proof.TripleDes.X86_64.Key.slot, Nat.mul_zero, Nat.zero_add] at first
      exact h.trans first
    · have before : c < 2 := by omega_using [hc, he]
      have sep : (Region.mk (VG.Proof.TripleDes.X86_64.Key.slot (origin.gpr .rdx) c j) 8).Disjoint
          ⟨origin.gpr .rdx + BitVec.ofNat 64 256, 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [before, hj]) (by decide)
      have hmem := frame.readW (a := VG.Proof.TripleDes.X86_64.Key.slot (origin.gpr .rdx) c j) (w := 64) (r := ⟨VG.Proof.TripleDes.X86_64.Key.slot (origin.gpr .rdx) c j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys c before j hj)
  · intro r hr
    have unused : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp], r ≠ .rax := by decide
    exact (ht.reg r (unused r hr)).trans (hs.reg r hr)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨VG.Proof.TripleDes.X86_64.Key.outputR origin, by simp, Offset.sub_base _ (by decide)⟩

def componentIndex (i : Nat) : Nat := if i < 16 then 0 else if i < 32 then 1 else 2

theorem index_partition : ∀ i < 48, VG.Proof.TripleDes.X86_64.Key.componentIndex i < 3 ∧ i % 16 < 16 ∧
    8 * i = 128 * VG.Proof.TripleDes.X86_64.Key.componentIndex i + 8 * (i % 16) := by decide

theorem Components.schedule {origin s : State} (h : VG.Proof.TripleDes.X86_64.Key.Components origin s 3) :
    Spec.TripleDes.scheduleAt s.mem (origin.gpr .rdx) =
      VG.Proof.TripleDes.expandedMemory origin.mem (origin.gpr .rdi) (origin.gpr .rsi).toNat := by
  apply Vector.ext
  intro i hi
  have fact := VG.Proof.TripleDes.X86_64.Key.index_partition i hi
  have keys := h.keys (VG.Proof.TripleDes.X86_64.Key.componentIndex i) fact.1 (i % 16) fact.2.1
  rw [VG.Proof.TripleDes.X86_64.Key.slot, ← fact.2.2] at keys
  rw [VG.Proof.TripleDes.scheduleAt_readW s.mem (origin.gpr .rdx) i hi]
  simp only [VG.Proof.TripleDes.expandedMemory, Vector.getElem_ofFn]
  by_cases h16 : i < 16
  · simpa only [VG.Proof.TripleDes.X86_64.Key.componentIndex, h16, ite_true] using keys
  · by_cases h32 : i < 32
    · simpa only [VG.Proof.TripleDes.X86_64.Key.componentIndex, h16, h32, ite_false, ite_true] using keys
    · simpa only [VG.Proof.TripleDes.X86_64.Key.componentIndex, h16, h32, ite_false] using keys


end VG.Proof.TripleDes.X86_64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Key.Body`. -/
section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Rc2.X86_64 (Keep)

theorem cmpLength_ok (s : State) :
    ∃ s', runBlock isa [.alu .cmp .rsi (.imm 16)] s = some s' ∧
      s'.zf = some (s.gpr .rsi == 16) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
    rfl, ?_, ?_⟩
  · rw [zf_arithFlags]
    exact congrArg some (by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      change (s.gpr .rsi - (16 : BitVec 64) = (0 : BitVec 64)) ↔ s.gpr .rsi = (16 : BitVec 64)
      bv_omega)
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Components.keep {origin s t : State} {n : Nat} (hs : VG.Proof.TripleDes.X86_64.Key.Components origin s n)
    (ht : Keep [] s t) : VG.Proof.TripleDes.X86_64.Key.Components origin t n :=
  ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r hr => (ht.reg r (by simp)).trans (hs.reg r hr), by rw [ht.mem]; exact hs.frame⟩

theorem beq16_toNat (x : BitVec 64) : (x == 16) = decide (x.toNat = 16) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    apply BitVec.eq_of_toNat_eq
    exact h

theorem body_ok (origin s : State) (hp : VG.Proof.TripleDes.X86_64.Key.Permissions origin) (hs : VG.Proof.TripleDes.X86_64.Key.Components origin s 0)
    (Q : State → Prop)
    (finish : ∀ t, VG.Proof.TripleDes.X86_64.Key.Components origin t 3 → WP isa (.block Impl.TripleDes.X86_64.Key.restore) t Q) :
    WP isa (.seq (Impl.TripleDes.X86_64.Key.component 0 0)
      (.seq (Impl.TripleDes.X86_64.Key.component 8 1)
        (.seq (.block [.alu .cmp .rsi (.imm 16)])
          (.seq (.ite .e (.block Impl.TripleDes.X86_64.Key.copyThird)
            (Impl.TripleDes.X86_64.Key.component 16 2)) (.block Impl.TripleDes.X86_64.Key.restore))))) s Q := by
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86_64.Key.componentStep_ok origin s 0 (by decide) hp hs (by rfl))
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86_64.Key.componentStep_ok origin s₁ 1 (by decide) hp hs₁ (by rfl))
  intro s₂ hs₂
  apply WP.seq
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := VG.Proof.TripleDes.X86_64.Key.cmpLength_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have hs₃ := hs₂.keep keep₃
  apply WP.seq
  apply WP.mono (Q := (VG.Proof.TripleDes.X86_64.Key.Components origin · 3)) ?_
  · intro t ht
    exact finish t ht
  have flag : s₃.zf = some (decide ((origin.gpr .rsi).toNat = 16)) := by
    rw [flag₃, hs₂.reg .rsi (by decide), VG.Proof.TripleDes.X86_64.Key.beq16_toNat]
  by_cases h16 : (origin.gpr .rsi).toNat = 16
  · apply WP.ite true (by simp only [eval, flag, h16, decide_true])
    · intro _; exact VG.Proof.TripleDes.X86_64.Key.copyThird_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simp only [eval, flag, h16, decide_false])
    · simp
    · intro _
      exact VG.Proof.TripleDes.X86_64.Key.componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

end VG.Proof.TripleDes.X86_64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Key.Save`. -/
section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

/-- The six callee-saved registers, in slot order. -/
def savedReg (i : Nat) : Reg := (Impl.TripleDes.X86_64.Key.savedRegs).getD i .rdi

theorem save_eq : Impl.TripleDes.X86_64.Key.save = VG.Proof.Rc2.X86_64.saveCode .rcx VG.Proof.TripleDes.X86_64.Key.savedReg 6 := by
  decide +kernel

theorem restore_eq : Impl.TripleDes.X86_64.Key.restore = VG.Proof.Rc2.X86_64.restoreCode .rcx VG.Proof.TripleDes.X86_64.Key.savedReg (List.range 6) := by
  decide +kernel

def Saved (original current : State) : Prop :=
  ∀ i < 6, current.mem.readW (current.gpr .rcx + BitVec.ofNat 64 (8 * i)) 64 =
    original.gpr (VG.Proof.TripleDes.X86_64.Key.savedReg i)

theorem save_ok (s : State)
    (hw : ∀ i < 6, InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block Impl.TripleDes.X86_64.Key.save) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ VG.Proof.TripleDes.X86_64.Key.Saved s s' ∧
      VG.Frame [⟨s.gpr .rcx, 48⟩] s.mem s'.mem) := by
  rw [VG.Proof.TripleDes.X86_64.Key.save_eq]
  apply WP.mono (VG.Proof.Rc2.X86_64.saveCode_ok s .rcx VG.Proof.TripleDes.X86_64.Key.savedReg 6 hw)
  intro s' hs
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_, ?_⟩
  · intro i hi
    rw [hs.1, hs.2.2.2]
    exact VG.Proof.Rc2.X86_64.saveMem_read _ _ _ 6 (by decide) i hi
  · rw [hs.2.2.2]
    exact VG.Proof.Rc2.X86_64.saveMem_frame _ _ _ 6 (by decide)

theorem savedReg_separate : ∀ i < 6, VG.Proof.TripleDes.X86_64.Key.savedReg i ≠ .rcx := by decide +kernel

theorem restore_ok (original s : State) (hsaved : VG.Proof.TripleDes.X86_64.Key.Saved original s)
    (hread : ∀ i < 6, InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block Impl.TripleDes.X86_64.Key.restore) s (fun s' =>
      (∀ r ∈ Impl.TripleDes.X86_64.Key.savedRegs, s'.gpr r = original.gpr r) ∧
      VG.Proof.Rc2.X86_64.Keep (Impl.TripleDes.X86_64.Key.savedRegs) s s') := by
  rw [VG.Proof.TripleDes.X86_64.Key.restore_eq]
  have hregs : (List.range 6).map VG.Proof.TripleDes.X86_64.Key.savedReg = Impl.TripleDes.X86_64.Key.savedRegs := by decide +kernel
  have h := VG.Proof.Rc2.X86_64.restoreCode_ok s .rcx VG.Proof.TripleDes.X86_64.Key.savedReg (List.range 6) original.gpr
    (fun i hi => VG.Proof.TripleDes.X86_64.Key.savedReg_separate i (List.mem_range.mp hi))
    (fun i hi => hread i (List.mem_range.mp hi))
    (fun i hi => hsaved i (List.mem_range.mp hi))
  rw [hregs] at h
  exact h



end VG.Proof.TripleDes.X86_64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Key.Contract`. -/
section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64

def contract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let output : Region := ⟨s.gpr .rdx, 384⟩
    let scratch : Region := ⟨s.gpr .rcx, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [output, scratch] ∧ key.Disjoint output ∧ key.Disjoint scratch ∧
      output.Disjoint scratch ∧ ret.Disjoint output ∧ ret.Disjoint scratch ∧
      Spec.TripleDes.validKey (s.gpr .rsi).toNat
  post s s' := Spec.TripleDes.scheduleAt s'.mem (s.gpr .rdx) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub := PublicRegs [.rdi, .rsi, .rdx, .rcx]

end VG.Proof.TripleDes.X86_64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Key.Correct`. -/
section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64

 theorem expand_correct (s : State) (hs : contract.pre s) :
    WP isa Impl.TripleDes.X86_64.Key.expandKey s (fun s' => gprPreserved s s' ∧ contract.post s s') := by
  obtain ⟨hrd, hwr, keyOutput, keyScratch, outputScratch, retOutput, retScratch, valid⟩ := hs
  have scratchWrites : ∀ i < 6, InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rcx, 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  rw [Impl.TripleDes.X86_64.Key.expandKey]
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86_64.Key.save_ok s scratchWrites)
  intro s₁ h₁
  have g₁ (r : Reg) : s₁.gpr r = s.gpr r := congrFun h₁.1 r
  have hp : VG.Proof.TripleDes.X86_64.Key.Permissions s₁ := by
    constructor
    · intro offset hoff
      rw [h₁.2.1, h₁.2.2.1, g₁, hrd, hwr]
      exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp,
        Offset.contains_base _ (by simpa only [g₁] using hoff) (by
          have bound := BitVec.isLt (s.gpr .rsi)
          rw [g₁] at hoff
          omega_using [hoff, bound])⟩
    · intro offset hoff
      rw [h₁.2.2.1, g₁, hwr]
      exact ⟨⟨s.gpr .rdx, 384⟩, by simp, Offset.contains_base _ hoff (by omega_using [hoff])⟩
    · simpa only [VG.Proof.TripleDes.X86_64.Key.keyR, VG.Proof.TripleDes.X86_64.Key.outputR, g₁] using keyOutput
    · simpa only [g₁] using valid
  apply VG.Proof.TripleDes.X86_64.Key.body_ok s₁ s₁ hp ⟨fun _ h => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  intro s₂ h₂
  have g₂ (r : Reg) (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp]) : s₂.gpr r = s.gpr r :=
    (h₂.reg r hr).trans (g₁ r)
  have frame₂ : Frame [⟨s.gpr .rdx, 384⟩] s₁.mem s₂.mem := by
    have h := h₂.frame
    rw [VG.Proof.TripleDes.X86_64.Key.outputR, g₁] at h
    exact h
  have saved₂ : VG.Proof.TripleDes.X86_64.Key.Saved s s₂ := by
    intro i hi
    have sub : Region.Sub ⟨s.gpr .rcx + BitVec.ofNat 64 (8 * i), 8⟩ ⟨s.gpr .rcx, 512⟩ :=
      Offset.sub_base _ (by omega_using [hi])
    have mem := frame₂.readW (a := s.gpr .rcx + BitVec.ofNat 64 (8 * i)) (w := 64)
      (r := ⟨s.gpr .rcx + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact (outputScratch.sub_right sub).symm)
      (by decide)
    rw [g₂ .rcx (by decide)]
    have saved₁ := h₁.2.2.2.1 i hi
    rw [g₁] at saved₁
    exact mem.trans saved₁
  have scratchReads : ∀ i < 6, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rcx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [h₂.rd, h₂.wr, h₁.2.1, h₁.2.2.1, g₂ .rcx (by decide)]
    obtain ⟨r, hr, hc⟩ := scratchWrites i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.mono (VG.Proof.TripleDes.X86_64.Key.restore_ok s s₂ saved₂ scratchReads)
  intro s₃ h₃
  have scratchFrame : Frame [⟨s.gpr .rcx, 512⟩] s.mem s₁.mem := h₁.2.2.2.2.sub (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨s.gpr .rcx, 512⟩, by simp, Region.sub_prefix (by decide)⟩)
  have initialBytes := VG.Proof.TripleDes.bytesAt_eq_of_frame (s.gpr .rdi) (s.gpr .rsi).toNat
    scratchFrame (Nat.le_of_lt (BitVec.isLt _)) (by simpa using keyScratch)
  constructor
  · constructor
    · intro r hr
      by_cases hrsp : r = .rsp
      · subst r
        exact (h₃.2.reg .rsp (by decide)).trans (g₂ .rsp (by decide))
      · have saved : ∀ r ∈ calleeSaved, r ≠ .rsp → r ∈ Impl.TripleDes.X86_64.Key.savedRegs := by decide
        exact h₃.1 r (saved r hr hrsp)
    · have frame : Frame [⟨s.gpr .rdx, 384⟩, ⟨s.gpr .rcx, 512⟩] s.mem s₃.mem := by
        rw [h₃.2.mem]
        exact (scratchFrame.mono (by simp)).trans (frame₂.mono (by simp))
      apply frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
      simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
        And.intro retOutput retScratch
  · have result := h₂.schedule
    simp only [g₁] at result
    rw [← VG.Proof.TripleDes.expandKey_memory s₁.mem (s.gpr .rdi) (s.gpr .rsi).toNat valid,
      initialBytes] at result
    change Spec.TripleDes.scheduleAt s₃.mem (s.gpr .rdx) = _
    rw [h₃.2.mem]
    exact result

end VG.Proof.TripleDes.X86_64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Key.Verified`. -/
section

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 384⟩, ⟨0x3000, 512⟩]

theorem correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa Impl.TripleDes.X86_64.Key.expandKey s t s' ∧ abiPreserved s s' ∧ contract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.TripleDes.X86_64.Key.expand_correct s hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx, .rcx] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx := by simp [PublicRegs]

theorem verified : Verified target Impl.TripleDes.X86_64.Key.expandKey
    (Proof.TripleDes.expandKeyScratchContract abi) := by
  refine Verified.of_correct VG.Proof.TripleDes.X86_64.Key.correct (expandKey_constantTime _) ?_
  sig_implies [Proof.TripleDes.expandKeyScratchContract, Proof.TripleDes.expandKeyScratchSig, Spec.TripleDes.expandKeyPre, Spec.TripleDes.expandKeyPost, abi, argRegs,
    VG.Proof.TripleDes.X86_64.Key.contract, VG.Proof.TripleDes.X86_64.Key.publicRegs_four] [satState] using VG.Proof.TripleDes.X86_64.Key.satState

end VG.Proof.TripleDes.X86_64.Key

end
