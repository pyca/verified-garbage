import VerifiedGarbage.Proof.TripleDes.AArch64.VerifiedBlock
import VerifiedGarbage.Proof.TripleDes.KeySchedule
import VerifiedGarbage.Proof.Rc2.AArch64.Block
import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.KeyMemory
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.TripleDes.Scratch

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Key.Rotation`. -/
section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64
open VG.Proof.Rc2.AArch64 (Keep)

structure RotatePost (c d : BitVec 28) (n : Nat) (s s' : State) : Prop where
  c : s'.gpr .x19 = (c.rotateLeft n).setWidth 64
  d : s'.gpr .x20 = (d.rotateLeft n).setWidth 64
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .x4 → r ≠ .x19 → r ≠ .x20 → s'.gpr r = s.gpr r

theorem rotate_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .x19 = c.setWidth 64) (hd : s.gpr .x20 = d.setWidth 64)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 28) :
    WP isa (Impl.TripleDes.AArch64.Key.rotate n) s (VG.Proof.TripleDes.AArch64.Key.RotatePost c d n s) := by
  rw [Impl.TripleDes.AArch64.Key.rotate, WP.block_append_iff]
  obtain ⟨s₁, run₁, c₁, mem₁, rd₁, wr₁, _, reg₁⟩ := rotate28_ok s .x19 (by decide) c hc n hn hn'
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have d₁ : s₁.gpr .x20 = d.setWidth 64 := (reg₁ .x20 (by decide) (by decide)).trans hd
  obtain ⟨s₂, run₂, d₂, mem₂, rd₂, wr₂, _, reg₂⟩ := rotate28_ok s₁ .x20 (by decide) d d₁ n hn hn'
  refine WP.of_runBlock ⟨s₂, run₂, ⟨(reg₂ .x19 (by decide) (by decide)).trans c₁, d₂,
    mem₂.trans mem₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩⟩
  intro r ha hc hd
  exact (reg₂ r hd ha).trans (reg₁ r hc ha)

theorem comparison_values : ∀ j < 16, ∀ k < 16,
    ((BitVec.ofNat 64 j >>> 1) == (0 : BitVec 64)) = decide (j < 2) ∧
    ((BitVec.ofNat 64 j - BitVec.ofNat 64 k) == (0 : BitVec 64)) = decide (j = k) := by
  decide

theorem write_keep (s : State) (v : BitVec 64) : Keep [.x4] s (s.write .x .x4 v) := by
  refine ⟨?_, mem_write _ _ _ _, rd_write _ _ _ _, wr_write _ _ _ _⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  exact gpr_write_of_ne _ _ _ hr

theorem lowTest_ok (s : State) (j : Nat) (hj : j < 16)
    (hv : s.gpr .x21 = BitVec.ofNat 64 j) :
    ∃ s', runBlock isa [.lsr .x .x4 .x21 1] s = some s' ∧
      isa.eval (.zero .x .x4) s' = some (decide (j < 2)) ∧ Keep [.x4] s s' := by
  refine ⟨s.write .x .x4 (s.gpr .x21 >>> 1), ?_, ?_, VG.Proof.TripleDes.AArch64.Key.write_keep _ _⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show (1 : Nat) < 64 from by decide, ite_true, State.read, BitVec.setWidth_eq]
  · change VG.AArch64.eval (.zero .x .x4) _ = _
    simp only [VG.AArch64.eval, State.read, gpr_write_self, BitVec.setWidth_eq, hv]
    exact congrArg some (VG.Proof.TripleDes.AArch64.Key.comparison_values j hj 0 (by decide)).1

theorem eqTest_ok (s : State) (j k : Nat) (hj : j < 16) (hk : k < 16)
    (hv : s.gpr .x21 = BitVec.ofNat 64 j) :
    ∃ s', runBlock isa [.subImm .x .x4 .x21 k] s = some s' ∧
      isa.eval (.zero .x .x4) s' = some (decide (j = k)) ∧ Keep [.x4] s s' := by
  refine ⟨s.write .x .x4 (s.gpr .x21 - BitVec.ofNat 64 k), ?_, ?_, VG.Proof.TripleDes.AArch64.Key.write_keep _ _⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show k < 4096 from by omega, ite_true, State.read, BitVec.setWidth_eq]
  · change VG.AArch64.eval (.zero .x .x4) _ = _
    simp only [VG.AArch64.eval, State.read, gpr_write_self, BitVec.setWidth_eq, hv]
    exact congrArg some (VG.Proof.TripleDes.AArch64.Key.comparison_values j hj k hk).2

theorem rotation_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .x19 = c.setWidth 64) (hd : s.gpr .x20 = d.setWidth 64)
    (hjreg : s.gpr .x21 = BitVec.ofNat 64 j) :
    WP isa Impl.TripleDes.AArch64.Key.rotation s
      (VG.Proof.TripleDes.AArch64.Key.RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
  rw [Impl.TripleDes.AArch64.Key.rotation]
  apply WP.seq
  obtain ⟨s₁, run₁, cond₁, keep₁⟩ := VG.Proof.TripleDes.AArch64.Key.lowTest_ok s j hj hjreg
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hrot (s' : State) (h : Keep [.x4] s s') (n : Nat) (hn : 1 ≤ n) (hn' : n < 28)
      (hv : Spec.TripleDes.rotations.getD j 0 = n) :
      WP isa (Impl.TripleDes.AArch64.Key.rotate n) s' (VG.Proof.TripleDes.AArch64.Key.RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
    apply WP.mono (VG.Proof.TripleDes.AArch64.Key.rotate_ok s' c d ((h.reg .x19 (by simp)).trans hc)
      ((h.reg .x20 (by simp)).trans hd) n hn hn')
    intro t ht
    rw [hv]
    exact ⟨ht.c, ht.d, ht.mem.trans h.mem, ht.rd.trans h.rd, ht.wr.trans h.wr,
      fun r ha hc hd => (ht.reg r ha hc hd).trans (h.reg r (by simpa only [List.mem_singleton] using ha))⟩
  have combine {a b : State} (ha : Keep [.x4] s a) (hb : Keep [.x4] a b) : Keep [.x4] s b :=
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
      obtain ⟨s₂, run₂, cond₂, keep₂⟩ := VG.Proof.TripleDes.AArch64.Key.eqTest_ok s₁ j 8 hj (by decide)
        ((keep₁.reg .x21 (by simp)).trans hjreg)
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
          obtain ⟨s₃, run₃, cond₃, keep₃⟩ := VG.Proof.TripleDes.AArch64.Key.eqTest_ok s₂ j 15 hj (by decide)
            ((keep₂'.reg .x21 (by simp)).trans hjreg)
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

end VG.Proof.TripleDes.AArch64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Key.Permutation`. -/
section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

 theorem pc1_ok (s : VG.AArch64.State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc1 64 .x5 .x4 .x6 .x7) s = some s' ∧
      s'.gpr .x5 = (Spec.TripleDes.permute Spec.TripleDes.pc1 (s.gpr .x4)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation1.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc1 (by decide) (by decide) (by decide)
       .x4 .x5 (instrs keyPermutation1.lit) keyPermutation1_check s
  have hcode : permuteCode Spec.TripleDes.pc1 64 .x5 .x4 .x6 .x7 = instrs keyPermutation1.lit :=
    congrArg instrs keyPermutation1.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, sp, mem, regs⟩
  exact word.trans (congrArg (fun x => (Spec.TripleDes.permute Spec.TripleDes.pc1 x).setWidth 64)
    (BitVec.setWidth_eq _))

theorem pc2_ok (s : VG.AArch64.State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc2 56 .x5 .x4 .x6 .x7) s = some s' ∧
      s'.gpr .x5 = (Spec.TripleDes.permute Spec.TripleDes.pc2 ((s.gpr .x4).setWidth 56)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation2.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc2 (by decide) (by decide) (by decide)
       .x4 .x5 (instrs keyPermutation2.lit) keyPermutation2_check s
  have hcode : permuteCode Spec.TripleDes.pc2 56 .x5 .x4 .x6 .x7 = instrs keyPermutation2.lit :=
    congrArg instrs keyPermutation2.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, word, rd, wr, sp, mem, regs⟩

end VG.Proof.TripleDes.AArch64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Key.Load`. -/
section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64

def keyKept : List Reg := [.x0, .x1, .x2, .x3, .x23, .x24, .x25, .x26, .x27, .x28, .x30]

theorem readKey_ok (s : VG.AArch64.State) (offset : Nat) (ho : offset % 8 = 0 ∧ offset < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 offset) 8) :
    ∃ s', runBlock isa [.ldr .x .x4 .x0 offset, .rev .x4 .x4] s = some s' ∧
      s'.gpr .x4 = Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .x0 + BitVec.ofNat 64 offset)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [runBlock_cons, VG.AArch64.exec_ldr_x ho hr, runStep_some, runBlock_nil,
      exec_rev, State.read, BitVec.setWidth_eq, gpr_write_self]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write_self, BitVec.setWidth_eq]
    exact (decodeBlock_readW s.mem _).symm
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · intro r hr; simp only [gpr_write, hr, ite_false]

def loadTail (component : Nat) : List Instr :=
  [.lsr .x .x19 .x5 28, VG.Impl.TripleDes.AArch64.rr .x20 .x5] ++ VG.Impl.TripleDes.AArch64.mask .x20 28 ++
    [VG.Impl.TripleDes.AArch64.imm .x21 0, .addImm .x .x22 .x2 (128 * component)]

theorem loadTail_ok (s : VG.AArch64.State) (component : Nat) (hc : component < 3) (x : BitVec 56)
    (hx : s.gpr .x5 = x.setWidth 64) :
    ∃ s', runBlock isa (VG.Proof.TripleDes.AArch64.Key.loadTail component) s = some s' ∧
      s'.gpr .x19 = ((x >>> 28).setWidth 28).setWidth 64 ∧
      s'.gpr .x20 = (x.setWidth 28).setWidth 64 ∧ s'.gpr .x21 = 0 ∧
      s'.gpr .x22 = s.gpr .x2 + BitVec.ofNat 64 (128 * component) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ [Reg.x19, .x20, .x21, .x22] → s'.gpr r = s.gpr r) := by
  have hb : 128 * component < 4096 := by omega
  refine ⟨_, by
    simp only [VG.Proof.TripleDes.AArch64.Key.loadTail, VG.Impl.TripleDes.AArch64.rr, VG.Impl.TripleDes.AArch64.imm, VG.Impl.TripleDes.AArch64.mask, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits, hb,
      show (28 : Nat) < 64 from by decide, show (36 : Nat) < 64 from by decide,
      show (0 : Nat) < 64 from by decide, show (0 : Nat) < 4096 from by decide,
      Nat.mul_zero, ite_true, State.read, BitVec.setWidth_eq, gpr_write,
      BitVec.add_zero, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    rw [hx]; exact VG.Proof.TripleDes.split28_upper x
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    rw [hx, mask_word _ 28 (by decide) (by decide), BitVec.setWidth_setWidth_of_le x (by decide : 28 ≤ 64)]
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

structure LoadPost (x : BitVec 56) (component : Nat) (s s' : VG.AArch64.State) : Prop where
  c : s'.gpr .x19 = ((x >>> 28).setWidth 28).setWidth 64
  d : s'.gpr .x20 = (x.setWidth 28).setWidth 64
  counter : s'.gpr .x21 = 0
  ptr : s'.gpr .x22 = s.gpr .x2 + BitVec.ofNat 64 (128 * component)
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ VG.Proof.TripleDes.AArch64.Key.keyKept, s'.gpr r = s.gpr r

theorem load_ok (s : VG.AArch64.State) (offset component : Nat) (hc : component < 3)
    (ho : offset % 8 = 0 ∧ offset < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 offset) 8) :
    WP isa (.block (Impl.TripleDes.AArch64.Key.load offset component)) s
      (VG.Proof.TripleDes.AArch64.Key.LoadPost (Spec.TripleDes.permute Spec.TripleDes.pc1 (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .x0 + BitVec.ofNat 64 offset)))) component s) := by
  have code : Impl.TripleDes.AArch64.Key.load offset component =
      (([.ldr .x .x4 .x0 offset, .rev .x4 .x4] : List Instr) ++
        permuteCode Spec.TripleDes.pc1 64 .x5 .x4 .x6 .x7) ++ VG.Proof.TripleDes.AArch64.Key.loadTail component := by
    simp only [Impl.TripleDes.AArch64.Key.load, VG.Proof.TripleDes.AArch64.Key.loadTail, List.append_assoc]
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, key₁, mem₁, rd₁, wr₁, reg₁⟩ := VG.Proof.TripleDes.AArch64.Key.readKey_ok s offset ho hr
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, _, mem₂, reg₂⟩ := VG.Proof.TripleDes.AArch64.Key.pc1_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [key₁] at word₂
  obtain ⟨s₃, run₃, c₃, d₃, counter₃, ptr₃, mem₃, rd₃, wr₃, reg₃⟩ := VG.Proof.TripleDes.AArch64.Key.loadTail_ok s₂ component hc _ word₂
  refine WP.of_runBlock ⟨s₃, run₃, ⟨c₃, d₃, counter₃, ?_, mem₃.trans (mem₂.trans mem₁),
    rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_⟩⟩
  · have rdx₂ : s₂.gpr .x2 = s.gpr .x2 :=
      (reg₂ .x2 (by decide +kernel)).trans (reg₁ .x2 (by decide))
    rw [rdx₂] at ptr₃
    exact ptr₃
  · intro r hr
    have unused : ∀ r ∈ VG.Proof.TripleDes.AArch64.Key.keyKept,
        r ∉ [Reg.x19, .x20, .x21, .x22] ∧ r ≠ .x4 := by decide
    have hcheck : ∀ r ∈ VG.Proof.TripleDes.AArch64.Key.keyKept,
        ((instrs keyPermutation1.lit).all fun op => dstOf op != some r) = true := by decide +kernel
    exact (reg₃ r (unused r hr).1).trans ((reg₂ r (hcheck r hr)).trans (reg₁ r (unused r hr).2))

end VG.Proof.TripleDes.AArch64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Key.Store`. -/
section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64

def pack : List Instr := [.lsl .x .x4 .x19 28, .logic .eor .x .x4 .x4 .x20]

def tail : List Instr := [.str .x .x5 .x22 0, .addImm .x .x22 .x22 8,
  .addImm .x .x21 .x21 1, .subImm .x .x4 .x21 16]

theorem pack_ok (s : VG.AArch64.State) (c d : BitVec 28)
    (hc : s.gpr .x19 = c.setWidth 64) (hd : s.gpr .x20 = d.setWidth 64) :
    ∃ s', runBlock isa VG.Proof.TripleDes.AArch64.Key.pack s = some s' ∧
      (s'.gpr .x4).setWidth 56 = c ++ d ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [VG.Proof.TripleDes.AArch64.Key.pack, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show (28 : Nat) < 64 from by decide, ite_true, State.read,
      BitVec.setWidth_eq, gpr_write_self]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    rw [hc, hd]; exact pack28_shift c d
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · intro r hr; simp only [gpr_write, hr, ite_false]

theorem nextRound_values : ∀ j < 16,
    BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) ∧
    ((BitVec.ofNat 64 j + 1 - (16 : BitVec 64)) != 0) = decide (j ≠ 15) := by decide

theorem tail_ok (s : VG.AArch64.State) (j : Nat) (hj : j < 16)
    (hc : s.gpr .x21 = BitVec.ofNat 64 j)
    (hw : InRegions s.wr (s.gpr .x22) 8) :
    ∃ s', runBlock isa VG.Proof.TripleDes.AArch64.Key.tail s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .x22) (s.gpr .x5) ∧
      s'.gpr .x22 = s.gpr .x22 + 8 ∧ s'.gpr .x21 = BitVec.ofNat 64 (j + 1) ∧
      isa.eval (.nonzero .x .x4) s' = some (decide (j ≠ 15)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .x4 → r ≠ .x21 → r ≠ .x22 → s'.gpr r = s.gpr r) := by
  have hstore := VG.AArch64.exec_str_x (t := .x5) (n := .x22) (off := 0) (by decide)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw)
  refine ⟨_, by
    rw [VG.Proof.TripleDes.AArch64.Key.tail, runBlock_cons, hstore, runStep_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show (8 : Nat) < 4096 from by decide, show (1 : Nat) < 4096 from by decide,
      show (16 : Nat) < 4096 from by decide, ite_true, State.read, BitVec.setWidth_eq,
      gpr_write, reduceCtorEq, ite_false, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_write, BitVec.add_zero]
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    rw [hc]; exact (VG.Proof.TripleDes.AArch64.Key.nextRound_values j hj).1
  · change VG.AArch64.eval (.nonzero .x .x4) _ = _
    simp only [VG.AArch64.eval, State.read, gpr_write, BitVec.setWidth_eq,
      reduceCtorEq, ite_true, ite_false, hc]
    exact congrArg some (VG.Proof.TripleDes.AArch64.Key.nextRound_values j hj).2
  · simp only [rd_write]
  · simp only [wr_write]
  · intro r h4 h21 h22; simp only [gpr_write, h4, h21, h22, ite_false]

structure StorePost (c d : BitVec 28) (j : Nat) (s s' : VG.AArch64.State) : Prop where
  mem : s'.mem = s.mem.writeW (s.gpr .x22) ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64)
  ptr : s'.gpr .x22 = s.gpr .x22 + 8
  counter : s'.gpr .x21 = BitVec.ofNat 64 (j + 1)
  flag : isa.eval (.nonzero .x .x4) s' = some (decide (j ≠ 15))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ (VG.Proof.TripleDes.AArch64.Key.keyKept ++ [.x19, .x20]), s'.gpr r = s.gpr r

theorem storeRound_ok (s : VG.AArch64.State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .x19 = c.setWidth 64) (hd : s.gpr .x20 = d.setWidth 64)
    (hjreg : s.gpr .x21 = BitVec.ofNat 64 j) (hw : InRegions s.wr (s.gpr .x22) 8) :
    WP isa (.block Impl.TripleDes.AArch64.Key.storeRound) s (VG.Proof.TripleDes.AArch64.Key.StorePost c d j s) := by
  have code : Impl.TripleDes.AArch64.Key.storeRound =
      (VG.Proof.TripleDes.AArch64.Key.pack ++ permuteCode Spec.TripleDes.pc2 56 .x5 .x4 .x6 .x7) ++ VG.Proof.TripleDes.AArch64.Key.tail := rfl
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, reg₁⟩ := VG.Proof.TripleDes.AArch64.Key.pack_ok s c d hc hd
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, _, mem₂, reg₂⟩ := VG.Proof.TripleDes.AArch64.Key.pc2_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [word₁] at word₂
  have checks : ∀ r ∈ (VG.Proof.TripleDes.AArch64.Key.keyKept ++ [.x19, .x20, .x21, .x22]),
      ((instrs keyPermutation2.lit).all fun op => dstOf op != some r) = true := by decide +kernel
  have keep₂ : ∀ r ∈ (VG.Proof.TripleDes.AArch64.Key.keyKept ++ [.x19, .x20, .x21, .x22]), s₂.gpr r = s.gpr r := by
    intro r hr
    have unused : ∀ r ∈ (VG.Proof.TripleDes.AArch64.Key.keyKept ++ [.x19, .x20, .x21, .x22]), r ≠ .x4 := by decide
    exact (reg₂ r (checks r hr)).trans (reg₁ r (unused r hr))
  have counter₂ := (keep₂ .x21 (by decide)).trans hjreg
  have write₂ : InRegions s₂.wr (s₂.gpr .x22) 8 := by
    rw [wr₂, wr₁, keep₂ .x22 (by decide)]; exact hw
  obtain ⟨s₃, run₃, mem₃, ptr₃, counter₃, flag₃, rd₃, wr₃, reg₃⟩ := VG.Proof.TripleDes.AArch64.Key.tail_ok s₂ j hj counter₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ⟨?_, ?_, counter₃, flag₃, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), ?_⟩⟩
  · rw [mem₃, mem₂, mem₁, keep₂ .x22 (by decide), word₂]
  · rw [ptr₃, keep₂ .x22 (by decide)]
  · intro r hr
    have incl : ∀ r ∈ (VG.Proof.TripleDes.AArch64.Key.keyKept ++ [.x19, .x20]),
        r ≠ .x4 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ∈ (VG.Proof.TripleDes.AArch64.Key.keyKept ++ [.x19, .x20, .x21, .x22]) := by decide
    exact (reg₃ r (incl r hr).1 (incl r hr).2.1 (incl r hr).2.2.1).trans (keep₂ r (incl r hr).2.2.2)

end VG.Proof.TripleDes.AArch64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Key.Loop`. -/
section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64
open VG.Proof.TripleDes.AArch64.Key (keyKept)
open VG.Proof.TripleDes (keyPrefix keyInitial keyStep keyPrefix_succ)

structure LoopState (key : BitVec 64) (base : Addr) (origin : State) (j : Nat) (s : State) : Prop where
  c : s.gpr .x19 = (keyPrefix key j).1.setWidth 64
  d : s.gpr .x20 = (keyPrefix key j).2.1.setWidth 64
  counter : s.gpr .x21 = BitVec.ofNat 64 j
  pointer : s.gpr .x22 = base + BitVec.ofNat 64 (8 * j)
  keys : ∀ i < j, ∀ hi : i < 16, s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 =
    ((keyPrefix key j).2.2[i]'hi).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r ∈ VG.Proof.TripleDes.AArch64.Key.keyKept, s.gpr r = origin.gpr r
  frame : Frame [⟨base, 128⟩] origin.mem s.mem

def LoopInv (key : BitVec 64) (base : Addr) (origin : State) (n : Nat) (s : State) : Prop :=
  1 ≤ n ∧ n ≤ 16 ∧ VG.Proof.TripleDes.AArch64.Key.LoopState key base origin (16 - n) s

theorem loopBody_ok (key : BitVec 64) (base : Addr) (origin : State)
    (hw : ∀ j < 16, InRegions origin.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (j : Nat) (hj : j < 16) (s : State) (hs : VG.Proof.TripleDes.AArch64.Key.LoopState key base origin j s) :
    WP isa (.seq Impl.TripleDes.AArch64.Key.rotation (.block Impl.TripleDes.AArch64.Key.storeRound)) s
      (fun s' => isa.eval (.nonzero .x .x4) s' = some (decide (j ≠ 15)) ∧ VG.Proof.TripleDes.AArch64.Key.LoopState key base origin (j + 1) s') := by
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.AArch64.Key.rotation_ok s _ _ j hj hs.c hs.d hs.counter)
  intro s₁ h₁
  have unused : ∀ r ∈ (VG.Proof.TripleDes.AArch64.Key.keyKept ++ [.x21, .x22]),
      r ≠ .x4 ∧ r ≠ .x19 ∧ r ≠ .x20 := by decide
  have reg₁ : ∀ r ∈ (VG.Proof.TripleDes.AArch64.Key.keyKept ++ [.x21, .x22]), s₁.gpr r = s.gpr r := by
    intro r hr
    exact h₁.reg r (unused r hr).1 (unused r hr).2.1 (unused r hr).2.2
  have write₁ : InRegions s₁.wr (s₁.gpr .x22) 8 := by
    rw [h₁.wr, hs.wr, reg₁ .x22 (by decide), hs.pointer]
    exact hw j hj
  apply WP.mono (VG.Proof.TripleDes.AArch64.Key.storeRound_ok s₁ _ _ j hj h₁.c h₁.d
    ((reg₁ .x21 (by decide)).trans hs.counter) write₁)
  intro s₂ h₂
  have hmem : s₂.mem = s.mem.writeW (base + BitVec.ofNat 64 (8 * j))
      ((Spec.TripleDes.permute Spec.TripleDes.pc2
        ((keyPrefix key j).1.rotateLeft (Spec.TripleDes.rotations.getD j 0) ++
          (keyPrefix key j).2.1.rotateLeft (Spec.TripleDes.rotations.getD j 0))).setWidth 64) := by
    rw [h₂.mem, h₁.mem, reg₁ .x22 (by decide), hs.pointer]
  refine ⟨h₂.flag, ⟨?_, ?_, h₂.counter, ?_, ?_, h₂.rd.trans (h₁.rd.trans hs.rd),
    h₂.wr.trans (h₁.wr.trans hs.wr), ?_, ?_⟩⟩
  · rw [keyPrefix_succ]
    exact (h₂.reg .x19 (by decide)).trans h₁.c
  · rw [keyPrefix_succ]
    exact (h₂.reg .x20 (by decide)).trans h₁.d
  · rw [h₂.ptr, reg₁ .x22 (by decide), hs.pointer]
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
    have incl : ∀ r ∈ VG.Proof.TripleDes.AArch64.Key.keyKept,
        r ∈ (VG.Proof.TripleDes.AArch64.Key.keyKept ++ [.x19, .x20]) ∧
        r ∈ (VG.Proof.TripleDes.AArch64.Key.keyKept ++ [.x21, .x22]) := by decide
    exact (h₂.reg r (incl r hr).1).trans ((reg₁ r (incl r hr).2).trans (hs.reg r hr))
  · rw [hmem]
    exact hs.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base base (by omega_using [hj]) (by omega_using [hj]))

theorem loopStep (key : BitVec 64) (base : Addr) (origin : State)
    (hw : ∀ j < 16, InRegions origin.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (n : Nat) (s : State) (hs : VG.Proof.TripleDes.AArch64.Key.LoopInv key base origin n s) :
    WP isa (.seq Impl.TripleDes.AArch64.Key.rotation (.block Impl.TripleDes.AArch64.Key.storeRound)) s
      (fun s' => (isa.eval (.nonzero .x .x4) s' = some false ∧ VG.Proof.TripleDes.AArch64.Key.LoopState key base origin 16 s') ∨
        (isa.eval (.nonzero .x .x4) s' = some true ∧ ∃ m < n, VG.Proof.TripleDes.AArch64.Key.LoopInv key base origin m s')) := by
  apply WP.mono (VG.Proof.TripleDes.AArch64.Key.loopBody_ok key base origin hw (16 - n) (by omega_using [hs.1]) s hs.2.2)
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

theorem loop_ok (key : BitVec 64) (base : Addr) (s : State)
    (hw : ∀ j < 16, InRegions s.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (hc : s.gpr .x19 = (keyInitial key).1.setWidth 64)
    (hd : s.gpr .x20 = (keyInitial key).2.1.setWidth 64)
    (hcount : s.gpr .x21 = 0) (hptr : s.gpr .x22 = base) :
    WP isa (.loop (.seq Impl.TripleDes.AArch64.Key.rotation
      (.block Impl.TripleDes.AArch64.Key.storeRound)) (.nonzero .x .x4)) s (VG.Proof.TripleDes.AArch64.Key.LoopState key base s 16) := by
  apply WP.loop (M := isa) (body := .seq Impl.TripleDes.AArch64.Key.rotation
      (.block Impl.TripleDes.AArch64.Key.storeRound)) (c := .nonzero .x .x4)
    (Q := VG.Proof.TripleDes.AArch64.Key.LoopState key base s 16) (VG.Proof.TripleDes.AArch64.Key.LoopInv key base s) (VG.Proof.TripleDes.AArch64.Key.loopStep key base s hw) 16 s
  refine ⟨by decide, by decide, hc, hd, hcount, ?_, ?_, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  · exact hptr.trans (BitVec.add_zero base).symm
  · intro i hi
    omega

end VG.Proof.TripleDes.AArch64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Key.Component`. -/
section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64
open VG.Proof.TripleDes.AArch64.Key (keyKept)

structure ComponentPost (keys : Spec.TripleDes.DesSchedule) (base : Addr) (s s' : State) : Prop where
  keys : ∀ i < 16, s'.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 = (keys.getD i 0).setWidth 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ VG.Proof.TripleDes.AArch64.Key.keyKept, s'.gpr r = s.gpr r
  frame : Frame [⟨base, 128⟩] s.mem s'.mem

theorem component_ok (s : State) (offset component : Nat) (hc : component < 3)
    (ho : offset % 8 = 0 ∧ offset < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 offset) 8)
    (hw : ∀ j < 16, InRegions s.wr
      (s.gpr .x2 + BitVec.ofNat 64 (128 * component) + BitVec.ofNat 64 (8 * j)) 8) :
    WP isa (Impl.TripleDes.AArch64.Key.component offset component) s
      (VG.Proof.TripleDes.AArch64.Key.ComponentPost (Spec.TripleDes.expandDesKey (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .x0 + BitVec.ofNat 64 offset))))
        (s.gpr .x2 + BitVec.ofNat 64 (128 * component)) s) := by
  rw [Impl.TripleDes.AArch64.Key.component]
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.AArch64.Key.load_ok s offset component hc ho hr)
  intro s₁ h₁
  have writes : ∀ j < 16, InRegions s₁.wr
      (s.gpr .x2 + BitVec.ofNat 64 (128 * component) + BitVec.ofNat 64 (8 * j)) 8 := by
    rw [h₁.wr]; exact hw
  apply WP.mono (VG.Proof.TripleDes.AArch64.Key.loop_ok _ _ s₁ writes h₁.c h₁.d h₁.counter h₁.ptr)
  intro s₂ h₂
  refine ⟨?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), ?_⟩
  · intro i hi
    rw [VG.Proof.TripleDes.expandDesKey_prefix, VG.Proof.TripleDes.vector_getD _ i hi 0]
    exact h₂.keys i hi hi
  · rw [← h₁.mem]
    exact h₂.frame

end VG.Proof.TripleDes.AArch64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Key.Copy`. -/
section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64
open VG.Proof.Rc2.AArch64 (Keep)

theorem copy64_ok (s : State) (src dst : Reg) (a b : Nat) (hne : dst ≠ .x4)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 a) 8)
    (writable : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 b) 8)
    (ha : a % 8 = 0 ∧ a < 32768 := by decide)
    (hb : b % 8 = 0 ∧ b < 32768 := by decide) :
    ∃ s', runBlock isa [.ldr .x .x4 src a, .str .x .x4 dst b] s = some s' ∧
      Keep [.x4] {s with
        mem := s.mem.writeW (s.gpr dst + BitVec.ofNat 64 b) (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)} s' := by
  have hw : InRegions (s.write .x .x4 (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)).wr
      ((s.write .x .x4 (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)).gpr dst + BitVec.ofNat 64 b) 8 := by
    simpa only [wr_write, gpr_write, hne, ite_false] using writable
  refine ⟨_, by
    rw [runBlock_cons, VG.AArch64.exec_ldr_x ha readable, runStep_some,
      runBlock_cons, VG.AArch64.exec_str_x hb hw, runStep_some, runBlock_nil], ?_⟩
  constructor
  · intro r hr
    have hn : r ≠ .x4 := by intro h; subst r; exact hr (by simp)
    exact gpr_write_of_ne _ _ _ hn
  · simp only [gpr_write, hne, ite_false, ite_true, BitVec.setWidth_eq, mem_write]
  · rfl
  · rfl

 def copyCode (n : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    [.ldr .x .x4 .x2 (8 * j), .str .x .x4 .x2 (256 + 8 * j)]

structure CopyPost (base : Addr) (s : State) (n : Nat) (s' : State) : Prop where
  keys : ∀ i < n, s'.mem.readW (base + BitVec.ofNat 64 (256 + 8 * i)) 64 =
    s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .x4 → s'.gpr r = s.gpr r
  frame : Frame [⟨base + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copy_ok (s : State) (n : Nat) (hn : n ≤ 16)
    (hr : ∀ i < 16, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8)
    (hw : ∀ i < 16, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (256 + 8 * i)) 8) :
    WP isa (.block (VG.Proof.TripleDes.AArch64.Key.copyCode n)) s (VG.Proof.TripleDes.AArch64.Key.CopyPost (s.gpr .x2) s n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ hi => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [VG.Proof.TripleDes.AArch64.Key.copyCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    apply WP.mono (ih (by omega))
    intro s₁ h₁
    have hbase : s₁.gpr .x2 = s.gpr .x2 := h₁.reg .x2 (by decide)
    have readable : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x2 + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [h₁.rd, h₁.wr, hbase]; exact hr n (by omega)
    have writable : InRegions s₁.wr (s₁.gpr .x2 + BitVec.ofNat 64 (256 + 8 * n)) 8 := by
      rw [h₁.wr, hbase]; exact hw n (by omega)
    obtain ⟨s₂, run₂, keep₂⟩ := VG.Proof.TripleDes.AArch64.Key.copy64_ok s₁ .x2 .x2
      (8 * n) (256 + 8 * n) (by decide) readable writable (by omega) (by omega)
    have source : s₁.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (8 * n)) 64 =
        s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (8 * n)) 64 := by
      apply h₁.frame.readW (r := ⟨s.gpr .x2 + BitVec.ofNat 64 (8 * n), 8⟩)
        (Region.contains_self _ _) _ (by decide)
      intro r h
      obtain rfl := List.mem_singleton.mp h
      exact Offset.disjoint (s.gpr .x2) (by omega) (by omega) (by decide)
    have mem₂ : s₂.mem = s₁.mem.writeW (s.gpr .x2 + BitVec.ofNat 64 (256 + 8 * n))
        (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (8 * n)) 64) := by
      have hm := keep₂.mem
      rw [hbase, source] at hm
      exact hm
    refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr,
      fun r hr => (keep₂.reg r (by simpa only [List.mem_singleton] using hr)).trans (h₁.reg r hr), ?_⟩⟩
    · intro i hi
      rw [mem₂]
      by_cases he : i = n
      · subst i; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep (s.gpr .x2) (by omega) (by omega) (by omega)) (by decide)]
        exact h₁.keys i (by omega)
    · rw [mem₂]
      apply h₁.frame.writeW (List.mem_singleton_self _) _
      have hc := Offset.contains_base (s.gpr .x2 + BitVec.ofNat 64 256)
        (d := 8 * n) (n := 8) (k := 128) (by omega) (by omega)
      rw [Offset.add_ofNat_add_ofNat] at hc
      exact hc

end VG.Proof.TripleDes.AArch64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Key.Composition`. -/
section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64
open VG.Proof.TripleDes (componentKeys componentOffset)

abbrev keyR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
abbrev outputR (s : State) : Region := ⟨s.gpr .x2, 384⟩

def slot (base : Addr) (c j : Nat) : Addr := base + BitVec.ofNat 64 (128 * c + 8 * j)

structure Components (origin s : State) (done : Nat) : Prop where
  keys : ∀ c < done, ∀ j < 16, s.mem.readW (VG.Proof.TripleDes.AArch64.Key.slot (origin.gpr .x2) c j) 64 =
    ((componentKeys origin.mem (origin.gpr .x0) (origin.gpr .x1).toNat c).getD j 0).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r ∈ VG.Proof.TripleDes.AArch64.Key.keyKept, s.gpr r = origin.gpr r
  frame : Frame [VG.Proof.TripleDes.AArch64.Key.outputR origin] origin.mem s.mem

structure Permissions (s : State) : Prop where
  reads : ∀ offset, offset + 8 ≤ (s.gpr .x1).toNat →
    InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 offset) 8
  writes : ∀ offset, offset + 8 ≤ 384 → InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 offset) 8
  keyOutput : (VG.Proof.TripleDes.AArch64.Key.keyR s).Disjoint (VG.Proof.TripleDes.AArch64.Key.outputR s)
  valid : Spec.TripleDes.validKey (s.gpr .x1).toNat

theorem componentStep_ok (origin s : State) (c : Nat) (hc : c < 3)
    (hp : VG.Proof.TripleDes.AArch64.Key.Permissions origin) (hs : VG.Proof.TripleDes.AArch64.Key.Components origin s c)
    (hoff : componentOffset (origin.gpr .x1).toNat c = 8 * c) :
    WP isa (Impl.TripleDes.AArch64.Key.component (8 * c) c) s
      (VG.Proof.TripleDes.AArch64.Key.Components origin · (c + 1)) := by
  have offsetBound := VG.Proof.TripleDes.componentOffset_bound _ c hp.valid hc
  rw [hoff] at offsetBound
  have read : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (8 * c)) 8 := by
    rw [hs.rd, hs.wr, hs.reg .x0 (by decide)]
    exact hp.reads _ offsetBound
  have write : ∀ j < 16, InRegions s.wr
      (s.gpr .x2 + BitVec.ofNat 64 (128 * c) + BitVec.ofNat 64 (8 * j)) 8 := by
    intro j hj
    rw [hs.wr, hs.reg .x2 (by decide), Offset.add_ofNat_add_ofNat]
    exact hp.writes _ (by omega_using [hc, hj])
  apply WP.mono (VG.Proof.TripleDes.AArch64.Key.component_ok s (8 * c) c hc (by omega) read write)
  intro t ht
  have frame : Frame [⟨origin.gpr .x2 + BitVec.ofNat 64 (128 * c), 128⟩] s.mem t.mem := by
    have hf := ht.frame
    rw [hs.reg .x2 (by decide)] at hf
    exact hf
  have key : Spec.TripleDes.blockAt s.mem (s.gpr .x0 + BitVec.ofNat 64 (8 * c)) =
      Spec.TripleDes.blockAt origin.mem (origin.gpr .x0 + BitVec.ofNat 64 (8 * c)) := by
    rw [hs.reg .x0 (by decide)]
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
      rw [key, hs.reg .x2 (by decide), Offset.add_ofNat_add_ofNat] at h
      unfold componentKeys
      rw [hoff]
      exact h
    · have before : k < c := by omega_using [hk, he]
      have sep : (Region.mk (VG.Proof.TripleDes.AArch64.Key.slot (origin.gpr .x2) k j) 8).Disjoint
          ⟨origin.gpr .x2 + BitVec.ofNat 64 (128 * c), 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [hk, hc, hj]) (by omega_using [hc])
      have hmem := frame.readW (a := VG.Proof.TripleDes.AArch64.Key.slot (origin.gpr .x2) k j) (w := 64) (r := ⟨VG.Proof.TripleDes.AArch64.Key.slot (origin.gpr .x2) k j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys k before j hj)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨VG.Proof.TripleDes.AArch64.Key.outputR origin, by simp, Offset.sub_base _ (by omega_using [hc])⟩

theorem copyThird_ok (origin s : State) (hp : VG.Proof.TripleDes.AArch64.Key.Permissions origin)
    (hs : VG.Proof.TripleDes.AArch64.Key.Components origin s 2) (hn : (origin.gpr .x1).toNat = 16) :
    WP isa (.block Impl.TripleDes.AArch64.Key.copyThird) s (VG.Proof.TripleDes.AArch64.Key.Components origin · 3) := by
  have reads : ∀ i < 16, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hs.rd, hs.wr, hs.reg .x2 (by decide)]
    obtain ⟨r, hr, hc⟩ := hp.writes (8 * i) (by omega_using [hi])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writes : ∀ i < 16, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (256 + 8 * i)) 8 := by
    intro i hi
    rw [hs.wr, hs.reg .x2 (by decide)]
    exact hp.writes _ (by omega_using [hi])
  apply WP.mono (VG.Proof.TripleDes.AArch64.Key.copy_ok s 16 (by decide) reads writes)
  intro t ht
  have frame : Frame [⟨origin.gpr .x2 + BitVec.ofNat 64 256, 128⟩] s.mem t.mem := by
    have h := ht.frame
    rw [hs.reg .x2 (by decide)] at h
    exact h
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr, ?_, hs.frame.trans (frame.sub ?_)⟩
  · intro c hc j hj
    by_cases he : c = 2
    · subst c
      have hRepeat : componentKeys origin.mem (origin.gpr .x0) (origin.gpr .x1).toNat 2 =
          componentKeys origin.mem (origin.gpr .x0) (origin.gpr .x1).toNat 0 := by
        rw [hn]; rfl
      have h := ht.keys j hj
      rw [hs.reg .x2 (by decide)] at h
      change t.mem.readW (origin.gpr .x2 + BitVec.ofNat 64 (256 + 8 * j)) 64 = _
      rw [hRepeat]
      have first := hs.keys 0 (by decide) j hj
      simp only [VG.Proof.TripleDes.AArch64.Key.slot, Nat.mul_zero, Nat.zero_add] at first
      exact h.trans first
    · have before : c < 2 := by omega_using [hc, he]
      have sep : (Region.mk (VG.Proof.TripleDes.AArch64.Key.slot (origin.gpr .x2) c j) 8).Disjoint
          ⟨origin.gpr .x2 + BitVec.ofNat 64 256, 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [before, hj]) (by decide)
      have hmem := frame.readW (a := VG.Proof.TripleDes.AArch64.Key.slot (origin.gpr .x2) c j) (w := 64) (r := ⟨VG.Proof.TripleDes.AArch64.Key.slot (origin.gpr .x2) c j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys c before j hj)
  · intro r hr
    have unused : ∀ r ∈ VG.Proof.TripleDes.AArch64.Key.keyKept, r ≠ .x4 := by decide
    exact (ht.reg r (unused r hr)).trans (hs.reg r hr)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨VG.Proof.TripleDes.AArch64.Key.outputR origin, by simp, Offset.sub_base _ (by decide)⟩

def componentIndex (i : Nat) : Nat := if i < 16 then 0 else if i < 32 then 1 else 2

theorem index_partition : ∀ i < 48, VG.Proof.TripleDes.AArch64.Key.componentIndex i < 3 ∧ i % 16 < 16 ∧
    8 * i = 128 * VG.Proof.TripleDes.AArch64.Key.componentIndex i + 8 * (i % 16) := by decide

theorem Components.schedule {origin s : State} (h : VG.Proof.TripleDes.AArch64.Key.Components origin s 3) :
    Spec.TripleDes.scheduleAt s.mem (origin.gpr .x2) =
      VG.Proof.TripleDes.expandedMemory origin.mem (origin.gpr .x0) (origin.gpr .x1).toNat := by
  apply Vector.ext
  intro i hi
  have fact := VG.Proof.TripleDes.AArch64.Key.index_partition i hi
  have keys := h.keys (VG.Proof.TripleDes.AArch64.Key.componentIndex i) fact.1 (i % 16) fact.2.1
  rw [VG.Proof.TripleDes.AArch64.Key.slot, ← fact.2.2] at keys
  rw [VG.Proof.TripleDes.scheduleAt_readW s.mem (origin.gpr .x2) i hi]
  simp only [VG.Proof.TripleDes.expandedMemory, Vector.getElem_ofFn]
  by_cases h16 : i < 16
  · simpa only [VG.Proof.TripleDes.AArch64.Key.componentIndex, h16, ite_true] using keys
  · by_cases h32 : i < 32
    · simpa only [VG.Proof.TripleDes.AArch64.Key.componentIndex, h16, h32, ite_false, ite_true] using keys
    · simpa only [VG.Proof.TripleDes.AArch64.Key.componentIndex, h16, h32, ite_false] using keys


end VG.Proof.TripleDes.AArch64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Key.Body`. -/
section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.Rc2.AArch64 (Keep)

theorem cmpLength_ok (s : State) :
    ∃ s', runBlock isa [.subImm .x .x4 .x1 16] s = some s' ∧
      isa.eval (.zero .x .x4) s' = some (s.gpr .x1 == 16) ∧ Keep [.x4] s s' := by
  refine ⟨s.write .x .x4 (s.gpr .x1 - 16), ?_, ?_, VG.Proof.TripleDes.AArch64.Key.write_keep _ _⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show (16 : Nat) < 4096 from by decide, ite_true, State.read, BitVec.setWidth_eq]
    rfl
  · change VG.AArch64.eval (.zero .x .x4) _ = _
    simp only [VG.AArch64.eval, State.read, gpr_write_self, BitVec.setWidth_eq]
    exact congrArg some (by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      bv_omega)

theorem Components.keep {origin s t : State} {n : Nat} (hs : VG.Proof.TripleDes.AArch64.Key.Components origin s n)
    (ht : Keep [.x4] s t) : VG.Proof.TripleDes.AArch64.Key.Components origin t n :=
  ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r hr => (ht.reg r (by revert hr; cases r <;> decide)).trans (hs.reg r hr), by rw [ht.mem]; exact hs.frame⟩

theorem beq16_toNat (x : BitVec 64) : (x == 16) = decide (x.toNat = 16) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    apply BitVec.eq_of_toNat_eq
    exact h

theorem body_ok (origin s : State) (hp : VG.Proof.TripleDes.AArch64.Key.Permissions origin) (hs : VG.Proof.TripleDes.AArch64.Key.Components origin s 0)
    (Q : State → Prop)
    (finish : ∀ t, VG.Proof.TripleDes.AArch64.Key.Components origin t 3 → WP isa (.block Impl.TripleDes.AArch64.Key.restore) t Q) :
    WP isa (.seq (Impl.TripleDes.AArch64.Key.component 0 0)
      (.seq (Impl.TripleDes.AArch64.Key.component 8 1)
        (.seq (.block [.subImm .x .x4 .x1 16])
          (.seq (.ite (.zero .x .x4) (.block Impl.TripleDes.AArch64.Key.copyThird)
            (Impl.TripleDes.AArch64.Key.component 16 2)) (.block Impl.TripleDes.AArch64.Key.restore))))) s Q := by
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.AArch64.Key.componentStep_ok origin s 0 (by decide) hp hs (by rfl))
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.AArch64.Key.componentStep_ok origin s₁ 1 (by decide) hp hs₁ (by rfl))
  intro s₂ hs₂
  apply WP.seq
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := VG.Proof.TripleDes.AArch64.Key.cmpLength_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have hs₃ := hs₂.keep keep₃
  apply WP.seq
  apply WP.mono (Q := (VG.Proof.TripleDes.AArch64.Key.Components origin · 3)) ?_
  · intro t ht
    exact finish t ht
  have flag : isa.eval (.zero .x .x4) s₃ = some (decide ((origin.gpr .x1).toNat = 16)) := by
    rw [flag₃, hs₂.reg .x1 (by decide), VG.Proof.TripleDes.AArch64.Key.beq16_toNat]
  by_cases h16 : (origin.gpr .x1).toNat = 16
  · apply WP.ite true (by simpa only [h16, decide_true] using flag)
    · intro _; exact VG.Proof.TripleDes.AArch64.Key.copyThird_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simpa only [h16, decide_false] using flag)
    · simp
    · intro _
      exact VG.Proof.TripleDes.AArch64.Key.componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

end VG.Proof.TripleDes.AArch64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Key.Save`. -/
section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

/-- The four callee-saved registers, in slot order. -/
def savedReg (i : Nat) : Reg := (Impl.TripleDes.AArch64.Key.savedRegs).getD i .x19

theorem save_eq : Impl.TripleDes.AArch64.Key.save = Spill.saveCode .x3 (Spill.slots VG.Proof.TripleDes.AArch64.Key.savedReg 4) := by
  decide +kernel

theorem restore_eq : Impl.TripleDes.AArch64.Key.restore = Spill.restoreCode .x3 (Spill.slots VG.Proof.TripleDes.AArch64.Key.savedReg 4) := by
  decide +kernel

def Saved (original current : State) : Prop :=
  ∀ i < 4, current.mem.readW (current.gpr .x3 + BitVec.ofNat 64 (8 * i)) 64 =
    original.gpr (VG.Proof.TripleDes.AArch64.Key.savedReg i)

theorem save_ok (s : State)
    (hw : ∀ i < 4, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block Impl.TripleDes.AArch64.Key.save) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ VG.Proof.TripleDes.AArch64.Key.Saved s s' ∧
      Frame [⟨s.gpr .x3, 32⟩] s.mem s'.mem) := by
  rw [VG.Proof.TripleDes.AArch64.Key.save_eq]
  refine WP.mono (Spill.save_wp (by decide) (Spill.forall_slots hw)) fun s' h =>
    ⟨h.gpr, h.rd, h.wr, fun i hi => ?_, ?_⟩
  · rw [h.gpr, h.mem]
    exact Spill.saveMem_saved (l := Spill.slots VG.Proof.TripleDes.AArch64.Key.savedReg 4) (by decide) s.mem (s.gpr .x3) s.gpr
      (VG.Proof.TripleDes.AArch64.Key.savedReg i, 8 * i) (Spill.mem_slots hi)
  · rw [h.mem]; exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem savedReg_separate : ∀ i < 4, VG.Proof.TripleDes.AArch64.Key.savedReg i ≠ .x3 := by decide +kernel

theorem restore_ok (original s : State) (hsaved : VG.Proof.TripleDes.AArch64.Key.Saved original s)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block Impl.TripleDes.AArch64.Key.restore) s (fun s' =>
      (∀ r ∈ Impl.TripleDes.AArch64.Key.savedRegs, s'.gpr r = original.gpr r) ∧
      VG.Proof.Rc2.AArch64.Keep (Impl.TripleDes.AArch64.Key.savedRegs) s s') := by
  rw [VG.Proof.TripleDes.AArch64.Key.restore_eq]
  have hregs : (Spill.slots VG.Proof.TripleDes.AArch64.Key.savedReg 4).map Prod.fst = Impl.TripleDes.AArch64.Key.savedRegs := by
    decide +kernel
  exact WP.mono (Spill.restore_wp rfl (by decide) (by decide) (Spill.forall_slots hread)
    (Spill.forall_slots hsaved)) fun s' h =>
    ⟨fun r hr => h.gpr_of (.inl (hregs ▸ hr)), ⟨fun r hr => h.other r (hregs ▸ hr), h.mem, h.rd, h.wr⟩⟩

end VG.Proof.TripleDes.AArch64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Key.Contract`. -/
section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64

def contract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let output : Region := ⟨s.gpr .x2, 384⟩
    let scratch : Region := ⟨s.gpr .x3, 512⟩
    s.rd = [key] ∧ s.wr = [output, scratch] ∧ key.Disjoint output ∧ key.Disjoint scratch ∧
      output.Disjoint scratch ∧
      Spec.TripleDes.validKey (s.gpr .x1).toNat
  post s s' := Spec.TripleDes.scheduleAt s'.mem (s.gpr .x2) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub := VG.Proof.TripleDes.AArch64.PublicRegs [.x0, .x1, .x2, .x3]

end VG.Proof.TripleDes.AArch64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Key.Correct`. -/
section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64

 theorem expand_correct (s : State) (hs : contract.pre s) :
    WP isa Impl.TripleDes.AArch64.Key.expandKey s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ contract.post s s') := by
  obtain ⟨hrd, hwr, keyOutput, keyScratch, outputScratch, valid⟩ := hs
  have scratchWrites : ∀ i < 4, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .x3, 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  rw [Impl.TripleDes.AArch64.Key.expandKey]
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.AArch64.Key.save_ok s scratchWrites)
  intro s₁ h₁
  have g₁ (r : Reg) : s₁.gpr r = s.gpr r := congrFun h₁.1 r
  have hp : VG.Proof.TripleDes.AArch64.Key.Permissions s₁ := by
    constructor
    · intro offset hoff
      rw [h₁.2.1, h₁.2.2.1, g₁, hrd, hwr]
      exact ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, by simp,
        Offset.contains_base _ (by simpa only [g₁] using hoff) (by
          have bound := BitVec.isLt (s.gpr .x1)
          rw [g₁] at hoff
          omega_using [hoff, bound])⟩
    · intro offset hoff
      rw [h₁.2.2.1, g₁, hwr]
      exact ⟨⟨s.gpr .x2, 384⟩, by simp, Offset.contains_base _ hoff (by omega_using [hoff])⟩
    · simpa only [VG.Proof.TripleDes.AArch64.Key.keyR, VG.Proof.TripleDes.AArch64.Key.outputR, g₁] using keyOutput
    · simpa only [g₁] using valid
  apply VG.Proof.TripleDes.AArch64.Key.body_ok s₁ s₁ hp ⟨fun _ h => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  intro s₂ h₂
  have g₂ (r : Reg) (hr : r ∈ VG.Proof.TripleDes.AArch64.Key.keyKept) : s₂.gpr r = s.gpr r :=
    (h₂.reg r hr).trans (g₁ r)
  have frame₂ : Frame [⟨s.gpr .x2, 384⟩] s₁.mem s₂.mem := by
    have h := h₂.frame
    rw [VG.Proof.TripleDes.AArch64.Key.outputR, g₁] at h
    exact h
  have saved₂ : VG.Proof.TripleDes.AArch64.Key.Saved s s₂ := by
    intro i hi
    have sub : Region.Sub ⟨s.gpr .x3 + BitVec.ofNat 64 (8 * i), 8⟩ ⟨s.gpr .x3, 512⟩ :=
      Offset.sub_base _ (by omega_using [hi])
    have mem := frame₂.readW (a := s.gpr .x3 + BitVec.ofNat 64 (8 * i)) (w := 64)
      (r := ⟨s.gpr .x3 + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact (outputScratch.sub_right sub).symm)
      (by decide)
    rw [g₂ .x3 (by decide)]
    have saved₁ := h₁.2.2.2.1 i hi
    rw [g₁] at saved₁
    exact mem.trans saved₁
  have scratchReads : ∀ i < 4, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x3 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [h₂.rd, h₂.wr, h₁.2.1, h₁.2.2.1, g₂ .x3 (by decide)]
    obtain ⟨r, hr, hc⟩ := scratchWrites i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.mono (VG.Proof.TripleDes.AArch64.Key.restore_ok s s₂ saved₂ scratchReads)
  intro s₃ h₃
  have scratchFrame : Frame [⟨s.gpr .x3, 512⟩] s.mem s₁.mem := h₁.2.2.2.2.sub (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨s.gpr .x3, 512⟩, by simp, Region.sub_prefix (by decide)⟩)
  have initialBytes := VG.Proof.TripleDes.bytesAt_eq_of_frame (s.gpr .x0) (s.gpr .x1).toNat
    scratchFrame (Nat.le_of_lt (BitVec.isLt _)) (by simpa using keyScratch)
  constructor
  · intro r hr
    have kept : ∀ r ∈ preserved, r ∈ Impl.TripleDes.AArch64.Key.savedRegs ∨ r ∈ VG.Proof.TripleDes.AArch64.Key.keyKept := by decide
    rcases kept r hr with saved | other
    · exact h₃.1 r saved
    · exact (h₃.2.reg r (by revert other; cases r <;> decide)).trans (g₂ r other)
  · have result := h₂.schedule
    simp only [g₁] at result
    rw [← VG.Proof.TripleDes.expandKey_memory s₁.mem (s.gpr .x0) (s.gpr .x1).toNat valid,
      initialBytes] at result
    change Spec.TripleDes.scheduleAt s₃.mem (s.gpr .x2) = _
    rw [h₃.2.mem]
    exact result

end VG.Proof.TripleDes.AArch64.Key

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Key.Verified`. -/
section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 384⟩, ⟨0x3000, 512⟩]

theorem correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa Impl.TripleDes.AArch64.Key.expandKey s t s' ∧ abiPreserved s s' ∧ contract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.TripleDes.AArch64.Key.expand_correct s hs
  exact ⟨t, s', he, ⟨ha, VG.AArch64.Exec.sp he, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem publicRegs_four (s₁ s₂ : State) : VG.Proof.TripleDes.AArch64.PublicRegs [.x0, .x1, .x2, .x3] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 := by simp [VG.Proof.TripleDes.AArch64.PublicRegs]

theorem verified : Verified target Impl.TripleDes.AArch64.Key.expandKey
    (Proof.TripleDes.expandKeyScratchContract abi) := by
  refine Verified.of_correct VG.Proof.TripleDes.AArch64.Key.correct (VG.Proof.TripleDes.AArch64.expandKey_constantTime _) ?_
  sig_implies [Proof.TripleDes.expandKeyScratchContract, Proof.TripleDes.expandKeyScratchSig, Spec.TripleDes.expandKeyPre, Spec.TripleDes.expandKeyPost, abi, argRegs,
    VG.Proof.TripleDes.AArch64.Key.contract, VG.Proof.TripleDes.AArch64.Key.publicRegs_four] [satState] using VG.Proof.TripleDes.AArch64.Key.satState

end VG.Proof.TripleDes.AArch64.Key

end
