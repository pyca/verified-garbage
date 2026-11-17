module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ConstantTime
public import VerifiedGarbage.Spec.TripleDes.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Lit
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.TripleDes.KeyMemory
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Word
public import VerifiedGarbage.Proof.TripleDes.KeySchedule
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.ExpandKey
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bytes
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Permutation

/-! ### `TripleDes.PPC64LE.Key.Rotation`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.Key.Load`, which this module and modules that import it used -/

section

/-! ### `TripleDes.PPC64LE.Key.Permutation`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Key

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

theorem pc1_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc1 64 .r9 .r8 .r10 .r11) s = some s' ∧
      s'.gpr .r9 = (Spec.TripleDes.permute Spec.TripleDes.pc1 (s.gpr .r8)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation1.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc1 (by decide) (by decide) (by decide)
       .r8 .r9 (instrs keyPermutation1.lit) keyPermutation1_check s
  have hcode : permuteCode Spec.TripleDes.pc1 64 .r9 .r8 .r10 .r11 = instrs keyPermutation1.lit :=
    congrArg instrs keyPermutation1.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, mem, regs⟩
  exact word.trans (congrArg (fun x => (Spec.TripleDes.permute Spec.TripleDes.pc1 x).setWidth 64)
    (BitVec.setWidth_eq _))

theorem pc2_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc2 56 .r9 .r8 .r10 .r11) s = some s' ∧
      s'.gpr .r9 = (Spec.TripleDes.permute Spec.TripleDes.pc2 ((s.gpr .r8).setWidth 56)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation2.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc2 (by decide) (by decide) (by decide)
       .r8 .r9 (instrs keyPermutation2.lit) keyPermutation2_check s
  have hcode : permuteCode Spec.TripleDes.pc2 56 .r9 .r8 .r10 .r11 = instrs keyPermutation2.lit :=
    congrArg instrs keyPermutation2.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, word, rd, wr, mem, regs⟩

end VG.Proof.TripleDes.PPC64LE.Key

end

end

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Key

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

/-- The registers key expansion keeps: its arguments. -/
def keyKept : List Reg := [.r3, .r4, .r5]

theorem readKey_ok (s : State) (offset : Nat) (ho : offset < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 offset) 8) :
    ∃ s', runBlock isa [.li .r8 offset, .loadRev .d .r8 .r3 .r8] s = some s' ∧
      s'.gpr .r8 = Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .r3 + BitVec.ofNat 64 offset)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) := by
  let s₁ := s.write .r8 (BitVec.ofNat 64 offset)
  have ha : s₁.gpr .r3 + s₁.gpr .r8 = s.gpr .r3 + BitVec.ofNat 64 offset := by
    simp only [s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
  have hload := exec_loadRev_d (s := s₁) (t := .r8) (a := .r3) (b := .r8) (by decide)
    (by rw [ha]; exact hr)
  rw [ha] at hload
  let s₂ := s₁.write .r8 (rev64 (s₁.mem.readW (s.gpr .r3 + BitVec.ofNat 64 offset) 64))
  refine ⟨s₂, by
    rw [runBlock_cons, exec_li ho, runStep_some, runBlock_cons, hload, runStep_some,
      runBlock_nil], ?_, rfl, rfl, rfl, ?_⟩
  · rw [gpr_write_self]
    exact (decodeBlock_readW s.mem _).symm
  · intro r hr
    simp only [s₂, s₁, gpr_write, hr, ite_false]

def loadTail (component : Nat) : List Instr :=
  [.lsr .d .r0 .r9 28, rr .r7 .r9] ++ mask .r7 28 ++
    [imm .r12 0, .addi .r6 .r5 (128 * component)]

theorem loadTail_ok (s : State) (component : Nat) (hc : component < 3) (x : BitVec 56)
    (hx : s.gpr .r9 = x.setWidth 64) :
    ∃ s', runBlock isa (loadTail component) s = some s' ∧
      s'.gpr .r0 = ((x >>> 28).setWidth 28).setWidth 64 ∧
      s'.gpr .r7 = (x.setWidth 28).setWidth 64 ∧ s'.gpr .r12 = 0 ∧
      s'.gpr .r6 = s.gpr .r5 + BitVec.ofNat 64 (128 * component) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ [Reg.r0, .r7, .r12, .r6] → s'.gpr r = s.gpr r) := by
  have hb : 128 * component < 2 ^ 15 := by omega_using [hc]
  let s₁ := s.write .r0 (s.gpr .r9 >>> 28)
  let s₂ := s₁.write .r7 (s₁.gpr .r9 ||| s₁.gpr .r9)
  let s₃ := s₂.write .r7 (s₂.gpr .r7 <<< (64 - 28))
  let s₄ := s₃.write .r7 (s₃.gpr .r7 >>> (64 - 28))
  let s₅ := s₄.write .r12 (BitVec.ofNat 64 0)
  let s₆ := s₅.write .r6 (s₅.gpr .r5 + BitVec.ofNat 64 (128 * component))
  refine ⟨s₆, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [loadTail, rr, mask, imm, List.cons_append, List.nil_append]
    rw [runBlock_cons, exec_lsr_d (by decide), runStep_some,
      runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_lsl (by decide), runStep_some,
      runBlock_cons, exec_lsr_d (by decide), runStep_some, runBlock_cons, exec_li (by decide),
      runStep_some, runBlock_cons, exec_addi (by decide) hb, runStep_some, runBlock_nil]
  · simp only [s₆, s₅, s₄, s₃, s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
    rw [hx]; exact VG.Proof.TripleDes.split28_upper x
  · simp only [s₆, s₅, s₄, s₃, s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false,
      BitVec.or_self]
    rw [hx, mask_word _ 28 (by decide) (by decide),
      BitVec.setWidth_setWidth_of_le x (by decide : 28 ≤ 64)]
  · simp only [s₆, s₅, gpr_write, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [s₆, s₅, s₄, s₃, s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [s₆, s₅, s₄, s₃, s₂, s₁, gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

structure LoadPost (x : BitVec 56) (component : Nat) (s s' : State) : Prop where
  c : s'.gpr .r0 = ((x >>> 28).setWidth 28).setWidth 64
  d : s'.gpr .r7 = (x.setWidth 28).setWidth 64
  counter : s'.gpr .r12 = 0
  ptr : s'.gpr .r6 = s.gpr .r5 + BitVec.ofNat 64 (128 * component)
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ keyKept, s'.gpr r = s.gpr r

theorem load_ok (s : State) (offset component : Nat) (hc : component < 3)
    (ho : offset < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 offset) 8) :
    WP isa (.block (Impl.TripleDes.PPC64LE.Key.load offset component)) s
      (LoadPost (Spec.TripleDes.permute Spec.TripleDes.pc1 (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .r3 + BitVec.ofNat 64 offset)))) component s) := by
  have code : Impl.TripleDes.PPC64LE.Key.load offset component =
      (([.li .r8 offset, .loadRev .d .r8 .r3 .r8] : List Instr) ++
        permuteCode Spec.TripleDes.pc1 64 .r9 .r8 .r10 .r11) ++ loadTail component := by
    simp only [Impl.TripleDes.PPC64LE.Key.load, loadTail, List.append_assoc]
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, key₁, mem₁, rd₁, wr₁, reg₁⟩ := readKey_ok s offset ho hr
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, reg₂⟩ := pc1_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [key₁] at word₂
  obtain ⟨s₃, run₃, c₃, d₃, counter₃, ptr₃, mem₃, rd₃, wr₃, reg₃⟩ :=
    loadTail_ok s₂ component hc _ word₂
  have hcheck : ∀ r ∈ keyKept,
      ((instrs keyPermutation1.lit).all fun op => dstOf op != some r) = true := by decide +kernel
  refine WP.of_runBlock ⟨s₃, run₃, ⟨c₃, d₃, counter₃, ?_, mem₃.trans (mem₂.trans mem₁),
    rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_⟩⟩
  · have r5₂ : s₂.gpr .r5 = s.gpr .r5 :=
      (reg₂ .r5 (hcheck .r5 (by decide))).trans (reg₁ .r5 (by decide))
    rw [r5₂] at ptr₃
    exact ptr₃
  · intro r hr
    have unused : ∀ r ∈ keyKept, r ∉ [Reg.r0, .r7, .r12, .r6] ∧ r ≠ .r8 := by decide
    exact (reg₃ r (unused r hr).1).trans ((reg₂ r (hcheck r hr)).trans (reg₁ r (unused r hr).2))

end VG.Proof.TripleDes.PPC64LE.Key

end

end

/-! ### `TripleDes.PPC64LE.KeySteps`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

theorem rotate28_ok (s : State) (r : Reg) (hr : r ≠ .r8)
    (x : BitVec 28) (hx : s.gpr r = x.setWidth 64)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 28) :
    ∃ s', runBlock isa (Key.rotate28 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r', r' ≠ r → r' ≠ .r8 → s'.gpr r' = s.gpr r') := by
  have hleft : 64 - n < 64 := by omega_using [hn]
  have hright : 28 - n < 64 := by omega_using []
  let s₁ := s.write .r8 (s.gpr r >>> (28 - n))
  let s₂ := s₁.write r ((s₁.gpr r).rotateRight (64 - n))
  let s₃ := s₂.write r (s₂.gpr r ^^^ s₂.gpr .r8)
  let s₄ := s₃.write r (s₃.gpr r <<< (64 - 28))
  let s₅ := s₄.write r (s₄.gpr r >>> (64 - 28))
  refine ⟨s₅, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · rw [Key.rotate28, mask, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      runBlock_cons, exec_lsr_d hright, runStep_some, runBlock_cons, exec_rotr_d hleft,
      runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_lsl (by decide),
      runStep_some, runBlock_cons, exec_lsr_d (by decide), runStep_some, runBlock_nil]
  · have h₁ : s₁.gpr r = s.gpr r := gpr_write_of_ne _ _ hr
    have h₈ : s₂.gpr .r8 = s.gpr r >>> (28 - n) := by
      rw [gpr_write_of_ne _ _ (Ne.symm hr), gpr_write_self]
    simp only [s₅, s₄, s₃, gpr_write_self]
    rw [h₈, show s₂.gpr r = (s₁.gpr r).rotateRight (64 - n) from gpr_write_self _ _ _, h₁, hx,
      mask_word _ 28 (by decide) (by decide)]
    exact (VG.Proof.TripleDes.mask28 _).symm.trans (VG.Proof.TripleDes.rotate28_word x n hn hn')
  · intro r' h1 h2
    simp only [s₅, s₄, s₃, s₂, s₁, gpr_write, h1, h2, ite_false]

end VG.Proof.TripleDes.PPC64LE

end

end


@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Key

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

structure RotatePost (c d : BitVec 28) (n : Nat) (s s' : State) : Prop where
  c : s'.gpr .r0 = (c.rotateLeft n).setWidth 64
  d : s'.gpr .r7 = (d.rotateLeft n).setWidth 64
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .r8 → r ≠ .r0 → r ≠ .r7 → s'.gpr r = s.gpr r

theorem rotate_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .r0 = c.setWidth 64) (hd : s.gpr .r7 = d.setWidth 64)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 28) :
    WP isa (Impl.TripleDes.PPC64LE.Key.rotate n) s (RotatePost c d n s) := by
  rw [Impl.TripleDes.PPC64LE.Key.rotate, WP.block_append_iff]
  obtain ⟨s₁, run₁, c₁, mem₁, rd₁, wr₁, reg₁⟩ := rotate28_ok s .r0 (by decide) c hc n hn hn'
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have d₁ : s₁.gpr .r7 = d.setWidth 64 := (reg₁ .r7 (by decide) (by decide)).trans hd
  obtain ⟨s₂, run₂, d₂, mem₂, rd₂, wr₂, reg₂⟩ := rotate28_ok s₁ .r7 (by decide) d d₁ n hn hn'
  refine WP.of_runBlock ⟨s₂, run₂, ⟨(reg₂ .r0 (by decide) (by decide)).trans c₁, d₂,
    mem₂.trans mem₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩⟩
  intro r ha hc hd
  exact (reg₂ r hd ha).trans (reg₁ r hc ha)

theorem comparison_values : ∀ j < 16, ∀ k < 16,
    ((BitVec.ofNat 64 j >>> 1) == (0 : BitVec 64)) = decide (j < 2) ∧
    ((BitVec.ofNat 64 j - BitVec.ofNat 64 k) == (0 : BitVec 64)) = decide (j = k) := by
  decide

theorem write_keep (s : State) (v : BitVec 64) : Kept [.r8] s (s.write .r8 v) := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  exact gpr_write_of_ne _ _ hr

theorem lowTest_ok (s : State) (j : Nat) (hj : j < 16)
    (hv : s.gpr .r12 = BitVec.ofNat 64 j) :
    ∃ s', runBlock isa [.lsr .d .r8 .r12 1] s = some s' ∧
      isa.eval (.zero .d .r8) s' = some (decide (j < 2)) ∧ Kept [.r8] s s' := by
  refine ⟨s.write .r8 (s.gpr .r12 >>> 1), ?_, ?_, write_keep _ _⟩
  · rw [runBlock_cons, exec_lsr_d (by decide), runStep_some, runBlock_nil]
  · change VG.PPC64LE.eval (.zero .d .r8) _ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, gpr_write_self, BitVec.setWidth_eq, hv]
    exact congrArg some (comparison_values j hj 0 (by decide)).1

theorem eqTest_ok (s : State) (j k : Nat) (hj : j < 16) (hk : k < 16)
    (hv : s.gpr .r12 = BitVec.ofNat 64 j) :
    ∃ s', runBlock isa [.subi .r8 .r12 k] s = some s' ∧
      isa.eval (.zero .d .r8) s' = some (decide (j = k)) ∧ Kept [.r8] s s' := by
  refine ⟨s.write .r8 (s.gpr .r12 - BitVec.ofNat 64 k), ?_, ?_, write_keep _ _⟩
  · rw [runBlock_cons, exec_subi (by decide) (by omega_using [hk]), runStep_some, runBlock_nil]
  · change VG.PPC64LE.eval (.zero .d .r8) _ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, gpr_write_self, BitVec.setWidth_eq, hv]
    exact congrArg some (comparison_values j hj k hk).2

theorem rotation_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r0 = c.setWidth 64) (hd : s.gpr .r7 = d.setWidth 64)
    (hjreg : s.gpr .r12 = BitVec.ofNat 64 j) :
    WP isa Impl.TripleDes.PPC64LE.Key.rotation s
      (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
  rw [Impl.TripleDes.PPC64LE.Key.rotation]
  apply WP.seq
  obtain ⟨s₁, run₁, cond₁, keep₁⟩ := lowTest_ok s j hj hjreg
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hrot (s' : State) (h : Kept [.r8] s s') (n : Nat) (hn : 1 ≤ n) (hn' : n < 28)
      (hv : Spec.TripleDes.rotations.getD j 0 = n) :
      WP isa (Impl.TripleDes.PPC64LE.Key.rotate n) s' (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
    apply WP.mono (rotate_ok s' c d ((h.reg .r0 (by simp)).trans hc)
      ((h.reg .r7 (by simp)).trans hd) n hn hn')
    intro t ht
    rw [hv]
    exact ⟨ht.c, ht.d, ht.mem.trans h.mem, ht.rd.trans h.rd, ht.wr.trans h.wr,
      fun r ha hc hd => (ht.reg r ha hc hd).trans (h.reg r (by simpa only [List.mem_singleton] using ha))⟩
  have combine {a b : State} (ha : Kept [.r8] s a) (hb : Kept [.r8] a b) : Kept [.r8] s b :=
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
      obtain ⟨s₂, run₂, cond₂, keep₂⟩ := eqTest_ok s₁ j 8 hj (by decide)
        ((keep₁.reg .r12 (by simp)).trans hjreg)
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
          obtain ⟨s₃, run₃, cond₃, keep₃⟩ := eqTest_ok s₂ j 15 hj (by decide)
            ((keep₂'.reg .r12 (by simp)).trans hjreg)
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

end VG.Proof.TripleDes.PPC64LE.Key

end

end

/-! ### `TripleDes.PPC64LE.Key.Body`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.Key.Composition`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.Key.Copy`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Key

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

theorem copy64_ok (s : State) (src dst : Reg) (a b : Nat) (hne : dst ≠ .r8)
    (hsrc : src ≠ .r0) (hdst : dst ≠ .r0)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 a) 8)
    (writable : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 b) 8)
    (ha : a < 32768 ∧ a % 4 = 0 := by decide)
    (hb : b < 32768 ∧ b % 4 = 0 := by decide) :
    ∃ s', runBlock isa [.load .d .r8 src a, .store .d .r8 dst b] s = some s' ∧
      Kept [.r8] {s with
        mem := s.mem.writeW (s.gpr dst + BitVec.ofNat 64 b) (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)} s' := by
  let s₁ := s.write .r8 (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)
  have hd : s₁.gpr dst = s.gpr dst := gpr_write_of_ne _ _ hne
  have hw : InRegions s₁.wr (s₁.gpr dst + BitVec.ofNat 64 b) 8 := by
    rw [hd]; exact writable
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s₁.gpr dst + BitVec.ofNat 64 b) (s₁.gpr .r8) }, by
    rw [runBlock_cons, exec_load_d hsrc ha readable, runStep_some,
      runBlock_cons, exec_store_d hdst hb hw, runStep_some, runBlock_nil], ?_⟩
  constructor
  · intro r hr
    have hn : r ≠ .r8 := by intro h; subst r; exact hr (by simp)
    exact gpr_write_of_ne _ _ hn
  · change s.mem.writeW (s₁.gpr dst + BitVec.ofNat 64 b) (s₁.gpr .r8) = _
    rw [hd, gpr_write_self]
  · rfl
  · rfl

def copyCode (n : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    [.load .d .r8 .r5 (8 * j), .store .d .r8 .r5 (256 + 8 * j)]

structure CopyPost (base : Addr) (s : State) (n : Nat) (s' : State) : Prop where
  keys : ∀ i < n, s'.mem.readW (base + BitVec.ofNat 64 (256 + 8 * i)) 64 =
    s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .r8 → s'.gpr r = s.gpr r
  frame : Frame [⟨base + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copy_ok (s : State) (n : Nat) (hn : n ≤ 16)
    (hr : ∀ i < 16, InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8)
    (hw : ∀ i < 16, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (256 + 8 * i)) 8) :
    WP isa (.block (copyCode n)) s (CopyPost (s.gpr .r5) s n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ hi => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [copyCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    apply WP.mono (ih (by omega_using [hn]))
    intro s₁ h₁
    have hbase : s₁.gpr .r5 = s.gpr .r5 := h₁.reg .r5 (by decide)
    have readable : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r5 + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [h₁.rd, h₁.wr, hbase]; exact hr n (by omega_using [hn])
    have writable : InRegions s₁.wr (s₁.gpr .r5 + BitVec.ofNat 64 (256 + 8 * n)) 8 := by
      rw [h₁.wr, hbase]; exact hw n (by omega_using [hn])
    obtain ⟨s₂, run₂, keep₂⟩ := copy64_ok s₁ .r5 .r5
      (8 * n) (256 + 8 * n) (by decide) (by decide) (by decide) readable writable (by omega_using [hn])
      (by omega_using [hn])
    have source : s₁.mem.readW (s.gpr .r5 + BitVec.ofNat 64 (8 * n)) 64 =
        s.mem.readW (s.gpr .r5 + BitVec.ofNat 64 (8 * n)) 64 := by
      apply h₁.frame.readW (r := ⟨s.gpr .r5 + BitVec.ofNat 64 (8 * n), 8⟩)
        (Region.contains_self _ _) _ (by decide)
      intro r h
      obtain rfl := List.mem_singleton.mp h
      exact Offset.disjoint (s.gpr .r5) (by omega_using [hn]) (by omega_using [hn]) (by decide)
    have mem₂ : s₂.mem = s₁.mem.writeW (s.gpr .r5 + BitVec.ofNat 64 (256 + 8 * n))
        (s.mem.readW (s.gpr .r5 + BitVec.ofNat 64 (8 * n)) 64) := by
      have hm := keep₂.mem
      rw [hbase, source] at hm
      exact hm
    refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr,
      fun r hr => (keep₂.reg r (by simpa only [List.mem_singleton] using hr)).trans (h₁.reg r hr), ?_⟩⟩
    · intro i hi
      rw [mem₂]
      by_cases he : i = n
      · subst i; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep (s.gpr .r5) (by omega_using [he]) (by omega_using [hn, hi]) (by omega_using [hn])) (by decide)]
        exact h₁.keys i (by omega_using [hi, he])
    · rw [mem₂]
      apply h₁.frame.writeW (List.mem_singleton_self _) _
      have hc := Offset.contains_base (s.gpr .r5 + BitVec.ofNat 64 256)
        (d := 8 * n) (n := 8) (k := 128) (by omega_using [hn]) (by omega_using [hn])
      rw [Offset.add_ofNat_add_ofNat] at hc
      exact hc

end VG.Proof.TripleDes.PPC64LE.Key

end

end

/-! ### `TripleDes.PPC64LE.Key.Component`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.Key.Loop`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.Key.Store`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Key

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

def pack : List Instr := [.lsl .r8 .r0 28, .logic .xor .r8 .r8 .r7]

def tail : List Instr := [.store .d .r9 .r6 0, .addi .r6 .r6 8, .addi .r12 .r12 1, .subi .r8 .r12 16]

theorem pack_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .r0 = c.setWidth 64) (hd : s.gpr .r7 = d.setWidth 64) :
    ∃ s', runBlock isa pack s = some s' ∧
      (s'.gpr .r8).setWidth 56 = c ++ d ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) := by
  let s₁ := s.write .r8 (s.gpr .r0 <<< 28)
  let s₂ := s₁.write .r8 (s₁.gpr .r8 ^^^ s₁.gpr .r7)
  refine ⟨s₂, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · rw [pack, runBlock_cons, exec_lsl (by decide), runStep_some, runBlock_cons, exec_logic,
      runStep_some, runBlock_nil]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
    rw [hc, hd]; exact pack28_shift c d
  · intro r hr; simp only [s₂, s₁, gpr_write, hr, ite_false]

theorem nextRound_values : ∀ j < 16,
    BitVec.ofNat 64 j + BitVec.ofNat 64 1 = BitVec.ofNat 64 (j + 1) ∧
    ((BitVec.ofNat 64 j + BitVec.ofNat 64 1 - BitVec.ofNat 64 16) != 0) = decide (j ≠ 15) := by
  decide

theorem tail_ok (s : State) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r12 = BitVec.ofNat 64 j)
    (hw : InRegions s.wr (s.gpr .r6) 8) :
    ∃ s', runBlock isa tail s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r6) (s.gpr .r9) ∧
      s'.gpr .r6 = s.gpr .r6 + 8 ∧ s'.gpr .r12 = BitVec.ofNat 64 (j + 1) ∧
      isa.eval (.nonzero .d .r8) s' = some (decide (j ≠ 15)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r8 → r ≠ .r12 → r ≠ .r6 → s'.gpr r = s.gpr r) := by
  have hstore := exec_store_d (s := s) (t := .r9) (n := .r6) (off := 0) (by decide) (by decide)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw)
  let s₁ : State := { s with mem := s.mem.writeW (s.gpr .r6 + BitVec.ofNat 64 0) (s.gpr .r9) }
  let s₂ := s₁.write .r6 (s₁.gpr .r6 + BitVec.ofNat 64 8)
  let s₃ := s₂.write .r12 (s₂.gpr .r12 + BitVec.ofNat 64 1)
  let s₄ := s₃.write .r8 (s₃.gpr .r12 - BitVec.ofNat 64 16)
  have h12 : s₃.gpr .r12 = BitVec.ofNat 64 (j + 1) := by
    simp only [s₃, s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
    rw [hc]; exact (nextRound_values j hj).1
  refine ⟨s₄, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · rw [tail, runBlock_cons, hstore, runStep_some, runBlock_cons, exec_addi (by decide) (by decide),
      runStep_some, runBlock_cons, exec_addi (by decide) (by decide), runStep_some, runBlock_cons,
      exec_subi (by decide) (by decide), runStep_some, runBlock_nil]
  · change s.mem.writeW (s.gpr .r6 + BitVec.ofNat 64 0) (s.gpr .r9) = _
    rw [BitVec.add_zero]
  · simp only [s₄, s₃, s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [s₄, gpr_write, reduceCtorEq, ite_false]; exact h12
  · change VG.PPC64LE.eval (.nonzero .d .r8) s₄ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, s₄, gpr_write_self]
    rw [h12, ← (nextRound_values j hj).1]
    exact congrArg some (nextRound_values j hj).2
  · intro r h8 h12 h6
    simp only [s₄, s₃, s₂, s₁, gpr_write, h8, h12, h6, ite_false]

structure StorePost (c d : BitVec 28) (j : Nat) (s s' : State) : Prop where
  mem : s'.mem = s.mem.writeW (s.gpr .r6) ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64)
  ptr : s'.gpr .r6 = s.gpr .r6 + 8
  counter : s'.gpr .r12 = BitVec.ofNat 64 (j + 1)
  flag : isa.eval (.nonzero .d .r8) s' = some (decide (j ≠ 15))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ (keyKept ++ [.r0, .r7]), s'.gpr r = s.gpr r

theorem storeRound_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r0 = c.setWidth 64) (hd : s.gpr .r7 = d.setWidth 64)
    (hjreg : s.gpr .r12 = BitVec.ofNat 64 j) (hw : InRegions s.wr (s.gpr .r6) 8) :
    WP isa (.block Impl.TripleDes.PPC64LE.Key.storeRound) s (StorePost c d j s) := by
  have code : Impl.TripleDes.PPC64LE.Key.storeRound =
      (pack ++ permuteCode Spec.TripleDes.pc2 56 .r9 .r8 .r10 .r11) ++ tail := rfl
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, reg₁⟩ := pack_ok s c d hc hd
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, reg₂⟩ := pc2_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [word₁] at word₂
  have checks : ∀ r ∈ (keyKept ++ [.r0, .r7, .r12, .r6]),
      ((instrs keyPermutation2.lit).all fun op => dstOf op != some r) = true := by decide +kernel
  have keep₂ : ∀ r ∈ (keyKept ++ [.r0, .r7, .r12, .r6]), s₂.gpr r = s.gpr r := by
    intro r hr
    have unused : ∀ r ∈ (keyKept ++ [.r0, .r7, .r12, .r6]), r ≠ .r8 := by decide
    exact (reg₂ r (checks r hr)).trans (reg₁ r (unused r hr))
  have counter₂ := (keep₂ .r12 (by decide)).trans hjreg
  have write₂ : InRegions s₂.wr (s₂.gpr .r6) 8 := by
    rw [wr₂, wr₁, keep₂ .r6 (by decide)]; exact hw
  obtain ⟨s₃, run₃, mem₃, ptr₃, counter₃, flag₃, rd₃, wr₃, reg₃⟩ := tail_ok s₂ j hj counter₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ⟨?_, ?_, counter₃, flag₃, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), ?_⟩⟩
  · rw [mem₃, mem₂, mem₁, keep₂ .r6 (by decide), word₂]
  · rw [ptr₃, keep₂ .r6 (by decide)]
  · intro r hr
    have incl : ∀ r ∈ (keyKept ++ [.r0, .r7]),
        r ≠ .r8 ∧ r ≠ .r12 ∧ r ≠ .r6 ∧ r ∈ (keyKept ++ [.r0, .r7, .r12, .r6]) := by decide
    exact (reg₃ r (incl r hr).1 (incl r hr).2.1 (incl r hr).2.2.1).trans (keep₂ r (incl r hr).2.2.2)

end VG.Proof.TripleDes.PPC64LE.Key

end

end


@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Key

open VG VG.PPC64LE
open VG.Proof.TripleDes (keyPrefix keyInitial keyStep keyPrefix_succ)

structure LoopState (key : BitVec 64) (base : Addr) (origin : State) (j : Nat) (s : State) : Prop where
  c : s.gpr .r0 = (keyPrefix key j).1.setWidth 64
  d : s.gpr .r7 = (keyPrefix key j).2.1.setWidth 64
  counter : s.gpr .r12 = BitVec.ofNat 64 j
  pointer : s.gpr .r6 = base + BitVec.ofNat 64 (8 * j)
  keys : ∀ i < j, ∀ hi : i < 16, s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 =
    ((keyPrefix key j).2.2[i]'hi).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r ∈ keyKept, s.gpr r = origin.gpr r
  frame : Frame [⟨base, 128⟩] origin.mem s.mem

def LoopInv (key : BitVec 64) (base : Addr) (origin : State) (n : Nat) (s : State) : Prop :=
  1 ≤ n ∧ n ≤ 16 ∧ LoopState key base origin (16 - n) s

theorem loopBody_ok (key : BitVec 64) (base : Addr) (origin : State)
    (hw : ∀ j < 16, InRegions origin.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (j : Nat) (hj : j < 16) (s : State) (hs : LoopState key base origin j s) :
    WP isa (.seq Impl.TripleDes.PPC64LE.Key.rotation (.block Impl.TripleDes.PPC64LE.Key.storeRound)) s
      (fun s' => isa.eval (.nonzero .d .r8) s' = some (decide (j ≠ 15)) ∧ LoopState key base origin (j + 1) s') := by
  apply WP.seq
  apply WP.mono (rotation_ok s _ _ j hj hs.c hs.d hs.counter)
  intro s₁ h₁
  have unused : ∀ r ∈ (keyKept ++ [.r12, .r6]),
      r ≠ .r8 ∧ r ≠ .r0 ∧ r ≠ .r7 := by decide
  have reg₁ : ∀ r ∈ (keyKept ++ [.r12, .r6]), s₁.gpr r = s.gpr r := by
    intro r hr
    exact h₁.reg r (unused r hr).1 (unused r hr).2.1 (unused r hr).2.2
  have write₁ : InRegions s₁.wr (s₁.gpr .r6) 8 := by
    rw [h₁.wr, hs.wr, reg₁ .r6 (by decide), hs.pointer]
    exact hw j hj
  apply WP.mono (storeRound_ok s₁ _ _ j hj h₁.c h₁.d
    ((reg₁ .r12 (by decide)).trans hs.counter) write₁)
  intro s₂ h₂
  have hmem : s₂.mem = s.mem.writeW (base + BitVec.ofNat 64 (8 * j))
      ((Spec.TripleDes.permute Spec.TripleDes.pc2
        ((keyPrefix key j).1.rotateLeft (Spec.TripleDes.rotations.getD j 0) ++
          (keyPrefix key j).2.1.rotateLeft (Spec.TripleDes.rotations.getD j 0))).setWidth 64) := by
    rw [h₂.mem, h₁.mem, reg₁ .r6 (by decide), hs.pointer]
  refine ⟨h₂.flag, ⟨?_, ?_, h₂.counter, ?_, ?_, h₂.rd.trans (h₁.rd.trans hs.rd),
    h₂.wr.trans (h₁.wr.trans hs.wr), ?_, ?_⟩⟩
  · rw [keyPrefix_succ]
    exact (h₂.reg .r0 (by decide)).trans h₁.c
  · rw [keyPrefix_succ]
    exact (h₂.reg .r7 (by decide)).trans h₁.d
  · rw [h₂.ptr, reg₁ .r6 (by decide), hs.pointer]
    change base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 8 = _
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega_using [])
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
    have incl : ∀ r ∈ keyKept,
        r ∈ (keyKept ++ [.r0, .r7]) ∧
        r ∈ (keyKept ++ [.r12, .r6]) := by decide
    exact (h₂.reg r (incl r hr).1).trans ((reg₁ r (incl r hr).2).trans (hs.reg r hr))
  · rw [hmem]
    exact hs.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base base (by omega_using [hj]) (by omega_using [hj]))

theorem loopStep (key : BitVec 64) (base : Addr) (origin : State)
    (hw : ∀ j < 16, InRegions origin.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (n : Nat) (s : State) (hs : LoopInv key base origin n s) :
    WP isa (.seq Impl.TripleDes.PPC64LE.Key.rotation (.block Impl.TripleDes.PPC64LE.Key.storeRound)) s
      (fun s' => (isa.eval (.nonzero .d .r8) s' = some false ∧ LoopState key base origin 16 s') ∨
        (isa.eval (.nonzero .d .r8) s' = some true ∧ ∃ m < n, LoopInv key base origin m s')) := by
  apply WP.mono (loopBody_ok key base origin hw (16 - n) (by omega_using [hs.1]) s hs.2.2)
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
    (hc : s.gpr .r0 = (keyInitial key).1.setWidth 64)
    (hd : s.gpr .r7 = (keyInitial key).2.1.setWidth 64)
    (hcount : s.gpr .r12 = 0) (hptr : s.gpr .r6 = base) :
    WP isa (.loop (.seq Impl.TripleDes.PPC64LE.Key.rotation
      (.block Impl.TripleDes.PPC64LE.Key.storeRound)) (.nonzero .d .r8)) s (LoopState key base s 16) := by
  apply WP.loop (M := isa) (body := .seq Impl.TripleDes.PPC64LE.Key.rotation
      (.block Impl.TripleDes.PPC64LE.Key.storeRound)) (c := .nonzero .d .r8)
    (Q := LoopState key base s 16) (LoopInv key base s) (loopStep key base s hw) 16 s
  refine ⟨by decide, by decide, hc, hd, hcount, ?_, ?_, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  · exact hptr.trans (BitVec.add_zero base).symm
  · intro i hi
    omega

end VG.Proof.TripleDes.PPC64LE.Key

end

end


@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Key

open VG VG.PPC64LE

structure ComponentPost (keys : Spec.TripleDes.DesSchedule) (base : Addr) (s s' : State) : Prop where
  keys : ∀ i < 16, s'.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 = (keys.getD i 0).setWidth 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ keyKept, s'.gpr r = s.gpr r
  frame : Frame [⟨base, 128⟩] s.mem s'.mem

theorem component_ok (s : State) (offset component : Nat) (hc : component < 3)
    (ho : offset % 8 = 0 ∧ offset < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 offset) 8)
    (hw : ∀ j < 16, InRegions s.wr
      (s.gpr .r5 + BitVec.ofNat 64 (128 * component) + BitVec.ofNat 64 (8 * j)) 8) :
    WP isa (Impl.TripleDes.PPC64LE.Key.component offset component) s
      (ComponentPost (Spec.TripleDes.expandDesKey (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .r3 + BitVec.ofNat 64 offset))))
        (s.gpr .r5 + BitVec.ofNat 64 (128 * component)) s) := by
  rw [Impl.TripleDes.PPC64LE.Key.component]
  apply WP.seq
  apply WP.mono (load_ok s offset component hc ho.2 hr)
  intro s₁ h₁
  have writes : ∀ j < 16, InRegions s₁.wr
      (s.gpr .r5 + BitVec.ofNat 64 (128 * component) + BitVec.ofNat 64 (8 * j)) 8 := by
    rw [h₁.wr]; exact hw
  apply WP.mono (loop_ok _ _ s₁ writes h₁.c h₁.d h₁.counter h₁.ptr)
  intro s₂ h₂
  refine ⟨?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), ?_⟩
  · intro i hi
    rw [VG.Proof.TripleDes.expandDesKey_prefix, VG.Proof.TripleDes.vector_getD _ i hi 0]
    exact h₂.keys i hi hi
  · rw [← h₁.mem]
    exact h₂.frame

end VG.Proof.TripleDes.PPC64LE.Key

end

end


@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Key

open VG VG.PPC64LE
open VG.Proof.TripleDes (componentKeys componentOffset)

abbrev keyR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev outputR (s : State) : Region := ⟨s.gpr .r5, 384⟩

def slot (base : Addr) (c j : Nat) : Addr := base + BitVec.ofNat 64 (128 * c + 8 * j)

structure Components (origin s : State) (done : Nat) : Prop where
  keys : ∀ c < done, ∀ j < 16, s.mem.readW (slot (origin.gpr .r5) c j) 64 =
    ((componentKeys origin.mem (origin.gpr .r3) (origin.gpr .r4).toNat c).getD j 0).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r ∈ keyKept, s.gpr r = origin.gpr r
  frame : Frame [outputR origin] origin.mem s.mem

structure Permissions (s : State) : Prop where
  reads : ∀ offset, offset + 8 ≤ (s.gpr .r4).toNat →
    InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 offset) 8
  writes : ∀ offset, offset + 8 ≤ 384 → InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 offset) 8
  keyOutput : (keyR s).Disjoint (outputR s)
  valid : Spec.TripleDes.validKey (s.gpr .r4).toNat

theorem componentStep_ok (origin s : State) (c : Nat) (hc : c < 3)
    (hp : Permissions origin) (hs : Components origin s c)
    (hoff : componentOffset (origin.gpr .r4).toNat c = 8 * c) :
    WP isa (Impl.TripleDes.PPC64LE.Key.component (8 * c) c) s
      (Components origin · (c + 1)) := by
  have offsetBound := VG.Proof.TripleDes.componentOffset_bound _ c hp.valid hc
  rw [hoff] at offsetBound
  have read : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (8 * c)) 8 := by
    rw [hs.rd, hs.wr, hs.reg .r3 (by decide)]
    exact hp.reads _ offsetBound
  have write : ∀ j < 16, InRegions s.wr
      (s.gpr .r5 + BitVec.ofNat 64 (128 * c) + BitVec.ofNat 64 (8 * j)) 8 := by
    intro j hj
    rw [hs.wr, hs.reg .r5 (by decide), Offset.add_ofNat_add_ofNat]
    exact hp.writes _ (by omega_using [hc, hj])
  apply WP.mono (component_ok s (8 * c) c hc (by omega_using [hc]) read write)
  intro t ht
  have frame : Frame [⟨origin.gpr .r5 + BitVec.ofNat 64 (128 * c), 128⟩] s.mem t.mem := by
    have hf := ht.frame
    rw [hs.reg .r5 (by decide)] at hf
    exact hf
  have key : Spec.TripleDes.blockAt s.mem (s.gpr .r3 + BitVec.ofNat 64 (8 * c)) =
      Spec.TripleDes.blockAt origin.mem (origin.gpr .r3 + BitVec.ofNat 64 (8 * c)) := by
    rw [hs.reg .r3 (by decide)]
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
      rw [key, hs.reg .r5 (by decide), Offset.add_ofNat_add_ofNat] at h
      unfold componentKeys
      rw [hoff]
      exact h
    · have before : k < c := by omega_using [hk, he]
      have sep : (Region.mk (slot (origin.gpr .r5) k j) 8).Disjoint
          ⟨origin.gpr .r5 + BitVec.ofNat 64 (128 * c), 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [hk, hc, hj]) (by omega_using [hc])
      have hmem := frame.readW (a := slot (origin.gpr .r5) k j) (w := 64) (r := ⟨slot (origin.gpr .r5) k j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys k before j hj)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by omega_using [hc])⟩

theorem copyThird_ok (origin s : State) (hp : Permissions origin)
    (hs : Components origin s 2) (hn : (origin.gpr .r4).toNat = 16) :
    WP isa (.block Impl.TripleDes.PPC64LE.Key.copyThird) s (Components origin · 3) := by
  have reads : ∀ i < 16, InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hs.rd, hs.wr, hs.reg .r5 (by decide)]
    obtain ⟨r, hr, hc⟩ := hp.writes (8 * i) (by omega_using [hi])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writes : ∀ i < 16, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (256 + 8 * i)) 8 := by
    intro i hi
    rw [hs.wr, hs.reg .r5 (by decide)]
    exact hp.writes _ (by omega_using [hi])
  apply WP.mono (copy_ok s 16 (by decide) reads writes)
  intro t ht
  have frame : Frame [⟨origin.gpr .r5 + BitVec.ofNat 64 256, 128⟩] s.mem t.mem := by
    have h := ht.frame
    rw [hs.reg .r5 (by decide)] at h
    exact h
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr, ?_, hs.frame.trans (frame.sub ?_)⟩
  · intro c hc j hj
    by_cases he : c = 2
    · subst c
      have hRepeat : componentKeys origin.mem (origin.gpr .r3) (origin.gpr .r4).toNat 2 =
          componentKeys origin.mem (origin.gpr .r3) (origin.gpr .r4).toNat 0 := by
        rw [hn]; rfl
      have h := ht.keys j hj
      rw [hs.reg .r5 (by decide)] at h
      change t.mem.readW (origin.gpr .r5 + BitVec.ofNat 64 (256 + 8 * j)) 64 = _
      rw [hRepeat]
      have first := hs.keys 0 (by decide) j hj
      simp only [slot, Nat.mul_zero, Nat.zero_add] at first
      exact h.trans first
    · have before : c < 2 := by omega_using [hc, he]
      have sep : (Region.mk (slot (origin.gpr .r5) c j) 8).Disjoint
          ⟨origin.gpr .r5 + BitVec.ofNat 64 256, 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [before, hj]) (by decide)
      have hmem := frame.readW (a := slot (origin.gpr .r5) c j) (w := 64) (r := ⟨slot (origin.gpr .r5) c j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys c before j hj)
  · intro r hr
    have unused : ∀ r ∈ keyKept, r ≠ .r8 := by decide
    exact (ht.reg r (unused r hr)).trans (hs.reg r hr)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by decide)⟩

def componentIndex (i : Nat) : Nat := if i < 16 then 0 else if i < 32 then 1 else 2

theorem index_partition : ∀ i < 48, componentIndex i < 3 ∧ i % 16 < 16 ∧
    8 * i = 128 * componentIndex i + 8 * (i % 16) := by decide

theorem Components.schedule {origin s : State} (h : Components origin s 3) :
    Spec.TripleDes.scheduleAt s.mem (origin.gpr .r5) =
      VG.Proof.TripleDes.expandedMemory origin.mem (origin.gpr .r3) (origin.gpr .r4).toNat := by
  apply Vector.ext
  intro i hi
  have fact := index_partition i hi
  have keys := h.keys (componentIndex i) fact.1 (i % 16) fact.2.1
  rw [slot, ← fact.2.2] at keys
  rw [VG.Proof.TripleDes.scheduleAt_readW s.mem (origin.gpr .r5) i hi]
  simp only [VG.Proof.TripleDes.expandedMemory, Vector.getElem_ofFn]
  by_cases h16 : i < 16
  · simpa only [componentIndex, h16, ite_true] using keys
  · by_cases h32 : i < 32
    · simpa only [componentIndex, h16, h32, ite_false, ite_true] using keys
    · simpa only [componentIndex, h16, h32, ite_false] using keys


end VG.Proof.TripleDes.PPC64LE.Key

end

end


@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Key

open VG VG.PPC64LE

theorem cmpLength_ok (s : State) :
    ∃ s', runBlock isa [.subi .r8 .r4 16] s = some s' ∧
      isa.eval (.zero .d .r8) s' = some (s.gpr .r4 == 16) ∧ Kept [.r8] s s' := by
  refine ⟨s.write .r8 (s.gpr .r4 - BitVec.ofNat 64 16), ?_, ?_, write_keep _ _⟩
  · rw [runBlock_cons, exec_subi (by decide) (by decide), runStep_some, runBlock_nil]
  · change VG.PPC64LE.eval (.zero .d .r8) _ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, gpr_write_self, BitVec.setWidth_eq]
    exact congrArg some (by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      bv_omega)

theorem Components.keep {origin s t : State} {n : Nat} (hs : Components origin s n)
    (ht : Kept [.r8] s t) : Components origin t n :=
  ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r hr => (ht.reg r (by revert hr; cases r <;> decide)).trans (hs.reg r hr),
    by rw [ht.mem]; exact hs.frame⟩

theorem beq16_toNat (x : BitVec 64) : (x == 16) = decide (x.toNat = 16) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    apply BitVec.eq_of_toNat_eq
    exact h

theorem body_ok (origin s : State) (hp : Permissions origin) (hs : Components origin s 0) :
    WP isa Impl.TripleDes.PPC64LE.Key.expandKey s (Components origin · 3) := by
  rw [Impl.TripleDes.PPC64LE.Key.expandKey]
  apply WP.seq
  apply WP.mono (componentStep_ok origin s 0 (by decide) hp hs (by rfl))
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (componentStep_ok origin s₁ 1 (by decide) hp hs₁ (by rfl))
  intro s₂ hs₂
  apply WP.seq
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := cmpLength_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have hs₃ := hs₂.keep keep₃
  have flag : isa.eval (.zero .d .r8) s₃ = some (decide ((origin.gpr .r4).toNat = 16)) := by
    rw [flag₃, hs₂.reg .r4 (by decide), beq16_toNat]
  by_cases h16 : (origin.gpr .r4).toNat = 16
  · apply WP.ite true (by simpa only [h16, decide_true] using flag)
    · intro _; exact copyThird_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simpa only [h16, decide_false] using flag)
    · simp
    · intro _
      exact componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

end VG.Proof.TripleDes.PPC64LE.Key

end

end


/-!
# Triple DES key expansion on PPC64LE, verified

The code writes only volatile registers and needs no working space, so it is
verified against `expandKeyContract` with no stack.
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Key

open VG VG.PPC64LE

def contract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let output : Region := ⟨s.gpr .r5, 384⟩
    s.rd = [key] ∧ s.wr = [output] ∧ key.Disjoint output ∧
      Spec.TripleDes.validKey (s.gpr .r4).toNat
  post s s' := Spec.TripleDes.scheduleAt s'.mem (s.gpr .r5) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  pub := PublicRegs [.r3, .r4, .r5]

/-- The registers the code writes: all volatile. -/
def written : List Reg := [.r0, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem expand_correct (s : State) (hs : contract.pre s) :
    WP isa Impl.TripleDes.PPC64LE.Key.expandKey s (contract.post s) := by
  obtain ⟨hrd, hwr, keyOutput, valid⟩ := hs
  have hp : Permissions s := by
    constructor
    · intro offset hoff
      rw [hrd, hwr]
      exact ⟨⟨s.gpr .r3, (s.gpr .r4).toNat⟩, by simp,
        Offset.contains_base _ hoff (by
          have bound := BitVec.isLt (s.gpr .r4)
          omega_using [hoff, bound])⟩
    · intro offset hoff
      rw [hwr]
      exact ⟨⟨s.gpr .r5, 384⟩, by simp, Offset.contains_base _ hoff (by omega_using [hoff])⟩
    · exact keyOutput
    · exact valid
  apply WP.mono (body_ok s s hp ⟨fun _ h => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩)
  intro s₂ h₂
  have result := h₂.schedule
  rw [← VG.Proof.TripleDes.expandKey_memory s.mem (s.gpr .r3) (s.gpr .r4).toNat valid] at result
  exact result

theorem correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa Impl.TripleDes.PPC64LE.Key.expandKey s t s' ∧ abiPreserved s s' ∧
      contract.post s s' := by
  obtain ⟨t, s', he, hpost, hkeep⟩ :=
    WP.keep written (expand_correct s hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, abiPreserved_of_keep he hkeep (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), hpost⟩

def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 384⟩]

theorem publicRegs_three (s₁ s₂ : State) : PublicRegs [.r3, .r4, .r5] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 := by simp [PublicRegs]

theorem verified : Verified target Impl.TripleDes.PPC64LE.Key.expandKey
    (Spec.TripleDes.expandKeyContract abi) := by
  refine Verified.of_correct correct (expandKey_constantTime _) ?_
  sig_implies [Spec.TripleDes.expandKeyContract, Spec.TripleDes.expandKeySig,
    Spec.TripleDes.expandKeyPre, Spec.TripleDes.expandKeyPost, abi, argRegs,
    contract, publicRegs_three] [satState] using satState

end VG.Proof.TripleDes.PPC64LE.Key
