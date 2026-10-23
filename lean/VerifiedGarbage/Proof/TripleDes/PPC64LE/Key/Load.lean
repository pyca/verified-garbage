module

import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Permutation
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bytes
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Word
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

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
  have hb : 128 * component < 2 ^ 15 := by omega
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
