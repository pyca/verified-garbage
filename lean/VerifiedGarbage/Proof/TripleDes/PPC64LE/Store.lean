module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.BlockIO
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Initial
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Word
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

def packHalves : List Instr := [.rotr .d .r6 .r14 32, .logic .xor .r6 .r6 .r15]

theorem rotateRight_extend (l : BitVec 32) :
    (l.setWidth 64).rotateRight 32 = l.setWidth 64 <<< 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j < 32
  · simp [h, hj]
  · simp [h, hj]

theorem packHalves_ok (s : State) (l r : BitVec 32)
    (hl : s.gpr .r14 = l.setWidth 64) (hr : s.gpr .r15 = r.setWidth 64) :
    ∃ s', runBlock isa packHalves s = some s' ∧
      s'.gpr .r6 = l ++ r ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q, q ≠ .r6 → s'.gpr q = s.gpr q) := by
  let s₁ := s.write .r6 ((s.gpr .r14).rotateRight 32)
  let s₂ := s₁.write .r6 (s₁.gpr .r6 ^^^ s₁.gpr .r15)
  refine ⟨s₂, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · rw [packHalves, runBlock_cons, exec_rotr_d (by decide), runStep_some, runBlock_cons,
      exec_logic, runStep_some, runBlock_nil]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false, hl, hr,
      rotateRight_extend]
    exact packHalves_shift l r
  · intro q hq
    simp only [s₂, s₁, gpr_write, hq, ite_false]

theorem final_preserves : loadKept.all (fun r =>
    (instrs finalPermutation.lit).all (fun op => dstOf op != some r)) = true := by
  decide +kernel

theorem writeData_ok (s : State) (hwrite : InRegions s.wr (s.gpr .r4) 8) :
    ∃ s', runBlock isa [.li .r7 0, .storeRev .d .r8 .r4 .r7] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r4) (rev64 (s.gpr .r8)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q, q ≠ .r7 → s'.gpr q = s.gpr q) := by
  let s₁ := s.write .r7 (BitVec.ofNat 64 0)
  have ha : s₁.gpr .r4 + s₁.gpr .r7 = s.gpr .r4 := by
    simp only [s₁, gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.add_zero]
  have hstore := exec_storeRev_d (s := s₁) (t := .r8) (a := .r4) (b := .r7) (by decide)
    (by rw [ha]; exact hwrite)
  rw [ha] at hstore
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s.gpr .r4) (rev64 (s₁.gpr .r8)) }, by
    rw [runBlock_cons, exec_li (by decide), runStep_some, runBlock_cons, hstore, runStep_some,
      runBlock_nil], ?_, rfl, rfl, ?_⟩
  · change s.mem.writeW (s.gpr .r4) (rev64 (s₁.gpr .r8)) = _
    rw [show s₁.gpr .r8 = s.gpr .r8 from gpr_write_of_ne _ _ (by decide)]
  · intro q hq
    exact gpr_write_of_ne _ _ hq

theorem blockStore_ok (s : State) (l r : BitVec 32)
    (hl : s.gpr .r14 = l.setWidth 64) (hr : s.gpr .r15 = r.setWidth 64)
    (hwrite : InRegions s.wr (s.gpr .r4) 8) :
    ∃ s', runBlock isa blockStore s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r4)
        (rev64 (Spec.TripleDes.permute Spec.TripleDes.fp (l ++ r))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ loadKept, s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, regs₁⟩ := packHalves_ok s l r hl hr
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, regs₂⟩ := final_raw_ok s₁
  have r4₁ : s₁.gpr .r4 = s.gpr .r4 := regs₁ .r4 (by decide)
  have r4₂ : s₂.gpr .r4 = s.gpr .r4 :=
    (regs₂ .r4 (List.all_eq_true.mp final_preserves .r4 (by decide))).trans r4₁
  obtain ⟨s₃, run₃, mem₃, rd₃, wr₃, regs₃⟩ := writeData_ok s₂ (by
    rw [r4₂, wr₂, wr₁]; exact hwrite)
  have hhead := runAppend_some _ _ _ _ _ run₁ run₂
  have htail := runAppend_some _ _ _ _ _ hhead run₃
  have hcode : blockStore =
      (packHalves ++ permuteCode Spec.TripleDes.fp 64 .r8 .r6 .r9 .r10) ++
      ([.li .r7 0, .storeRev .d .r8 .r4 .r7] : List Instr) := rfl
  refine ⟨s₃, (congrArg (fun is => runBlock isa is s) hcode).trans htail, ?_,
    rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_⟩
  · rw [mem₃, mem₂, mem₁, r4₂, word₂, word₁]
  · intro q hq
    have hno := List.all_eq_true.mp final_preserves q hq
    have hne : q ≠ .r6 ∧ q ≠ .r7 := by clear hno; revert hq; cases q <;> decide
    exact (regs₃ q hne.2).trans ((regs₂ q hno).trans (regs₁ q hne.1))

end VG.Proof.TripleDes.PPC64LE
