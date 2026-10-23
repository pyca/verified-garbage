module
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Lit
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Pass

import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bytes
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Initial
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Box
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Block

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

/-- The registers the block's load and store keep. -/
def loadKept : List Reg := passKept

theorem readData_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .r4) 8) :
    ∃ s', runBlock isa [.li .r6 0, .loadRev .d .r7 .r4 .r6] s = some s' ∧
      s'.gpr .r7 = Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .r4)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r) := by
  let s₁ := s.write .r6 (BitVec.ofNat 64 0)
  have ha : s₁.gpr .r4 + s₁.gpr .r6 = s.gpr .r4 := by
    simp only [s₁, gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.add_zero]
  have hload := exec_loadRev_d (s := s₁) (t := .r7) (a := .r4) (b := .r6) (by decide)
    (by rw [ha]; exact hread)
  rw [ha] at hload
  let s₂ := s₁.write .r7 (rev64 (s₁.mem.readW (s.gpr .r4) 64))
  refine ⟨s₂, by
    rw [runBlock_cons, exec_li (by decide), runStep_some, runBlock_cons, hload, runStep_some,
      runBlock_nil], ?_, rfl, rfl, rfl, ?_⟩
  · rw [gpr_write_self]
    exact (decodeBlock_readW s.mem (s.gpr .r4)).symm
  · intro r h6 h7
    simp only [s₂, s₁, gpr_write, h6, h7, ite_false]

theorem rotateRight_zero32 (x : BitVec 32) : x.rotateRight 0 = x := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]

def splitHalves : List Instr := [.lsr .d .r14 .r8 32, .rotr .w .r15 .r8 0]

theorem splitHalves_ok (s : State) :
    ∃ s', runBlock isa splitHalves s = some s' ∧
      s'.gpr .r14 = s.gpr .r8 >>> 32 ∧
      s'.gpr .r15 = ((s.gpr .r8).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) := by
  let s₁ := s.write .r14 (s.gpr .r8 >>> 32)
  let s₂ := s₁.write .r15 (((s₁.gpr .r8).setWidth 32).rotateRight 0 |>.setWidth 64)
  refine ⟨s₂, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · rw [splitHalves, runBlock_cons, exec_lsr_d (by decide), runStep_some, runBlock_cons,
      exec_rotr_w (by decide), runStep_some, runBlock_nil]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false, rotateRight_zero32]
  · intro r h14 h15
    simp only [s₂, s₁, gpr_write, h14, h15, ite_false]

theorem upperHalf_extend (x : BitVec 64) :
    x >>> 32 = ((x >>> 32).setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h : j < 32
  · simp only [h, hj, decide_true, Bool.true_and]
  · have hz : x.getLsbD (32 + j) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp only [h, hj, decide_false, decide_true, Bool.false_and, Bool.true_and, hz]

theorem runAppend_some (xs ys : List Instr) (s t u : State)
    (hx : runBlock isa xs s = some t) (hy : runBlock isa ys t = some u) :
    runBlock isa (xs ++ ys) s = some u := by
  calc
    runBlock isa (xs ++ ys) s = (runBlock isa xs s).bind (runBlock isa ys) :=
      runBoxes_append xs ys s
    _ = (some t).bind (runBlock isa ys) := congrArg (fun v => v.bind (runBlock isa ys)) hx
    _ = runBlock isa ys t := Option.bind_some t (runBlock isa ys)
    _ = some u := hy

theorem initial_preserves : loadKept.all (fun r =>
    (instrs initialPermutation.lit).all (fun op => dstOf op != some r)) = true := by
  decide +kernel

theorem blockLoad_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .r4) 8) :
    ∃ s', runBlock isa blockLoad s = some s' ∧
      s'.gpr .r14 =
        (((Spec.TripleDes.permute Spec.TripleDes.ip
          (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .r4)))) >>> 32).setWidth 32).setWidth 64 ∧
      s'.gpr .r15 =
        ((Spec.TripleDes.permute Spec.TripleDes.ip
          (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .r4)))).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ loadKept, s'.gpr r = s.gpr r) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, regs₁⟩ := readData_ok s hread
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, regs₂⟩ := initial_raw_ok s₁
  obtain ⟨s₃, run₃, left₃, right₃, mem₃, rd₃, wr₃, regs₃⟩ := splitHalves_ok s₂
  have hword : s₂.gpr .r8 = Spec.TripleDes.permute Spec.TripleDes.ip
      (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .r4))) :=
    word₂.trans (congrArg (Spec.TripleDes.permute Spec.TripleDes.ip) word₁)
  have hhead := runAppend_some _ _ _ _ _ run₁ run₂
  have htail := runAppend_some _ _ _ _ _ hhead run₃
  have hcode : blockLoad =
      (([.li .r6 0, .loadRev .d .r7 .r4 .r6] : List Instr) ++
        permuteCode Spec.TripleDes.ip 64 .r8 .r7 .r9 .r10) ++ splitHalves := by
    simp only [blockLoad, splitHalves, List.append_assoc]
  refine ⟨s₃, (congrArg (fun is => runBlock isa is s) hcode).trans htail, ?_, ?_,
    mem₃.trans (mem₂.trans mem₁), rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), ?_⟩
  · exact left₃.trans ((congrArg (fun x : BitVec 64 => x >>> 32) hword).trans (upperHalf_extend _))
  · exact right₃.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hword)
  · intro r hr
    have hno := List.all_eq_true.mp initial_preserves r hr
    have hne : r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r14 ∧ r ≠ .r15 := by
      clear hno; revert hr; cases r <;> decide
    exact (regs₃ r hne.2.2.1 hne.2.2.2).trans ((regs₂ r hno).trans (regs₁ r hne.1 hne.2.1))

end VG.Proof.TripleDes.PPC64LE
