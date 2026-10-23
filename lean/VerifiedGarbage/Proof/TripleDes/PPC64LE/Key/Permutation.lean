module
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Lit

import VerifiedGarbage.Proof.TripleDes.PPC64LE.Permutation
import VerifiedGarbage.Proof.Framework.Mem

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
