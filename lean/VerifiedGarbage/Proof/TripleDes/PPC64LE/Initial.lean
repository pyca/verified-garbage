module
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Lit

import VerifiedGarbage.Proof.TripleDes.PPC64LE.Permutation
import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.Framework.Mem
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE
open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

theorem initial_ok (s : State) :
    ∃ s', runBlock isa (instrs initialPermutation.lit) s = some s' ∧
      s'.gpr .r8 = (Spec.TripleDes.permute Spec.TripleDes.ip
        ((s.gpr .r7).setWidth 64)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) :=
  fixedPermutation_ok Spec.TripleDes.ip (by decide) (by decide)
    VG.Proof.TripleDes.ip_bounds .r7 .r8 (instrs initialPermutation.lit) initialPermutation_check s
end VG.Proof.TripleDes.PPC64LE
namespace VG.Proof.TripleDes.PPC64LE
open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

theorem initial_raw_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.ip 64 .r8 .r7 .r9 .r10) s = some s' ∧
      s'.gpr .r8 = Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .r7) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ := initial_ok s
  have hcode : permuteCode Spec.TripleDes.ip 64 .r8 .r7 .r9 .r10 =
      instrs initialPermutation.lit := congrArg instrs initialPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, mem, regs⟩
  exact word.trans ((BitVec.setWidth_eq _).trans
    (congrArg (Spec.TripleDes.permute Spec.TripleDes.ip) (BitVec.setWidth_eq _)))
end VG.Proof.TripleDes.PPC64LE

namespace VG.Proof.TripleDes.PPC64LE
open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE
theorem final_ok (s : State) :
    ∃ s', runBlock isa (instrs finalPermutation.lit) s = some s' ∧
      s'.gpr .r8 = (Spec.TripleDes.permute Spec.TripleDes.fp
        ((s.gpr .r6).setWidth 64)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) :=
  fixedPermutation_ok Spec.TripleDes.fp (by decide) (by decide)
    VG.Proof.TripleDes.fp_bounds .r6 .r8 (instrs finalPermutation.lit) finalPermutation_check s

theorem final_raw_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.fp 64 .r8 .r6 .r9 .r10) s = some s' ∧
      s'.gpr .r8 = Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .r6) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ := final_ok s
  have hcode : permuteCode Spec.TripleDes.fp 64 .r8 .r6 .r9 .r10 =
      instrs finalPermutation.lit := congrArg instrs finalPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, mem, regs⟩
  exact word.trans ((BitVec.setWidth_eq _).trans
    (congrArg (Spec.TripleDes.permute Spec.TripleDes.fp) (BitVec.setWidth_eq _)))

end VG.Proof.TripleDes.PPC64LE
