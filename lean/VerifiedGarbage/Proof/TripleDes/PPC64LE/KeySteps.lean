module

public import VerifiedGarbage.Impl.TripleDes.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Word
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.TripleDes.Word

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
  have hleft : 64 - n < 64 := by omega
  have hright : 28 - n < 64 := by omega
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
