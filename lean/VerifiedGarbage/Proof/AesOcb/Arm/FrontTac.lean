module

public import VerifiedGarbage.Proof.AesOcb.Arm.Body
public import VerifiedGarbage.Proof.AesOcb.Arm.Nonce

/-! # The tactics of `Front.lean`

In a module of their own: a macro costs much more to elaborate where it is
defined than where it is imported. -/

@[expose] public section

namespace VG.Proof.AesOcb.Arm

/-- Proves that a block of `W` misses a frame of parts of `W` and the stack
below `sp`. -/
macro "wdisj" L:term : tactic => `(tactic| plain_simp_names (
                   simp only [nonceR, hashR, bodyR, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
                   and_intros
                   all_goals first
                     | (with_reducible refine Lay.w_w $L ?_ ?_ ?_) <;> decide
                     | (with_reducible refine (Lay.bw' $L ?_).symm) <;> decide
                     | (with_reducible refine (Lay.d_w' $L ?_).symm) <;> decide))

/-- Proves that the data misses a frame of parts of `W` and the stack below
`sp`. -/
macro "ddisj" L:term : tactic => `(tactic| plain_simp_names (
                   simp only [nonceR, hashR, bodyR, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
                   and_intros
                   all_goals first
                     | (with_reducible refine Lay.d_w' $L ?_) <;> decide
                     | with_reducible exact (Lay.bd $L).symm))

end VG.Proof.AesOcb.Arm
