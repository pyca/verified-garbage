module

public import VerifiedGarbage.Impl.Gcm.AArch64.Xor3
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.Interleave

@[expose] public section
namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64 VG.Impl.Gcm.AArch64.Stitch
open VG.Proof.Aes.AArch64.Aese (setV_setV setV_v_self setV_v_of_ne)

/-- Lowering preserves the entire machine state, including aliased operands. -/
theorem run_xor3Base (d a b c : VReg) (s : State) :
    runBlock isa (xor3Base d a b c) s = exec (.vop (.eor3 d a b c)) s := by
  by_cases hc : c = d
  · subst c
    by_cases hb : b = d
    · subst b
      simp only [xor3Base, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      change some (s.setV d (s.v a ||| s.v a)) = some (s.setV d (s.v a ^^^ s.v d ^^^ s.v d))
      simp [BitVec.xor_assoc]
    · simp [xor3Base, hb]
      change some ((s.setV d (s.v d ^^^ s.v a)).setV d _) = some (s.setV d _)
      rw [setV_v_self, setV_v_of_ne _ _ hb, setV_setV]
      simp [BitVec.xor_comm, BitVec.xor_assoc]
  · simp [xor3Base, hc]
    change some ((s.setV d (s.v a ^^^ s.v b)).setV d _) = some (s.setV d _)
    rw [setV_v_self, setV_v_of_ne _ _ hc, setV_setV]

theorem run_lowerXor3 (i : Instr) (s : State) :
    runBlock isa (lowerXor3 i) s = exec i s := by
  unfold lowerXor3
  split
  · exact run_xor3Base _ _ _ _ _
  · change (exec _ s).bind some = exec _ s
    cases exec i s <;> rfl

theorem run_lowerXor3_block (code : List Instr) (s : State) :
    runBlock isa (code.flatMap lowerXor3) s = runBlock isa code s := by
  induction code generalizing s with
  | nil => rfl
  | cons i rest ih =>
    rw [List.flatMap_cons, VG.AArch64.Interleave.runBlock_append, run_lowerXor3]
    change (exec i s).bind _ = (exec i s).bind _
    exact congrArg ((exec i s).bind ·) (funext ih)

end VG.Proof.Gcm.AArch64.Stitch
