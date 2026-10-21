module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.FrontTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyBodyTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Safety
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StartPair

/-! # The shared body retains exactly the declared exponent and retry observations -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86.Key (Environment BodyPair)

theorem enterInput_trace (E : Environment) (valid : E.Valid) (sp : BitVec 32) (e p q p' q' : Nat) :
    RelCT isa (BodyPair E sp e p q p' q') VG.Impl.RsaKeyGen.X86.Key.enter
      (RuntimeStart E sp e p q p' q') := by
  intro s t tr ur u v P A C
  obtain ⟨trace, start⟩ := VG.Proof.RsaKeyGen.X86.Key.enterInput_trace E valid sp e p q p' q'
    _ _ _ _ _ _ P A C
  obtain ⟨CS, _, _, _⟩ := wp_result (VG.Proof.RsaKeyGen.X86.KeyArgs.enter_ok P.left.arguments) A
  obtain ⟨CT, _, _, _⟩ := wp_result (VG.Proof.RsaKeyGen.X86.KeyArgs.enter_ok P.right.arguments) C
  exact ⟨trace, start, context_workspace valid CS start.inputs.left.ws,
    context_workspace valid CT start.inputs.right.ws, CS, CT⟩

theorem body_trace (E : Environment) (valid : E.Valid) (sp : BitVec 32) (e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (BodyPair E sp e p q p' q') VG.Impl.RsaKeyGen.X86.KeyRuntime.body
      (VG.X86.Taint.Agree (τr [.esp])) := by
  intro s t tr ur u v P A C
  have raw := RelCT.seq (enterInput_trace E valid sp e p q p' q')
    (front_trace E valid sp e p q p' q' release)
  refine ⟨(raw _ _ _ _ _ _ P A C).1, agree_regs ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  rw [Exec.gpr body_noSp A, Exec.gpr body_noSp C]
  exact P.left.arguments.sp.trans P.right.arguments.sp.symm

end VG.Proof.RsaKeyGen.X86.KeyRuntime
