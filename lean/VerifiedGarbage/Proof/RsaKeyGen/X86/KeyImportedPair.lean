module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadInputsTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInputPair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadInputs

/-! # Secret input snapshots are imported into native arithmetic with matching public state -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86

structure SizedStart (E : Environment) (e p q p' q' : Nat) (s t : State) : Prop where
  inputs : InputPair E s t
  leftExponent : inputExponent E s.mem = e
  rightExponent : inputExponent E t.mem = e
  leftP : inputPrime E s.mem 2 = p
  leftQ : inputPrime E s.mem 3 = q
  rightP : inputPrime E t.mem 2 = p'
  rightQ : inputPrime E t.mem 3 = q'

structure ImportedPair (E : Environment) (e p q p' q' : Nat) (s t : State) : Prop where
  inputs : InputPair E s t
  left : CoreStart E.base E.size E.n E.k e p q s
  right : CoreStart E.base E.size E.n E.k e p' q' t
  agree : VG.X86.Taint.Agree (workspaceTaint true) s t

theorem inputReady_trace (E : Environment) (e p q p' q' : Nat) :
    RelCT isa (SizedStart E e p q p' q') (inputCode E.n) (ImportedPair E e p q p' q') := by
  intro s t tr ur u v P A C
  obtain ⟨trace, inputs, agree⟩ := inputCode_trace E _ _ _ _ _ _ P.inputs A C
  obtain ⟨_, left, _, _⟩ := wp_result (loadInputs_ok P.inputs.left) A
  obtain ⟨_, right, _, _⟩ := wp_result (loadInputs_ok P.inputs.right) C
  rw [P.leftExponent, P.leftP, P.leftQ] at left
  rw [P.rightExponent, P.rightP, P.rightQ] at right
  exact ⟨trace, inputs, left, right, agree⟩

end VG.Proof.RsaKeyGen.X86.Key
