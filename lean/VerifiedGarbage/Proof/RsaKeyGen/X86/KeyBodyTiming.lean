module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyBody
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportedPair
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWidthTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEntryTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpCode
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The complete native key body obeys the shared public exponent and retry leak -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

structure BodyPair (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat) (s t : State) : Prop where
  left : EntryInput E sp s
  right : EntryInput E sp t
  leftExponent : inputExponent E s.mem = e
  rightExponent : inputExponent E t.mem = e
  leftP : inputPrime E s.mem 2 = p
  leftQ : inputPrime E s.mem 3 = q
  rightP : inputPrime E t.mem 2 = p'
  rightQ : inputPrime E t.mem 3 = q'

theorem enterInput_trace (E : Environment) (v : E.Valid) (sp : BitVec 32) (e p q p' q' : Nat) :
    RelCT isa (BodyPair E sp e p q p' q') VG.Impl.RsaKeyGen.X86.Key.enter (SizedStart E e p q p' q') := by
  intro s t tr ur u z P A C
  have trace := (KeyArgs.enter_trace _ _ _ _ _ _ ⟨P.left.arguments, P.right.arguments⟩ A C).1
  obtain ⟨leftInput, leftFrame, leftKeeps⟩ := wp_result (enter_input_ok v P.left) A
  obtain ⟨rightInput, rightFrame, rightKeeps⟩ := wp_result (enter_input_ok v P.right) C
  refine ⟨trace, ⟨⟨leftInput, rightInput, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
    exact P.left.arguments.sp.trans P.right.arguments.sp.symm
  · unfold inputExponent
    rw [leftInput.exponent_preserved leftFrame]
    exact P.leftExponent
  · unfold inputExponent
    rw [rightInput.exponent_preserved rightFrame]
    exact P.rightExponent
  · unfold inputPrime
    rw [leftInput.output_preserved (by decide : 2 < 7) leftFrame]
    exact P.leftP
  · unfold inputPrime
    rw [leftInput.output_preserved (by decide : 3 < 7) leftFrame]
    exact P.leftQ
  · unfold inputPrime
    rw [rightInput.output_preserved (by decide : 2 < 7) rightFrame]
    exact P.rightP
  · unfold inputPrime
    rw [rightInput.output_preserved (by decide : 3 < 7) rightFrame]
    exact P.rightQ

theorem body_trace (E : Environment) (v : E.Valid) (sp : BitVec 32) (e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (BodyPair E sp e p q p' q') VG.Impl.RsaKeyGen.X86.Key.body (VG.X86.Taint.Agree (τr [.esp])) := by
  intro s t tr ur u z P A C
  have raw : RelCT isa (BodyPair E sp e p q p' q') VG.Impl.RsaKeyGen.X86.Key.body (fun _ _ => True) :=
    RelCT.seq (enterInput_trace E v sp e p q p' q') (front_trace E v e p q p' q' release)
  refine ⟨(raw _ _ _ _ _ _ P A C).1, agree_regs ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  rw [Exec.gpr KeyNoSp.body_noSp A, Exec.gpr KeyNoSp.body_noSp C]
  exact P.left.arguments.sp.trans P.right.arguments.sp.symm

end VG.Proof.RsaKeyGen.X86.Key
