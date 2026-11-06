module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyBody
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportedPair
public import VerifiedGarbage.Proof.Framework.X86.RelCT

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExportState
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePortTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDSelectTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputReady
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateWidthTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEntry
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
import VerifiedGarbage.Proof.Framework.X86.Wp
/-! # The complete native key body obeys the shared public exponent and retry leak -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyEntryTiming.lean`, which only this module imported.
section

/-! # Copying the eighteen native key arguments has a public address trace -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyArgs
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.CandidateArgs

def EntryPair (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s t : State) : Prop :=
  Entry base size p inputs s ∧ Entry base size p inputs t

theorem pointer_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (S : Entry base size p inputs s) :
    WP isa (.block [.mov .edi (.mem (arg 16))]) s fun t => t.gpr .edi = inputs 16 ∧ Keeps [.edi] s t := by
  refine wp_movS (S.read 16 (by decide)) fun t T _ => WP.block_nil ⟨T.gpr, T.keeps⟩

theorem pointer_trace {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} :
    RelCT isa (EntryPair base size p inputs) (.block [.mov .edi (.mem (arg 16))])
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  intro s t tr ur u v ⟨S, T⟩ A C
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .edi (.mem (arg 16))])
      (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
  have start : VG.X86.Taint.Agree (τr [.esp]) s t := agree_regs (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact S.sp.trans T.sp.symm)
  obtain ⟨leftValue, leftKeeps⟩ := wp_result (pointer_ok S) A
  obtain ⟨rightValue, rightKeeps⟩ := wp_result (pointer_ok T) C
  refine ⟨(raw _ _ _ _ _ _ start A C).1, agree_regs ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
    exact S.sp.trans T.sp.symm
  · exact leftValue.trans rightValue.symm

theorem enter_trace {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} :
    RelCT isa (EntryPair base size p inputs) VG.Impl.RsaKeyGen.X86.Key.enter (fun _ _ => True) := by
  have copied : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (copies 18) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ H => H)
      (hc := VG.Taint.hintOf taint (τr [.esp, .edi]) (copies 18))
    kernel_rfl
  exact RelCT.seq pointer_trace copied

end VG.Proof.RsaKeyGen.X86.KeyArgs
end

end

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

end VG.Proof.RsaKeyGen.X86.Key
