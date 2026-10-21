module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestCoreTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrivateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateStack
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.Syms

/-! # All prepared witnesses share one public private frame and one released iteration count -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.Mont.X86

structure TestPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop
    extends DrawnPair E eBytes pBytes qBytes rBytes sBytes s t where
  savedLeft : val32 s.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E rBytes - 1
  savedRight : val32 t.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E sBytes - 1

theorem capacity_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (space : 44 ≤ size) :
    WP isa (.block [.mov .edx (.mem (sc 40))]) s fun t => Upd s t .edx (s.mem.readW (off base 40) 32) :=
  wp_movS (readSrc_sc S space) fun _ U _ => WP.block_nil U

theorem private_pair {P : MillerRabinLoop.Parameters} {other : Nat} {entropy : List Byte} {s t : State}
    (I : CandidatePrepare.Input P s) (J : CandidatePrepare.Input (P.withSecret other entropy) t)
    (iterations : P.iterations = (P.withSecret other entropy).iterations) : CandidateTest.CorePair P other entropy s t := by
  refine ⟨?_, I, J, iterations⟩
  apply agree_regs
  intro r mem
  change r ∈ [.esp, .edi] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact I.prepare.caller.sp.trans J.prepare.caller.sp.symm
  · exact BitVec.eq_of_toNat_eq (I.prepare.scratch.edi_toNat.trans J.prepare.scratch.edi_toNat.symm)

theorem test_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (iterations : (E.parameters rBytes).iterations = (E.parameters sBytes).iterations)
    (enough : E.length ≤ E.randLength) :
    RelCT isa (TestPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateTest.code E.width montName mont roundName round) (fun _ _ => True) := by
  intro s t tr ur u z H A B
  have space : 256 ≤ E.size := v.geometry.headerFit
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block [.mov .edx (.mem (sc 40))])
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  cases A with
  | seq argsA frameA =>
    cases B with
    | seq argsB frameB =>
      have argsTrace := (raw _ _ _ _ _ _ H.toDrawnPair.inputs.agree argsA argsB).1
      have Ua := wp_result (capacity_ok H.left.input.scratch (by omega)) argsA
      have Ub := wp_result (capacity_ok H.right.input.scratch (by omega)) argsB
      have Da := H.left.keepMem v Ua.mem Ua.keeps (by decide) (by decide) Ua.syms
      have Db := H.right.keepMem v Ub.mem Ub.keeps (by decide) (by decide) Ub.syms
      have capA : _ := Ua.gpr.trans (H.left.input.header 10 (by decide))
      have capB : _ := Ub.gpr.trans (H.right.input.header 10 (by decide))
      cases frameA with
      | frame pushA bodyA popA =>
        cases frameB with
        | frame pushB bodyB popB =>
          have ea := alloc_some pushA
          have eb := alloc_some pushB
          subst ea eb
          cases bodyA with
          | seq storeA coreA =>
            cases bodyB with
            | seq storeB coreB =>
              have slotA := wp_result (CandidateFrame.slot_ok (g := E.geometry) (capacity := E.capacity) Da.input.scratch (by rw [Da.input.stack]; exact v.low)
                (by rw [Da.input.stack]; exact v.workspaceStack) capA) storeA
              have slotB := wp_result (CandidateFrame.slot_ok (g := E.geometry) (capacity := E.capacity) Db.input.scratch (by rw [Db.input.stack]; exact v.low)
                (by rw [Db.input.stack]; exact v.workspaceStack) capB) storeB
              obtain ⟨Sa, Ca, _, Fa, Ka⟩ := slotA
              obtain ⟨Sb, Cb, _, Fb, Kb⟩ := slotB
              rw [CandidateFrame.privateSp, Da.input.stack] at Ca
              rw [CandidateFrame.privateSp, Db.input.stack] at Cb
              rw [Da.input.stack] at Fa
              rw [Db.input.stack] at Fb
              have Ia := private_input v Da (by rw [Ua.mem]; exact H.savedLeft) Sa Ca Fa (Ka.mono (by decide))
              have Ib := private_input v Db (by rw [Ub.mem]; exact H.savedRight) Sb Cb Fb (Kb.mono (by decide))
              have initial := private_pair Ia Ib iterations
              have coreTrace := (CandidateTest.core_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack
                (v.parameters_valid rBytes H.left.input.memory.entropyLength) v.width_bounds.2
                (v.parameters_valid sBytes H.right.input.memory.entropyLength) (by change 8 * E.width ≤ E.randLength; rw [v.length_eq]; exact enough)
                _ _ _ _ _ _ initial coreA coreB).1
              have storeRaw : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.store (at_ .esp 24) .edx])
                  (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
              have storeTrace := (storeRaw _ _ _ _ _ _ (by
                apply agree_regs
                intro r mem
                obtain rfl := List.mem_singleton.mp mem
                rw [allocFrame_esp, allocFrame_esp, Da.input.stack, Db.input.stack]) storeA storeB).1
              refine ⟨?_, trivial⟩
              change _ ++ ([] ++ (_ ++ _) ++ []) = _ ++ ([] ++ (_ ++ _) ++ [])
              rw [argsTrace, storeTrace, coreTrace]

end VG.Proof.RsaKeyGen.X86.Candidate
