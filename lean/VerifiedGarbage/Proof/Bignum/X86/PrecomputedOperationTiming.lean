module
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedFn
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedABI
public import VerifiedGarbage.Spec.Weierstrass.Point

import VerifiedGarbage.Proof.Bignum.X86.PrecomputedBodyTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicEntryTiming
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedArgumentsEq
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedOperation
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInstalled
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedResources
import VerifiedGarbage.Proof.Bignum.WordsFrame
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # The cdecl checked-public operation leaks only its public key and geometry -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (argumentPointer wp_result)

theorem precomputedOperation_trace {s t : State} (A : PrecomputedABI s) (B : PrecomputedABI t)
    (args : ∀ i < 10, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (N : Spec.Rsa.wordsAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.wordsAt t.mem (argumentPointer t 2) (arg t 3).toNat)
    (Ex : Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 4) (arg t 5).toNat)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa PrecomputedFn.code s tr sf) (F : Exec isa PrecomputedFn.code t ur tf) : tr = ur := by
  have A1 := args 1 (by decide)
  have A2 := args 2 (by decide)
  have A3 := args 3 (by decide)
  have A4 := args 4 (by decide)
  have A5 := args 5 (by decide)
  have A8 := args 8 (by decide)
  have A9 := args 9 (by decide)
  cases E with
  | @seq _ _ _ u _ _ _ E1 Erest =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 Frest =>
      have T1 := (publicEntry_relCT _ _ _ _ _ _
        ⟨SP, A8, (A.stackArgument (by decide : 8 < 10)).readSrc,
          (B.stackArgument (by decide : 8 < 10)).readSrc⟩ E1 F1).1
      obtain ⟨Is, _, Ks, Os⟩ := wp_result (precomputedInstalled_ok A) E1
      obtain ⟨It, _, Kt, Ot⟩ := wp_result (precomputedInstalled_ok B) F1
      have Iv : PrecomputedInputs (argumentPointer s 8) ((arg s 9).toNat * 8) (arg s 1).toNat (arg s) v := by
        have J := It.argsEq (fun i hi => (args i hi).symm)
        simpa only [argumentPointer, ← A8, ← A9, ← A1] using J
      have Ov : VG.Proof.Mont.Outside (argumentPointer s 8) 0 ((arg s 9).toNat * 8) t.mem v.mem := by
        simpa only [argumentPointer, ← A8, ← A9] using Ot
      have Pair : PrecomputedPair (argumentPointer s 8) ((arg s 9).toNat * 8) (arg s 1).toNat (arg s) u v :=
        ⟨Is, Iv, (Ks.1 _ (by decide)).trans (SP.trans (Kt.1 _ (by decide)).symm)⟩
      have Ns := scratch_words Os (by have := A.scratchBound; omega) (n := 2 * Spec.Rsa.modulusWords (arg s 1).toNat) (by have := Is.dimensions; omega)
        (by simpa only [show 8 * (2 * Spec.Rsa.modulusWords (arg s 1).toNat) = 16 * Spec.Rsa.modulusWords (arg s 1).toNat by omega] using Is.preApart)
      have Nt := scratch_words Ov (by have := A.scratchBound; omega) (n := 2 * Spec.Rsa.modulusWords (arg s 1).toNat) (by have := Iv.dimensions; omega)
        (by simpa only [show 8 * (2 * Spec.Rsa.modulusWords (arg s 1).toNat) = 16 * Spec.Rsa.modulusWords (arg s 1).toNat by omega] using Iv.preApart)
      have Es := scratch_bytes Os (by have := (arg s 5).isLt; omega) Is.eApart
      have Et := scratch_bytes Ov (by have := (arg s 5).isLt; omega) Iv.eApart
      have NN : Spec.Rsa.wordsAt u.mem (byteAddr (arg s 2)) (2 * Spec.Rsa.modulusWords (arg s 1).toNat) =
          Spec.Rsa.wordsAt v.mem (byteAddr (arg s 2)) (2 * Spec.Rsa.modulusWords (arg s 1).toNat) := by
        rw [Ns, Nt]
        simpa only [argumentPointer, byteAddr, ← A2, ← A3, A.preLength, Spec.Rsa.precomputedWords] using N
      have EE : Spec.Rsa.bytesAt u.mem (byteAddr (arg s 4)) (arg s 5).toNat =
          Spec.Rsa.bytesAt v.mem (byteAddr (arg s 4)) (arg s 5).toNat := by
        rw [Es, Et]
        simpa only [argumentPointer, byteAddr, ← A4, ← A5] using Ex
      cases Erest with
      | @seq _ _ _ w _ _ _ E2 E3 =>
        cases Frest with
        | @seq _ _ _ z _ _ _ F2 F3 =>
          have T2 := precomputedBody_trace ⟨Pair, NN⟩ EE E2 F2
          obtain ⟨_, Ksu⟩ := wp_result (PublicContext.precomputedBody_ok Is) E2
          obtain ⟨_, Ktv⟩ := wp_result (PublicContext.precomputedBody_ok Iv) F2
          have Agree : VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false) w z :=
            agree_regs (by
              intro r hr
              obtain rfl := List.mem_singleton.mp hr
              rw [Ksu.1 _ (by decide), Ktv.1 _ (by decide)]
              exact Pair.agree.rf.1 _ (by decide))
          have T3 := (publicRestore_relCT _ _ _ _ _ _ Agree E3 F3).1
          rw [T1, T2, T3]

end VG.Proof.Bignum.X86
