module
public import VerifiedGarbage.Proof.Bignum.X86.CrtABI
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Impl.Bignum.X86.CrtFn

import VerifiedGarbage.Proof.Bignum.X86.CrtBodyTiming
import VerifiedGarbage.Proof.Bignum.X86.CrtEntryTiming
import VerifiedGarbage.Proof.Bignum.X86.CrtArgumentsEq
import VerifiedGarbage.Proof.Bignum.X86.CrtBody
import VerifiedGarbage.Proof.Bignum.X86.CrtInstalled
import VerifiedGarbage.Proof.Bignum.X86.CrtResources
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # The cdecl checked-public operation leaks only its public key and geometry -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (argumentPointer wp_result)

theorem operation_trace {s t : State} (A : CrtABI s) (B : CrtABI t)
    (args : ∀ i < 18, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (N : Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa Crt.code s tr sf) (F : Exec isa Crt.code t ur tf) : tr = ur := by
  have A2 := args 2 (by decide)
  have A3 := args 3 (by decide)
  have A8 := args 16 (by decide)
  have A9 := args 17 (by decide)
  cases E with
  | @seq _ _ _ u _ _ _ E1 Erest =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 Frest =>
      have T1 := (entry_relCT _ _ _ _ _ _
        ⟨SP, A8, (A.stackArgument (by decide : 16 < 18)).readSrc,
          (B.stackArgument (by decide : 16 < 18)).readSrc⟩ E1 F1).1
      obtain ⟨Is, _, Ks, Os⟩ := wp_result (installed_ok A) E1
      obtain ⟨It, _, Kt, Ot⟩ := wp_result (installed_ok B) F1
      have Iv : Inputs (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) v := by
        have J := It.argsEq (fun i hi => (args i hi).symm)
        simpa only [argumentPointer, ← A8, ← A9, ← A3] using J
      have Ov : VG.Proof.Mont.Outside (argumentPointer s 16) 0 ((arg s 17).toNat * 8) t.mem v.mem := by
        simpa only [argumentPointer, ← A8, ← A9] using Ot
      have Pair : Pair (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) u v :=
        ⟨Is, Iv, (Ks.1 _ (by decide)).trans (SP.trans (Kt.1 _ (by decide)).symm)⟩
      have Ns := scratch_bytes Os (by have := A.lengths.2; omega) (Is.apart 2 (by decide))
      have Nt := scratch_bytes Ov (by have := A.lengths.2; omega) (Iv.apart 2 (by decide))
      have NN : Spec.Rsa.bytesAt u.mem (byteAddr (arg s 2)) (arg s 3).toNat =
          Spec.Rsa.bytesAt v.mem (byteAddr (arg s 2)) (arg s 3).toNat := by
        rw [Ns, Nt]
        simpa only [argumentPointer, byteAddr, ← A2, ← A3] using N
      cases Erest with
      | @seq _ _ _ w _ _ _ E2 E3 =>
        cases Frest with
        | @seq _ _ _ z _ _ _ F2 F3 =>
          have T2 := (body_relCT _ _ _ _ _ _ _ _ _ _ ⟨Pair, NN⟩ E2 F2).1
          obtain ⟨_, Ksu⟩ := wp_result (body_ok Is) E2
          obtain ⟨_, Ktv⟩ := wp_result (body_ok Iv) F2
          have Agree : VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false) w z :=
            agree_regs (by
              intro r hr
              obtain rfl := List.mem_singleton.mp hr
              rw [Ksu.1 _ (by decide), Ktv.1 _ (by decide)]
              exact Pair.agree.rf.1 _ (by decide))
          have T3 := (restore_relCT _ _ _ _ _ _ Agree E3 F3).1
          rw [T1, T2, T3]

end VG.Proof.Bignum.X86.Crt
