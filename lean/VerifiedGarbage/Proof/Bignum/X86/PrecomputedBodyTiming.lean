module

import VerifiedGarbage.Proof.Bignum.X86.PrecomputedExponentTiming
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedValidTiming
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedFailureTiming
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedExponentArgs
import VerifiedGarbage.Proof.Bignum.X86.PublicExponentArgs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Exponent acceptance chooses between two traces using only public bytes -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem precomputedBody_trace {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t : State}
    (H : PrecomputedValidPair base bytes len args s t)
    (same : Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat =
      Spec.Rsa.bytesAt t.mem (byteAddr (args 4)) (args 5).toNat)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa PrecomputedFn.body s tr sf) (F : Exec isa PrecomputedFn.body t ur tf) : tr = ur := by
  have Branch : RelCT isa (fun s t => PrecomputedValidPair base bytes len args s t ∧ s.zf = t.zf)
      (.ite .e PublicFn.failure PrecomputedFn.valid) (fun _ _ => True) := by
    apply VG.RelCT.ite (M := isa) (c := .e) (fun _ _ h => h.2)
    · exact (precomputedFailure_relCT base bytes len args).mono (fun _ _ h => h.1.1.1) (fun _ _ h => h)
    · exact (precomputedValid_relCT base bytes len args).mono (fun _ _ h => h.1.1) (fun _ _ h => h)
  have Compare : RelCT isa (fun _ _ => True) (.block [.alu .cmp .eax (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (hc := .block [])
    rfl
  cases E with
  | seq E1 Erest =>
    cases F with
    | seq F1 Frest =>
      have T1 := precomputedExponent_trace H.1 same E1 F1
      obtain ⟨Vs, _, _, Ms, Ks⟩ := wp_result (precomputedExponentScan_ok H.1.left) E1
      obtain ⟨Vt, _, _, Mt, Kt⟩ := wp_result (precomputedExponentScan_ok H.1.right) F1
      rw [same] at Vs
      have Next := H.keepMem Ks Kt (by decide) (by decide) Ms Mt
      cases Erest with
      | seq E2 E3 =>
        cases Frest with
        | seq F2 F3 =>
          have T2 := (Compare _ _ _ _ _ _ trivial E2 F2).1
          obtain ⟨Zs, Mvs, Kvs⟩ := wp_result (exponentFlag_ok _ Vs) E2
          obtain ⟨Zt, Mvt, Kvt⟩ := wp_result (exponentFlag_ok _ Vt) F2
          have Last := Next.keepMem Kvs Kvt (by simp) (by simp) Mvs Mvt
          have T3 := (Branch _ _ _ _ _ _ ⟨Last, Zs.trans Zt.symm⟩ E3 F3).1
          rw [T1, T2, T3]

end VG.Proof.Bignum.X86
