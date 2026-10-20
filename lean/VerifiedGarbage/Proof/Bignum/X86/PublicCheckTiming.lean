module

public import VerifiedGarbage.Proof.Bignum.X86.PublicExponentTiming
public import VerifiedGarbage.Proof.Bignum.X86.PublicValidTiming
public import VerifiedGarbage.Proof.Bignum.X86.PublicFailureTiming

import VerifiedGarbage.Proof.Bignum.X86.PublicExponentArgs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Exponent acceptance chooses between two traces using only public bytes -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem publicCheckExponent_trace {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t : State}
    (H : ValidPair base bytes len args s t)
    (same : Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat =
      Spec.Rsa.bytesAt t.mem (byteAddr (args 4)) (args 5).toNat)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa PublicFn.checkExponent s tr sf) (F : Exec isa PublicFn.checkExponent t ur tf) : tr = ur := by
  have Branch : RelCT isa (fun s t => (ValidPair base bytes len args s t ∧
        s.gpr .ebx = t.gpr .ebx ∧ s.gpr .edx = t.gpr .edx) ∧ s.zf = t.zf)
      (.ite .e PublicFn.failure PublicFn.valid) (fun _ _ => True) := by
    apply VG.RelCT.ite (M := isa) (c := .e) (fun _ _ h => h.2)
    · exact (publicFailure_relCT base bytes len args).mono (fun _ _ h => h.1.1.1.1) (fun _ _ h => h)
    · exact (publicValid_relCT base bytes len args).mono (fun _ _ h => h.1.1) (fun _ _ h => h)
  have Compare : RelCT isa (fun _ _ => True) (.block [.alu .cmp .eax (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (hc := .block [])
    rfl
  cases E with
  | seq E1 Erest =>
    cases F with
    | seq F1 Frest =>
      have T1 := publicExponent_trace H.1 same E1 F1
      obtain ⟨Vs, Bs, Ds, Ms, Ks⟩ := wp_result (publicExponent_ok H.1.left) E1
      obtain ⟨Vt, Bt, Dt, Mt, Kt⟩ := wp_result (publicExponent_ok H.1.right) F1
      rw [same] at Vs Bs Ds
      have Next := H.keepMem Ks Kt (by decide) (by decide) Ms Mt
      cases Erest with
      | seq E2 E3 =>
        cases Frest with
        | seq F2 F3 =>
          have T2 := (Compare _ _ _ _ _ _ trivial E2 F2).1
          obtain ⟨Zs, Mvs, Kvs⟩ := wp_result (exponentFlag_ok _ Vs) E2
          obtain ⟨Zt, Mvt, Kvt⟩ := wp_result (exponentFlag_ok _ Vt) F2
          have Last := Next.keepMem Kvs Kvt (by simp) (by simp) Mvs Mvt
          have Rb : _ = _ := ((Kvs.1 .ebx (by simp)).trans (Bs.trans
            (Bt.symm.trans (Kvt.1 .ebx (by simp)).symm)))
          have Rd : _ = _ := ((Kvs.1 .edx (by simp)).trans (Ds.trans
            (Dt.symm.trans (Kvt.1 .edx (by simp)).symm)))
          have T3 := (Branch _ _ _ _ _ _ ⟨⟨Last, Rb, Rd⟩, Zs.trans Zt.symm⟩ E3 F3).1
          rw [T1, T2, T3]

end VG.Proof.Bignum.X86
