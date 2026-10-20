module
public import VerifiedGarbage.Proof.Rsa.X86.KcPair
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Bignum.X86.ExponentCheckTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Exponent-validation traces depend only on the declared public exponent bytes -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86

theorem exponent_trace {g : CallGeometry} {s t : State}
    (H : Pair g s t)
    (same : Spec.Rsa.bytesAt s.mem (byteAddr (g.args 2)) (g.args 3).toNat =
      Spec.Rsa.bytesAt t.mem (byteAddr (g.args 2)) (g.args 3).toNat)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 2)) exponentCheck) s tr sf) (F : Exec isa (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 2)) exponentCheck) t ur tf) : tr = ur := by
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have T1 := (loadArguments_relCT 2 3 (g.args 2) (g.args 3) _ _ _ _ _ _
        ⟨H.agree, (H.left.arguments 2 (by cases g.full <;> decide)).readSrc, (H.right.arguments 2 (by cases g.full <;> decide)).readSrc,
          (H.left.arguments 3 (by cases g.full <;> decide)).readSrc, (H.right.arguments 3 (by cases g.full <;> decide)).readSrc⟩ E1 F1).1
      obtain ⟨Ps, Cs, Ms, Ks⟩ := wp_result (argumentPair_ok (by decide) (by decide)
        (H.left.arguments 2 (by cases g.full <;> decide)).readSrc (H.left.arguments 3 (by cases g.full <;> decide)).readSrc) E1
      obtain ⟨Pt, Ct, Mt, Kt⟩ := wp_result (argumentPair_ok (by decide) (by decide)
        (H.right.arguments 2 (by cases g.full <;> decide)).readSrc (H.right.arguments 3 (by cases g.full <;> decide)).readSrc) F1
      have T2 := exponentCheck_trace (ep := g.args 2)
        (eb := Spec.Rsa.bytesAt s.mem (byteAddr (g.args 2)) (g.args 3).toNat)
        (by rw [bytesAt_length]; exact H.left.inputPositive 1 (by cases g.full <;> decide))
        (by rw [bytesAt_length]; exact (g.args 3).isLt)
        (by rw [bytesAt_length]; exact H.left.inputFit 1 (by cases g.full <;> decide))
        (by rw [bytesAt_length, Ks.2.1, Ks.2.2]; exact H.left.inputRead 1 (by cases g.full <;> decide))
        (by rw [bytesAt_length, Kt.2.1, Kt.2.2]; exact H.right.inputRead 1 (by cases g.full <;> decide))
        (by intro i hi; rw [Ms]; simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range])
        (by
          intro i hi
          rw [Mt]
          have Eq := List.getElem_of_eq same hi
          simpa only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range] using Eq.symm)
        Ps Pt (by rw [bytesAt_length, BitVec.ofNat_toNat]; exact Cs)
        (by rw [bytesAt_length, BitVec.ofNat_toNat]; exact Ct) E2 F2
      rw [T1, T2]

end VG.Proof.Rsa.X86.KeyCheck
