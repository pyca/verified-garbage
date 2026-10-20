module

public import VerifiedGarbage.Proof.Bignum.X86.PublicPair
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86.ExponentCheckTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Public exponent argument loading and scanning share a common trace -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem publicExponent_trace {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t : State}
    (H : PublicPair base bytes len args s t)
    (same : Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat =
      Spec.Rsa.bytesAt t.mem (byteAddr (args 4)) (args 5).toNat)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa PublicFn.scanExponent s tr sf) (F : Exec isa PublicFn.scanExponent t ur tf) : tr = ur := by
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have T1 := (loadArguments_relCT 4 5 (args 4) (args 5) _ _ _ _ _ _
        ⟨H.agree, (H.left.stack 4 (by decide)).readSrc, (H.right.stack 4 (by decide)).readSrc,
          (H.left.stack 5 (by decide)).readSrc, (H.right.stack 5 (by decide)).readSrc⟩ E1 F1).1
      obtain ⟨Ps, Cs, Ms, Ks⟩ := wp_result (argumentPair_ok (by decide) (by decide)
        (H.left.stack 4 (by decide)).readSrc (H.left.stack 5 (by decide)).readSrc) E1
      obtain ⟨Pt, Ct, Mt, Kt⟩ := wp_result (argumentPair_ok (by decide) (by decide)
        (H.right.stack 4 (by decide)).readSrc (H.right.stack 5 (by decide)).readSrc) F1
      have T2 := exponentCheck_trace (ep := args 4)
        (eb := Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)
        (by rw [bytesAt_length]; exact H.left.ePositive)
        (by rw [bytesAt_length]; exact (args 5).isLt)
        (by rw [bytesAt_length]; exact H.left.eFit)
        (by rw [bytesAt_length, Ks.2.1, Ks.2.2]; exact H.left.eRead)
        (by rw [bytesAt_length, Kt.2.1, Kt.2.2]; exact H.right.eRead)
        (by intro i hi; rw [Ms]; simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range])
        (by
          intro i hi
          rw [Mt]
          have Eq := List.getElem_of_eq same hi
          simpa only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range] using Eq.symm)
        Ps Pt (by rw [bytesAt_length, BitVec.ofNat_toNat]; exact Cs)
        (by rw [bytesAt_length, BitVec.ofNat_toNat]; exact Ct) E2 F2
      rw [T1, T2]

end VG.Proof.Bignum.X86
