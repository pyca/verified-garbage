module
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.Framework.GetElem


/-! # The shared contract exposes only call geometry and the public modulus -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem precomputeArguments {s t : State} (H : (Spec.Rsa.publicPrecomputeContract abi 96).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 6, arg s i = arg t i := by
  sig_pub [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem precomputeModulusLeak {s t : State} (H : (Spec.Rsa.publicPrecomputeContract abi 96).pub s t) :
    (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat).map (·.toNat) =
      (Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat).map (·.toNat) := by
  sig_pub [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes] at H
  exact H.2.1

theorem precomputeModulusBytes {s t : State} (H : (Spec.Rsa.publicPrecomputeContract abi 96).pub s t) :
    Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat :=
  (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp (precomputeModulusLeak H)

end VG.Proof.Bignum.X86
