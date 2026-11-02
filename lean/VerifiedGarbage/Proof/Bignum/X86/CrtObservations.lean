module
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Rsa.Contract


/-! # Extract the shared contract's public cdecl arguments and key bytes -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem arguments {s t : State} (H : (Proof.Rsa.privateCrtContract abi 96).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 18, arg s i = arg t i := by
  sig_pub [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem modulusBytes {s t : State} (H : (Proof.Rsa.privateCrtContract abi 96).pub s t) :
    Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat := by
  have Leak : (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat).map (·.toNat) =
      (Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat).map (·.toNat) := by
    sig_pub [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes] at H
    exact H.2.1
  exact (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp Leak

end VG.Proof.Bignum.X86.Crt
