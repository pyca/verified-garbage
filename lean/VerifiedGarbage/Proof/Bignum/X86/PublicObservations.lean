module
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Rsa.Contract


/-! # Extract the shared contract's public cdecl arguments and key bytes -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem publicArguments {s t : State} (H : (Proof.Rsa.publicCheckedContract abi 20).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 10, arg s i = arg t i := by
  sig_pub [Proof.Rsa.publicCheckedContract, Proof.Rsa.publicSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem publicKeyLeak {s t : State} (H : (Proof.Rsa.publicCheckedContract abi 20).pub s t) :
    (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat ++
      Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat).map (·.toNat) =
    (Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat ++
      Spec.Rsa.bytesAt t.mem (argumentPointer t 4) (arg t 5).toNat).map (·.toNat) := by
  sig_pub [Proof.Rsa.publicCheckedContract, Proof.Rsa.publicSig, abi, argSlots, argVal, argBytes] at H
  exact H.2.1

theorem publicKeyBytes {s t : State} (H : (Proof.Rsa.publicCheckedContract abi 20).pub s t) :
    Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat ∧
    Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 4) (arg t 5).toNat := by
  have Leak := publicKeyLeak H
  have Bytes := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp Leak
  apply (List.append_inj' Bytes ?_)
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  exact congrArg (fun x : BitVec 32 => x.toNat) ((publicArguments H).2 5 (by decide))

end VG.Proof.Bignum.X86
