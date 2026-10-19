module
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI


/-! # Extract the shared contract's public cdecl arguments and key bytes -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem precomputedArguments {s t : State} (H : (Spec.Rsa.publicPrecomputedCheckedContract abi 20).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 10, arg s i = arg t i := by
  sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem precomputedKeyLeak {s t : State} (H : (Spec.Rsa.publicPrecomputedCheckedContract abi 20).pub s t) :
    (Spec.Rsa.wordsAt s.mem (argumentPointer s 2) (arg s 3).toNat).map (·.toNat) ++
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat).map (·.toNat) =
    (Spec.Rsa.wordsAt t.mem (argumentPointer t 2) (arg t 3).toNat).map (·.toNat) ++
      (Spec.Rsa.bytesAt t.mem (argumentPointer t 4) (arg t 5).toNat).map (·.toNat) := by
  sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal, argBytes] at H
  exact H.2.1

theorem precomputedKeyBytes {s t : State} (H : (Spec.Rsa.publicPrecomputedCheckedContract abi 20).pub s t) :
    Spec.Rsa.wordsAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.wordsAt t.mem (argumentPointer t 2) (arg t 3).toNat ∧
    Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 4) (arg t 5).toNat := by
  have Leak := precomputedKeyLeak H
  have Length : ((Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat).map (·.toNat)).length =
      ((Spec.Rsa.bytesAt t.mem (argumentPointer t 4) (arg t 5).toNat).map (·.toNat)).length := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
    exact congrArg (fun x : BitVec 32 => x.toNat) ((precomputedArguments H).2 5 (by decide))
  have Both := List.append_inj' Leak Length
  exact ⟨(List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp Both.1,
    (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp Both.2⟩

end VG.Proof.Bignum.X86
