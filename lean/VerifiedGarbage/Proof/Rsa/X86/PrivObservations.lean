module
public import VerifiedGarbage.Proof.Rsa.X86.PrivContractGeometry
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.RandomFinish


/-! # Extract the shared contract's public cdecl arguments and key bytes -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem arguments {s t : State} (H : (Spec.Rsa.privateCheckedContract abi stackBytes).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 20, arg s i = arg t i := by
  sig_pub [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem publicBytes {s t : State} (H : (Spec.Rsa.privateCheckedContract abi stackBytes).pub s t) :
    privateBytes s 0 = privateBytes t 0 ∧ privateBytes s 1 = privateBytes t 1 := by
  have Args := arguments H
  have Leak : ((privateBytes s 0) ++ (privateBytes s 1)).map (·.toNat) =
      ((privateBytes t 0) ++ (privateBytes t 1)).map (·.toNat) := by
    sig_pub [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes] at H
    simpa only [List.map_append, privateBytes, privateGeometry, PrivGeometry.sourceLength,
      Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd,
      VG.Proof.Bignum.X86.byteAddr] using H.2.1
  have both := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp Leak
  have sameLength : (privateBytes s 0).length = (privateBytes t 0).length := by
    simp only [privateBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    change (arg s 3).toNat = (arg t 3).toNat
    rw [Args.2 3 (by decide)]
  exact ⟨List.append_inj_left both sameLength, List.append_inj_right both sameLength⟩

theorem publicGeometry {s t : State} (H : (Spec.Rsa.privateCheckedContract abi stackBytes).pub s t) :
    privateGeometry s = privateGeometry t := by
  obtain ⟨sp, args⟩ := arguments H
  have sources : (fun i : Fin 8 => arg s (2 + 2 * i.val)) =
      (fun i : Fin 8 => arg t (2 + 2 * i.val)) := by
    funext i
    exact args _ (by omega)
  simp only [privateGeometry, sp, sources, args 0 (by decide), args 18 (by decide),
    args 3 (by decide), args 5 (by decide), args 9 (by decide), args 11 (by decide), args 19 (by decide)]
end VG.Proof.Rsa.X86.PrivChecked
