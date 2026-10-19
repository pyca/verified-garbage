module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignContractInput

/-! # Extract the shared contract's public cdecl arguments and key bytes -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem arguments {s t : State} (H : (Spec.RsaPkcs1Sig.signContract abi sigStack).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 21, arg s i = arg t i := by
  sig_pub [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem publicBytes {s t : State} (H : (Spec.RsaPkcs1Sig.signContract abi sigStack).pub s t) :
    signBytes s 0 = signBytes t 0 ∧ signBytes s 1 = signBytes t 1 := by
  have Args := arguments H
  have Leak : ((signBytes s 0) ++ (signBytes s 1)).map (·.toNat) =
      ((signBytes t 0) ++ (signBytes t 1)).map (·.toNat) := by
    sig_pub [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argSlots, argVal, argBytes] at H
    simpa only [List.map_append, signBytes, signGeometry, Geometry.sourceLength,
      Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd, Nat.reduceLT, ite_true,
      VG.Proof.Bignum.X86.byteAddr] using H.2.1
  have both := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp Leak
  have sameLength : (signBytes s 0).length = (signBytes t 0).length := by
    simp only [signBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    change (arg s 3).toNat = (arg t 3).toNat
    rw [Args.2 3 (by decide)]
  exact ⟨List.append_inj_left both sameLength, List.append_inj_right both sameLength⟩

theorem publicGeometry {s t : State} (H : (Spec.RsaPkcs1Sig.signContract abi sigStack).pub s t) :
    signGeometry s = signGeometry t := by
  obtain ⟨sp, args⟩ := arguments H
  have sources : (fun i : Fin 8 => arg s (if i.val < 2 then 2 + 2 * i.val else if i.val = 2 then 7 else 3 + 2 * i.val)) =
      (fun i : Fin 8 => arg t (if i.val < 2 then 2 + 2 * i.val else if i.val = 2 then 7 else 3 + 2 * i.val)) := by
    funext i
    apply args
    split
    · omega
    · split <;> omega
  simp only [signGeometry, sp, sources, args 0 (by decide), args 19 (by decide),
    args 3 (by decide), args 5 (by decide), args 10 (by decide), args 12 (by decide), args 20 (by decide), args 6 (by decide), args 8 (by decide)]
end VG.Proof.RsaPkcs1Sig.X86.Sgn
