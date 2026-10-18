module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptContractInput
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicBytes

/-! # The shared leakage fixes geometry, the exponent, and cached key words -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Proof.Bignum.X86

theorem arguments {s t : State} (H : (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi encryptStack).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 14, arg s i = arg t i := by
  sig_pub [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · with_reducible assumption
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
        i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem publicGeometry {s t : State} (H : (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi encryptStack).pub s t) :
    encryptGeometry s = encryptGeometry t := by
  obtain ⟨sp, args⟩ := arguments H
  have sources : (encryptGeometry s).sources = (encryptGeometry t).sources := by
    funext i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    exacts [args 2 (by decide), args 4 (by decide), args 6 (by decide), args 8 (by decide), args 12 (by decide)]
  simp only [encryptGeometry, sp, args 0 (by decide), args 10 (by decide), args 3 (by decide),
    args 5 (by decide), args 7 (by decide), args 9 (by decide), args 13 (by decide), args 11 (by decide)]
  exact congrArg (fun ps => Geometry.mk _ _ _ ps _ _ _ _ _ _) sources

theorem publicBytes {s t : State} (H : (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi encryptStack).pub s t) :
    encryptBytes s 1 = encryptBytes t 1 ∧ encryptBytes s 4 = encryptBytes t 4 := by
  have geometry := publicGeometry H
  have Leak : (encryptBytes s 0 ++ encryptBytes s 1).map (·.toNat) ++
      (Spec.Rsa.wordsAt s.mem (byteAddr ((encryptGeometry s).sources 4)) (encryptGeometry s).preLength).map (·.toNat) =
      (encryptBytes t 0 ++ encryptBytes t 1).map (·.toNat) ++
      (Spec.Rsa.wordsAt t.mem (byteAddr ((encryptGeometry t).sources 4)) (encryptGeometry t).preLength).map (·.toNat) := by
    sig_pub [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argSlots, argVal, argBytes] at H
    exact H.2.1
  have wordLength : ((Spec.Rsa.wordsAt s.mem (byteAddr ((encryptGeometry s).sources 4)) (encryptGeometry s).preLength).map (·.toNat)).length =
      ((Spec.Rsa.wordsAt t.mem (byteAddr ((encryptGeometry t).sources 4)) (encryptGeometry t).preLength).map (·.toNat)).length := by
    simp only [List.length_map, Spec.Rsa.wordsAt, List.length_range, geometry]
  have both := List.append_inj' Leak wordLength
  have bytes := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp both.1
  have words := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp both.2
  have nLength : (encryptBytes s 0).length = (encryptBytes t 0).length := by
    simp only [encryptBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range, geometry]
  refine ⟨List.append_inj_right bytes nLength, ?_⟩
  rw [geometry] at words
  unfold encryptBytes
  rw [geometry]
  exact VG.Proof.RsaPkcs1Sig.X86.Ver.bytesAt_of_words words

end VG.Proof.RsaPkcs1Enc.X86.Enc
