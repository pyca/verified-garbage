module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyContractGeometry
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicBytes
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Weierstrass

/-! # The shared verifier leakage fixes every immutable input byte -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Bignum.X86

theorem arguments {s t : State} (H : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 13, arg s i = arg t i := by
  sig_pub [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · with_reducible assumption
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem publicGeometry {s t : State} (H : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pub s t) :
    verifyGeometry s = verifyGeometry t := by
  obtain ⟨sp, args⟩ := arguments H
  have sources : (verifyGeometry s).sources = (verifyGeometry t).sources := by
    funext i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    exacts [args 0 (by decide), args 2 (by decide), args 5 (by decide), args 7 (by decide), args 11 (by decide)]
  simp only [verifyGeometry, sp, args 9 (by decide), args 1 (by decide), args 4 (by decide),
    args 3 (by decide), args 6 (by decide), args 8 (by decide), args 12 (by decide), args 10 (by decide)]
  exact congrArg (fun ps => Geometry.mk _ _ ps _ _ _ _ _ _ _) sources

theorem publicBytes {s t : State} (H : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pub s t) :
    verifyBytes s = verifyBytes t := by
  have args := (arguments H).2
  have geometry := publicGeometry H
  have Leak : (verifyBytes s 0 ++ verifyBytes s 1 ++ verifyBytes s 2 ++ verifyBytes s 3).map (·.toNat) ++
      (Spec.Rsa.wordsAt s.mem (byteAddr ((verifyGeometry s).sources 4)) (verifyGeometry s).preLength).map (·.toNat) =
      (verifyBytes t 0 ++ verifyBytes t 1 ++ verifyBytes t 2 ++ verifyBytes t 3).map (·.toNat) ++
      (Spec.Rsa.wordsAt t.mem (byteAddr ((verifyGeometry t).sources 4)) (verifyGeometry t).preLength).map (·.toNat) := by
    sig_pub [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argSlots, argVal, argBytes] at H
    exact H.2.1
  have wordLength : ((Spec.Rsa.wordsAt s.mem (byteAddr ((verifyGeometry s).sources 4)) (verifyGeometry s).preLength).map (·.toNat)).length =
      ((Spec.Rsa.wordsAt t.mem (byteAddr ((verifyGeometry t).sources 4)) (verifyGeometry t).preLength).map (·.toNat)).length := by
    simp only [List.length_map, Spec.Rsa.wordsAt, List.length_range, geometry]
  have both := List.append_inj' Leak wordLength
  have bytes := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp both.1
  have words := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp both.2
  have lengths (i : Fin 5) : (verifyBytes s i).length = (verifyBytes t i).length := by
    simp only [verifyBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range, geometry]
  simp only [List.append_assoc] at bytes
  have first := List.append_inj_left bytes (lengths 0)
  have rest := List.append_inj_right bytes (lengths 0)
  have second := List.append_inj_left rest (lengths 1)
  have tail := List.append_inj_right rest (lengths 1)
  have third := List.append_inj_left tail (lengths 2)
  have fourth := List.append_inj_right tail (lengths 2)
  have fifth : verifyBytes s 4 = verifyBytes t 4 := by
    rw [geometry] at words
    unfold verifyBytes
    rw [geometry]
    exact bytesAt_of_words words
  funext i
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  exacts [first, second, third, fourth, fifth]

end VG.Proof.RsaPkcs1Sig.X86.Ver
