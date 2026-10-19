module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverContractInput
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicBytes

/-! # The shared verifier leakage fixes every immutable input byte -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86

theorem arguments {s t : State} (H : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 13, arg s i = arg t i := by
  sig_pub [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · with_reducible assumption
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem publicGeometry {s t : State} (H : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pub s t) :
    recoverGeometry s = recoverGeometry t := by
  obtain ⟨sp, args⟩ := arguments H
  have sources : (recoverGeometry s).sources = (recoverGeometry t).sources := by
    funext i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    exacts [args 2 (by decide), args 4 (by decide), args 7 (by decide), args 11 (by decide)]
  simp only [recoverGeometry, sp, args 0 (by decide), args 1 (by decide), args 9 (by decide),
    args 3 (by decide), args 6 (by decide), args 5 (by decide), args 8 (by decide), args 12 (by decide), args 10 (by decide)]
  exact congrArg (fun ps => Geometry.mk _ _ _ _ ps _ _ _ _ _ _) sources

theorem publicBytes {s t : State} (H : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pub s t) :
    recoverBytes s = recoverBytes t := by
  have args := (arguments H).2
  have geometry := publicGeometry H
  have Leak : (recoverBytes s 0 ++ recoverBytes s 1 ++ recoverBytes s 2).map (·.toNat) ++
      (Spec.Rsa.wordsAt s.mem (byteAddr ((recoverGeometry s).sources 3)) (recoverGeometry s).preLength).map (·.toNat) =
      (recoverBytes t 0 ++ recoverBytes t 1 ++ recoverBytes t 2).map (·.toNat) ++
      (Spec.Rsa.wordsAt t.mem (byteAddr ((recoverGeometry t).sources 3)) (recoverGeometry t).preLength).map (·.toNat) := by
    sig_pub [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argSlots, argVal, argBytes] at H
    exact H.2.1
  have wordLength : ((Spec.Rsa.wordsAt s.mem (byteAddr ((recoverGeometry s).sources 3)) (recoverGeometry s).preLength).map (·.toNat)).length =
      ((Spec.Rsa.wordsAt t.mem (byteAddr ((recoverGeometry t).sources 3)) (recoverGeometry t).preLength).map (·.toNat)).length := by
    simp only [List.length_map, Spec.Rsa.wordsAt, List.length_range, geometry]
  have both := List.append_inj' Leak wordLength
  have bytes := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp both.1
  have words := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp both.2
  have lengths (i : Fin 4) : (recoverBytes s i).length = (recoverBytes t i).length := by
    simp only [recoverBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range, geometry]
  simp only [List.append_assoc] at bytes
  have first := List.append_inj_left bytes (lengths 0)
  have rest := List.append_inj_right bytes (lengths 0)
  have second := List.append_inj_left rest (lengths 1)
  have tail := List.append_inj_right rest (lengths 1)
  have third := tail
  have fourth : recoverBytes s 3 = recoverBytes t 3 := by
    rw [geometry] at words
    unfold recoverBytes
    rw [geometry]
    exact VG.Proof.RsaPkcs1Sig.X86.Ver.bytesAt_of_words words
  funext i
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
  exacts [first, second, third, fourth]

end VG.Proof.RsaPkcs1Sig.X86.Rcv
