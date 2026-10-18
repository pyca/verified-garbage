module

public import VerifiedGarbage.Proof.Rsa.X86.KcABI

/-! # Public observations of both RSA key-validation contracts -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Impl.Rsa.X86.KeyCheck

theorem arguments_eq {full : Bool} {s t : State} (h : (contract full).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < scratchArg full + 2, arg s i = arg t i := by
  cases full
  · change (Spec.Rsa.checkCrtKeyContract abi 20).pub s t at h
    sig_pub [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argSlots, argVal, argBytes] at h
    sig_split h
    constructor
    · assumption
    · intro i hi
      change i < 16 at hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · change (Spec.Rsa.checkKeyContract abi 20).pub s t at h
    sig_pub [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argSlots, argVal, argBytes] at h
    sig_split h
    constructor
    · assumption
    · intro i hi
      change i < 18 at hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem publicBytes_eq {full : Bool} {s t : State} (h : (contract full).pub s t) :
    inputBytes (caller full s) s.mem 0 = inputBytes (caller full t) t.mem 0 ∧
    inputBytes (caller full s) s.mem 1 = inputBytes (caller full t) t.mem 1 := by
  have args := arguments_eq h
  have leak : ((inputBytes (caller full s) s.mem 0) ++ (inputBytes (caller full s) s.mem 1)).map (·.toNat) =
      ((inputBytes (caller full t) t.mem 0) ++ (inputBytes (caller full t) t.mem 1)).map (·.toNat) := by
    cases full
    · change (Spec.Rsa.checkCrtKeyContract abi 20).pub s t at h
      sig_pub [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argSlots, argVal, argBytes] at h
      exact h.2.1
    · change (Spec.Rsa.checkKeyContract abi 20).pub s t at h
      sig_pub [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argSlots, argVal, argBytes] at h
      exact h.2.1
  have both := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp leak
  have sameLength : (inputBytes (caller full s) s.mem 0).length = (inputBytes (caller full t) t.mem 0).length := by
    simp only [inputBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    change (arg s 1).toNat = (arg t 1).toNat
    rw [args.2 1 (by cases full <;> decide)]
  exact ⟨List.append_inj_left both sameLength, List.append_inj_right both sameLength⟩
end VG.Proof.Rsa.X86.KeyCheck
