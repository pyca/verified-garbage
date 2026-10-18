module

public import VerifiedGarbage.Proof.Rsa.X86.CvABI

/-! # The shared CRT contract exposes call geometry and modulus bytes -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem arguments_eq {s t : State} (h : (Spec.Rsa.crtValuesContract abi 20).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 16, arg s i = arg t i := by
  sig_pub [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argSlots, argVal, argBytes] at h
  sig_split h
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
        i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem modulus_eq {s t : State} (h : (Spec.Rsa.crtValuesContract abi 20).pub s t) :
    inputBytes (caller s) s.mem 0 = inputBytes (caller t) t.mem 0 := by
  have leak : (Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 7).toNat).map (·.toNat) =
      (Spec.Rsa.bytesAt t.mem (argumentPointer t 6) (arg t 7).toNat).map (·.toNat) := by
    sig_pub [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argSlots, argVal, argBytes] at h
    exact h.2.1
  exact (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp leak

end VG.Proof.Rsa.X86.CrtValues
