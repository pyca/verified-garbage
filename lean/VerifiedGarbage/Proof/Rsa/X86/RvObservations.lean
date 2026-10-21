module

public import VerifiedGarbage.Proof.Rsa.X86.RvABI
public import VerifiedGarbage.Proof.Rsa.X86.RvResult
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The shared recovery contract exposes call geometry and modulus bytes -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem arguments_eq {s t : State} (h : (Spec.Rsa.recoverPrimesContract abi 40).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 12, arg s i = arg t i := by
  sig_pub [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argSlots, argVal, argBytes] at h
  sig_split h
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
        i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem observations_eq {s t : State} (h : (Spec.Rsa.recoverPrimesContract abi 40).pub s t) :
    inputBytes (caller s) s.mem 0 = inputBytes (caller t) t.mem 0 ∧
      (calculated (caller s) s.mem).2 = (calculated (caller t) t.mem).2 := by
  have args := (arguments_eq h).2
  have leak :
      (inputBytes (caller s) s.mem 0 ++ inputBytes (caller s) s.mem 1).map (·.toNat) ++
        [(calculated (caller s) s.mem).2] =
      (inputBytes (caller t) t.mem 0 ++ inputBytes (caller t) t.mem 1).map (·.toNat) ++
        [(calculated (caller t) t.mem).2] := by
    sig_pub [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argSlots, argVal, argBytes] at h
    exact h.2.1
  have lenN : (inputBytes (caller s) s.mem 0).length = (inputBytes (caller t) t.mem 0).length := by
    simp only [inputBytes, VG.Proof.Bignum.bytesAt_length, caller, CallGeometry.buffer]
    exact congrArg BitVec.toNat (args 5 (by decide))
  have lenE : (inputBytes (caller s) s.mem 1).length = (inputBytes (caller t) t.mem 1).length := by
    simp only [inputBytes, VG.Proof.Bignum.bytesAt_length, caller, CallGeometry.buffer]
    exact congrArg BitVec.toNat (args 7 (by decide))
  obtain ⟨bytes, tries⟩ := List.append_inj leak (by simp only [List.length_map, List.length_append, lenN, lenE])
  have both := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp bytes
  exact ⟨(List.append_inj both lenN).1, List.singleton_inj.mp tries⟩

end VG.Proof.Rsa.X86.Recover
