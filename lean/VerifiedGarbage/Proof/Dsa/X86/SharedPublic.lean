module
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Weierstrass.PointContract


/-! # Public cdecl observations supplied by the shared DSA contracts -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86

theorem verifyingPublicArgs {s t : State} (H : (Spec.Dsa.verifyContract abi 108).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 10, arg s i = arg t i := by
  sig_pub [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem signingPublicArgs {s t : State} (H : (Spec.Dsa.signContract abi 108).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 11, arg s i = arg t i := by
  sig_pub [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem verifyingPublicLeak {s t : State} (H : (Spec.Dsa.verifyContract abi 108).pub s t) :
    Spec.Dsa.publicBytesLeak (arg s 2).toNat (arg s 3).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) =
    Spec.Dsa.publicBytesLeak (arg t 2).toNat (arg t 3).toNat
      (Spec.Rsa.bytesAt t.mem (argumentPointer t 0) (arg t 1).toNat) := by
  sig_pub [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argSlots, argVal, argBytes] at H
  exact (List.append_inj' H.2.1 (List.length_singleton.trans List.length_singleton.symm)).1

theorem signingPublicLeak {s t : State} (H : (Spec.Dsa.signContract abi 108).pub s t) :
    Spec.Dsa.publicBytesLeak (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat) =
    Spec.Dsa.publicBytesLeak (arg t 4).toNat (arg t 6).toNat
      (Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat) := by
  sig_pub [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes] at H
  exact (List.append_inj' H.2.1 (List.length_singleton.trans List.length_singleton.symm)).1

end VG.Proof.Dsa.X86
