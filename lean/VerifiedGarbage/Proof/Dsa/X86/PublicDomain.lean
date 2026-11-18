module

public import VerifiedGarbage.Proof.Dsa.X86.SignLayout
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! ### `Dsa.X86.SharedPublic`, which this module and modules that import it used -/

section

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
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega_using [hi]
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem signingPublicArgs {s t : State} (H : (Spec.Dsa.signContract abi 108).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 11, arg s i = arg t i := by
  sig_pub [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega_using [hi]
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

end

end

/-! # Public packed-key leakage determines the two domain moduli -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86

theorem publicPrefix_component {a b : List Byte} {n offset len : Nat}
    (h : a.take n = b.take n) (bound : offset + len ≤ n) :
    (a.drop offset).take len = (b.drop offset).take len := by
  have H := congrArg (fun bs : List Byte => (bs.drop offset).take len) h
  simp only [List.drop_take, List.take_take, Nat.min_eq_left (by omega_using [bound] : len ≤ n - offset)] at H
  exact H

theorem publicLeak_domain {pLen qLen : Nat} {a b : List Byte}
    (H : Spec.Dsa.publicBytesLeak pLen qLen a = Spec.Dsa.publicBytesLeak pLen qLen b) :
    (Spec.Dsa.publicKeyBytes pLen qLen a).params.p = (Spec.Dsa.publicKeyBytes pLen qLen b).params.p ∧
    (Spec.Dsa.publicKeyBytes pLen qLen a).params.q = (Spec.Dsa.publicKeyBytes pLen qLen b).params.q := by
  have Bytes := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 H
  have P := publicPrefix_component (offset := 0) (len := pLen) Bytes (by omega_using [])
  have Q := publicPrefix_component (offset := pLen) (len := qLen) Bytes (by omega_using [])
  simp only [List.drop_zero] at P
  exact ⟨congrArg Spec.Dsa.decodeBE P, congrArg Spec.Dsa.decodeBE Q⟩

theorem verifyingPublicDomain {s t : State} (H : (Spec.Dsa.verifyContract abi 108).pub s t) :
    (verifyKey s).params.p = (verifyKey t).params.p ∧ (verifyKey s).params.q = (verifyKey t).params.q := by
  have Args := (verifyingPublicArgs H).2
  have Leak := verifyingPublicLeak H
  rw [Args 2 (by decide), Args 3 (by decide)] at Leak
  have D := publicLeak_domain Leak
  simpa only [verifyKey, Args 2 (by decide), Args 3 (by decide)] using D

theorem signingPublicDomain {s t : State} (H : (Spec.Dsa.signContract abi 108).pub s t) :
    (signKey s).params.p = (signKey t).params.p ∧ (signKey s).params.q = (signKey t).params.q := by
  have Args := (signingPublicArgs H).2
  have Leak := signingPublicLeak H
  rw [Args 4 (by decide), Args 6 (by decide)] at Leak
  have D := publicLeak_domain Leak
  simpa only [signKey, Args 4 (by decide), Args 6 (by decide)] using D

end VG.Proof.Dsa.X86
