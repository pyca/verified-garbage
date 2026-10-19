module
public import VerifiedGarbage.Proof.Dsa.X86.SignLayout
public import VerifiedGarbage.Proof.Dsa.X86.VerifyLayout

import VerifiedGarbage.Proof.Dsa.X86.SharedPublic

/-! # Public packed-key leakage determines the two domain moduli -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86

theorem publicPrefix_component {a b : List Byte} {n offset len : Nat}
    (h : a.take n = b.take n) (bound : offset + len ≤ n) :
    (a.drop offset).take len = (b.drop offset).take len := by
  have H := congrArg (fun bs : List Byte => (bs.drop offset).take len) h
  simp only [List.drop_take, List.take_take, Nat.min_eq_left (by omega : len ≤ n - offset)] at H
  exact H

theorem publicLeak_domain {pLen qLen : Nat} {a b : List Byte}
    (H : Spec.Dsa.publicBytesLeak pLen qLen a = Spec.Dsa.publicBytesLeak pLen qLen b) :
    (Spec.Dsa.publicKeyBytes pLen qLen a).params.p = (Spec.Dsa.publicKeyBytes pLen qLen b).params.p ∧
    (Spec.Dsa.publicKeyBytes pLen qLen a).params.q = (Spec.Dsa.publicKeyBytes pLen qLen b).params.q := by
  have Bytes := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 H
  have P := publicPrefix_component (offset := 0) (len := pLen) Bytes (by omega)
  have Q := publicPrefix_component (offset := pLen) (len := qLen) Bytes (by omega)
  simp only [List.drop_zero] at P
  exact ⟨congrArg Spec.Dsa.decodeBE P, congrArg Spec.Dsa.decodeBE Q⟩

theorem verifyingPublicDomain {s t : State} (H : (Spec.Dsa.verifyContract abi 32).pub s t) :
    (verifyKey s).params.p = (verifyKey t).params.p ∧ (verifyKey s).params.q = (verifyKey t).params.q := by
  have Args := (verifyingPublicArgs H).2
  have Leak := verifyingPublicLeak H
  rw [Args 2 (by decide), Args 3 (by decide)] at Leak
  have D := publicLeak_domain Leak
  simpa only [verifyKey, Args 2 (by decide), Args 3 (by decide)] using D

theorem signingPublicDomain {s t : State} (H : (Spec.Dsa.signContract abi 32).pub s t) :
    (signKey s).params.p = (signKey t).params.p ∧ (signKey s).params.q = (signKey t).params.q := by
  have Args := (signingPublicArgs H).2
  have Leak := signingPublicLeak H
  rw [Args 4 (by decide), Args 6 (by decide)] at Leak
  have D := publicLeak_domain Leak
  simpa only [signKey, Args 4 (by decide), Args 6 (by decide)] using D

end VG.Proof.Dsa.X86
