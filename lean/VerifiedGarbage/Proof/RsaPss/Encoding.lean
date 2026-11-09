module

public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.Proof.Mgf1.Basic

/-!
# EMSA-PSS: clearing the leftmost bits

`clearTop` keeps the length of the octets it clears (`clearTop_length`).
-/

@[expose] public section

namespace VG.Proof.RsaPss

open Spec Spec.RsaPss

open Mgf1 (Hash xorBytes mgf1)
open Proof.Mgf1 (Valid xorBytes_length xorBytes_xorBytes mgf1_length)

/-! ## Clearing the leftmost bits -/

theorem clearTop_length (z : Nat) : ∀ bs : List Byte, (clearTop z bs).length = bs.length
  | [] => rfl
  | _ :: _ => rfl

end VG.Proof.RsaPss
