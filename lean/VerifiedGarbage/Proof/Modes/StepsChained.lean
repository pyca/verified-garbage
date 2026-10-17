module

public import VerifiedGarbage.Proof.Modes.Steps
public import VerifiedGarbage.Impl.Modes.CbcChained

/-!
# CBC that updates the chaining value, one step at a time, for any target

`Mode.cbcEncChained` and `Mode.cbcDecChained` compute CBC's step functions
as `Mode.cbcEnc` and `Mode.cbcDec` do (`cbcEncChained_computes`, …), and the
chaining value after the last step is the one to continue from,
`Spec.Cbc.next` (`encrypt_run_next`, `decrypt_run_next`). Nothing here
depends on a target.
-/

@[expose] public section

namespace VG.Proof.Modes

open VG VG.Impl.Modes
open VG.Spec.Cbc (Cipher xor)

theorem encrypt_run_next (ciph : Cipher) : ∀ (iv : List Byte) (xs : List (List Byte)),
    Spec.Cbc.next iv (Spec.Cbc.encrypt ciph iv xs) = (run (cbcEncF ciph) iv xs).2
  | _, [] => rfl
  | iv, x :: xs => by
    rw [Spec.Cbc.encrypt, Spec.Cbc.next, List.getLastD_cons, ← Spec.Cbc.next, encrypt_run_next ciph _ xs]; rfl

theorem decrypt_run_next (ciph : Cipher) : ∀ (iv : List Byte) (xs : List (List Byte)),
    Spec.Cbc.next iv xs = (run (cbcDecF ciph) iv xs).2
  | _, [] => rfl
  | iv, x :: xs => by
    rw [Spec.Cbc.next, List.getLastD_cons, ← Spec.Cbc.next, decrypt_run_next ciph x xs]; rfl

section
variable {bw : Nat} {ciph : Cipher} (hc : ∀ b, (ciph b).length = 4 * bw)
include hc

theorem cbcEncChained_computes : Computes (Mode.cbcEncChained bw) (4 * bw) ciph (cbcEncF ciph) :=
  cbcEnc_computes hc

theorem cbcDecChained_computes : Computes (Mode.cbcDecChained bw) (4 * bw) ciph (cbcDecF ciph) :=
  cbcDec_computes hc

end

end VG.Proof.Modes
