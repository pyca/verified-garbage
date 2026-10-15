module

public import VerifiedGarbage.Proof.Rsa.Arm.DivShift
public import VerifiedGarbage.Proof.Rsa.Arm.DivShiftCT
public import VerifiedGarbage.Proof.Rsa.Arm.DivReduceCT
public import VerifiedGarbage.Proof.Rsa.Arm.DivBitCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # One division iteration is independent of the secret numerator and divisor -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Div
open VG VG.Arm VG.Impl.Rsa.Arm.Div VG.Proof.Bignum.Arm

theorem step_ct {g : Geometry} :
    RelCT isa (fun s t => Context g s ∧ Context g t) step (fun _ _ => True) := by
  have shiftWp (s : State) (h : Context g s) : WP isa shift s (Context g) :=
    WP.mono (shift_ok h) (fun _ h => h.2.2.1)
  have reduceWp (s : State) (h : Context g s) : WP isa reduce s (Context g) :=
    WP.mono (reduce_ok h) (fun _ h => h.2.2.1)
  exact (pair_posts (shift_ct (g := g)) shiftWp).seq
    ((pair_posts (reduce_ct (g := g)) reduceWp).seq quotientBit_ct)

end VG.Proof.Rsa.Arm.Div
