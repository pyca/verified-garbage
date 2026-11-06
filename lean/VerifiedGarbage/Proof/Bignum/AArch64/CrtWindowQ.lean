module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Proof.Bignum.CrtWindowFrameWide

import VerifiedGarbage.Proof.Bignum.AArch64.CrtQ
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow

/-!
# RSA with the CRT on AArch64: `q`'s phase

`qPhase`: `m_q = c^dQ mod q` into `q`'s `Y`, if `q` divides
`n` and the modulus' `X_m ≡ c R`.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive (xRange32 tabBytes32 to_x32 x_below32)
open VG.Proof.MlKem.AArch64 (Keep)

/-- The start of a prime's phase (`unitPhase_ok`). -/
def unitSteps (mul : Nat → Nat → Nat → Prog isa) (sl : Nat) : List (Prog isa) :=
  gPow mul sl ++ [.block [ldh .x0 sl]] ++ redc mul Public.aY ++ copyArr Public.aY aXc ++
    [.block [leave]]

/-- The power in a prime's phase (`powPhase_ok`). -/
def powSteps (window : Prog isa) (select : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (sl sd slen : Nat) : List (Prog isa) :=
  [.block [ldh .x0 sl]] ++ redc mul Public.aY ++ [VG.Impl.Rsa.AArch64.WindowFive.expLoop window mul select sd slen]

theorem qPhase_eq (window : Prog isa) (select : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : VG.Impl.Rsa.AArch64.WindowFive.qPhase window mul select =
    unitSteps mul sWsQ ++ ([mul Public.aY Public.aXm Public.aY] ++
      (powSteps window select mul sWsQ sDq sQlen ++ [mul Public.aY Public.aY Public.aOne, .block [leave]])) := by
  simp only [VG.Impl.Rsa.AArch64.WindowFive.qPhase, unitSteps, powSteps, enterQ, List.append_assoc, List.cons_append, List.nil_append]

end VG.Proof.Bignum.AArch64.WindowFive
