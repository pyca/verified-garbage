module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowQ
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowPhases
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.CrtWindowPRanges

/-!
# RSA with the CRT on AArch64: `p`'s phase

`pPhase`: `m_p = c^dP mod p` as `pPhase`'s `qPhase` computes `m_q`, then
`m_q R_p mod p` (from `m_q G mod n`, `mqPart_ok`), and
`h = (m_p - m_q) qInv mod p` into `p`'s `Y` (`hPart_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive (xRange32 tabBytes32 px_hdr px_above px_wv x_below32 pxR_bound)
open VG.Proof.MlKem.AArch64 (Keep)

theorem pPhase_eq (window : Prog isa) (select : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : VG.Impl.Rsa.AArch64.WindowFive.pPhase window select mul =
    unitSteps mul sWsP ++ (mqSteps mul ++ ([mul Public.aY Public.aXm Public.aY] ++
      (powSteps window select mul sWsP sDp sPlen ++ (([.block [leave]] : List (Prog isa)) ++ hSteps mul)))) := by
  simp only [VG.Impl.Rsa.AArch64.WindowFive.pPhase, unitSteps, powSteps, mqSteps, hSteps, enterP, List.append_assoc, List.cons_append,
    List.nil_append]

end VG.Proof.Bignum.AArch64.WindowFive
