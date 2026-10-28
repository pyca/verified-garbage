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
`h = (m_p - m_q) qInv mod p` into `p`'s `Y` (`hPart_ok`, `pPhase_ok`).
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

/-- `p`'s phase: `h = (m_p - m_q) qInv mod p` into `p`'s `Y` if `p` divides
`N`, `X_m ≡ c R (mod N)`, `m_q` in `q`'s `Y` and `qInv` (masked by `c`). -/
theorem pPhase_ok (W : Window) (M : Mont) (S : Selector) {s : State} {B : Addr} {Z w : Nat} {minv mx mq : BitVec 64}
    {N X C o wx oq wq : Nat} {ep qp : Addr} {eb qib : List Byte} {c : Bool}
    (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes32 wx ≤ oq)
    (hqhi : oq + slot wq 8 + wsTab wq ≤ Z) (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hwq : 1 ≤ wq) (hwq' : wq ≤ w)
    (hslv : word s.mem B (8 * sWsP) = off B o) (hws : WsAt s.mem B o wx mx)
    (hslq : word s.mem B (8 * sWsQ) = off B oq) (hwsq : WsAt s.mem B oq wq mq)
    (hN : NVals s B w minv N) (hodd : N % 2 = 1) (hN1 : 1 < N)
    (hXm : wv s.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hmask : word s.mem (off B o) (8 * sMaskX) = mask c) (hc : c = true → X ∣ N)
    (hep : word s.mem B (8 * sDp) = ep) (hel : word s.mem B (8 * sPlen) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb)
    (hqp : word s.mem B (8 * sQinv) = qp) (hql : qib.length = eb.length) (hqs : Src s B Z qp qib)
    (hqw : (qib.length + 7) / 8 ≤ wx) (hqi : c = true → Spec.Rsa.os2ip qib < X) :
    WP isa (seqs (VG.Impl.Rsa.AArch64.WindowFive.pPhase W.code S.code M.mm)) s fun t => Good t B Z w minv ∧ WsAt t.mem B o wx mx ∧ XVals t B o wx mx X ∧
      wv t.mem (off B o) (slot wx Public.aY) wx < X ∧
      (c = true → ∃ a b, a % X = C ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X ∧
        b % X = wv s.mem (off B oq) (slot wq Public.aY) wq * 2 ^ (64 * wx) % X ∧ b < X ∧
        wv t.mem (off B o) (slot wx Public.aY) wx * 2 ^ (64 * wx) % X =
          (a + X - b) % X * Spec.Rsa.os2ip qib % X) ∧
      Frm B (pRanges w ++ [xRange32 o wx]) s.mem t.mem ∧ Keep mmRegs s t := by
  -- `pPhase`'s proof with this exponentiation: `tabBytes32` is `wsTab`, `xRange32` is `xRange`.
  rw [pPhase_eq]
  exact pPhase_gen M (fun sd slen => [VG.Impl.Rsa.AArch64.WindowFive.expLoop W.code M.mm S.code sd slen])
    (@powPhase_ok W M S) hg hw hw28 hlo hhi hqhi hwx2 hwx hwq hwq' hslv hws hslq hwsq hN hodd hN1 hXm hX hX1
    hXodd hmask hc hep hel hL1 hL2 he hqp hql hqs hqw hqi

end VG.Proof.Bignum.AArch64.WindowFive
