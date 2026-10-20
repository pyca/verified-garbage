module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFront
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive
public import VerifiedGarbage.Proof.Bignum.CrtWindowFiveLayout
import Mathlib.Data.Int.ModEq

/-!
# RSA with the CRT on AArch64: up to the checks

From the header `entry` leaves, for a valid modulus: the modulus' setup (as
`vg_rsa_public`'s, then `c R mod n`), the primes' workspaces and the checks
(`front_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive
open VG.Proof.MlKem.AArch64 (Keep)

/-- After the checks: the three workspaces, the modulus' values, the mask
`M` and the primes `M ? p : 3`, `M ? q : 3`. -/
structure CrtReady (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N C P Q : Nat)
    (M : Bool) : Prop where
  good : Good t B Z w minv
  nv : NVals t B w minv N
  xm : wv t.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N
  msk : word t.mem B (8 * Public.sMask) = mask M
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ32 w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  pxv : XVals t B (offP w) (wsWords pl) mp (if M then P else 3)
  pmask : word t.mem (off B (offP w)) (8 * sMaskX) = mask M
  qws : WsAt t.mem B (offQ32 w pl) (wsWords ql) mq
  qxv : XVals t B (offQ32 w pl) (wsWords ql) mq (if M then Q else 3)
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : Keep mmRegs s t

structure PReady (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N C P Q QI : Nat) : Prop
    where
  n : NReady s t B Z w minv N C
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ32 w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  qws : WsAt t.mem B (offQ32 w pl) (wsWords ql) mq
  pv : wv t.mem (off B (offP w)) (slot (wsWords pl) Public.aN) (wsWords pl) = P
  qiv : wv t.mem (off B (offP w)) (slot (wsWords pl) aChunk) (wsWords pl) = QI
  qv : wv t.mem (off B (offQ32 w pl)) (slot (wsWords ql) Public.aN) (wsWords ql) = Q

/-- The primes' workspaces, from `n`'s setup. -/
theorem setupPart_ok {s t₃ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv : BitVec 64}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (_hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hr : NReady s t₃ B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)) :
    WP isa (seqs VG.Impl.Rsa.AArch64.WindowFive.primesSetup) t₃ fun t => ∃ mp mq, PReady s t B Z ((k + 7) / 8) pl ql minv mp mq
      (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) :=
  -- `Crt.primesSetup`'s proof: the same code, and `offQ32` is `offQ`.
  WP.mono (VG.Proof.Bignum.AArch64.setupPart_ok h hr) fun _ ⟨mp, mq, r⟩ =>
    ⟨mp, mq, r.n, r.wsP, r.wsQ, r.pws, r.qws, r.pv, r.qiv, r.qv⟩


/-- The checks, from the primes' workspaces. -/
theorem checksPart_ok {s t₄ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (_hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : PReady s t₄ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs checks) t₄ fun t => ∃ mp' mq',
      CrtReady s t B Z ((k + 7) / 8) pl ql minv mp' mq' (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :=
  -- The checks' proof: the same code, and `offQ32` is `offQ`.
  WP.mono (VG.Proof.Bignum.AArch64.checksPart_ok h hv ⟨hr.n, hr.wsP, hr.wsQ, hr.pws, hr.qws, hr.pv, hr.qiv, hr.qv⟩)
    fun _ ⟨mp', mq', r⟩ => ⟨mp', mq', r.good, r.nv, r.xm, r.msk, r.wsP, r.wsQ, r.pws, r.pxv, r.pmask, r.qws, r.qxv,
      r.hfix, r.iscr, r.keep⟩


/-- Up to the checks, for a valid modulus. -/
theorem front_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa (seqs (nSetup M.mm ++ VG.Impl.Rsa.AArch64.WindowFive.primesSetup ++ checks)) s fun t => ∃ minv mp mq,
      CrtReady s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :=
  wp_seqs_append (by simp [nSetup]) (by simp [checks]) (wp_seqs_append (by simp [nSetup])
    (by simp [VG.Impl.Rsa.AArch64.WindowFive.primesSetup]) (WP.mono (nPart_ok M h hv) fun _ ⟨minv, hr⟩ =>
      WP.mono (setupPart_ok h hwide hr) fun _ ⟨_, _, hr'⟩ =>
        WP.mono (checksPart_ok h hwide hv hr') fun _ ⟨mp', mq', hr''⟩ => ⟨minv, mp', mq', hr''⟩))

end VG.Proof.Bignum.AArch64.WindowFive
