module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Bignum.CrtWindowFiveLayout
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Bignum.AArch64.CrtSetup

/-!
# RSA with the CRT on AArch64: setting up the primes

`primesSetup`, from the modulus' workspace: the workspaces of `p` and `q`
after it, `p` and `qInv` into `p`'s, and `q` into `q`'s
(`primesSetup_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum VG.Proof.Bignum.CrtWindowFive
open VG.Proof.MlKem.AArch64 (Keep)

/-- `primesSetup`: the primes' workspaces, `p` and `qInv` into `p`'s (arrays
`aN` and `aChunk`), and `q` into `q`'s. -/
theorem primesSetup_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {pl ql : Nat} {pp qp ip : Addr}
    {pb qb ib : List Byte} (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw30 : w < 2 ^ 28)
    (hZ : offQ32 w pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hpl : word s.mem B (8 * sPlen) = BitVec.ofNat 64 pl) (hql : word s.mem B (8 * sQlen) = BitVec.ofNat 64 ql)
    (hpp : word s.mem B (8 * sP) = pp) (hqp : word s.mem B (8 * sQ) = qp) (hip : word s.mem B (8 * sQinv) = ip)
    (hpb : Src s B Z pp pb) (hqb : Src s B Z qp qb) (hib : Src s B Z ip ib)
    (hpbl : pb.length = pl) (hqbl : qb.length = ql) (hibl : ib.length = pl)
    (hpl1 : 1 ≤ pl) (hpl2 : pl < 8 * w) (hql1 : 1 ≤ ql) (hql2 : ql < 8 * w) :
    WP isa (seqs VG.Impl.Rsa.AArch64.WindowFive.primesSetup) s fun t => Good t B Z w minv ∧
      word t.mem B (8 * sWsP) = off B (offP w) ∧ word t.mem B (8 * sWsQ) = off B (offQ32 w pl) ∧
      (∃ mp, WsAt t.mem B (offP w) (wsWords pl) mp) ∧ (∃ mq, WsAt t.mem B (offQ32 w pl) (wsWords ql) mq) ∧
      wv t.mem (off B (offP w)) (slot (wsWords pl) Public.aN) (wsWords pl) = Spec.Rsa.os2ip pb ∧
      wv t.mem (off B (offP w)) (slot (wsWords pl) aChunk) (wsWords pl) = Spec.Rsa.os2ip ib ∧
      wv t.mem (off B (offQ32 w pl)) (slot (wsWords ql) Public.aN) (wsWords ql) = Spec.Rsa.os2ip qb ∧
      Frm B [(8 * sWsP, 8), (8 * sWsQ, 8), (offP w, slot (wsWords pl) 8 + tabBytes32 (wsWords pl) + slot (wsWords ql) 8)]
        s.mem t.mem ∧
      Keep mmRegs s t :=
  -- The same code and layout as `Crt.primesSetup`: `wsEndT32` is `wsEndT`, and
  -- `tabBytes32` (so `offQ32`) is `wsTab` (`offQ`).
  VG.Proof.Bignum.AArch64.primesSetup_ok hg hw hw30 hZ hpl hql hpp hqp hip hpb hqb hib hpbl hqbl hibl hpl1
    hpl2 hql1 hql2

end VG.Proof.Bignum.AArch64.WindowFive
