module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Load
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Bignum.PPC64LE.ModExpPow
import VerifiedGarbage.Proof.Bignum.PPC64LE.ModArithReduce
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# DSA on PPC64LE: `p mod q`, the P space, and the checks of g and y

* `pModQ_ok`: q into the Q space's array 0, and `r0 = 0` exactly when
  `p mod q = 1`;
* `setupP_ok`: p into the P space's array 0 and `R² mod p` into its array 8;
* `checkElem_ok`: a number of `p_len` octets into the P space's array 4, and
  `r0 = 0` exactly when it is above 1, below p, and its q-th power modulo p
  is 1.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE
open VG.Proof.Bignum (slot)

/-- The registers `pModQ` writes. -/
def pModQRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r20, .r23, .r24, .r25, .r29,
    .r30, .r31]

/-- `pModQ`: into the Q space, q into its array 0 (word 4 zero), and `r0 = 0`
exactly when `p mod q = 1`. -/
theorem pModQ_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S) (hk : Src s L key (3 * L.pl + L.ql))
    (hq : 0 < qOf s.mem L key) :
    WP isa pModQ s fun t =>
      (InQ t L ∧ arrQ t.mem L 0 = qOf s.mem L key ∧ word t.mem L.Q (slot 4 0 + 8 * 4) = 0 ∧
        (t.gpr .r0 = 0 ↔ pOf s.mem L key % qOf s.mem L key = 1) ∧ Body L s.mem t.mem) ∧
        Keep pModQRegs s t := by
  sorry

/-- The registers `setupP` writes. -/
def setupPRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r20, .r23, .r29, .r31]

/-- `setupP`: into the P space, p into its array 0 (word `w` zero) and
`R² mod p` (`R = 2^(64 w)`) into its array 8. -/
theorem setupP_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S) (hk : Src s L key (3 * L.pl + L.ql))
    (hp : 2 ≤ pOf s.mem L key) :
    WP isa setupP s fun t =>
      (InP t L ∧ arrP t.mem L 0 = pOf s.mem L key ∧ word t.mem L.S (slot L.wp 0 + 8 * L.wp) = 0 ∧
        arrP t.mem L 8 = 2 ^ (128 * L.wp) % pOf s.mem L key ∧ Body L s.mem t.mem) ∧
        Keep setupPRegs s t := by
  sorry

/-- The registers `checkElem` writes. -/
def elemRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24,
    .r25, .r30, .r31]

/-- `checkElem`, in the P space with p in array 0 and `R² mod p` in array 8:
the `p_len` octets at `E` (`r12`, `p_len` in `r6`) into array 4, and `r0 = 0`
exactly when their number `e` has `1 < e < p` and `e^q mod p = 1`. Arrays 0
and 8 are kept. -/
theorem checkElem_ok {s : State} {L : Lay} {key sig dig E : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hh : Hdr s.mem L key sig dig) (hin : InP s L) (hk : Src s L key (3 * L.pl + L.ql))
    (he : Src s L E L.pl) (h12 : s.gpr .r12 = E) (h6 : s.gpr .r6 = BitVec.ofNat 64 L.pl)
    (hp0 : arrP s.mem L 0 = p) (hz0 : word s.mem L.S (slot L.wp 0 + 8 * L.wp) = 0) (hp : 2 ≤ p)
    (hpo : p % 2 = 1) (hrr : arrP s.mem L 8 = 2 ^ (128 * L.wp) % p) :
    WP isa checkElem s fun t =>
      (InP t L ∧ arrP t.mem L 0 = p ∧ word t.mem L.S (slot L.wp 0 + 8 * L.wp) = 0 ∧
        arrP t.mem L 8 = arrP s.mem L 8 ∧
        (t.gpr .r0 = 0 ↔ (1 < Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) ∧
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) < p ∧
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem E L.pl) ^ qOf s.mem L key % p = 1)) ∧
        Body L s.mem t.mem) ∧
        Keep elemRegs s t := by
  sorry

end VG.Proof.Dsa.PPC64LE
