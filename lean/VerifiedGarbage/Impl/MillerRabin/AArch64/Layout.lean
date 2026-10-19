module
public import VerifiedGarbage.Impl.Bignum.Layout
import VerifiedGarbage.Impl.Rsa.AArch64.Crt
public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Impl.Rsa.AArch64


/-! # Workspace representation shared by RSA and FFDH Miller–Rabin -/

@[expose] public section

namespace VG.Impl.RsaKeyGen.AArch64.Candidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Keys

/-! ## Header slots

`out_len` is in `vg_rsa_public`'s `sK`, from which `Keys.head` computes
`w`; `Keys.head` also sets the stride (`sStride`) and the mask `sMask` all
ones, which `finPrime` stores `c` under; `r2Steps` counts its doublings in
`sCnt`, which is otherwise a temporary (`kT0`). -/

def kOut : Nat := sFn 0
def kUsedP : Nat := sFn 1
def kLen : Nat := sK
def kE : Nat := sFn 3
def kElen : Nat := sFn 4
def kP : Nat := sFn 5
def kPlen : Nat := sFn 7
def kRand : Nat := sFn 8
def kRandLen : Nat := sFn 9
/-- The octets of `rand` read so far. -/
def kUsed : Nat := sFn 11
/-- Temporaries. -/
def kT0 : Nat := sCnt
def kT1 : Nat := sFn 13
def kT2 : Nat := sFn 14
/-- Miller–Rabin's state: what became of the last witness. -/
def kStat : Nat := sFn 15
/-- The mask of the witness being uniform (header slot 0, which no register
is saved in). -/
def kU : Nat := 0
/-- `gcd(c − 1, e)`, and Miller–Rabin's mask of `y = −1` (slot 1). -/
def kG : Nat := 1

/-- Miller–Rabin's slots, once `e` and `p` are no longer needed: the uniform
witnesses it needs, the witnesses so far plus one, the uniform ones, the
flag, the word of `E` being scanned, the words left and the windows left. -/
def kChecks : Nat := kE
def kI : Nat := kElen
def kUni : Nat := kP
def kFlag : Nat := kPlen
def kV : Nat := kT0
def kWords : Nat := kT1
def kBits : Nat := kT2

/-! ## Arrays

Besides `vg_rsa_public`'s eight: `b R mod c` (`aB`), `R mod c` (`aR1`),
`c − R mod c` (`aRm1`), then the table of small primes (`aTab`, 256 words).
Miller–Rabin's table of the powers `T_j = b^j R mod c` (`j < 16`, entry `j`
the array `aT0 + j`) overlaps it, written only after trial division; then
the exponent `(c − 1) / 2^σ` (`aE`, with the lowest set bit of `c − 1`'s
lowest nonzero word after its `w` words). `aX` holds `p`, then `c − 1`,
then the witness. -/

def aB : Nat := 8
def aR1 : Nat := 9
def aRm1 : Nat := 10
def aTab : Nat := 11
def aT0 : Nat := 11
def aE : Nat := 27

end VG.Impl.RsaKeyGen.AArch64.Candidate
