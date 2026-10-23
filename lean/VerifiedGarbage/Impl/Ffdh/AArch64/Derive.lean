module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain

/-!
# Finite-field Diffie–Hellman on AArch64: an imported scalar's public value

`vg_ffdh_derive_public` (`Spec/Ffdh/DerivePublicContract.lean`), on the
pieces of `Domain.lean`: x checked as a scalar as `vg_ffdh_check_private`
checks it (`CheckPrivate.scalarRange`; 2 returned and zeros written
otherwise, the one branch on x); then `y = g^x mod p` over x's `x_len`
octets, as `vg_ffdh_exchange` raises its peer's value, its range as the
acceptance (a power of the checked generator is in its subgroup), y stored
masked by it (zeros for 0) and `3 − 2 flag` returned, without a branch.
-/

@[expose] public section

namespace VG.Impl.Ffdh.AArch64.Domain

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Impl.Bignum.Public (aXm aY sK)
open VG.Impl.Rsa.AArch64.Crt (ldw stw loadArr leave)

namespace DerivePublic

variable (window select : Prog isa) (mul : Nat → Nat → Nat → Prog isa)

/-- `(y, y_len, domain, domain_len, p_len, x, x_len, scratch, scratch_len)`:
`scratch` in `x7`. -/
def entry : List Instr :=
  [stw .x0 .x7 sOut, stw .x2 .x7 sDom, stw .x3 .x7 sDomLen, stw .x4 .x7 sK, stw .x5 .x7 sX, stw .x6 .x7 sXl,
    mov .x0 .x7]

/-- From the inner workspace: zeros to `y`, and 2 returned. -/
def fail : Prog isa := seqs [.block [leave], Keys.zeroOut sOut sK, ret 2]

/-- With x in range: `y = g^x mod p`, its flag `1 < y < p − 1` in `x9` and
`sF`; y masked by the flag to `y` (zeros for 0), and `3 − 2 flag` returned,
without a branch. -/
def tail : List (Prog isa) :=
  r2Steps mul ++ pow window select mul sG sK sX sXl ++ range aY ++
    [.block [ldh .x12 sW, ldh .x8 (sArr aY), ldh .x5 Crt.sLink, ldw .x1 .x5 sOut, ldw .x9 .x5 sK,
      .add .x .x1 .x1 .x9, movi .x7 0, ldh .x3 sF, .sub .x .x15 .x7 .x3],
      storeBE, .block [ldh .x9 sF, movi .x0 3, .lsl .x .x9 .x9 1, .sub .x .x0 .x0 .x9]]

def main : Prog isa :=
  seqs ([.block head] ++ pSetup ++ loadArr aXm sX sXl ++ CheckPrivate.scalarRange ++
    [.ite (.zero .x .x9) fail (seqs (tail window select mul))])

/-- `vg_ffdh_derive_public`. -/
def code : Prog isa :=
  .seq (.block (entry ++ domHead)) (.ite (.zero .x .x9) (ret 0) (main window select mul))

end DerivePublic

end VG.Impl.Ffdh.AArch64.Domain
