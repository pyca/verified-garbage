module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Domain

/-!
# Finite-field Diffie–Hellman on PPC64LE: a private key's public value

`vg_ffdh_derive_public` (`Spec/Ffdh/DerivePublicContract.lean`), in the
working space of `Domain.lean` at `scratch`, with x's address and length and
`y`'s address in the header's words 8–10, as `vg_ffdh_exchange` keeps x and
`out`:

* p is loaded into array 0 and checked as `vg_rsa_public_precompute` checks
  a modulus; otherwise the result is 0;
* x's `x_len` octets into array 4 (`xLoad`), and the constants of `consts`;
  the mask of x below the bound (q's `p_len` octets at `domain + 2 p_len`,
  loaded into array 1, or `p − 1` in array 6 without q) is `subMod`'s borrow
  into array 3, and that of `x = 0` is `eqMask`'s with array 5 (`xRange`);
* out of range, the status is 2 and `y` gets zeros, by `PublicChecked.output`
  under the zero mask;
* otherwise `y = g^x mod p` (g's octets at `domain + p_len`) as the exchange
  computes the shared value (`exPower`), written to `y` under the mask of
  `1 < y < p − 1` or replaced by zeros (`exOut`), and the status
  `3 − 2 r3`: 1 or 3.

The code branches on p's validity, whether there is q and x's range, which
the status reveals.
-/

@[expose] public section

namespace VG.Impl.Ffdh.PPC64LE.Derive

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Impl.MillerRabin.PPC64LE (eqMask)

/-- The registers saved in the working space (`r10`); x, `x_len` and `y`
into the header's words 8–10; `setup` for the domain (`r5`), `domain_len`
(`r6`) and `p_len` (`r7`); g's address into `r9`. -/
def dpFront : List Instr :=
  Domain.save .r10 ++ [.store .d .r8 .r23 64, .store .d .r9 .r23 72, .store .d .r3 .r23 80, .addi .r3 .r5 0,
    .addi .r4 .r6 0, .addi .r5 .r7 0] ++ Domain.setup ++ [.add .r9 .r21 .r28]

/-- x's address and length from the header, with array 4's base. -/
def xLoadPre : List Instr := base .r10 4 ++ [.load .d .r12 .r23 64, .load .d .r6 .r23 72]

/-- x's `x_len` octets into array 4, its word `w` := 0, and `r10` back to
array 0. -/
def xLoadRest : Prog isa :=
  .seq Precompute.loadN
    (.block [.add .r14 .r10 .r29, .subi .r14 .r14 16, .li .r0 0, .store .d .r0 .r14 0, .addi .r10 .r23 hdrBytes])

/-- `r10 :=` the bound's array: q's octets loaded into array 1, or array 6
(`p − 1`) without q. -/
def xBound : Prog isa :=
  .seq (.block hasQ) (.ite (.zero .d .r0)
    (.seq (.block ([.lsl .r12 .r28 1, .add .r12 .r12 .r21, .addi .r6 .r28 0] ++ base .r10 1)) Precompute.loadN)
    (.block (base .r10 6)))

/-- After x's load: the constants, `r26 :=` the mask of `0 < x < bound`. -/
def xMask : Prog isa :=
  .seq consts (.seq (.block (base .r8 4 ++ base .r9 3)) (.seq xBound (.seq subMod
    (.seq (.block [.addi .r26 .r20 0, .addi .r10 .r23 hdrBytes]) (.seq (eqMask .r19 4 5) (.block clear19))))))

/-- x into array 4, and `r26 :=` all ones if `0 < x < bound`, else 0. -/
def xRange : Prog isa := .seq (.block xLoadPre) (.seq xLoadRest xMask)

/-- x out of range: zeros to `y`, status 2. -/
def dpBad : Prog isa :=
  .seq (.block [.load .d .r27 .r23 80]) (.seq PublicChecked.output (.block [.li .r3 2]))

/-- `r3 := 3 − 2 r3`. -/
def status : List Instr := [.li .r0 3, .lsl .r3 .r3 1, .sub .r3 .r0 .r3]

/-- x in range: `g^x mod p` to `y` or zeros, status 1 or 3. -/
def dpGood : Prog isa :=
  .seq (.block [.add .r9 .r21 .r28]) (.seq exPower (.seq exOut (.block status)))

/-- After p's check. -/
def dpBody : Prog isa := .seq xRange (.ite (.zero .d .r26) dpBad dpGood)

/-- `vg_ffdh_derive_public(y, y_len, domain, domain_len, p_len, x, x_len,
scratch, scratch_len)`, the last on the stack. -/
def derivePublic : Prog isa :=
  .seq (.block dpFront) (.seq loadP
    (.seq (.ite (.zero .d .r0) dpBody (.block [.li .r3 0])) (.block Domain.restore)))

end VG.Impl.Ffdh.PPC64LE.Derive
