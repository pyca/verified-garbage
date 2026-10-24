module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Derive

/-!
# Finite-field Diffie–Hellman on PPC64LE: an imported key pair's check

`vg_ffdh_check_private` (`Spec/Ffdh/Contract.lean`), as
`vg_ffdh_derive_public` (`Derive.lean`) but for its output: with x in
range, `y` is valid and `y = g^x mod p` exactly when `g^x mod p` is in
`2..p − 2` (powers of a checked generator remain in its q subgroup) and
equals y. So, after x's range (`xRange`, status 2 out of range):

* `z = g^x mod p` into array 4 (`exPower`);
* the mask of `1 < z < p − 1` (`zMask`) and, with y's `p_len` octets loaded
  into array 8 (its address from the header's word 10), that of `z = y`
  (`eqMask`); the status is 1 under both masks, else 0.

The code branches on p's validity, whether there is q and x's range, which
the status reveals.
-/

@[expose] public section

namespace VG.Impl.Ffdh.PPC64LE.CheckPrivate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.Derive
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Impl.MillerRabin.PPC64LE (eqMask)

/-- The registers saved in the working space (`r10`); x, `x_len` and y into
the header's words 8–10; `setup` for the domain (`r3`), `domain_len` (`r4`)
and `p_len` (`r5`); g's address into `r9`. -/
def cpFront : List Instr :=
  Domain.save .r10 ++ [.store .d .r8 .r23 64, .store .d .r9 .r23 72, .store .d .r6 .r23 80] ++
    Domain.setup ++ [.add .r9 .r21 .r28]

/-- y's `p_len` octets (at `r12`) into array 8, and `r10` back to array 0. -/
def loadY : Prog isa :=
  .seq (.block (base .r10 8 ++ [.addi .r6 .r28 0])) (.seq Precompute.loadN (.block [.addi .r10 .r23 hdrBytes]))

/-- `r3 :=` 1 under the masks of `1 < z < p − 1` (`r26`) and `z = y`
(`r19`), else 0. -/
def both : List Instr := [.logic .and .r26 .r26 .r19, .li .r3 1, .logic .and .r3 .r3 .r26]

/-- With z in array 4 and y's address in `r12`: the working space back in
`r31`, the mask of `1 < z < p − 1`, y into array 8 and the mask of `z = y`;
`r3 :=` 1 or 0. -/
def cpTail : Prog isa :=
  .seq (.block [.addi .r31 .r23 0]) (.seq zMask (.seq loadY (.seq (eqMask .r19 4 8) (.block both))))

/-- y's address from the header's word 10, then `cpTail`. -/
def cpCmp : Prog isa := .seq (.block [.load .d .r12 .r23 80]) cpTail

/-- x in range: `r3 :=` 1 if `g^x mod p` is in `2..p − 2` and equals y,
else 0. -/
def cpGood : Prog isa := .seq (.block [.add .r9 .r21 .r28]) (.seq exPower cpCmp)

/-- After p's check. -/
def cpBody : Prog isa := .seq xRange (.ite (.zero .d .r26) (.block [.li .r3 2]) cpGood)

/-- `vg_ffdh_check_private(domain, domain_len, p_len, y, y_len, x, x_len,
scratch, scratch_len)`, the last on the stack. -/
def checkPrivate : Prog isa :=
  .seq (.block cpFront) (.seq loadP
    (.seq (.ite (.zero .d .r0) cpBody (.block [.li .r3 0])) (.block Domain.restore)))

end VG.Impl.Ffdh.PPC64LE.CheckPrivate
