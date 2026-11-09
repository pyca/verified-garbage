module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Prevalidated
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive

/-!
# DSA private-key validation and prevalidated signing on PPC64LE

`vg_dsa_validate_private_key(key = r3, key_len = r4, p_len = r5, q_len = r6,
scratch = r7, scratch_len = r8)` (`validate`), with the registers of
`vg_dsa_validate_public_key` (`Prevalidated.lean`): after the entry of
`vg_dsa_check_parameters` (`Params.entry`), `checkKey` (`Common.lean`)
checks the key's public part, branching on it alone, then the signer's
checks of x: the mask of `g^x mod p = y` (`Sign.keyPair`), and, with the
nonce's register `r28` pointing at x (`pointX`), the mask of `0 < x < q`
(`Derive.xRange`, the signer's nonce range check); the result is the mask's
low bit.

`vg_dsa_sign_prevalidated`, with the signer's arguments (`Sign.lean`), for
a key whose exact octets pass validation: after the signer's entry it sets
up the working spaces as `checkKey` leaves them (`Prevalidated.setup`, as
`vg_dsa_verify_prevalidated` does), with neither `g^q mod p = 1` nor
`y^q mod p = 1`, and signs (`Sign.body`) without `g^x mod p = y`: one
exponentiation, `g^k mod p`, where the checked signer made four. The
precondition rules out the sizes' failure, which zeroes `out`.
-/

@[expose] public section

namespace VG.Impl.Dsa.PPC64LE.PrevalidatedSign

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

/-- The nonce's register `r28` at x's octets, and the header's word `hMask`
into `r22`. -/
def pointX : List Instr := Sign.ptrX ++ [.load .d .r22 .r21 hMask, .addi .r28 .r12 0]

/-- After the check of the key's public part: `r3 :=` the low bit of the
masks of `g^x mod p = y` and `0 < x < q`. -/
def privateChecks : Prog isa :=
  .seq Sign.keyPair (.seq (.block pointX) (.seq Derive.xRange (.block [.li .r0 1, .logic .and .r3 .r20 .r0])))

/-- `vg_dsa_validate_private_key`. -/
def validate : Prog isa :=
  .seq (.block Params.entry) (.seq (checkKey privateChecks (.block [.li .r3 0])) (.block restore))

/-- `vg_dsa_sign_prevalidated`. -/
def sign : Prog isa :=
  .seq (.block Sign.entry) (.seq (Prevalidated.setup Sign.body Sign.zeroOut) (.block restore))

end VG.Impl.Dsa.PPC64LE.PrevalidatedSign
