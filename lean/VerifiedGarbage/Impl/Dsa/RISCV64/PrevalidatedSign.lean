module

public import VerifiedGarbage.Impl.Dsa.RISCV64.RandomSign
public import VerifiedGarbage.Impl.Dsa.RISCV64.Params
public import VerifiedGarbage.Impl.Dsa.RISCV64.Prevalidated

/-!
# DSA private-key validation and prevalidated signing on RISC-V

As on x86-64 and AArch64 (`Impl/Dsa/AArch64/PrevalidatedSign.lean`), for
`Spec/Dsa/PrevalidatedSign.lean`:

* `validate` is `vg_dsa_validate_private_key(key = a0, key_len = a1,
  p_len = a2, q_len = a3, scratch = a4, scratch_len = a5)`, with
  `vg_dsa_validate_public_key`'s arguments and entry (`Params.entry`). It
  makes every check `vg_dsa_sign` makes of the key: `checkSignKey` (the
  domain's checks, `1 < y < p`), then the mask of `g^x mod p = y`
  (`Sign.keyPair`) and of `0 < x < q` (`xRange`), whose low bit it returns.
  It branches on the key's public part only.
* `sign` is `vg_dsa_sign_prevalidated`, with `vg_dsa_sign`'s arguments, for
  a key that passes validation: after `vg_dsa_sign`'s entry it only sets up
  the working spaces (`Prevalidated.setup`, as `vg_dsa_verify_prevalidated`
  does), skipping the domain's checks and their `g^q mod p`, and in place of
  `keyPair`'s `g^x mod p` sets the mask to all ones (`setMask`), which the
  precondition makes the mask `keyPair` computes. Then signing's `tail`,
  with its one exponentiation, `g^k mod p`.
* `randomSign` is `vg_dsa_sign_random_prevalidated`: the randomized signer
  over `sign`.
-/

@[expose] public section

namespace VG.Impl.Dsa.RISCV64.PrevalidatedSign

open VG VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64

/-- In the Q space, with q in array 0: x into array 5, and `a0 :=` the low bit
of `hMask` and the mask of `0 < x < q` (0 in array 7). -/
def xRange : Prog isa :=
  .seq (.block enterQ) (.seq (zeroArr 7) (.seq (.block Sign.ptrX) (.seq (loadArr 5)
    (.seq (.block [.load .d .a4 .s6 hMask]) (.seq (Verify.inRange 5) (.block [.logicImm .and .a0 .a4 1]))))))

/-- `vg_dsa_validate_private_key`. -/
def validate : Prog isa :=
  .seq (.block Params.entry)
    (.seq (Sign.checkSignKey (.seq Sign.keyPair xRange) (.block [.li .a0 0])) (.block restore))

/-- The mask of the key's checks, all ones. -/
def setMask : List Instr := [.li .a0 (-1), .store .d .a0 .s6 hMask]

/-- The signing, for a key known to be valid. -/
def body : Prog isa := .seq (.block setMask) Sign.tail

/-- `vg_dsa_sign_prevalidated`. -/
def sign : Prog isa :=
  .seq (.block Sign.entry) (.seq (Prevalidated.setup body Sign.zeroOut) (.block restore))

/-- `vg_dsa_sign_random_prevalidated`. -/
def randomSign : Prog isa := RandomSign.codeWith "vg_dsa_sign_prevalidated" sign

end VG.Impl.Dsa.RISCV64.PrevalidatedSign
