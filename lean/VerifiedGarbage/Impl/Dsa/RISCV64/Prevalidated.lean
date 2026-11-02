module

public import VerifiedGarbage.Impl.Dsa.RISCV64.Verify
public import VerifiedGarbage.Impl.Dsa.RISCV64.Params

/-!
# DSA public-key validation and prevalidated verification on RISC-V

As on PPC64LE (`Impl/Dsa/PPC64LE/Prevalidated.lean`).
`vg_dsa_validate_public_key(key = a0, key_len = a1, p_len = a2, q_len = a3,
scratch = a4, scratch_len = a5)`: after the entry of
`vg_dsa_check_parameters` (`Params.entry`), `checkKey` (`Common.lean`)
branches on the key's public part, all of it public, and leaves 1 or 0.

`vg_dsa_verify_prevalidated`, with `vg_dsa_verify`'s arguments: its caller
guarantees that the key passes validation, so after `vg_dsa_verify`'s entry
it skips the checks of the key but the sizes, which give q's significant
octets (`sizes`, whose failure the precondition rules out), and only sets up
the working spaces `checkKey` leaves for verification: q in the Q space
(`setupQ`), p, `-p⁻¹ mod 2⁶⁴` and `R² mod p` in the P space (`setupP`). Then
the verification proper (`Verify.body`).
-/

@[expose] public section

namespace VG.Impl.Dsa.RISCV64.Prevalidated

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

/-- `vg_dsa_validate_public_key`. -/
def validate : Prog isa :=
  .seq (.block Params.entry) (.seq (checkKey (.block [.li .a0 1]) (.block [.li .a0 0])) (.block restore))

/-- The working spaces for a key known to be valid, as `checkKey` leaves them;
then `rest`, or `fail` if the sizes are not supported. -/
def setup (rest fail : Prog isa) : Prog isa := sizes (.seq setupQ (.seq setupP rest)) fail

/-- `vg_dsa_verify_prevalidated`. -/
def verify : Prog isa :=
  .seq (.block Verify.entry) (.seq (setup Verify.body (.block [.li .a0 0])) (.block restore))

end VG.Impl.Dsa.RISCV64.Prevalidated
