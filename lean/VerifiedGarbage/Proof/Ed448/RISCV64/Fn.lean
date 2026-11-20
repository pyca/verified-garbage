module

public import VerifiedGarbage.Impl.Ed448.RISCV64.Fn
public import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.PublicKeyVerified
public import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.SignVerified
public import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.VerifyVerified
public import VerifiedGarbage.Proof.Ed448.Facts
public import VerifiedGarbage.Proof.Ed448.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved

/-!
# Ed448 on RISC-V, as emitted

`vg_ed448_public_key`, `vg_ed448_sign_cached` and `vg_ed448_verify` with
their cleanup (`Impl.Ed448.RISCV64.Fn`): each meets its contract in constant
time and returns without secret residue (`VerifiedScrubbed`, by
`RISCV64.Scrub.verifiedScrubbed`), which is what its registration binds. What
the cleanup needs of each function's code (`Scrub.scrubSide`) is evaluated
here, by the kernel.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64.Fn

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Ed448.RISCV64.Scrub

theorem publicKey :
    VerifiedScrubbed target Impl.Ed448.RISCV64.Fn.publicKey (Spec.Ed448.publicKeyContract abi 1328) 0 :=
  verifiedScrubbed (api := Spec.Ed448.publicKeyApi) (W := 1328)
    { code := Impl.Ed448.RISCV64.Whole.publicKeyCode,
      verified := Whole.publicKey_framed Proof.Ed448.baseLadder2_ok }
    (publicKeyOut _) (by lit_decide)

theorem signCached :
    VerifiedScrubbed target Impl.Ed448.RISCV64.Fn.signCached (Spec.Ed448.signCachedContract abi 1696) 0 :=
  verifiedScrubbed (api := Spec.Ed448.signCachedApi) (W := 1696)
    { code := Impl.Ed448.RISCV64.Whole.signCachedCode,
      verified := Whole.signCached_framed Proof.Ed448.baseLadder2_ok }
    (signCachedOut _) (by lit_decide)

theorem verify :
    VerifiedScrubbed target Impl.Ed448.RISCV64.Fn.verify (Spec.Ed448.verifyContract abi 1616) 32 :=
  verifiedScrubbed (api := Spec.Ed448.verifyApi) (W := 1616)
    { code := Impl.Ed448.RISCV64.Whole.verifyCode, verified := Whole.verify_framed Proof.Ed448.recover_ok }
    (verifyOut _) (by lit_decide)

end VG.Proof.Ed448.RISCV64.Fn
