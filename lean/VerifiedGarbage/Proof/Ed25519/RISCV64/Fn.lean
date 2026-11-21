module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Fn
public import VerifiedGarbage.Proof.Ed25519.RISCV64.KeyPair
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.ExpandedVerified
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.VerifyMsgVerified
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved

/-!
# Ed25519 on RISC-V, as emitted

`vg_ed25519_key_pair`, `vg_ed25519_sign_expanded` and `vg_ed25519_verify`
with their cleanup (`Impl.Ed25519.RISCV64.Fn`): each meets its contract in
constant time and returns without secret residue (`VerifiedScrubbed`, by
`RISCV64.Scrub.verifiedScrubbedAll`), which is what its registration binds. What
the cleanup needs of each function's code (`Scrub.scrubSide`) is evaluated
here, by the kernel.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Fn

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Ed25519.RISCV64.Scrub
open VG.Impl.Ed25519.RISCV64 (combConsts bConsts)

theorem keyPair :
    VerifiedScrubbed target (Impl.Ed25519.RISCV64.Fn.keyPair KeyPair.dgCode)
      (Spec.Ed25519.keyPairContract (abi.withConsts combConsts) 480) 0 :=
  verifiedScrubbedAll (api := Spec.Ed25519.keyPairApi) (W := 480)
    { code := Impl.Ed25519.RISCV64.KeyPair.keyPair (Spec.Sha512.digest512Api.name ++ "_core")
        KeyPair.dgCode "vg_ed25519_public_key_expanded" Impl.Ed25519.RISCV64.Whole.publicKeyExpandedCode
      verified := KeyPair.verified }
    (keyPairOut combConsts _) (by lit_decide)

theorem signExpanded :
    VerifiedScrubbed target Impl.Ed25519.RISCV64.Fn.signExpanded
      (Spec.Ed25519.signExpandedContract (abi.withConsts combConsts) 496) 0 :=
  verifiedScrubbedAll (api := Spec.Ed25519.signExpandedApi) (W := 496)
    { code := Impl.Ed25519.RISCV64.Whole.signExpandedCode, verified := Whole.signExpanded_framed }
    (signExpandedOut combConsts _) (by lit_decide)

theorem verify :
    VerifiedScrubbed target Impl.Ed25519.RISCV64.Fn.verify
      (Spec.Ed25519.verifyContract (abi.withConsts bConsts) 480) 32 :=
  verifiedScrubbedAll (api := Spec.Ed25519.verifyApi) (W := 480)
    { code := Impl.Ed25519.RISCV64.Whole.verifyCode, verified := Whole.verify_framed }
    (verifyOut bConsts _) (by lit_decide)

end VG.Proof.Ed25519.RISCV64.Fn
