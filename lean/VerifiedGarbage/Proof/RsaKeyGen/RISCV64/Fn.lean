module

public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.KeyInit
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.KeyInit
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.Verified
public import VerifiedGarbage.Proof.Variants.MillerRabin.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Rsa.RISCV64.Scrub

/-!
# RSA key generation on RISC-V, as emitted

`vg_rsa_generate_init` with its cleanup
(`Impl.RsaKeyGen.RISCV64.KeyInit.Fn.init`) meets its contract in constant
time and returns without secret residue (`VerifiedScrubbed`, by
`RISCV64.Scrub.verifiedScrubbed`), which is what its registration binds.

The key search, `vg_rsa_generate`, is generic over the Miller-Rabin round
(`Proof.Variants.MillerRabin.RISCV64`): what its cleanup needs of its code
(`Scrub.scrubSide`: the depth of its frames, and that it calls nothing
indirectly) does not yet follow from what each round proves of its own code,
so its registrations are still built here with `RISCV64.Scrub.scrubOf`
(`keySearchSide`), for its registration file to bind.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Fn

open VG.RISCV64 VG.RISCV64.Scrub
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)
open VG.Proof.Rsa.RISCV64 (InvLaw)

theorem init_scrubbed :
    VerifiedScrubbed target Impl.RsaKeyGen.RISCV64.KeyInit.Fn.init (Spec.RsaKeyGen.keyInitContract abi) 32 :=
  verifiedScrubbed (api := Spec.RsaKeyGen.keyInitApi) (W := 0)
    { code := Impl.RsaKeyGen.RISCV64.KeyInit.init, verified := KeyInit.init_verified }
    Proof.Rsa.RISCV64.Scrub.keyInitOut (by lit_decide)

/-- `vg_rsa_generate` over each Miller-Rabin round, scrubbed. -/
def keySearchRegs [InvLaw] : List (Registration Spec.RsaKeyGen.keySearchApi RISCV64.target) :=
  Proof.Variants.MillerRabin.RISCV64.variants.attach.map
    fun (v : { v : RoundImpl // v ∈ Proof.Variants.MillerRabin.RISCV64.variants }) =>
      scrubOf {
        suffix := v.1.suffix
        code := Generate.genCode v.1
        verified := Generate.gen_verified v.1 }
        (Proof.Rsa.RISCV64.Scrub.keySearchOut Generate.tables Generate.stackUse)
        Generate.stackUse (Spec.RsaKeyGen.keySearchSig.retBits 64) (Generate.keySearchSide v.1 v.2)

end VG.Proof.RsaKeyGen.RISCV64.Fn
