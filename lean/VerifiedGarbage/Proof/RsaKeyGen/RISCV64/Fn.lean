module

public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.KeyInit
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.KeyInit
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.Verified
public import VerifiedGarbage.Proof.Variants.MillerRabin.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Rsa.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubCall
public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Fn

/-!
# RSA key generation on RISC-V, as emitted

`vg_rsa_generate_init` with its cleanup
(`Impl.RsaKeyGen.RISCV64.KeyInit.Fn.init`) meets its contract in constant
time and returns without secret residue (`VerifiedScrubbed`, by
`RISCV64.Scrub.verifiedScrubbed`), which is what its registration binds.

The key search, `vg_rsa_generate`, is generic over the Miller-Rabin round
(`Proof.Variants.MillerRabin.RISCV64`): as emitted
(`Impl.RsaKeyGen.RISCV64.Fn.keySearch`), for every round, it meets its
contract and returns without secret residue (`keySearch_scrubbed`). What its
cleanup needs of its code (`Scrub.scrubSide`) is evaluated once, with a stub of
96 bytes of stack in the place of the round (`body_stub_side`); the code with
a round is that code filled (`Scrub.Fill`), from what each round proves of its
own code where it is defined (`RoundImpl.stack`, `RoundImpl.icalls`).
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

/-- What the cleanup needs of the key search, with a stub of 96 bytes of
stack in the place of the round. -/
theorem body_stub_side :
    scrubSide (Impl.RsaKeyGen.RISCV64.Fn.body "" (holeStub 96)) 656 32 [] = true := by
  lit_decide

/-- The key search with the round `round` is its code with the stub, filled. -/
theorem body_fill {round : Prog isa} (suffix : String) (h : calleeSide round 96 = true) :
    Fill 0 [] (Impl.RsaKeyGen.RISCV64.Fn.body "" (holeStub 96))
      (Impl.RsaKeyGen.RISCV64.Fn.body suffix round) := by
  fill_calls

/-- `vg_rsa_generate` as emitted, with the Miller-Rabin round `v`: it meets
its contract in constant time and returns without secret residue. -/
theorem keySearch_scrubbed [InvLaw] (v : RoundImpl) :
    VerifiedScrubbed target (Impl.RsaKeyGen.RISCV64.Fn.keySearch v.suffix v.code)
      (Spec.RsaKeyGen.keySearchContract (abi.withConsts Generate.tables) Generate.stackUse) 32 :=
  verifiedScrubbed (api := Spec.RsaKeyGen.keySearchApi)
    { suffix := v.suffix
      code := Impl.RsaKeyGen.RISCV64.Fn.body v.suffix v.code
      verified := Generate.gen_verified v }
    (Proof.Rsa.RISCV64.Scrub.keySearchOut Generate.tables Generate.stackUse)
    (scrubSide_of_fill (body_fill v.suffix (calleeSide_of (depth_le_of_sdepth v.stack) v.icalls))
      body_stub_side (fun _ h => h) (fun _ h => absurd h List.not_mem_nil))

end VG.Proof.RsaKeyGen.RISCV64.Fn
