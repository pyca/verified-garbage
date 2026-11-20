module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Impl.Sha512.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Spec.Sha512.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha512.X86_64.Shared
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Spec.Sha512.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sha512.X86_64.Shared
meta import VerifiedGarbage.Proof.Sha512.Stream
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha512.PostOut
meta import VerifiedGarbage.Proof.Sha512.PostOut

/-!
# The SHA-512 family's `init` on x86-64, without secret residue

`vg_sha384_init`, `vg_sha512_init`, `vg_sha512_224_init` and
`vg_sha512_256_init`, each followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`), which clears the registers it writes. Their
postconditions read the memory on return only within the streaming state
(`Stream.repr_congr`). HMAC, PBKDF2 and Ed25519 call their code as the
internal `vg_<alg>_init_core` (`Proof.Pbkdf2.Md.X86_64.Sha512.hash`), which
clears what it leaves itself.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64

open VG.X86_64 VG.X86_64.Scrub

theorem initOut (iv : Spec.Sha512.HashValue) :
    PostOut (Spec.Sha512.initContract X86_64.abi iv) (Spec.Sha512.initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.initPost_out iv 64)

/-! ## The functions as emitted -/

theorem init384_codeSp : (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_384).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sha512.init384Api`'s function as emitted (`Impl.Sha512.X86_64.Fn.init384`) meets its contract in
constant time and returns without secret residue. -/
theorem init384_scrubbed :
    VerifiedScrubbed target Impl.Sha512.X86_64.Fn.init384 (Spec.Sha512.init384Api.contract X86_64.abi 0) 0 :=
  verifiedScrubbedSel (api := Spec.Sha512.init384Api)
    { code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_384
      verified := Shared.init Spec.Sha512.H0_384
      spSafe := init384_codeSp }
    .sse [] (initOut Spec.Sha512.H0_384) (RScrub.pubOk_nil _) (by taint_decide)

theorem init384_spSafe : Impl.Sha512.X86_64.Fn.init384.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe init384_codeSp

theorem init512_codeSp : (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sha512.init512Api`'s function as emitted (`Impl.Sha512.X86_64.Fn.init512`) meets its contract in
constant time and returns without secret residue. -/
theorem init512_scrubbed :
    VerifiedScrubbed target Impl.Sha512.X86_64.Fn.init512 (Spec.Sha512.init512Api.contract X86_64.abi 0) 0 :=
  verifiedScrubbedSel (api := Spec.Sha512.init512Api)
    { code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512
      verified := Shared.init Spec.Sha512.H0_512
      spSafe := init512_codeSp }
    .sse [] (initOut Spec.Sha512.H0_512) (RScrub.pubOk_nil _) (by taint_decide)

theorem init512_spSafe : Impl.Sha512.X86_64.Fn.init512.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe init512_codeSp

theorem init512_224_codeSp : (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_224).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sha512.init512_224Api`'s function as emitted (`Impl.Sha512.X86_64.Fn.init512_224`) meets its contract in
constant time and returns without secret residue. -/
theorem init512_224_scrubbed :
    VerifiedScrubbed target Impl.Sha512.X86_64.Fn.init512_224 (Spec.Sha512.init512_224Api.contract X86_64.abi 0) 0 :=
  verifiedScrubbedSel (api := Spec.Sha512.init512_224Api)
    { code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_224
      verified := Shared.init Spec.Sha512.H0_512_224
      spSafe := init512_224_codeSp }
    .sse [] (initOut Spec.Sha512.H0_512_224) (RScrub.pubOk_nil _) (by taint_decide)

theorem init512_224_spSafe : Impl.Sha512.X86_64.Fn.init512_224.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe init512_224_codeSp

theorem init512_256_codeSp : (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_256).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sha512.init512_256Api`'s function as emitted (`Impl.Sha512.X86_64.Fn.init512_256`) meets its contract in
constant time and returns without secret residue. -/
theorem init512_256_scrubbed :
    VerifiedScrubbed target Impl.Sha512.X86_64.Fn.init512_256 (Spec.Sha512.init512_256Api.contract X86_64.abi 0) 0 :=
  verifiedScrubbedSel (api := Spec.Sha512.init512_256Api)
    { code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_256
      verified := Shared.init Spec.Sha512.H0_512_256
      spSafe := init512_256_codeSp }
    .sse [] (initOut Spec.Sha512.H0_512_256) (RScrub.pubOk_nil _) (by taint_decide)

theorem init512_256_spSafe : Impl.Sha512.X86_64.Fn.init512_256.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe init512_256_codeSp
end VG.Proof.Sha512.X86_64
