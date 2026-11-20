module

public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Framework.X86.ScrubWiped
public import VerifiedGarbage.Impl.Aes.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.X86.Frame
public import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Aes.Scratch
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Framework.X86.ScrubWiped
meta import VerifiedGarbage.Impl.Aes.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Aes.X86.Frame
meta import VerifiedGarbage.Spec.Aes.Contract
meta import VerifiedGarbage.Proof.Aes.Scratch
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# AES's key expansion on x86 (32-bit), without secret residue

`vg_aes_expand_key` and `vg_aes_expand_key_aesni` run their code in a frame
that it wipes itself before it releases it, and that code calls nothing, so
nothing it wrote is left on the stack. Each as emitted (`Impl.Aes.X86.Fn`),
which then clears the registers alone, returns without secret residue
(`X86.Scrub.verifiedScrubbedWiped`, for any variant of the code: `wiped`;
`scalar_scrubbed`, `aesni_scrubbed`); its code is a closed term, which the
kernel evaluates for what that needs (`wipedSide`).
-/

@[expose] public section

namespace VG.Proof.Aes.X86.Scrub

open VG.X86 VG.X86.Scrub
open Impl.StackScratch.X86 (withStackScratchWiped)

/-- The code `c` of `vg_aes_expand_key_scratch` or of one of its variants, in
its frame, which it wipes itself, then the clearing of the registers alone:
it meets the contract and returns without secret residue. -/
theorem wiped {c : Prog isa} (h : Verified X86.target c (Proof.Aes.expandKeyScratchContract X86.abi))
    (hs : wipedSide c 532 3 128 = true) :
    VerifiedScrubbed X86.target (Impl.Scrub.X86.scrub 0 (withStackScratchWiped 532 3 128 c))
      (Spec.Aes.expandKeyContract X86.abi 532) 0 :=
  verifiedScrubbedWiped (sig := Spec.Aes.expandKeySig) (nm := "scratch") (e := .u64) (n := 64)
    (pre := Spec.Aes.expandKeyPre X86.abi.ptrBits) (post := Spec.Aes.expandKeyPost X86.abi.ptrBits)
    (bytes := 532) (words := 128) (Proof.Aes.expandKey_scratch h) (by decide) (by decide) hs
    (Proof.Aes.expandKeyPre_local _) (Proof.Aes.expandKeyPost_local _) (Proof.Aes.expandKeyPostOut_local _)
    Proof.Aes.X86.expandKeyFrameSat_pre rfl

-- The code, as literals for the kernel's evaluation.
materialize_code scalarLit := withStackScratchWiped 532 3 128 Impl.Aes.X86.expandKey
materialize_code aesniLit := withStackScratchWiped 532 3 128 Impl.Aes.X86.AesNi.expandKey

/-- `vg_aes_expand_key` as emitted (`Impl.Aes.X86.Fn.expandKey`) meets its
contract in constant time and returns without secret residue. -/
theorem scalar_scrubbed :
    VerifiedScrubbed X86.target Impl.Aes.X86.Fn.expandKey (Spec.Aes.expandKeyContract X86.abi 532) 0 :=
  wiped (Proof.Aes.X86.expandKey_verified) (by lit_decide)

/-- `vg_aes_expand_key_aesni` as emitted (`Impl.Aes.X86.Fn.expandKeyAesni`)
meets its contract in constant time and returns without secret residue. -/
theorem aesni_scrubbed :
    VerifiedScrubbed X86.target Impl.Aes.X86.Fn.expandKeyAesni (Spec.Aes.expandKeyContract X86.abi 532) 0 :=
  wiped (Proof.Aes.X86.AesNi.expandKey_verified
      ⟨Proof.Aes.X86.AesNi.expand128_ok, Proof.Aes.X86.AesNi.expand192_ok, Proof.Aes.X86.AesNi.expand256_ok⟩)
    (by lit_decide)

end VG.Proof.Aes.X86.Scrub
