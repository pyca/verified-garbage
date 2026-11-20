module

public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.Aes.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.X86.Frame
public import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Aes.Scratch
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.Aes.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Aes.X86.Frame
meta import VerifiedGarbage.Spec.Aes.Contract
meta import VerifiedGarbage.Proof.Aes.Scratch
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# AES's key expansion on x86 (32-bit), without secret residue

`vg_aes_expand_key` and `vg_aes_expand_key_aesni` read the memory on return
only within the key schedule (`expandKeyOut`, from
`Proof.Aes.expandKeyPostOut_local`): what the scrub of their frames and
calls needs (`X86.Scrub.PostOut`). Each as emitted (`Impl.Aes.X86.Fn`), which zeroes its
532 bytes of stack below `esp` and clears the registers, returns without
secret residue (`X86.Scrub.verifiedScrubbedF`: `scalar_scrubbed`,
`aesni_scrubbed`); its code is a closed term, which the kernel evaluates for
what that needs (`scrubFSide`).
-/

@[expose] public section

namespace VG.Proof.Aes.X86.Scrub

open VG.X86 VG.X86.Scrub
open Impl.StackScratch.X86 (withStackScratchWiped)

theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Aes.expandKeyContract abi stack) (Spec.Aes.expandKeySig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Aes.expandKeyPostOut_local _)

-- The code, as literals for the kernel's evaluation.
materialize_code scalarLit := withStackScratchWiped 532 3 128 Impl.Aes.X86.expandKey
materialize_code aesniLit := withStackScratchWiped 532 3 128 Impl.Aes.X86.AesNi.expandKey

/-- `vg_aes_expand_key` as emitted (`Impl.Aes.X86.Fn.expandKey`) meets its
contract in constant time and returns without secret residue. -/
theorem scalar_scrubbed :
    VerifiedScrubbed X86.target Impl.Aes.X86.Fn.expandKey (Spec.Aes.expandKeyContract X86.abi 532) 0 :=
  verifiedScrubbedF (api := Spec.Aes.expandKeyApi) {
      code := withStackScratchWiped 532 3 128 Impl.Aes.X86.expandKey
      verified := Proof.Aes.X86.scalar_expandKey_framed }
    (expandKeyOut _)

/-- `vg_aes_expand_key_aesni` as emitted (`Impl.Aes.X86.Fn.expandKeyAesni`)
meets its contract in constant time and returns without secret residue. -/
theorem aesni_scrubbed :
    VerifiedScrubbed X86.target Impl.Aes.X86.Fn.expandKeyAesni (Spec.Aes.expandKeyContract X86.abi 532) 0 :=
  verifiedScrubbedF (api := Spec.Aes.expandKeyApi) {
      suffix := "_aesni"
      code := withStackScratchWiped 532 3 128 Impl.Aes.X86.AesNi.expandKey
      verified := Proof.Aes.X86.aesni_expandKey_framed }
    (expandKeyOut _)

end VG.Proof.Aes.X86.Scrub
