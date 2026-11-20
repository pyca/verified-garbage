module

public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.X86.Frame
public import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Aes.Scratch
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
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
calls needs (`X86.Scrub.PostOut`). Each is registered with
`X86.Scrub.scrubFOf` (`scalarReg`, `aesniReg`), which zeroes its 532 bytes
of stack below `esp` and clears the registers; its code is a closed term,
which the kernel evaluates for what that needs (`scrubFSide`).
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

/-- `vg_aes_expand_key`, without secret residue. -/
def scalarReg : Registration Spec.Aes.expandKeyApi target :=
  scrubFOf {
      code := withStackScratchWiped 532 3 128 Impl.Aes.X86.expandKey
      verified := Proof.Aes.X86.scalar_expandKey_framed }
    (expandKeyOut _)

/-- `vg_aes_expand_key_aesni`, without secret residue. -/
def aesniReg : Registration Spec.Aes.expandKeyApi target :=
  scrubFOf {
      suffix := "_aesni"
      code := withStackScratchWiped 532 3 128 Impl.Aes.X86.AesNi.expandKey
      verified := Proof.Aes.X86.aesni_expandKey_framed }
    (expandKeyOut _)

end VG.Proof.Aes.X86.Scrub
