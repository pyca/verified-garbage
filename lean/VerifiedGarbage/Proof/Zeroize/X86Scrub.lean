module

public import VerifiedGarbage.Proof.Zeroize.X86
public import VerifiedGarbage.Impl.Zeroize.X86
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Zeroize.X86
meta import VerifiedGarbage.Impl.Zeroize.X86
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# `vg_zeroize` on x86, without secret residue

`vg_zeroize` calls nothing and has no frame: as emitted
(`Impl.Zeroize.X86.Fn.zeroize`), it is followed by `Impl.Scrub.X86.tail`
(`X86.Scrub.verifiedScrubbed`), which clears the registers a callee may
change, but the result's bits, the flags and `xmm0`–`xmm7`. What
the scrub needs of the code (no call, no frame, no MMX instruction) is one
Boolean, `X86.Scrub.scrubSide`, proved by evaluating the code once
(`lit_decide`). The functions that call it (AES-CBC, AES-ECB and ML-KEM's
wiped functions) call its code as the internal `vg_zeroize_core`, since they
clear what they leave themselves.
-/

@[expose] public section

namespace VG.Proof.Zeroize.X86

open VG.X86 VG.X86.Scrub

-- `vg_zeroize`'s code as a literal: the scrub's side condition
-- (`scrubSide`) is checked by evaluation (`lit_decide`).
materialize_code zeroizeLit := Impl.Zeroize.X86.zeroize

/-- `vg_zeroize` as emitted (`Impl.Zeroize.X86.Fn.zeroize`) meets its contract in constant
time and returns without secret residue. -/
theorem zeroize_scrubbed :
    VerifiedScrubbed target Impl.Zeroize.X86.Fn.zeroize (Spec.Zeroize.zeroizeContract abi) 0 :=
  verifiedScrubbed (api := Spec.Zeroize.zeroizeApi) { code := Impl.Zeroize.X86.zeroize, verified := verified }

end VG.Proof.Zeroize.X86
