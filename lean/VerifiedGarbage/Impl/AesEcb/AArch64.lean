module

public import VerifiedGarbage.Impl.Aes.AArch64.Callee
public import VerifiedGarbage.Impl.CallWipe.AArch64
public import VerifiedGarbage.Impl.Zeroize.AArch64Wide
public import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Writes

/-!
# AES-ECB on AArch64

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt`, for an implementation of
`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` (`Fn.blocks`). Where the
implementation needs no `scratch`, so writes nothing in it, the function is
its code, then the vector registers it writes cleared. Otherwise it is a call
of the implementation, then of `vg_zeroize` on the whole of `scratch`
(`wiped`), then its cleanup (`scrubOf`), which clears the registers that code
writes and zeroes its 32 bytes of stack.
-/

@[expose] public section

namespace VG.Impl.AesEcb.AArch64

open VG.AArch64

/-- A call of `name`, whose code is `body`, then of `vg_zeroize` on the
2048 bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.AArch64.callWipe .x4 2048 name body "vg_zeroize" Impl.Zeroize.AArch64.zeroizeWide

namespace Fn

/-- `vg_aes_ecb_encrypt`, or `vg_aes_ecb_decrypt`, over the blocks function
`b`, as emitted. -/
def blocks (b : Impl.Aes.AArch64.Blocks) : Prog isa :=
  if b.scratch = 0 then Impl.Scrub.AArch64.withClears [] b.clear.vecs none b.code
  else Impl.Scrub.AArch64.scrubOf 32 0 (wiped b.name b.code)

end Fn

end VG.Impl.AesEcb.AArch64
