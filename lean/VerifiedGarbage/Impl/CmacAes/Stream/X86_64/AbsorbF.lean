module

public import VerifiedGarbage.Impl.CmacAes.Stream.X86_64

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb` without working space

`absorb` (`Impl/CmacAes/Stream/X86_64.lean`) over an implementation of
`vg_cmac_aes_update` that needs no working space (`vg_cmac_aes_update_aesni`),
given `scratch - 2176`: the registers it saves at `scratch + 2176` are then
at the `scratch` it is given, and its scratch buffer is only those 48 bytes.
-/

-- separate module: a definition in `Impl/CmacAes/Stream/X86_64.lean` rebuilds every AES caller on x86-64

@[expose] public section

namespace VG.Impl.CmacAes.Stream.X86_64

open VG.X86_64

/-- `absorb`, given `scratch - 2176`. -/
def absorbF (u : Impl.CmacAes.X86_64.Update) : Prog isa :=
  .seq (.block [.alu .sub .r9 (.imm (BitVec.ofNat 32 2176))]) (absorb u)

end VG.Impl.CmacAes.Stream.X86_64
