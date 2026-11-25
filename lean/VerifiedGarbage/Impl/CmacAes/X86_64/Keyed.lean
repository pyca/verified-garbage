module

public import VerifiedGarbage.Impl.CmacAes.X86_64

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_update` over the bitsliced AES, keys once

`vg_cmac_aes_update` (`Impl/CmacAes/X86_64.lean`) chains its blocks by
calls of `vg_aes_ctr32` on one block at a time, and the bitsliced
implementation puts the whole key schedule in slices at every call. `updateK`
does that once, with `vg_aes_ctr32_keys` (`keys`, the bitsliced engine's),
into the scratch buffer the calls share, then chains the blocks by calls of
`vg_aes_ctr32_keyed` (`ctr32K`: `vg_aes_ctr32` without its key setup), which
leaves the round keys as they are. Both are given the working space 512 bytes
into the scratch buffer, as `vg_aes_ctr32` is (`Ctr32.scrOff`).

* `keys(schedule = rdi, rounds = rsi, scratch = r9)`.
* `ctr32K(schedule = rdi, rounds = rsi, counter = rdx, data = rcx, n = r8, scratch = r9)`
  does not read `schedule`.
-/

@[expose] public section

namespace VG.Impl.CmacAes.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64

/-- `vg_aes_ctr32_keys`: the round keys in slices, in the scratch buffer. -/
def keys : Prog isa := Sse.keys

/-- `vg_aes_ctr32_keyed`: `vg_aes_ctr32` from round keys already in the
scratch buffer. -/
def ctr32K : Prog isa :=
  .seq (.block [.mov .r11 (.reg .rcx), .alu .test .r8 (.reg .r8)]) (.ite .e (.block []) Sse.ctrLoop)

/-- `vg_aes_ctr32_keyed`, to call with its working space 512 bytes into the
scratch buffer (`ctrCall`). -/
def ctrK : Ctr32 := { name := "vg_aes_ctr32_keyed", code := ctr32K, scrOff := 512 }

/-- The arguments of `keys`: the key schedule and the rounds (ours) and the
working space 512 bytes into the scratch buffer (`r15`). -/
def keysArgs : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .r9 (.reg .r15),
   .alu .add .r9 (.imm (BitVec.ofNat 32 512))]

/-- `vg_cmac_aes_update` over the bitsliced AES: the round keys bitsliced
once, if there are blocks, then each block by `vg_aes_ctr32_keyed`. -/
def updateK : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.ite .e (.block [])
        (.seq (.seq (.block keysArgs) (.call "vg_aes_ctr32_keys" keys)) (.loop (body ctrK) .ne)))
      (.block restore))

end VG.Impl.CmacAes.X86_64
