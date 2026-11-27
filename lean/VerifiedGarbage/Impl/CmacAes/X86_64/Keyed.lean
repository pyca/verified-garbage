module

public import VerifiedGarbage.Impl.CmacAes.X86_64

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_update` over the bitsliced AES, keys once

`vg_cmac_aes_update` (`Impl/CmacAes/X86_64.lean`) chains its blocks by
calls of `vg_aes_ctr32` on one block at a time, and the bitsliced
implementation puts the whole key schedule in slices at every call. `updateK`
does that once, with `vg_aes_ctr32_keys` (`keys`, the bitsliced engine's),
into the scratch buffer the calls share, then chains the blocks by calls of
`vg_aes_ctr32_keyed` (`ctr32K`: `vg_aes_ctr32` without its key setup, a block at a
time), which leaves the round keys as they are. Both are given the working space 512 bytes
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

/-! ## One block

A batch of eight blocks (`Sse.encrypt8`) spends a tenth of its time taking
blocks to slices and back. For one block, block 0 of the batch, what the
other seven are does not matter, and both are much shorter. -/

/-- The counter block's halves, read as they were written (a 16-byte load of
two 8-byte stores would wait for them). -/
def load1 : List Instr :=
  [.mov .rax (.mem (at_ .rdx 0)), .mov .r10 (.mem (at_ .rdx 8)), .xop (.movq .xmm0 .rax), .xop (.movq .xmm4 .r10)]

/-- The slices `q (i + j)`, `0 < j < 4`, of slice `q i`'s groups of four bits. -/
def spread (i : Nat) : List Instr :=
  ([1, 2, 3] : List Nat).flatMap fun j => [Sse.mv (Sse.q (i + j)) (Sse.q i), Sse.srq (Sse.q (i + j)) j]

/-- From the block's halves (`q 0` and `q 4`) to slices, of which only block
0's bits are of it. -/
def toBs1 : List Instr :=
  Sse.exchange1 (Sse.q 0) (Sse.q 4) 3 ++ Sse.exchange1 (Sse.q 0) (Sse.q 4) 4 ++
    Sse.exchange1 (Sse.q 0) (Sse.q 4) 5 ++ Sse.exchange1 (Sse.q 0) (Sse.q 4) 2 ++ spread 0 ++ spread 4

/-- Block 0's bits of the slices `q (i + j)`, `j < 4`, together in `q i` (the
mask of block 0's bits is in `xmm9`). -/
def collect (i : Nat) : List Instr :=
  ([Sse.an (Sse.q i) .xmm9] : List Instr) ++ ([1, 2, 3] : List Nat).flatMap fun j =>
    [Sse.an (Sse.q (i + j)) .xmm9, Sse.slq (Sse.q (i + j)) j, Sse.px (Sse.q i) (Sse.q (i + j))]

/-- From slices to block 0's halves, in `q 0` and `q 4`. -/
def fromBs1 : List Instr :=
  ([Sse.ldx .xmm9 (Sse.maskSlot 0), Sse.ldx .xmm8 (Sse.maskSlot 1), Sse.an .xmm9 .xmm8] : List Instr) ++
    collect 0 ++ collect 4 ++ Sse.exchange1 (Sse.q 0) (Sse.q 4) 2 ++ Sse.exchange1 (Sse.q 0) (Sse.q 4) 5 ++
    Sse.exchange1 (Sse.q 0) (Sse.q 4) 4 ++ Sse.exchange1 (Sse.q 0) (Sse.q 4) 3

/-- The block XORed into one of the data, to `r11`, and the pointers moved on. -/
def xor1 : List Instr :=
  [Sse.unpckl .xmm0 .xmm4, .movdquLoad .xmm1 (at_ .rcx 0), Sse.px .xmm0 .xmm1, .movdquStore (at_ .r11 0) .xmm0,
   .alu .add .rcx (.imm 16), .alu .add .r11 (.imm 16), .mov .rdi (.imm 1)]

/-- One block in counter mode, with the batch's rounds (`Sse.encrypt8`). -/
def ctr1 : Prog isa :=
  .seq (.block (load1 ++ (toBs1 ++ (Sse.pairs ++
      ([.mov Sse.kp (.reg .r9), .alu .add Sse.kp (.imm (BitVec.ofNat 32 Sse.keysOff))] : List Instr) ++
      (Sse.addRoundKey Sse.q .xmm8 .xmm9 ++ [Sse.nextKey])))))
    (.seq (.loop (.block (Sse.roundA ++ Sse.roundB ++ ([.alu .sub .r10 (.imm 1)] : List Instr))) .ne)
      (.block (Sse.roundA ++ Sse.lastB ++ (fromBs1 ++ (xor1 ++ Sse.ctrNext)))))

/-- `vg_aes_ctr32_keyed`: `vg_aes_ctr32` from round keys already in the
scratch buffer, a block at a time. -/
def ctr32K : Prog isa :=
  .seq (.block [.mov .r11 (.reg .rcx), .alu .test .r8 (.reg .r8)]) (.ite .e (.block []) (.loop ctr1 .ne))

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
