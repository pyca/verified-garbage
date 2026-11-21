module

public import VerifiedGarbage.Impl.AesGcm.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.StackScratch.X86

/-!
# AES-OCB: x86 (32-bit) implementation

`vg_aes_ocb_init(key, key_len, ctx, scratch)`,
`vg_aes_ocb_seal(ctx, rounds, nonce, nonce_len, aad, aad_len, data, len, tag, tag_len, work)`
and `vg_aes_ocb_open` with the same arguments (`Spec/Ocb/Contract.lean`),
cdecl (every argument on the stack), with the working space (`scratch`,
`work`) as a last argument, which a frame on the stack allocates
(`Impl.StackScratch.X86.withStackScratch`), composed of calls of the
verified `vg_aes_expand_key_scratch`, `vg_aes_encrypt_blocks` and
`vg_aes_decrypt_blocks`, and generic over their implementations
(`Callees`): each function is emitted once for each. The algorithm is
x86-64's (`Impl/AesOcb/X86_64.lean`), on 32-bit words; the conventions are
x86's AES-GCM's (`Impl/AesGcm/X86.lean`):

* `init` expands the key into the key context and enciphers a zero block in
  place, at byte 240, for `L_*`.
* The whole blocks of the data are processed in three passes over the data,
  in place: XOR each block with its offset `Offset_i` (and, for `seal`, add
  it to the checksum), encipher or decipher all of them in one call, then
  XOR each with its offset again (and, for `open`, add it to the
  checksum). The offsets are recomputed in the third pass, from `Offset_0`.
  During a pass the offset and the checksum are in `xmm0` and `xmm1`
  (loaded from `W` before it, stored back after it), and each block goes
  through `xmm3` (`movdqu`, `pxor`: SSE2, the target's baseline). A pass
  takes four blocks at a time while it can (`quad`): the first three of
  them have `ntz(i)` 0, 1 and 0, so their `L_{ntz(i)}` are the table's
  first two entries, read where they are.
* `L_$` and `L_0` are `L_*` doubled once and twice. A doubling reads the
  four big-endian words of a block, shifts each left by one bit with the
  top bit of the next, and reduces the last by `{87}` through a mask from
  the first's top bit (`dbl`). The table (`ltable`, before the passes)
  holds `L_0` to `L_5` at `W + tblO`, each the one before doubled: of
  these, `L_j` for every `j` with `2^j` at most the number of whole blocks,
  so every `L_{ntz(i)}` of a block index `i` that is no multiple of 64.
* For a block of the data, `L_{ntz(i)}` is read where `lAddr` finds it,
  from the public `i`: in the table, at the entry reached by stepping once
  for each trailing zero bit of `i`, unless `i` is a multiple of 64, when
  it is `L_0` doubled `ntz(i)` times at `W + lO` (`lNtz`, with the offset
  and the checksum kept in `W` meanwhile).
* `HASH(K, A)` copies up to 8 blocks of the associated data at a time,
  each XORed with its offset, to `W + bufO`, and enciphers them there; for
  each of its blocks `L_{ntz(i)}` is `L_0` doubled `ntz(i)` times
  (`lNtz`), by a loop on the public `i`.
* `Offset_0` takes the bits `bottom … bottom + 127` of `Stretch` (§4.2),
  where `bottom` is the last 6 bits of the nonce, which is secret: the
  192-bit `Stretch`, six words at `W + stO`, is shifted left by 1, 2, 4, 8,
  16 and 32 bits, each shift kept or not by a mask from a bit of `bottom`
  (`stage`).
* `seal` computes the tag at `W` and copies its first `tag_len` bytes to
  `tag` (`tagOut`).
* `open` copies the received tag from `tag` to `W` (`recv`), compares the
  tags without a branch and masks the data with `0 − ok`, 16 bytes at a time
  (in `xmm0`) and then the last `len mod 16` one at a time.

The model has no left shift: `x << a` is `ror x, 32 − a` with the `a` low
bits masked off, and `x << 1` an addition.

## The working space `W` (`work`, `scratch`: 2560 bytes)

`[0, 16)`: the tag (out of `seal`; the received one, for `open`); then the
offset, the checksum, the sum of `HASH`, `L_$`, `L_0`, the current
`L_{ntz(i)}`, a block for one call; `[128, 144)`: our caller's `ebx`,
`esi`, `edi`, `ebp`; then the computed tag of `open`, the offset of `HASH`,
the arguments but `work`, `bottom`, `ntz`'s count, `Offset_0`, `Stretch`
and the variables of the pieces; `[288, 384)`: the table, of `L_0` to
`L_5` at most; `[384, 512)`: 8 blocks of the associated data;
`[512, 2560)`: the working space of the functions called.

## Registers

`ebp` holds `W` throughout; the functions called preserve it, and `ebx`,
`esi` and `edi`. While on a string, its pointer is in `esi` and `i` in
`edi`; counts are in `ebx` or in `W`. Everything else is reloaded from `W`
(the SSE registers hold nothing across a call).
Each call pushes its arguments in a frame of its own: `vg_aes_*_blocks`
five, `vg_aes_expand_key_scratch` four, with the return address 24 bytes of stack
at most. The callee's working space is passed in `ebp`, moved there before
the frame and back after it.

Only the pointers, the lengths, `rounds` and `tag_len` (and for `open`,
whether the tag is right) affect timing.
-/

@[expose] public section

namespace VG.Impl.AesOcb.X86

open VG.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry restore zero4 copyLoop xorLoop Fn)

/-- The implementations called: AES's encryption and decryption of whole
blocks and its key expansion. -/
structure Callees where
  enc : Fn
  dec : Fn
  key : Fn

/-! ## The working space -/

abbrev tagO : Nat := 0
abbrev ofsO : Nat := 16
abbrev ckO : Nat := 32
abbrev sumO : Nat := 48
abbrev ldO : Nat := 64
abbrev l0O : Nat := 80
abbrev lO : Nat := 96
abbrev tmpO : Nat := 112
abbrev t2O : Nat := 144
abbrev ohO : Nat := 160
abbrev ctxO : Nat := 176
abbrev rndO : Nat := 180
abbrev nO : Nat := 184
abbrev nlO : Nat := 188
abbrev aadO : Nat := 192
abbrev alenO : Nat := 196
abbrev dataO : Nat := 200
abbrev lenO : Nat := 204
abbrev tgO : Nat := 208
abbrev tlO : Nat := 212
abbrev botO : Nat := 216
/-- `i`, shifted right while `L_{ntz(i)}` is computed. -/
abbrev kO : Nat := 220
abbrev o0O : Nat := 224
/-- `Stretch`, six words, the most significant first. -/
abbrev stO : Nat := 240
/-- The blocks of the associated data left, while hashing. -/
abbrev hlO : Nat := 264
/-- Where the next block of a chunk goes. -/
abbrev fpO : Nat := 268
/-- The blocks of a chunk. -/
abbrev cntO : Nat := 272
/-- The bytes of a string after its whole blocks. -/
abbrev restO : Nat := 276
/-- The whole blocks of the data. -/
abbrev nbO : Nat := 280
/-- `open`'s result. -/
abbrev okO : Nat := 284
/-- The table of `L_0` to `L_5`. -/
abbrev tblO : Nat := 288
abbrev bufO : Nat := 384
abbrev scrO : Nat := 512

/-! ## Blocks of `W` -/

/-- `W + d ← W + s`. -/
def copy16 (s d : Nat) : List Instr :=
  [.mov .eax (slot s), .store (at_ .ebp d) .eax, .mov .eax (slot (s + 4)), .store (at_ .ebp (d + 4)) .eax,
   .mov .eax (slot (s + 8)), .store (at_ .ebp (d + 8)) .eax, .mov .eax (slot (s + 12)),
   .store (at_ .ebp (d + 12)) .eax]

/-- Word `k` of `W + d ← W + d ⊕ (b + s)`. -/
def xorW (b : Reg) (s d k : Nat) : List Instr :=
  [.mov .eax (slot (d + k)), .alu .xor .eax (.mem (at_ b (s + k))), .store (at_ .ebp (d + k)) .eax]

/-- `W + d ← W + d ⊕ (b + s)`. -/
def xor16 (b : Reg) (s d : Nat) : List Instr := xorW b s d 0 ++ xorW b s d 4 ++ xorW b s d 8 ++ xorW b s d 12

/-- Word `j` (below 3) of `double`: the word shifted left by one bit, with
the top bit of the next. -/
def dblW (b : Reg) (s d j : Nat) : List Instr :=
  [.mov .eax (.mem (at_ b (s + 4 * j))), .bswap .eax, .alu .add .eax (.reg .eax),
   .mov .ecx (.mem (at_ b (s + 4 * j + 4))), .bswap .ecx, .shift .shr .ecx 31, .alu .or .eax (.reg .ecx),
   .bswap .eax, .store (at_ .ebp (d + 4 * j)) .eax]

/-- `W + d ← double(b + s)` (§2): the block is big-endian, so each word is
byte-reversed, shifted left by one bit with the top bit of the next, and
byte-reversed back; the carry out of the first reduces the last by `{87}`
through a mask (in `edx`). The words are written in order, each after the
next is read, so `b + s` may be `W + d`. -/
def dbl (b : Reg) (s d : Nat) : List Instr :=
  ([.mov .eax (.mem (at_ b s)), .bswap .eax, .shift .shr .eax 31, .mov .edx (imm 0), .alu .sub .edx (.reg .eax),
   .alu .and .edx (imm 0x87)] : List Instr) ++
  dblW b s d 0 ++ dblW b s d 1 ++ dblW b s d 2 ++
  ([.mov .eax (.mem (at_ b (s + 12))), .bswap .eax, .alu .add .eax (.reg .eax), .alu .xor .eax (.reg .edx),
   .bswap .eax, .store (at_ .ebp (d + 12)) .eax] : List Instr)

/-- `W + lO ← L_{ntz(i)}` for `i ≥ 1` in `edi`: `L_0` doubled while the
low bit of `i` (at `W + kO`, shifted right each time) is zero. -/
def lNtz : Prog isa :=
  .seq (.block (copy16 l0O lO ++ ([.mov .eax (.reg .edi), .store (at_ .ebp kO) .eax, .alu .test .eax (imm 1)] : List Instr)))
    (.ite .e (.loop (.block (dbl .ebp lO lO ++ ([.mov .eax (slot kO), .shift .shr .eax 1,
        .store (at_ .ebp kO) .eax, .alu .test .eax (imm 1)] : List Instr))) .e)
      (.block []))

/-! ## Calls -/

section
variable (c : Callees)

/-- `vg_aes_*_blocks(eax, ecx, edx, ebx, ebp)`. -/
def blocksFrame (f : Fn) : Prog isa :=
  .frame (.push [.ebp, .ebx, .edx, .ecx, .eax]) (.call f.name f.code) (.pop .eax 5)

/-- `ENCIPHER` (`c.enc`) or `DECIPHER` (`c.dec`) of the `ebx` blocks at `edx`
(set up by `args`), with the key context's schedule and the working space
at `W + scrO`. -/
def callBlocks (f : Fn) (args : List Instr) : Prog isa :=
  .seq (.block (args ++ ([.mov .eax (slot ctxO), .mov .ecx (slot rndO), .alu .add .ebp (imm scrO)] : List Instr)))
    (.seq (blocksFrame f) (.block [.alu .sub .ebp (imm scrO)]))

end

/-- One block of `W`, at `W + d`. -/
def oneBlock (d : Nat) : List Instr := [.mov .edx (.reg .ebp), .alu .add .edx (imm d), .mov .ebx (imm 1)]

/-! ## `L_$`, `L_0` and `Offset_0` -/

/-- `L_$` and `L_0` from `L_*` (bytes 240–255 of the key context). -/
def lsetup : List Instr := ([.mov .ebx (slot ctxO)] : List Instr) ++ dbl .ebx 240 ldO ++ dbl .ebp ldO l0O

/-- `W + d ← pad(S)` (§4.1), `S` the bytes at `esi`, as many as `W + cO`
says (1 to 15): zeros, the bytes copied, and `0x80` after them. -/
def padTo (d cO : Nat) : Prog isa :=
  .seq (.block (zero4 d ++ ([.mov .edi (.reg .esi), .mov .edx (.reg .ebp), .alu .add .edx (imm d),
      .mov .ecx (slot cO)] : List Instr)))
    (.seq copyLoop (.block [.mov .eax (imm 0x80), .store8 (at_ .edx 0) .al]))

/-- The nonce block (§4.2), `num2str(TAGLEN mod 128, 7) ‖ zeros ‖ 1 ‖ N`, at
`W + tmpO`: zeros, the nonce's bytes copied to the end of the block, the 1
in the byte before them, and `TAGLEN`'s bits in the top of the first byte.
Then `bottom` (its last 6 bits) to `W + botO`, and those bits cleared. -/
def nonceBlock : Prog isa :=
  .seq (.block (zero4 tmpO ++ ([.mov .edi (slot nO), .mov .ecx (slot nlO), .mov .edx (.reg .ebp),
      .alu .add .edx (imm (tmpO + 16)), .alu .sub .edx (.reg .ecx)] : List Instr)))
    (.seq copyLoop
      (.block [.mov .ecx (slot nlO), .mov .edx (.reg .ebp), .alu .add .edx (imm (tmpO + 15)),
        .alu .sub .edx (.reg .ecx), .mov .eax (imm 1), .store8 (at_ .edx 0) .al,
        .mov .eax (slot tlO), .alu .and .eax (imm 15), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
        .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
        .movzx8 .ecx (at_ .ebp tmpO), .alu .or .ecx (.reg .eax), .store8 (at_ .ebp tmpO) .cl,
        .movzx8 .eax (at_ .ebp (tmpO + 15)), .mov .ecx (.reg .eax), .alu .and .ecx (imm 63),
        .store (at_ .ebp botO) .ecx, .alu .and .eax (imm 0xc0), .store8 (at_ .ebp (tmpO + 15)) .al]))

/-- `x << a` for `x` in `ecx` (from 1 to 31). -/
def shlEcx (a : Nat) : List Instr :=
  [.shift .ror .ecx (32 - a), .alu .and .ecx (.imm (BitVec.allOnes 32 <<< a))]

/-- Word `j` of `Stretch` replaced by `x'` (in `ecx`) if the mask in `ebx`
is all ones: `x ← x ⊕ ((x' ⊕ x) ∧ mask)`, `x` in `eax`. -/
def selW (j : Nat) : List Instr :=
  [.alu .xor .ecx (.reg .eax), .alu .and .ecx (.reg .ebx), .alu .xor .eax (.reg .ecx),
   .store (at_ .ebp (stO + 4 * j)) .eax]

/-- Word `j` (below 5) of the shift by `a` (from 1 to 31):
`x' = (x << a) ∨ (next >> (32 − a))`. -/
def stageW (a j : Nat) : List Instr :=
  ([.mov .eax (slot (stO + 4 * j)), .mov .ecx (.reg .eax)] : List Instr) ++ shlEcx a ++
  ([.mov .edx (slot (stO + 4 * j + 4)), .shift .shr .edx (32 - a), .alu .or .ecx (.reg .edx)] : List Instr) ++ selW j

/-- The mask of a stage, all ones if bit `k` of `bottom` is set, to `ebx`. -/
def stageMask (k : Nat) : List Instr :=
  ([.mov .eax (slot botO)] : List Instr) ++ (if k = 0 then [] else [.shift .shr .eax k]) ++
  ([.alu .and .eax (imm 1), .mov .ebx (imm 0), .alu .sub .ebx (.reg .eax)] : List Instr)

/-- One stage of the shift of `Stretch`: left by `a` (from 1 to 31) bits if
bit `k` of `bottom` is set. -/
def stage (k a : Nat) : List Instr :=
  stageMask k ++ stageW a 0 ++ stageW a 1 ++ stageW a 2 ++ stageW a 3 ++ stageW a 4 ++
  ([.mov .eax (slot (stO + 20)), .mov .ecx (.reg .eax)] : List Instr) ++ shlEcx a ++ selW 5

/-- Word `j` (below 5) of the shift by 32: `x' = next`. -/
def stage32W (j : Nat) : List Instr := ([.mov .eax (slot (stO + 4 * j)), .mov .ecx (slot (stO + 4 * j + 4))] : List Instr) ++ selW j

/-- The last stage: left by 32 bits if bit 5 of `bottom` is set. -/
def stage32 : List Instr :=
  stageMask 5 ++ stage32W 0 ++ stage32W 1 ++ stage32W 2 ++ stage32W 3 ++ stage32W 4 ++
  ([.mov .eax (slot (stO + 20)), .mov .ecx (imm 0)] : List Instr) ++ selW 5

/-- Word `j` of `Stretch`'s tail: `((x << 8) ∨ (y >> 24)) ⊕ x`, `x` and `y`
words `j` and `j + 1` of `Ktop`. -/
def tailW (j : Nat) : List Instr :=
  ([.mov .eax (slot (stO + 4 * j)), .mov .ecx (.reg .eax)] : List Instr) ++ shlEcx 8 ++
  ([.mov .edx (slot (stO + 4 * j + 4)), .shift .shr .edx 24, .alu .or .ecx (.reg .edx), .alu .xor .ecx (.reg .eax),
   .store (at_ .ebp (stO + 16 + 4 * j)) .ecx] : List Instr)

/-- `Stretch = Ktop ‖ (Ktop[1..64] ⊕ Ktop[9..72])` from `Ktop` at `W + tmpO`,
to `W + stO`, as numbers. -/
def stretch : List Instr :=
  [0, 1, 2, 3].flatMap (fun j => [.mov .eax (slot (tmpO + 4 * j)), .bswap .eax, .store (at_ .ebp (stO + 4 * j)) .eax]) ++
  tailW 0 ++ tailW 1

/-- `Offset_0`, the high 128 bits of `Stretch` shifted left by `bottom`, to
`W + ofsO` and `W + o0O`. -/
def offset0 : List Instr :=
  stretch ++ stage 0 1 ++ stage 1 2 ++ stage 2 4 ++ stage 3 8 ++ stage 4 16 ++ stage32 ++
  [0, 1, 2, 3].flatMap (fun j => [.mov .eax (slot (stO + 4 * j)), .bswap .eax,
    .store (at_ .ebp (ofsO + 4 * j)) .eax, .store (at_ .ebp (o0O + 4 * j)) .eax])

section
variable (c : Callees)

/-- `Offset_0`. -/
def nonce : Prog isa :=
  .seq nonceBlock (.seq (callBlocks c.enc (oneBlock tmpO)) (.block offset0))

/-! ## `HASH` -/

/-- One block of the associated data (at `esi`) XORed with its offset to
`W + fpO`'s address, `i` in `edi`; on to the next (ZF set when the chunk's
`ebx` blocks are done). -/
def hashFill : Prog isa :=
  .seq lNtz
    (.block (xor16 .ebp lO ohO ++ ([.mov .edx (slot fpO)] : List Instr) ++
      [0, 4, 8, 12].flatMap (fun k => [.mov .eax (.mem (at_ .esi k)), .alu .xor .eax (slot (ohO + k)),
        .store (at_ .edx k) .eax]) ++
      ([.alu .add .edx (imm 16), .store (at_ .ebp fpO) .edx, .alu .add .esi (imm 16), .alu .add .edi (imm 1),
       .alu .sub .ebx (imm 1)] : List Instr)))

/-- Add the `W + cntO` blocks at `W + bufO` to the sum. -/
def hashSum : Prog isa :=
  .seq (.block [.mov .ebx (slot cntO), .mov .edx (.reg .ebp), .alu .add .edx (imm bufO)])
    (.loop (.block (xor16 .edx 0 sumO ++ ([.alu .add .edx (imm 16), .alu .sub .ebx (imm 1)] : List Instr))) .ne)

/-- A chunk of up to 8 blocks: `min(8, blocks left)`, fill, encipher, add;
then on to the next (ZF set when none are left). -/
def hashChunk : Prog isa :=
  .seq (.block [.mov .ebx (slot hlO), .alu .cmp .ebx (imm 8)])
    (.seq (.ite .b (.block []) (.block [.mov .ebx (imm 8)]))
      (.seq (.block [.store (at_ .ebp cntO) .ebx, .mov .eax (.reg .ebp), .alu .add .eax (imm bufO),
          .store (at_ .ebp fpO) .eax])
        (.seq (.loop hashFill .ne)
          (.seq (callBlocks c.enc [.mov .edx (.reg .ebp), .alu .add .edx (imm bufO), .mov .ebx (slot cntO)])
            (.seq hashSum
              (.block [.mov .eax (slot hlO), .alu .sub .eax (slot cntO), .store (at_ .ebp hlO) .eax]))))))

/-- The rest of the associated data (`W + restO` bytes at `esi`), padded,
XORed with the offset `⊕ L_*`, enciphered and added to the sum. -/
def hashRest : Prog isa :=
  .seq (.block (([.mov .ebx (slot ctxO)] : List Instr) ++ xor16 .ebx 240 ohO))
    (.seq (padTo bufO restO)
      (.seq (.block (xor16 .ebp ohO bufO))
        (.seq (callBlocks c.enc (oneBlock bufO)) (.block (xor16 .ebp bufO sumO)))))

/-- `HASH(K, A)` to `W + sumO`. -/
def hash : Prog isa :=
  .seq (.block (zero4 sumO ++ zero4 ohO ++
      ([.mov .esi (slot aadO), .mov .eax (slot alenO), .mov .ecx (.reg .eax), .alu .and .ecx (imm 15),
       .store (at_ .ebp restO) .ecx, .shift .shr .eax 4, .store (at_ .ebp hlO) .eax, .mov .edi (imm 1),
       .alu .test .eax (.reg .eax)] : List Instr)))
    (.seq (.ite .e (.block []) (.loop (hashChunk c) .ne))
      (.seq (.block [.mov .eax (slot restO), .alu .test .eax (.reg .eax)])
        (.ite .e (.block []) (hashRest c))))

end

/-! ## The whole blocks -/

/-- The table from `L_j` on, with `k` more entries at most:
`L_{j+1} = double(L_j)`, 16 bytes after it, and so on, while `2^{j+1}` is at
most the number of whole blocks (at `W + nbO`). -/
def ltableFrom (j : Nat) : Nat → Prog isa
  | 0 => .block []
  | k + 1 =>
    .seq (.block [.mov .eax (slot nbO), .alu .cmp .eax (imm (2 ^ (j + 1)))])
      (.ite .b (.block [])
        (.seq (.block (dbl .ebp (tblO + 16 * j) (tblO + 16 * (j + 1)))) (ltableFrom (j + 1) k)))

/-- The table at `W + tblO`: `L_0`, copied, then `L_j` for `j` from 1 to 5
with `2^j` at most the number of whole blocks. -/
def ltable : Prog isa := .seq (.block (copy16 l0O tblO)) (ltableFrom 0 5)

/-- `edx ←` the address of `L_{ntz(i)}`, for `i ≥ 1` in `edi`. If `i` is a
multiple of 64, `W + lO`, where `lNtz` computes it, with the offset and the
checksum (`xmm0`, `xmm1`) kept at `W + ofsO` and `W + ckO` meanwhile.
Otherwise its entry in the table, `W + tblO + 16 ntz(i)`: 16 bytes on for
each time `i` (in `eax`, shifted right each time) is even. -/
def lAddr : Prog isa :=
  .seq (.block [.mov .eax (.reg .edi), .alu .test .eax (imm 63)])
    (.ite .e
      (.seq (.block [.movdquStore (at_ .ebp ofsO) .xmm0, .movdquStore (at_ .ebp ckO) .xmm1])
        (.seq lNtz (.block [.movdquLoad .xmm0 (at_ .ebp ofsO), .movdquLoad .xmm1 (at_ .ebp ckO),
          .mov .edx (.reg .ebp), .alu .add .edx (imm lO)])))
      (.seq (.block [.mov .edx (.reg .ebp), .alu .add .edx (imm tblO), .alu .test .eax (imm 1)])
        (.ite .ne (.block [])
          (.loop (.block [.alu .add .edx (imm 16), .shift .shr .eax 1, .alu .test .eax (imm 1)]) .e))))

/-- `Offset ← Offset ⊕ L_{ntz(i)}`, the offset in `xmm0` and `L_{ntz(i)}` at
`edx`. -/
def ofsDx : List Instr := [.movdquLoad .xmm2 (at_ .edx 0), .xop (.bin .pxor .xmm0 .xmm2)]

/-- The checksum, in `xmm1`, `⊕=` the block in `xmm3`. -/
def addCk : List Instr := [.xop (.bin .pxor .xmm1 .xmm3)]

/-- The block in `xmm3` `⊕=` the offset in `xmm0`. -/
def xorOfs : List Instr := [.xop (.bin .pxor .xmm3 .xmm0)]

/-- The block at `esi` loaded to `xmm3`, through `body`, and stored back;
then on to the next. -/
def blockOps (body : List Instr) : List Instr :=
  ([.movdquLoad .xmm3 (at_ .esi 0)] : List Instr) ++ body ++
  ([.movdquStore (at_ .esi 0) .xmm3, .alu .add .esi (imm 16), .alu .add .edi (imm 1)] : List Instr)

/-- The `ebx` blocks at `esi` (`ebx > 0`), one at a time, `i` in `edi`:
each through `body` after its offset. -/
def single (body : List Instr) : Prog isa :=
  .loop (.seq lAddr (.block (ofsDx ++ blockOps body ++ ([.alu .sub .ebx (imm 1)] : List Instr)))) .ne

/-- `Offset ← Offset ⊕ L_j`, the offset in `xmm0` and `L_j` in the table. -/
def ofsAt (j : Nat) : List Instr :=
  [.movdquLoad .xmm2 (at_ .ebp (tblO + 16 * j)), .xop (.bin .pxor .xmm0 .xmm2)]

/-- A block whose `ntz(i)` is `j`: its offset, then the block through
`body`. -/
def stepAt (j : Nat) (body : List Instr) : List Instr := ofsAt j ++ blockOps body

/-- The blocks at `esi`, four at a time while four are left (`ebx ≥ 4`),
from an `i` (in `edi`) that is 1 more than a multiple of 4: `ntz(i)` is 0,
1 and 0 for the first three, and the fourth's `L_{ntz(i)}` is where `lAddr`
finds it. -/
def quad (body : List Instr) : Prog isa :=
  .loop (.seq (.block (stepAt 0 body ++ stepAt 1 body ++ stepAt 0 body))
    (.seq lAddr (.block (ofsDx ++ blockOps body ++
      ([.alu .sub .ebx (imm 4), .alu .cmp .ebx (imm 4)] : List Instr))))) .ae

/-- A pass over the `ebx` whole blocks of the data at `esi` (`ebx > 0`),
with `i` from 1 in `edi`: the offset and the checksum in `xmm0` and `xmm1`,
from `W` and back; four blocks at a time, then the last three or fewer one
at a time. -/
def pass (body : List Instr) : Prog isa :=
  .seq (.block [.movdquLoad .xmm0 (at_ .ebp ofsO), .movdquLoad .xmm1 (at_ .ebp ckO), .alu .cmp .ebx (imm 4)])
    (.seq (.ite .b (.block []) (quad body))
      (.seq (.block [.alu .test .ebx (.reg .ebx)])
        (.seq (.ite .e (.block []) (single body))
          (.block [.movdquStore (at_ .ebp ofsO) .xmm0, .movdquStore (at_ .ebp ckO) .xmm1]))))

/-- The start of a pass: `esi` the data, `ebx` its whole blocks, `i = 1`. -/
def passStart : List Instr := [.mov .esi (slot dataO), .mov .ebx (slot nbO), .mov .edi (imm 1)]

section
variable (c : Callees)

/-- The whole blocks, with the table: `pre` (the first pass), `f` on all of
them, `post` (the third pass, the offsets recomputed from `Offset_0`). -/
def wholeIn (f : Fn) (pre post : List Instr) : Prog isa :=
  .seq (.block passStart)
    (.seq (pass pre)
      (.seq (callBlocks f [.mov .edx (slot dataO), .mov .ebx (slot nbO)])
        (.seq (.block (copy16 o0O ofsO ++ passStart)) (pass post))))

/-- The whole blocks: the table, then the passes around `f`. -/
def whole (f : Fn) (pre post : List Instr) : Prog isa := .seq ltable (wholeIn f pre post)

/-! ## The rest of the data and the tag -/

/-- `W + t2O ← pad(P_*)`, `P_*` the `W + restO` bytes at `esi` (1 to 15),
and add it to the checksum. -/
def padCk : Prog isa := .seq (padTo t2O restO) (.block (xor16 .ebp t2O ckO))

/-- The `W + restO` bytes at `esi` XORed with `Pad` at `W + tmpO`. -/
def xorPad : Prog isa :=
  .seq (.block [.mov .edi (.reg .esi), .mov .edx (.reg .ebp), .alu .add .edx (imm tmpO), .mov .ecx (slot restO)])
    xorLoop

/-- The rest of the data (`W + restO` bytes at `esi`, 1 to 15): `Offset_* =
Offset ⊕ L_*`, `Pad = ENCIPHER(K, Offset_*)`; for `seal` (`enc`) the
checksum of the plaintext, then the XOR; for `open`, the XOR, then the
checksum. -/
def rest (enc : Bool) : Prog isa :=
  .seq (.block (([.mov .ebx (slot ctxO)] : List Instr) ++ xor16 .ebx 240 ofsO ++ copy16 ofsO tmpO))
    (.seq (callBlocks c.enc (oneBlock tmpO))
      (if enc then .seq padCk xorPad else .seq xorPad padCk))

/-- The tag, `ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)`, to `W + d`. -/
def tag (d : Nat) : Prog isa :=
  .seq (.block (copy16 ckO tmpO ++ xor16 .ebp ofsO tmpO ++ xor16 .ebp ldO tmpO))
    (.seq (callBlocks c.enc (oneBlock tmpO))
      (.block (copy16 tmpO d ++ xor16 .ebp sumO d)))

/-! ## The functions -/

/-- The entry of `seal` and `open`: our caller's registers saved in `work`
(the eleventh argument), `ebp :=` `work`, the other arguments kept. -/
def ocbEntry : Prog isa :=
  entry 10 (keep 0 ctxO ++ keep 1 rndO ++ keep 2 nO ++ keep 3 nlO ++ keep 4 aadO ++ keep 5 alenO ++
    keep 6 dataO ++ keep 7 lenO ++ keep 8 tgO ++ keep 9 tlO)

/-- `L_$` and `L_0`, and the checksum zeroed. -/
def setup : List Instr := lsetup ++ zero4 ckO

/-- The data: whole blocks, then the rest. -/
def body (enc : Bool) : Prog isa :=
  .seq (.block [.mov .ebx (slot lenO), .shift .shr .ebx 4, .store (at_ .ebp nbO) .ebx, .alu .test .ebx (.reg .ebx)])
    (.seq (.ite .e (.block [])
        (if enc then whole c.enc (addCk ++ xorOfs) xorOfs else whole c.dec xorOfs (xorOfs ++ addCk)))
      (.seq (.block [.mov .esi (slot dataO), .mov .eax (slot lenO), .mov .ecx (.reg .eax), .alu .and .ecx (imm 15),
          .store (at_ .ebp restO) .ecx, .alu .sub .eax (.reg .ecx), .alu .add .esi (.reg .eax),
          .alu .test .ecx (.reg .ecx)])
        (.ite .e (.block []) (rest c enc))))

/-- `seal` (`enc`) or `open` up to the tag, at `W + d`: the entry, the
setup, `Offset_0`, `HASH`, the data and the tag. -/
def front (enc : Bool) (d : Nat) : Prog isa :=
  .seq ocbEntry (.seq (.block setup) (.seq (nonce c) (.seq (hash c) (.seq (body c enc) (tag c d)))))

/-- The first `tag_len` bytes of the tag at `W` copied to `tag`. -/
def tagOut : Prog isa :=
  .seq (.block [.mov .edi (.reg .ebp), .mov .edx (slot tgO), .mov .ecx (slot tlO)]) copyLoop

def «seal» : Prog isa := .seq (front c true tagO) (.seq tagOut (.block restore))

/-- The received tag, the `tag_len` bytes at `tag`, copied to `W`. -/
def recv : Prog isa :=
  .seq (.block [.mov .edi (slot tgO), .mov .edx (.reg .ebp), .mov .ecx (slot tlO)]) copyLoop

/-- `open`'s comparison of the first `tag_len` bytes of the tags (at `W` and
`W + t2O`), without a branch: `W + okO ← 1` if they are equal, else 0. -/
def cmp : Prog isa :=
  .seq (.block [.mov .edx (imm 0), .mov .edi (.reg .ebp), .mov .ecx (slot tlO)])
    (.seq (.loop (.block [.movzx8 .eax (at_ .edi 0), .movzx8 .ebx (at_ .edi t2O), .alu .xor .eax (.reg .ebx),
        .alu .or .edx (.reg .eax), .alu .add .edi (imm 1), .alu .sub .ecx (imm 1)]) .ne)
      (.block [.alu .sub .edx (imm 1), .shift .shr .edx 31, .store (at_ .ebp okO) .edx]))

/-- The data's `⌊len / 16⌋` whole blocks (counted down in `eax`) ANDed with
`0 − ok` (in every word of `xmm0`), 16 bytes at a time. -/
def maskBlocks : Prog isa :=
  .loop (.block [.movdquLoad .xmm1 (at_ .edi 0), .xop (.bin .pand .xmm1 .xmm0), .movdquStore (at_ .edi 0) .xmm1,
    .alu .add .edi (imm 16), .alu .sub .eax (imm 1)]) .ne

/-- The data's last `len mod 16` bytes (counted down in `ecx`) ANDed with
`0 − ok` (in `edx`), one at a time. -/
def maskBytes : Prog isa :=
  .loop (.block [.movzx8 .eax (at_ .edi 0), .alu .and .eax (.reg .edx), .store8 (at_ .edi 0) .al,
    .alu .add .edi (imm 1), .alu .sub .ecx (imm 1)]) .ne

/-- The data (`len` bytes) masked with `0 − ok`: its whole blocks, then the
rest. -/
def mask : Prog isa :=
  .seq (.block [.mov .edi (slot dataO), .mov .ecx (slot lenO), .mov .edx (imm 0), .alu .sub .edx (slot okO),
      .xop (.movd .xmm0 .edx), .xop (.pshufd .xmm0 .xmm0 0), .mov .eax (.reg .ecx), .shift .shr .eax 4,
      .alu .and .ecx (imm 15), .alu .test .eax (.reg .eax)])
    (.seq (.ite .e (.block []) maskBlocks)
      (.seq (.block [.alu .test .ecx (.reg .ecx)]) (.ite .e (.block []) maskBytes)))

def «open» : Prog isa :=
  .seq (front c false t2O) (.seq recv (.seq cmp (.seq mask (.block (([.mov .eax (slot okO)] : List Instr) ++ restore)))))

/-! ## The key setup -/

/-- `vg_aes_expand_key(eax, ecx, edx, ebp)`. -/
def keyFrame : Prog isa :=
  .frame (.push [.ebp, .edx, .ecx, .eax]) (.call c.key.name c.key.code) (.pop .eax 4)

/-- `vg_aes_ocb_init(key, key_len, ctx, scratch)`: our caller's registers
saved in `scratch`, the key expanded into the key context (with the working
space at `scratch + scrO`), then a zero block at byte 240 enciphered in
place, for `L_*`. -/
def init : Prog isa :=
  .seq (entry 3 (keep 0 nO ++ keep 1 nlO ++ keep 2 ctxO))
    (.seq (.block [.mov .eax (slot nO), .mov .ecx (slot nlO), .mov .edx (slot ctxO), .alu .add .ebp (imm scrO)])
      (.seq (keyFrame c)
        (.seq (.block [.alu .sub .ebp (imm scrO), .mov .edx (slot ctxO), .mov .eax (imm 0),
            .store (at_ .edx 240) .eax, .store (at_ .edx 244) .eax, .store (at_ .edx 248) .eax,
            .store (at_ .edx 252) .eax, .mov .eax (.reg .edx), .mov .ecx (slot nlO), .shift .shr .ecx 2,
            .alu .add .ecx (imm 6), .alu .add .edx (imm 240), .mov .ebx (imm 1), .alu .add .ebp (imm scrO)])
          (.seq (blocksFrame c.enc) (.block (([.alu .sub .ebp (imm scrO)] : List Instr) ++ restore))))))

end

end VG.Impl.AesOcb.X86

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that it and its callees use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

namespace VG.Impl.AesOcb.X86.Fn

open VG.X86
open Impl.StackScratch.X86 (withStackScratch)

/-- `vg_aes_ocb_init` over the functions `c`, as emitted. -/
def init (c : Impl.AesOcb.X86.Callees) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 2604 (withStackScratch 2580 3 (Impl.AesOcb.X86.init c))

/-- `vg_aes_ocb_seal` over the functions `c`, as emitted. -/
def «seal» (c : Impl.AesOcb.X86.Callees) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 2632 (withStackScratch 2608 10 (Impl.AesOcb.X86.«seal» c))

/-- `vg_aes_ocb_open` over the functions `c`, as emitted. -/
def «open» (c : Impl.AesOcb.X86.Callees) : Prog isa :=
  Impl.Scrub.X86.scrubAll 32 2632 (withStackScratch 2608 10 (Impl.AesOcb.X86.«open» c))

end VG.Impl.AesOcb.X86.Fn
