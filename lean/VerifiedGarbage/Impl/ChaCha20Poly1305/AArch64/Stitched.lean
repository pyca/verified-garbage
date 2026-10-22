module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitch
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Short
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.ShortRest
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Pad
import VerifiedGarbage.Impl.ChaCha20.AArch64.Neon4

/-!
# ChaCha20-Poly1305: AArch64, with Poly1305 inside the ChaCha20 kernel

`sealWith` and `openWith` (`../AArch64.lean`) encrypt the data with one
call and absorb it with another. With the eight-block kernel, `sealStitched`
and `openStitched` instead process the data's whole chunks of 512 bytes with
`Stitch.bulk`, which absorbs the ciphertext while it computes the keystream,
and only the rest with those calls:

* the counter is set to 1 and the stream's arguments to the data
  (`cryptSetup`); with fewer than 512 bytes, nothing more happens here;
* otherwise `x27` and `x28` are saved in the context (`[32, 48)`), the
  clamped key is stored where `Stitch.chunk` reads it (bytes 160–175 of the
  stream's working space) and the accumulator loaded into `x21`–`x23`
  (`polyIn`), the chunks run (`Stitch.bulk`), and the accumulator is reduced
  and stored, `x21` (the context) recomputed from `x0`, `x27` and `x28`
  restored, and `x22`, `x23` set to the data not yet absorbed: everything
  after the chunks when decrypting, and also the last chunk when encrypting
  (`polyOut`); the chunks use SVE2 as the stream does (`XorCallee.sve`);
* when encrypting, if data follows the chunks, the last chunk is
  absorbed while the keystream of the next four blocks is computed, and up to
  256 bytes of the rest encrypted with it (`Tail.rest`, below);
* the rest of the data is encrypted (`vg_chacha20_xor`, from where the
  chunks, or `Tail.rest`, stopped) and absorbed (from `x22`), in the order the
  direction needs; when decrypting more than `Pad.threshold` bytes, or
  between 64 and 256 or above 320 that are not whole blocks, the stream
  encrypts eight or four blocks of zeros at `ctx[768, 1280)` instead, which the rest is XORed
  with (`openRest`, which `sealRest` runs when encrypting).

The registers `x21`–`x25` and `x30` hold other values meanwhile; the
prologue saved them, and `restore` restores them.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.AArch64

open VG.AArch64
open VG.Impl.ChaCha20.AArch64 (XorCallee)
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Impl.Poly1305.AArch64 (const64)

/-- The counter set to 1, the stream's arguments set to the data (as in
`cryptWith`), and `x5 = 1` if there are fewer than 512 bytes. -/
def cryptSetup : List Instr :=
  ([.movz .w .x9 1 0, .str .w .x9 .x21 112, .addImm .x .x0 .x21 64, mov .x1 .x22,
    mov .x2 .x23, .addImm .x .x3 .x21 128] : List Instr) ++ VG.Impl.ChaCha20.AArch64.Mixed8.check

/-- `x27` and `x28` saved, the clamped key stored at `ctx[288, 304)`, and the
accumulator loaded into `x21`–`x23` (`x21`, the base, last). -/
def polyIn : List Instr :=
  ([.str .x .x27 .x21 32, .str .x .x28 .x21 40] : List Instr) ++
  const64 .x24 0x0ffffffc0fffffff ++
  ([.ldr .x .x25 .x21 472, .logic .and .x .x25 .x25 .x24, .str .x .x25 .x21 288] : List Instr) ++
  const64 .x24 0x0ffffffc0ffffffc ++
  ([.ldr .x .x25 .x21 480, .logic .and .x .x25 .x25 .x24, .str .x .x25 .x21 296,
   .ldr .x .x22 .x21 456, .ldr .x .x23 .x21 464, .ldr .x .x21 .x21 448] : List Instr)

/-- The accumulator reduced (`Poly1305.AArch64.Radix64.reduce`) and stored,
`x21`, `x27` and `x28` restored, and in `x22`, `x23` the data not yet
absorbed. -/
def polyOut (enc : Bool) : List Instr :=
  [mov .x4 .x21, mov .x5 .x22, mov .x6 .x23] ++ VG.Impl.Poly1305.AArch64.Radix64.reduce ++
  ([.subImm .x .x21 .x0 64, .str .x .x4 .x21 448, .str .x .x5 .x21 456, .str .x .x6 .x21 464,
   .ldr .x .x27 .x21 32, .ldr .x .x28 .x21 40] : List Instr) ++
  (if enc then [.subImm .x .x22 .x1 512, .addImm .x .x23 .x2 512] else [mov .x22 .x1, mov .x23 .x2])

/-! ## The rest after the chunks when encrypting

After the chunks (`Stitch.bulk`) and `polyOut true`, `seal` still has to
absorb the last chunk and to encrypt the rest. If a rest remains, `seal`
computes the keystream of its first four blocks (`kernel`, the four-block
kernel `Neon4`; with SVE2, each vector XOR and rotation is one XAR) while the
integer units absorb the last chunk (`Poly.block`: two blocks, and then three
after each double round), rather than calling `vg_chacha20_xor` for the rest
and then absorbing the chunk with it. The accumulator is loaded back into
`x21`–`x23` for that, and the clamped key stored again, as before the chunks
(`polyIn`); our caller's `x20` is kept in `x8`. The keystream goes to
`ctx[128, 384)`, the stream's working space, which holds nothing more after
the chunks but the clamped key the blocks read, at `[288, 304)`: it is zeroed
after the rounds, and the kernel XORs the keystream into it.

Then the accumulator is stored again (`polyOut false`), the counter advanced
past the four blocks, and the first `min(rest, 256)` bytes XORed with the
keystream (`Short.xorKs`); the stream's arguments are set to whatever
follows, which `vg_chacha20_xor` encrypts as without this code, and `x22`,
`x23` to the rest, which is absorbed after.

The branches are on the length only, and the addresses are the context, the
data and the chunk plus constants, so only the pointers and the lengths can
affect timing.
-/

namespace Tail

/-- A double round of the four-block kernel, with SVE2's XAR if `sve`. -/
def doubleRound (sve : Bool) : List Instr :=
  VG.Impl.ChaCha20.AArch64.Mixed5.roundOps.flatMap (VG.Impl.ChaCha20.AArch64.Neon4.Op.codeFor sve)

/-- Our caller's `x20` kept in `x8`, `x20` pointed at the last chunk (`x22`
after `polyOut true`), the rest (`x1`) kept in `x7`, and, as before the
chunks, the clamped key stored and the accumulator loaded (`polyIn`). -/
def load : List Instr := [mov .x8 .x20, mov .x20 .x22, mov .x7 .x1] ++ polyIn

/-- Two blocks of the chunk, and the rounds' count. -/
def start : List Instr := Poly.block ++ Poly.block ++ [.movz .x .x4 10 0]

/-- A double round, and three blocks. -/
def round (sve : Bool) : Prog isa :=
  .seq (.block (doubleRound sve)) (.block (Stitch.absorb3 ++ [.subImm .x .x4 .x4 1]))

def rounds (sve : Bool) : Prog isa := .loop (round sve) (.nonzero .x .x4)

/-- The buffer `x3[0, 256)` zeroed and the keystream XORed into it. -/
def finish : List Instr :=
  [.vop (.logic .eor .v28 .v28 .v28)] ++ (List.range 16).map (fun i => .strq .v28 .x3 (16 * i)) ++
    [mov .x1 .x3] ++ VG.Impl.ChaCha20.AArch64.Neon4.finish

/-- The keystream of four blocks into `x3[0, 256)`, with the 512 bytes from
`x20` absorbed. -/
def kernel (sve : Bool) : Prog isa :=
  .seq (.block VG.Impl.ChaCha20.AArch64.Neon4.setup)
    (.seq (.block start) (.seq (rounds sve) (.block finish)))

/-- The accumulator stored, `x22` set to the rest and `x23` to its length,
our caller's `x20` restored, and the counter advanced past the four blocks. -/
def out : List Instr :=
  polyOut false ++ [mov .x22 .x7, mov .x20 .x8] ++ VG.Impl.ChaCha20.AArch64.Mixed5.counter 4

/-- `x23 = min(x2, 256)`. -/
def take : Prog isa :=
  .seq (.block [.lsr .x .x9 .x2 8])
    (.ite (.zero .x .x9) (.block [mov .x23 .x2]) (.block [.movz .x .x23 256 0]))

/-- The stream's arguments set to what follows the bytes XORed, and `x23` to
the rest's length. -/
def args : List Instr :=
  [.add .x .x1 .x22 .x23, .sub .x .x2 .x2 .x23, .add .x .x23 .x2 .x23,
   .addImm .x .x0 .x21 64, .addImm .x .x3 .x21 128]

/-- The rest after the chunks, from `polyOut true`'s state. -/
def rest (sve : Bool) : Prog isa :=
  .seq (.block load)
    (.seq (kernel sve) (.seq (.block out) (.seq take (.seq Short.xorKs (.block args)))))

end Tail

/-- After the chunks: the accumulator stored (`polyOut`); when encrypting,
if a rest remains, its first four blocks' keystream computed while the last
chunk is absorbed, and up to 256 bytes of it encrypted (`Tail.rest`). -/
def afterBulk (sve enc : Bool) : Prog isa :=
  if enc then .seq (.block (polyOut true)) (.ite (.zero .x .x2) (.block []) (Tail.rest sve))
  else .block (polyOut enc)

/-- The whole chunks. -/
def cryptStitched (sve enc : Bool) : Prog isa :=
  .seq (.block cryptSetup)
    (.ite (.nonzero .x .x5) (.block [])
      (.seq (.block polyIn) (.seq (Stitch.bulk sve enc) (afterBulk sve enc))))

/-- The data from `x22` (`x23` bytes) encrypted or decrypted, continuing the
stream's counter. -/
def cryptRest (c : XorCallee) : Prog isa :=
  .seq (.block [.addImm .x .x0 .x21 64, mov .x1 .x22, mov .x2 .x23, .addImm .x .x3 .x21 128])
    (.call c.name c.code)

/-- The keystream of `n` bytes (256: four blocks; 512: eight) from the
stream's counter at `ctx[768, 768 + n)`, the data XORed with it, and
`ctx[768, 1280)` zeroed before and after (as `Pad.cryptPad`, but from the
counter the chunks left). -/
def padRest (c : XorCallee) (n : Nat) : Prog isa :=
  .seq (.block (Pad.zero ++ [.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 768, .movz .x .x2 (BitVec.ofNat 16 n) 0,
      .addImm .x .x3 .x21 128]))
    (.seq (.call c.name c.code) (.seq (Short.xorKsFrom 768) (.block Pad.zero)))

/-- `x9 = 0` iff `1 ≤ x23 ≤ 2^k`: `(x23 - 1) >> k`. -/
def atMost (k : Nat) : List Instr := [.subImm .x .x9 .x23 1, .lsr .x .x9 .x9 k]

/-- `x9 = 0` iff `x23 ≥ 321` (for `x23` below `2^63`): `(x23 - 321) >> 63`. -/
def above320 : List Instr := [.subImm .x .x9 .x23 321, .lsr .x .x9 .x9 63]

/-- The rest (`x22`, `x23` bytes, fewer than 512), when decrypting or (by
`sealRest`) encrypting. Above `Pad.threshold`, through the keystream of eight blocks (`padRest c 512`).
Otherwise with `cryptRest`, unless the rest is not whole blocks and the
stream (`Small.lean`) would compute two blocks with the scalar block
function, or a partial last block after its vector kernel: from 65 to 255
bytes, through the keystream of four blocks (`padRest c 256`), and from 321
(only without SVE2, whose threshold is 320), of eight. With a single scalar
block (at most 64 bytes, or 257 to 320) the stream is the faster. -/
def openRest (c : XorCallee) : Prog isa :=
  .seq (.block [.addImm .x .x9 .x23 (511 - Pad.threshold c.sve), .lsr .x .x9 .x9 9])
    (.ite (.zero .x .x9)
      (.seq (.block [.lsl .x .x9 .x23 58])
        (.ite (.zero .x .x9) (cryptRest c)
          (.seq (.block (atMost 6))
            (.ite (.zero .x .x9) (cryptRest c)
              (.seq (.block (atMost 8))
                (.ite (.zero .x .x9) (padRest c 256)
                  (.seq (.block above320)
                    (.ite (.zero .x .x9) (padRest c 512) (cryptRest c)))))))))
      (padRest c 512))

/-- The rest when encrypting, after the chunks and `Tail.rest` (the stream's
arguments: `x1`, `x2` bytes, fewer than 512), by `openRest`. `x22` and
`x23` (the data to absorb) are kept meanwhile in `x24` and `x25`, whose
additional data is already absorbed. -/
def sealRest (c : XorCallee) : Prog isa :=
  .seq (.block [mov .x24 .x22, mov .x25 .x23, mov .x22 .x1, mov .x23 .x2])
    (.seq (openRest c) (.block [mov .x22 .x24, mov .x23 .x25]))

/-- `sealStitched` but for the tag. -/
def sealStitchedMain (c : XorCallee) : Prog isa :=
  .seq prologue
  (.seq (macPad .x24 .x25)
  (.seq (.block lengths)
  (.seq (cryptStitched c.sve true)
  (.seq (sealRest c)
  (.seq (macPad .x22 .x23)
    absorbLengths)))))

def sealStitched (c : XorCallee) : Prog isa := .seq (sealStitchedMain c) sealTail

/-- `openStitched` up to the tag computed. -/
def openStitchedMain (c : XorCallee) : Prog isa :=
  .seq prologue
  (.seq (macPad .x24 .x25)
  (.seq (.block lengths)
  (.seq (cryptStitched c.sve false)
  (.seq (macPad .x22 .x23)
  (.seq (openRest c)
  (.seq absorbLengths
    (finalizeTo 48)))))))

def openStitched (c : XorCallee) : Prog isa := .seq (openStitchedMain c) openTail

/-! ## Decrypting 449 to 511 bytes

`OpenPad.openMain` is `open` up to the tag for 449 to 511 bytes: as
`Pad.openMain`, the kernel computes the keystream of eight blocks into the
context, but in one chunk with Poly1305 absorbing the data's first 448 bytes
(`Stitch.bulkPad`) rather than in a pass of its own:

* after the lengths, `ctx[704, 1280)` is zeroed, and the stream's arguments
  set: the counter to 1, the keystream's buffer of 512 bytes at
  `ctx + 256 + len` (`ctx[705, 1279)`), and the data's address in `x2`,
  which the chunk keeps in `x19`, where its phases read it; then, as
  before the chunks, the clamped key is stored and the accumulator loaded
  (`polyIn`);
* the chunk (`Stitch.bulkPad`), and the accumulator stored (`polyOut`); the
  analysis knows registers only, so the length is recovered from the
  buffer's address (`recover`), and the data's from `x2`;
* the rest of the data (1 to 63 bytes after the first 448) absorbed with its
  padding, then the lengths; the data XORed with the keystream (`xorKs`)
  and `ctx[704, 1280)` zeroed again.

Every address is the context, the data or the additional data plus
constants and the lengths, and every branch is on the lengths.
-/

namespace OpenPad

/-- `ctx[704, 1280)` zeroed, through `v0`. -/
def zero : List Instr :=
  .vop (.logic .eor .v0 .v0 .v0) :: (List.range 36).map fun i => .strq .v0 .x21 (704 + 16 * i)

/-- The counter set to 1, and the stream's arguments: the state, the buffer at
`ctx + 256 + len`, the data's address, and the working space. -/
def args : List Instr :=
  [.movz .w .x9 1 0, .str .w .x9 .x21 112, .addImm .x .x0 .x21 64, .add .x .x1 .x21 .x23,
   .addImm .x .x1 .x1 256, mov .x2 .x22, .addImm .x .x3 .x21 128]

/-- From `polyOut false`'s `x22` (the buffer) and `x23` (the data): the data in
`x22`, its length in `x23`, and the rest after 448 bytes in `x24`, `x25`. -/
def recover : List Instr :=
  [.sub .x .x25 .x22 .x21, .subImm .x .x25 .x25 704, mov .x22 .x23, .addImm .x .x24 .x22 448,
   .addImm .x .x23 .x25 448]

/-- The data XORed with the keystream at `ctx + 256 + len`. -/
def xorKs : Prog isa :=
  Short.xorKsWith [mov .x9 .x22, .add .x .x10 .x21 .x23, .addImm .x .x10 .x10 256, .lsr .x .x11 .x23 4]

/-- `open` up to the tag computed, for 449 to 511 bytes. -/
def openMain (sve : Bool) : Prog isa :=
  .seq prologue
  (.seq (macPad .x24 .x25)
  (.seq (.block lengths)
  (.seq (.block (zero ++ args ++ polyIn))
  (.seq (Stitch.bulkPad sve)
  (.seq (.block (polyOut false ++ recover))
  (.seq (macPad .x24 .x25)
  (.seq absorbLengths
  (.seq xorKs
  (.seq (.block zero)
    (finalizeTo 48))))))))))

end OpenPad

/-- `open` from `Short.lo` to 511 bytes: `ShortRest.lean`'s code up to
`Pad.threshold`, then from 449 bytes `OpenPad.openMain`, and between them
(with SVE2) `Pad.openMain`. -/
def openRoute (c : XorCallee) : Prog isa :=
  .seq (.block (Pad.split c.sve)) (.ite (.zero .x .x9) (ShortRest.openMain c)
    (if c.sve then
      .seq (.block (Pad.split false)) (.ite (.zero .x .x9) (Pad.openMain c) (OpenPad.openMain true))
    else OpenPad.openMain false))

/-- The code up to the tag (`sealTail`, `openTail`), which the taint analysis
checks on its own: for `Short.lo c.sve` to 511 bytes `Pad.lean`'s route when
encrypting and `openRoute` when decrypting (to `ShortRest.lean`'s code, which
runs `Short.lean`'s up to 256, or `Pad.lean`'s, or `OpenPad`'s), and
otherwise stitched with the eight-block kernel or not. -/
def sealMainCode (c : XorCallee) (stitched : Bool) : Prog isa :=
  .seq (.block (Short.check c.sve))
    (.ite (.zero .x .x9) (Pad.sealRoute c)
      (if stitched then sealStitchedMain c else sealMain c))

def openMainCode (c : XorCallee) (stitched : Bool) : Prog isa :=
  .seq (.block (Short.check c.sve))
    (.ite (.zero .x .x9) (openRoute c)
      (if stitched then openStitchedMain c else openMain c))

/-- The code for a stream backend. -/
def sealCode (c : XorCallee) (stitched : Bool) : Prog isa := .seq (sealMainCode c stitched) sealTail

def openCode (c : XorCallee) (stitched : Bool) : Prog isa := .seq (openMainCode c stitched) openTail

end VG.Impl.ChaCha20Poly1305.AArch64
