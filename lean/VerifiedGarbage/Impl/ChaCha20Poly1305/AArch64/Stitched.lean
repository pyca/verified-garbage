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

* the counter is set to 1 (`counterOne`; for some lengths, the one-time key is
  instead computed with the first 256 bytes' keystream, and the stitched code
  continues after them: `sealWideMain`, `openWideMain`, below) and the
  stream's arguments to the data (`cryptSetup`); with fewer than 512 bytes,
  nothing more happens here;
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
  with (`openRest`).

The registers `x21`–`x25` and `x30` hold other values meanwhile; the
prologue saved them, and `restore` restores them.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.AArch64

open VG.AArch64
open VG.Impl.ChaCha20.AArch64 (XorCallee)
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Impl.Poly1305.AArch64 (const64)

/-- The counter set to 1. -/
def counterOne : List Instr := [.movz .w .x9 1 0, .str .w .x9 .x21 112]

/-- The stream's arguments set to the data from `x22` (`x23` bytes), with the
state at `ctx + 64` (whose counter `counterOne` or `ShortRest.stash` set), and
`x5 = 1` if there are fewer than 512 bytes. -/
def cryptSetup : List Instr :=
  ([.addImm .x .x0 .x21 64, mov .x1 .x22, mov .x2 .x23, .addImm .x .x3 .x21 128] : List Instr) ++
    VG.Impl.ChaCha20.AArch64.Mixed8.check

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

/-- The rest when decrypting (`x22`, `x23` bytes, fewer than 512). Above
`Pad.threshold`, through the keystream of eight blocks (`padRest c 512`).
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

/-! ## The rest after the chunks when decrypting

After the chunks (`Stitch.bulk`) and `polyOut false`, `open` has absorbed
them all; what it still has to absorb is the rest itself, which it must
before decrypting it in place. With 65 to 256 bytes of rest (`TailO.test`),
it computes the rest's keystream as `seal` does (`Tail.kernel`'s four blocks,
into `ctx[128, 384)`), while the integer units absorb the rest's whole
blocks, up to two after each double round (`TailO.maybe`, while `x6`, the
blocks left, is not zero; at most sixteen, of twenty places), rather than
absorbing the rest and then calling `vg_chacha20_xor` on it. Then the
accumulator is stored, the rest's last partial block absorbed with its
padding (`macPad`), and the rest XORed with its keystream (`Short.xorKs`).
Shorter rests keep the stream's single scalar block (`openRest`). The
stitched code is laid out after the function's return (`Code.iteCold`), so
that the code the other lengths run keeps its addresses.

The rest's address and length are kept in `x7` and `x2` through the kernel,
and in `x24` and `x25` (free after the additional data) through `macPad`'s
call. The branches are on the length only.
-/

namespace TailO

/-- `x9 = 0` iff `65 ≤ x23 ≤ 256`: `b₂ - b₁ + 1`, with `b₁ = (x23 - 257) >> 63`
(`x23 < 257`) and `b₂ = (x23 - 65) >> 63` (`x23 < 65`), for `x23` below
`2^63`; then nine moves, which keep the block 64 bytes long with its branch,
so that the code after it keeps its alignment. -/
def test : List Instr :=
  [.subImm .x .x9 .x23 257, .lsr .x .x9 .x9 63, .subImm .x .x10 .x23 65, .lsr .x .x10 .x10 63,
    .sub .x .x9 .x10 .x9, .addImm .x .x9 .x9 1] ++ List.replicate 9 (.movz .x .x11 0 0)

/-- Our caller's `x20` kept in `x8`, `x20` pointed at the rest (`x22`), the
rest kept in `x7`, its whole blocks counted in `x6`, and, as before the
chunks, the clamped key stored and the accumulator loaded (`polyIn`). -/
def load : List Instr := [mov .x8 .x20, mov .x20 .x22, mov .x7 .x22, .lsr .x .x6 .x23 4] ++ polyIn

/-- A block of the rest, if one is left. -/
def maybe : Prog isa := .ite (.zero .x .x6) (.block []) (.block (Poly.block ++ [.subImm .x .x6 .x6 1]))

/-- Up to `k` blocks. -/
def maybes : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq maybe (maybes k)

/-- A double round, and up to `k` blocks. -/
def round (sve : Bool) (k : Nat) : Prog isa :=
  .seq (.block (Tail.doubleRound sve)) (.seq (maybes k) (.block [.subImm .x .x4 .x4 1]))

def rounds (sve : Bool) (k : Nat) : Prog isa := .loop (round sve k) (.nonzero .x .x4)

/-- The keystream of four blocks into `x3[0, 256)`, with up to `10 k` of the
whole blocks from `x20` absorbed. -/
def kernel (sve : Bool) (k : Nat) : Prog isa :=
  .seq (.block VG.Impl.ChaCha20.AArch64.Neon4.setup)
    (.seq (.block [.movz .x .x4 10 0]) (.seq (rounds sve k) (.block Tail.finish)))

/-- The accumulator stored, our caller's `x20` restored, `x22` and `x23` set
to the rest's last partial block, and the rest kept in `x24`, `x25`. -/
def out : List Instr :=
  polyOut false ++ [mov .x22 .x20, .add .x .x23 .x7 .x2, .sub .x .x23 .x23 .x20, mov .x20 .x8,
    mov .x24 .x7, mov .x25 .x2]

/-- The rest decrypted, its whole blocks absorbed with its keystream's
rounds, and its last partial block before it is XORed. -/
def rest (sve : Bool) : Prog isa :=
  .seq (.block load)
  (.seq (kernel sve 2)
  (.seq (.block out)
  (.seq (macPad .x22 .x23)
  (.seq (.block [mov .x22 .x24, mov .x23 .x25])
    Short.xorKs))))

end TailO

/-! ## Decrypting 513 (or 577) to 704 bytes: the one-time key from the stream

Before the chunks, `openStitchedMain` computes the one-time key with the
scalar block function (`prologue`), about as long as the stitched pass of
four blocks. From `keyLo` to 704 bytes, `OpenKey.openMain` instead takes it from
a call of the stream, which computes the keystream of counters 0 to 7 with
the eight-block kernel, and absorbs all the data in a stitched pass of four
blocks:

* after the prologue's first block (the ChaCha20 state for counter 0 at
  `ctx[64, 128)`), the state is copied to `ctx[640, 704)` (`copy`), since the
  stream leaves its state unspecified, `ctx[768, 1280)` zeroed (`Pad.zero`),
  and the stream encrypts it from the copy (`args`): the one-time key is its
  first 32 bytes, at `ctx[768, 800)`, and the keystream of the data's first
  448 bytes at `ctx[832, 1280)`;
* Poly1305 is initialized with the key, and absorbs the additional data;
* the counter at `ctx + 112` is set to 8, and, as `TailO.rest` does for the
  rest after the chunks, the four blocks of counters 8 to 11 computed into
  `ctx[128, 384)` while the data's whole blocks, at most 44, are absorbed, up
  to five after each double round, then its last partial block;
* the data's first 448 bytes are XORed with their keystream at
  `ctx + 832`, the rest with theirs at `ctx + 128`; the lengths are
  absorbed, and `ctx[768, 1280)` is zeroed again.

The branches are on the length only, and the addresses are the context, the
data and the additional data plus constants.
-/

namespace OpenKey

/-- Word `k` of the state at `ctx[64, 128)` copied to `ctx[640, 704)`, through `w9`. -/
def copyW (k : Nat) : List Instr := [.ldr .w .x9 .x21 (64 + 4 * k), .str .w .x9 .x21 (640 + 4 * k)]

/-- The state copied. -/
def copy : List Instr := (List.range 16).flatMap copyW

/-- The stream's arguments: the copy, `ctx[768, 1280)`, and the working space. -/
def args : List Instr :=
  [.addImm .x .x0 .x21 640, .addImm .x .x1 .x21 768, .movz .x .x2 512 0, .addImm .x .x3 .x21 128]

/-- Poly1305's arguments: its state, and the key at `ctx + 768`. -/
def keyArgs : List Instr := [.addImm .x .x0 .x21 448, .addImm .x .x1 .x21 768]

/-- The counter set to 8, and the kernel's arguments: the state, the buffer
`ctx[128, 384)` and the data's length in `x2`. -/
def pre : List Instr :=
  [.movz .w .x9 8 0, .str .w .x9 .x21 112, .addImm .x .x0 .x21 64, .addImm .x .x3 .x21 128,
    mov .x2 .x23]

/-- The data's first 448 bytes XORed with their keystream at `ctx + 832`. -/
def xorFirst : Prog isa :=
  .seq (.block [mov .x14 .x23, .movz .x .x23 448 0])
    (.seq (Short.xorKsFrom 832) (.block [mov .x23 .x14]))

/-- The rest of the data, after 448 bytes. -/
def skip : List Instr := [.addImm .x .x22 .x22 448, .subImm .x .x23 .x23 448]

/-- `open` up to the tag computed, for 513 to 704 bytes. -/
def openMain (c : XorCallee) : Prog isa :=
  .seq (.block (save ++ moves ++ initState ++ ([.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 128] : List Instr)))
  (.seq (.block (copy ++ Pad.zero ++ args))
  (.seq (.call c.name c.code)
  (.seq (.block keyArgs)
  (.seq (.call "vg_poly1305_init" Impl.Poly1305.AArch64.init)
  (.seq (macPad .x24 .x25)
  (.seq (.block lengths)
  (.seq (.block (pre ++ TailO.load))
  (.seq (TailO.kernel c.sve 5)
  (.seq (.block TailO.out)
  (.seq (macPad .x22 .x23)
  (.seq (.block [mov .x22 .x24, mov .x23 .x25])
  (.seq xorFirst
  (.seq (.block skip)
  (.seq Short.xorKs
  (.seq absorbLengths
  (.seq (.block Pad.zero)
    (finalizeTo 48)))))))))))))))))

end OpenKey

/-- `seal` but for the tag, from the counter set to 1 (`counterOne`) after the
one-time key's block (`prologue`). -/
def sealStitchedMain (c : XorCallee) : Prog isa :=
  .seq prologue
  (.seq (macPad .x24 .x25)
  (.seq (.block lengths)
  (.seq (.block counterOne)
  (.seq (cryptStitched c.sve true)
  (.seq (.call c.name c.code)
  (.seq (macPad .x22 .x23)
    absorbLengths))))))

def sealStitched (c : XorCallee) : Prog isa := .seq (sealStitchedMain c) sealTail

/-- `openStitched` up to the tag computed. -/
def openStitchedMain (c : XorCallee) : Prog isa :=
  .seq prologue
  (.seq (macPad .x24 .x25)
  (.seq (.block lengths)
  (.seq (.block counterOne)
  (.seq (cryptStitched c.sve false)
  (.seq (.block TailO.test)
  (.seq (Code.iteCold (.zero .x .x9) (TailO.rest c.sve) (.seq (macPad .x22 .x23) (openRest c)))
  (.seq absorbLengths
    (finalizeTo 48))))))))

/-! ## The one-time key with the first 256 bytes

For some lengths from 768 bytes (`route`), `sealWideMain` and `openWideMain`
compute the one-time key with the keystream of the first 256 bytes, in one
pass of `Short.lean`'s kernel of five blocks rather than with the scalar
block function before the chunks: the state is copied with counter 5
(`ShortRest.stash`), and after the additional data those bytes are XORed with
their keystream (`ShortRest.first`) and absorbed (`absorbFirst`), in the order
the direction needs, and `x22`, `x23` set to the data after them
(`skipFirst`), from where `cryptStitched` continues. -/

/-- The data's first 256 bytes absorbed. -/
def absorbFirst : Prog isa :=
  .seq (.block [.addImm .x .x0 .x21 448, mov .x1 .x22, .movz .x .x2 16 0])
    (.call "vg_poly1305_blocks" Impl.Poly1305.AArch64.Radix64.blocks)

/-- `x22` and `x23` set to the data after its first 256 bytes. -/
def skipFirst : List Instr := [.addImm .x .x22 .x22 256, .subImm .x .x23 .x23 256]

/-- `sealStitchedMain`, with the one-time key from the pass of five blocks. -/
def sealWideMain (c : XorCallee) : Prog isa :=
  .seq (Short.prologue c.sve)
  (.seq (.block ShortRest.stash)
  (.seq (macPad .x24 .x25)
  (.seq (.block lengths)
  (.seq ShortRest.first
  (.seq absorbFirst
  (.seq (.block skipFirst)
  (.seq (cryptStitched c.sve true)
  (.seq (.call c.name c.code)
  (.seq (macPad .x22 .x23)
    absorbLengths)))))))))

/-- `openStitchedMain`, with the one-time key from the pass of five blocks. -/
def openWideMain (c : XorCallee) : Prog isa :=
  .seq (Short.prologue c.sve)
  (.seq (.block ShortRest.stash)
  (.seq (macPad .x24 .x25)
  (.seq absorbFirst
  (.seq ShortRest.first
  (.seq (.block lengths)
  (.seq (.block skipFirst)
  (.seq (cryptStitched c.sve false)
  (.seq (macPad .x22 .x23)
  (.seq (openRest c)
  (.seq absorbLengths
    (finalizeTo 48)))))))))))

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

/-- The lengths `sealWideMain` and `openWideMain` take: from 768 bytes, those
whose rest after whole chunks of 512 (`r`) is in `[lo, lo + 2 ^ sh)`, where
the measurements found them faster (on Neoverse N2: seal 769, 896 and 1350
bytes with SVE2, 896 and 1350 without; open 768, 769, 896 and 1350 with SVE2,
768 and 769 without); elsewhere, the shorter rest they leave after the
chunks or whole chunks shifted by 256 bytes cost more than the pass saves. -/
def wideLo (sve enc : Bool) : Nat := if enc then (if sve then 257 else 321) else 256
def wideSh (sve enc : Bool) : Nat := if enc || sve then 9 else 6

/-- `x9 = 0` iff `wideLo ≤ r < wideLo + 2 ^ wideSh`, with `r` the length
modulo 512: `(r - wideLo) >> wideSh`, which wraps around below. From 768
bytes `r ≥ 256` holds; below, `Short.check` leaves this code only lengths
under 64 or from 512 to 767, whose `r` is below 256. The eleven `x10`
writes keep the block 64 bytes long with its branch, so that the code after
it (`sealStitchedMain` and `openStitchedMain`, for the other lengths, laid
out after the branch) keeps the alignment it had before this check
(`Short.check`'s comment). -/
def route (sve enc : Bool) : List Instr :=
  [.lsl .x .x9 .x5 55, .lsr .x .x9 .x9 55, .subImm .x .x9 .x9 (wideLo sve enc),
    .lsr .x .x9 .x9 (wideSh sve enc)] ++ List.replicate 11 (.movz .x .x10 0 0)

/-- The shortest length `OpenKey.openMain` takes: 513 with SVE2. Without
it, from 513 to 576 bytes the stitched code's rest (1 to 64 bytes) goes to
the stream, cheaper there than the pass of four blocks without XAR; from 577
it computes that pass already (`TailO`), and the one-time key's block is
what `OpenKey.openMain` saves (Neoverse N2: decrypting 513 bytes 9.9% faster
with SVE2, 8.8% slower without). -/
def keyLo (sve : Bool) : Nat := if sve then 513 else 577

/-- `route` when decrypting, after `x10 = 0` iff `keyLo sve ≤ x5 ≤ 704`, the
lengths `OpenKey.openMain` takes: `b₂ - b₁ + 1`, with `b₁ = (x5 - 705) >> 63`
(`x5 < 705`, in `x9`) and `b₂ = (x5 - keyLo sve) >> 63` (`x5 < keyLo sve`),
for any `x5`. Four moves first keep the block, with its two branches, 64
bytes long, as `route`'s with its branch, so that `openStitchedMain` keeps
its alignment; only `x9` and `x10` are written. -/
def routeOpen (sve : Bool) : List Instr :=
  List.replicate 4 (.movz .x .x10 0 0) ++
    [.subImm .x .x9 .x5 705, .lsr .x .x9 .x9 63, .subImm .x .x10 .x5 (keyLo sve), .lsr .x .x10 .x10 63,
      .sub .x .x10 .x10 .x9, .addImm .x .x10 .x10 1] ++ (route sve false).take 4

/-- The code up to the tag (`sealTail`, `openTail`), which the taint analysis
checks on its own: for `Short.lo c.sve` to 511 bytes `Pad.lean`'s route when
encrypting and `openRoute` when decrypting (to `ShortRest.lean`'s code, which
runs `Short.lean`'s up to 256, or `Pad.lean`'s, or `OpenPad`'s), and
otherwise stitched with the eight-block kernel (from the pass of five blocks
for the lengths `route` picks) or not. -/
def sealMainCode (c : XorCallee) (stitched : Bool) : Prog isa :=
  .seq (.block (Short.check c.sve))
    (.ite (.zero .x .x9) (Pad.sealRoute c)
      (if stitched then .seq (.block (route c.sve true))
        (.ite (.zero .x .x9) (sealWideMain c) (sealStitchedMain c))
      else sealMain c))

def openMainCode (c : XorCallee) (stitched : Bool) : Prog isa :=
  .seq (.block (Short.check c.sve))
    (.ite (.zero .x .x9) (openRoute c)
      (if stitched then .seq (.block (routeOpen c.sve))
        (.ite (.zero .x .x9) (openWideMain c)
          (Code.iteCold (.zero .x .x10) (OpenKey.openMain c) (openStitchedMain c)))
      else openMain c))

/-- The code for a stream backend. -/
def sealCode (c : XorCallee) (stitched : Bool) : Prog isa := .seq (sealMainCode c stitched) sealTail

def openCode (c : XorCallee) (stitched : Bool) : Prog isa := .seq (openMainCode c stitched) openTail

end VG.Impl.ChaCha20Poly1305.AArch64
