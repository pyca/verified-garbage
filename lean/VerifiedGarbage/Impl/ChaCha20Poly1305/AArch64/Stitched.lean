module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitch
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Short
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.ShortRest
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
  direction needs.

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

/-- `sealStitched` but for the tag. -/
def sealStitchedMain (c : XorCallee) : Prog isa :=
  .seq prologue
  (.seq (macPad .x24 .x25)
  (.seq (.block lengths)
  (.seq (cryptStitched c.sve true)
  (.seq (.call c.name c.code)
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
  (.seq (cryptRest c)
  (.seq absorbLengths
    (finalizeTo 48)))))))

def openStitched (c : XorCallee) : Prog isa := .seq (openStitchedMain c) openTail

/-- The code up to the tag (`sealTail`, `openTail`), which the taint analysis
checks on its own: for `Short.lo c.sve` to 511 bytes `ShortRest.lean`'s (which
runs `Short.lean`'s up to 256), and otherwise stitched with the eight-block
kernel or not. -/
def sealMainCode (c : XorCallee) (stitched : Bool) : Prog isa :=
  .seq (.block (Short.check c.sve))
    (.ite (.zero .x .x9) (ShortRest.sealMain c)
      (if stitched then sealStitchedMain c else sealMain c))

def openMainCode (c : XorCallee) (stitched : Bool) : Prog isa :=
  .seq (.block (Short.check c.sve))
    (.ite (.zero .x .x9) (ShortRest.openMain c)
      (if stitched then openStitchedMain c else openMain c))

/-- The code for a stream backend. -/
def sealCode (c : XorCallee) (stitched : Bool) : Prog isa := .seq (sealMainCode c stitched) sealTail

def openCode (c : XorCallee) (stitched : Bool) : Prog isa := .seq (openMainCode c stitched) openTail

end VG.Impl.ChaCha20Poly1305.AArch64
