module

public import VerifiedGarbage.Impl.Sha256.PPC64LE.Stream
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Spec.Hmac.Generic

/-!
# HMAC-SHA-256: PPC64LE implementation

The same algorithm as on AArch64 (`VG.Impl.Hmac.AArch64`): two SHA-256
streaming states (`inner`, `outer`; see `VG.Spec.Hmac`).

* `init(inner = r3, outer = r4, key = r5, key_len = r6, scratch = r7)`
  stores `H⁽⁰⁾` in both states, the block `K₀ ⊕ ipad` in the inner buffer
  and `K₀ ⊕ opad` in the outer one, and compresses both (calling
  `vg_sha256_compress`).
* `finalize(inner = r3, outer = r4, count = r5, out = r6, scratch = r7)`
  finalizes the inner state (calling `vg_sha256_finalize_scratch`), makes the inner
  state represent `(K₀ ⊕ opad) ‖ digest` (96 bytes) from the outer hash value
  and that digest, and finalizes it again into `out`.

Both move the link register to `r0` and save it in a frame around the
whole function, as the streaming SHA-256 functions do.

`vg_hmac_sha256_init`, which takes a key of any length, chooses on entry
(`initAny`): a key of at most 64 bytes goes to `init` in a frame of its own,
as `vg_hmac_sha256_init_scratch` does with its caller's; a longer one to
`initLong`, which hashes it with SHA-256's verified streaming functions
(`vg_sha256_update_scratch` and `vg_sha256_finalize_scratch`) and calls
`vg_hmac_sha256_init_scratch` with its digest, in a frame it zeroes before
returning, since it holds the digest and the hash's state.
-/

@[expose] public section

namespace VG.Impl.Hmac.PPC64LE

open VG.PPC64LE
open VG.Impl.Sha256.PPC64LE.Stream (mov compressAt save restore)

/-! ## `init`

As in the streaming SHA-256 `update`, the call of the compression function
(`compressAt`: the block at `r4` into the hash value at `r26`, with scratch
space `r27`) preserves `r14`–`r31`, so our variables live in `r26`–`r31`,
and our caller's values of those are saved in `scratch[112..160)`.

Registers: `r26` = the state being compressed (`inner`, then `outer`), `r27`
= `scratch`, `r28` = `outer`, `r29` = the next key byte, `r30` = key bytes
left, `r31` = the byte index, `r12` = `0x36` (`ipad`), `r0` = `0x5c`
(`opad`). Byte `r31` of a buffer is addressed as `32(r11)` with
`r11 = state + r31`. -/

/-- `H⁽⁰⁾` into the state at `b`. -/
def h0 (b : Reg) : List Instr :=
  (List.range 8).flatMap fun k =>
    [.lis .r8 (Spec.Sha256.H0[k]!.extractLsb' 16 16),
     .ori .r8 .r8 (Spec.Sha256.H0[k]!.extractLsb' 0 16),
     .store .w .r8 b (4 * k)]

/-- The key bytes, XORed with `ipad` into the inner buffer and `opad` into the outer one. -/
def keyLoop : Prog isa :=
  .loop (.block [.lbz .r8 .r29 0,
    .logic .xor .r9 .r8 .r12, .add .r11 .r26 .r31, .stb .r9 .r11 32,
    .logic .xor .r9 .r8 .r0, .add .r11 .r28 .r31, .stb .r9 .r11 32,
    .addi .r29 .r29 1, .addi .r31 .r31 1, .subi .r30 .r30 1]) (.nonzero .d .r30)

/-- The zero bytes after the key (`r10` of them), XORed likewise. -/
def padLoop : Prog isa :=
  .loop (.block [.add .r11 .r26 .r31, .stb .r12 .r11 32, .add .r11 .r28 .r31, .stb .r0 .r11 32,
    .addi .r31 .r31 1, .subi .r10 .r10 1]) (.nonzero .d .r10)

/-- `init`, but for saving the link register. -/
def initMain : Prog isa :=
  .seq (.block (save .r7 ++ [mov .r26 .r3, mov .r27 .r7, mov .r28 .r4, mov .r29 .r5, mov .r30 .r6] ++
      h0 .r26 ++ h0 .r28 ++ [.li .r12 0x36, .li .r0 0x5c, .li .r31 0]))
  (.seq (.ite (.zero .d .r30) (.block []) keyLoop)
  (.seq (.block [.li .r10 64, .sub .r10 .r10 .r31])
  (.seq (.ite (.zero .d .r10) (.block []) padLoop)
  (.seq (.block [.addi .r4 .r26 32])
  (.seq compressAt
  (.seq (.block [mov .r26 .r28, .addi .r4 .r26 32])
  (.seq compressAt
    (.block restore))))))))

def init : Prog isa :=
  .seq (.block [.mflr .r0]) (.seq (.frame (.push .r0) initMain (.pop .r0)) (.block [.mtlr .r0]))

/-! ## `finalize`

The outer hash value is first copied to `scratch[208..240)`; the inner state
is finalized into `scratch[176..208)`; then the inner state is overwritten
with the outer hash value and that digest, so that it represents
`(K₀ ⊕ opad) ‖ digest`, and finalized again into `out`.

`out`, `inner` and `scratch` are kept in `r23`, `r24` and `r25`, which the
calls of `vg_sha256_finalize_scratch` preserve and never even write (so the taint
analysis knows they are still public after them); our caller's values of
those are saved in `scratch[240..248)` and `scratch[160..176)`, and our
return address in a stack frame. -/

/-- Copying 32-bit word `k` from `o₁(src)` to `o₂(dst)`. -/
def cp32 (src dst : Reg) (o₁ o₂ k : Nat) : List Instr :=
  [.load .w .r8 src (o₁ + 4 * k), .store .w .r8 dst (o₂ + 4 * k)]

/-- Copying 64-bit word `k` from `o₁(src)` to `o₂(dst)`. -/
def cp64 (src dst : Reg) (o₁ o₂ k : Nat) : List Instr :=
  [.load .d .r8 src (o₁ + 8 * k), .store .d .r8 dst (o₂ + 8 * k)]

/-- The outer hash value into `scratch[208..240)`. -/
def saveOuter : List Instr := (List.range 8).flatMap (cp32 .r4 .r7 0 208)

/-- The outer hash value and the first digest into the inner state. -/
def loadOuter : List Instr :=
  (List.range 8).flatMap (cp32 .r25 .r24 208 0) ++ (List.range 4).flatMap (cp64 .r25 .r24 176 32)

/-- A call of `vg_sha256_finalize_scratch`. -/
def sha256Finalize : Prog isa :=
  .call Spec.Sha256.finalizeScratchApi.name Impl.Sha256.PPC64LE.Stream.finalize

/-- `finalize`, but for saving the link register. -/
def finalizeMain : Prog isa :=
  .seq (.block ([.store .d .r23 .r7 240, .store .d .r24 .r7 160, .store .d .r25 .r7 168,
      mov .r23 .r6, mov .r24 .r3, mov .r25 .r7] ++ saveOuter ++
      [mov .r4 .r5, .addi .r5 .r7 176, mov .r6 .r7]))
  (.seq sha256Finalize
  (.seq (.block (loadOuter ++ [mov .r3 .r24, .li .r4 96, mov .r5 .r23, mov .r6 .r25]))
  (.seq sha256Finalize
    (.block [.load .d .r23 .r25 240, .load .d .r24 .r25 160, .load .d .r25 .r25 168]))))

def finalize : Prog isa :=
  .seq (.block [.mflr .r0]) (.seq (.frame (.push .r0) finalizeMain (.pop .r0)) (.block [.mtlr .r0]))

/-! ## `init` for a key of any length

`initLong(inner = r3, outer = r4, key = r5, key_len = r6, scratch = r7)`,
for a key longer than 64 bytes. Its scratch space: `scratch[0..160)` is
that of the functions it calls, `scratch[160..256)` the SHA-256 state the key
is hashed in, `scratch[256..288)` the digest, and our caller's `r20`–`r24` are
saved in `scratch[288..328)`. Across the calls, which neither write nor even
save them (so the taint analysis knows they stay public), `r20` =
the SHA-256 state, `r21` = `scratch`, `r22` = `inner`, `r23` = `outer` and
`r24` = `key_len`. -/

/-- A call of `vg_sha256_update_scratch`. -/
def sha256Update : Prog isa :=
  .call Spec.Sha256.updateScratchApi.name Impl.Sha256.PPC64LE.Stream.update

/-- A call of `vg_hmac_sha256_init_scratch`. -/
def hmacInitScratch : Prog isa := .call Spec.Hmac.sha256I.initScratchApi.name init

/-- `initLong`, but for saving the link register. -/
def initLongMain : Prog isa :=
  .seq (.block ([.store .d .r20 .r7 288, .store .d .r21 .r7 296, .store .d .r22 .r7 304,
      .store .d .r23 .r7 312, .store .d .r24 .r7 320,
      mov .r21 .r7, mov .r22 .r3, mov .r23 .r4, mov .r24 .r6, .addi .r20 .r7 160] ++ h0 .r20 ++
      [mov .r3 .r20, .li .r4 0, mov .r7 .r21]))
  (.seq sha256Update
  (.seq (.block [mov .r3 .r20, mov .r4 .r24, .addi .r5 .r21 256, mov .r6 .r21])
  (.seq sha256Finalize
  (.seq (.block [mov .r3 .r22, mov .r4 .r23, .addi .r5 .r21 256, .li .r6 32, mov .r7 .r21])
  (.seq hmacInitScratch
    (.block [.load .d .r20 .r21 288, .load .d .r22 .r21 304, .load .d .r23 .r21 312,
      .load .d .r24 .r21 320, .load .d .r21 .r21 296]))))))

def initLong : Prog isa :=
  .seq (.block [.mflr .r0]) (.seq (.frame (.push .r0) initLongMain (.pop .r0)) (.block [.mtlr .r0]))

/-- Sets `r12` to a nonzero value exactly when `key_len` (`r6`) is more than
64: `key_len >> 7` (nonzero from 128) plus `((key_len & 127) + 63) >> 7`
(1 from 65 to 127). It writes only `r11` and `r12`, and no memory. -/
def entryCmp : List Instr :=
  [.lsr .d .r12 .r6 7, .li .r11 127, .logic .and .r11 .r6 .r11, .addi .r11 .r11 63,
    .lsr .d .r11 .r11 7, .add .r12 .r12 .r11]

/-- Runs `long` for a key longer than 64 bytes, out of line, and `short`
otherwise. -/
def initEntry (short long : Prog isa) : Prog isa :=
  .seq (.block entryCmp) (Code.iteCold (.nonzero .d .r12) long short)

/-- The frame of `initLong`, sized so that both paths take the same stack:
`initLong`'s frame and that of the functions it calls (96 bytes) and this
one, as `init`'s frame (864 bytes) and its own (48 bytes). -/
def longFrame : Nat := 816

/-- The doublewords of `initLong`'s scratch space it writes, which are zeroed
before returning. -/
def longWords : Nat := 41

/-- `vg_hmac_sha256_init`, for a key of any length. -/
def initAny : Prog isa :=
  initEntry (Impl.StackScratch.PPC64LE.withStackScratch 864 .r7 init)
    (Impl.StackScratch.PPC64LE.withStackScratchWiped longFrame .r7 longWords initLong)

end VG.Impl.Hmac.PPC64LE
