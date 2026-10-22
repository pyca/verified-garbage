module

public import VerifiedGarbage.Impl.AesGcm.AArch64
public import VerifiedGarbage.Impl.Sm4.AArch64.Ctr32
public import VerifiedGarbage.Impl.Sm4.AArch64.ExpandKey
public import VerifiedGarbage.Impl.StackScratch.AArch64

/-!
# SM4-GCM: AArch64 implementation

The SM4-GCM functions of `Spec/Sm4/Gcm/Contract.lean`, composed of calls of
the verified `vg_sm4_expand_key`, `vg_sm4_ctr32` and `vg_ghash`, as AES-GCM's
(`Impl/AesGcm/AArch64.lean`), whose loops, copies, comparisons and register
conventions they share. They are generic over the implementation of
`vg_ghash` they call (`Callees`), and emitted once for each.

They differ from AES-GCM's in what they call and where:

* The key context is SM4's schedule (bytes 0–127) and the hash subkey `H`
  (bytes 128–143); there is no number of rounds, and `x22` is unused.
* `vg_sm4_ctr32` takes `(schedule = x0, counter = x1, data = x2, n = x3)`, and
  `vg_sm4_expand_key` `(key = x0, schedule = x1)`: both keep their working
  space in frames on the stack below ours (3264 and 3168 bytes), and take no
  working space from us.
* So the working space `W` is 768 bytes: AES-GCM's layout up to `vg_ghash`'s
  256 bytes at `W + 512`.
-/

@[expose] public section

namespace VG.Impl.Sm4Gcm.AArch64

open VG.AArch64
open VG.Impl.AesGcm.AArch64 (Fn mov ptr imm tO uO aadO alenO dataO lenO tlO scrO save restore copyB copy
  minK xorB xor j012 initState cmp tagIn tagOut tagLenOk fo textArgs verRet)

/-- `vg_sm4_ctr32`'s code, with its working space on the stack (as its
artifact, `Artifacts/Sm4Gcm/AArch64.lean`). -/
def ctrCode : Prog isa := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.ctr32

/-- `vg_sm4_expand_key`'s code (as its artifact, `Artifacts/Sm4/AArch64.lean`). -/
def keyCode : Prog isa := Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x2 396 Impl.Sm4.AArch64.expandKey

/-- The implementation of `vg_ghash` called. -/
structure Callees where
  gh : Fn

variable (c : Callees)

/-! ## GHASH -/

/-- The arguments of `vg_ghash` but the data and the number of blocks: the
hash subkey, the accumulator at `x20 + yo` and the working space. -/
def ghArgs (yo : Nat) : List Instr := [ptr .x0 .x21 240, ptr .x1 .x20 yo, ptr .x4 .x19 scrO]

def ghCall : Prog isa := .call c.gh.name c.gh.code

/-- Before the first call of `absorb`: the buffer filled from `x23`, and the
arguments for absorbing it if it is full (`x3` blocks, one or none). -/
def absSeg1 (yo : Nat) : Prog isa :=
  .seq minK
  (.seq (.block [.add .x .x11 .x20 .x25, ptr .x11 .x11 32, mov .x12 .x23, mov .x13 .x10])
  (.seq copyB
  (.seq (.block [.add .x .x23 .x23 .x10, .sub .x .x24 .x24 .x10, .add .x .x9 .x25 .x10,
      .subImm .x .x9 .x9 16])
  (.seq (.ite (.zero .x .x9) (.block [imm .x3 1]) (.block [imm .x3 0]))
    (.block (ghArgs yo ++ [ptr .x2 .x20 32]))))))

/-- Before the second call: the whole blocks at `x23`. -/
def absSeg2 (yo : Nat) : List Instr :=
  ([.lsr .x .x3 .x24 4, mov .x2 .x23] : List Instr) ++ ghArgs yo ++
    ([.lsl .x .x9 .x3 4, .add .x .x23 .x23 .x9, .sub .x .x24 .x24 .x9] : List Instr)

/-- The last `x24` bytes at `x23` buffered. -/
def absTail : Prog isa :=
  .seq (.block [ptr .x11 .x20 32, mov .x12 .x23, mov .x13 .x24]) copy

def absorb (yo : Nat) : Prog isa :=
  .seq (absSeg1 yo) (.seq (ghCall c) (.seq (.block (absSeg2 yo)) (.seq (ghCall c) absTail)))

/-- `absorb yo` with nothing buffered (`x25 = 0`): no buffer to fill first. -/
def absorbAl (yo : Nat) : Prog isa := .seq (.block (absSeg2 yo)) (.seq (ghCall c) absTail)

/-- The `x25` bytes at `x12` padded with zeros in `T`, and the arguments for
absorbing `T` if they are not none. -/
def padSeg (yo : Nat) (src : List Instr) : Prog isa :=
  .seq (.block (src ++ [imm .x9 0, .str .x .x9 .x19 tO, .str .x .x9 .x19 (tO + 8), ptr .x11 .x19 tO,
      mov .x13 .x25]))
  (.seq copy
  (.seq (.ite (.zero .x .x25) (.block [imm .x3 0]) (.block [imm .x3 1]))
    (.block (ghArgs yo ++ [ptr .x2 .x19 tO]))))

/-- The `x25` buffered bytes, padded with zeros in `T`, absorbed. -/
def flush (yo : Nat) : Prog isa := .seq (padSeg yo [ptr .x12 .x20 32]) (ghCall c)

/-- The lengths block of `ra` and `rb` bytes (as `[8 ra]₆₄ ‖ [8 rb]₆₄`) in `T`. -/
def lensSeg (yo : Nat) (ra rb : Reg) : List Instr :=
  ([.lsl .x .x9 ra 3, .rev .x9 .x9, .str .x .x9 .x19 tO, .lsl .x .x9 rb 3, .rev .x9 .x9,
    .str .x .x9 .x19 (tO + 8), imm .x3 1] : List Instr) ++ ghArgs yo ++ [ptr .x2 .x19 tO]

/-- The lengths block of `ra` and `rb` bytes, absorbed. -/
def lens (yo : Nat) (ra rb : Reg) : Prog isa := .seq (.block (lensSeg yo ra rb)) (ghCall c)

/-! ## Counter mode -/

/-- The arguments of `vg_sm4_ctr32` but the data and the number of blocks:
the schedule (the key context) and the counter block at `x20 + 48`. -/
def ctrArgs : List Instr := [mov .x0 .x21, ptr .x1 .x20 48]

def ctrCall : Prog isa := .call "vg_sm4_ctr32" ctrCode

/-- The arguments for the whole blocks at `x23`, and `x23` and `x24` past them. -/
def crArgs : List Instr :=
  ([.lsr .x .x3 .x24 4, mov .x2 .x23] : List Instr) ++ ctrArgs ++
    ([.lsl .x .x9 .x3 4, .add .x .x23 .x23 .x9, .sub .x .x24 .x24 .x9] : List Instr)

/-- The rest of the keystream block, from byte `x25` (unless it is 0), into
`x23`, and the arguments for the whole blocks after it. -/
def crSeg1 : Prog isa :=
  .seq (.ite (.zero .x .x25) (.block [imm .x10 0]) minK)
  (.seq (.block [.add .x .x11 .x20 .x25, ptr .x11 .x11 64, mov .x12 .x23, mov .x13 .x10])
  (.seq xorB
    (.block (([.add .x .x23 .x23 .x10, .sub .x .x24 .x24 .x10, .lsr .x .x3 .x24 4, mov .x2 .x23] : List Instr) ++
      ctrArgs ++ ([.lsl .x .x9 .x3 4, .add .x .x23 .x23 .x9, .sub .x .x24 .x24 .x9] : List Instr)))))

/-- The arguments for a new keystream block (one block, if there are bytes
left, or none). -/
def crSeg2 : Prog isa :=
  .seq (.ite (.zero .x .x24) (.block [imm .x3 0])
      (.block [imm .x3 1, imm .x9 0, .str .x .x9 .x20 64, .str .x .x9 .x20 72]))
    (.block (ctrArgs ++ [ptr .x2 .x20 64]))

/-- The last `x24` bytes at `x23`, with the new keystream block. -/
def crTail : Prog isa :=
  .seq (.block [ptr .x11 .x20 64, mov .x12 .x23, mov .x13 .x24]) xor

def crypt : Prog isa :=
  .seq crSeg1 (.seq ctrCall (.seq crSeg2 (.seq ctrCall crTail)))

/-- `crypt` from the start of a keystream block (`x25 = 0`): no rest of a
block to use first. -/
def cryptAl : Prog isa := .seq (.block crArgs) (.seq ctrCall (.seq crSeg2 (.seq ctrCall crTail)))

/-! ## The tag and `J₀` -/

/-- The accumulator copied to `W + o`, and the arguments for XORing
`CIPH_K(J₀)` into it. -/
def tagSeg (o : Nat) : List Instr :=
  [.ldr .x .x9 .x20 16, .str .x .x9 .x19 o, .ldr .x .x9 .x20 24, .str .x .x9 .x19 (o + 8),
    mov .x0 .x21, mov .x1 .x20, ptr .x2 .x19 o, imm .x3 1]

/-- The tag of the lengths in `x26` and `x27` into `W + o`. -/
def tag (o : Nat) : Prog isa :=
  .seq (lens c 16 .x26 .x27) (.seq (.block (tagSeg o)) ctrCall)

/-- The arguments for absorbing the whole blocks of the nonce into a zero
accumulator at `x20`, and its last `x25` bytes at `x23`. -/
def j0Seg : List Instr :=
  [imm .x9 0, .str .x .x9 .x20 0, .str .x .x9 .x20 8, .lsr .x .x3 .x24 4, mov .x2 .x23] ++ ghArgs 0 ++
    ([.lsl .x .x9 .x3 4, .add .x .x23 .x23 .x9, imm .x10 15, .logic .and .x .x25 .x24 .x10] : List Instr)

/-- `J₀` of any nonce but a 12-byte one, with its length in `x26` and 0 in `x27`. -/
def j0hash : Prog isa :=
  .seq (.block j0Seg) (.seq (ghCall c) (.seq (padSeg 0 [mov .x12 .x23]) (.seq (ghCall c)
    (lens c 0 .x27 .x26))))

/-- The streaming state for the `x24`-byte nonce at `x23` (its length also
in `x26`, and 0 in `x27`). -/
def j0 : Prog isa :=
  .seq (.block [.subImm .x .x9 .x24 12])
    (.seq (.ite (.zero .x .x9) (.block j012) (j0hash c)) (.block initState))

/-! ## The functions -/

/-- `vg_sm4_gcm_init(key = x0, ctx = x1, scratch = x2)`: the schedule from
the key (`x0`) to the context (`x1`). -/
def initSeg1 : List Instr := save .x2 ++ [mov .x19 .x2, mov .x21 .x1]

/-- `H = CIPH_K(0¹²⁸)`: the zero block at the context's `H`, encrypted in
counter mode from a zero counter block in `T`. -/
def initSeg2 : List Instr :=
  [imm .x9 0, .str .x .x9 .x21 240, .str .x .x9 .x21 248, .str .x .x9 .x19 tO,
    .str .x .x9 .x19 (tO + 8), mov .x0 .x21, ptr .x1 .x19 tO, ptr .x2 .x21 240, imm .x3 1]

def init : Prog isa :=
  .seq (.block initSeg1)
  (.seq (.call "vg_sm4_expand_key" keyCode)
  (.seq (.block initSeg2)
  (.seq ctrCall
    (.block restore))))

/-- The entry of `encrypt` and `decrypt`: `(ctx = x0, state = x1,
aad_len = x2, text_len = x3, data = x4, len = x5, scratch = x6)`: `x26` the
length, `x27` the text so far and `x28` the data, and `aad_len mod 16` in
`x25`. -/
def crEntry : List Instr :=
  save .x6 ++ [mov .x19 .x6, mov .x20 .x1, mov .x21 .x0, mov .x26 .x5, mov .x27 .x3,
    mov .x28 .x4, imm .x9 15, .logic .and .x .x25 .x2 .x9]

/-- The text absorbed into GHASH, if there is any. -/
def textAbs : Prog isa := .ite (.zero .x .x26) (.block []) (absorb c 16)

/-- The additional data padded if this is the first text, and the text
(`x26` bytes at `x28`, after `x27` bytes) encrypted and absorbed. -/
def encBody : Prog isa :=
  .seq fo (.seq (flush c 16) (.seq (.block textArgs) (.seq crypt
    (.seq (.block [mov .x23 .x28, mov .x24 .x26]) (textAbs c)))))

/-- The additional data padded if this is the first text, and the text
absorbed. -/
def decAbs : Prog isa :=
  .seq fo (.seq (flush c 16) (.seq (.block textArgs) (textAbs c)))

/-- `decAbs`, and the text decrypted. -/
def decBody : Prog isa :=
  .seq (decAbs c) (.seq (.block [mov .x23 .x28, mov .x24 .x26]) crypt)

/-- `vg_sm4_gcm_stream_encrypt`. -/
def streamEncrypt : Prog isa := .seq (.block crEntry) (.seq (encBody c) (.block restore))

/-- `vg_sm4_gcm_stream_decrypt`. -/
def streamDecrypt : Prog isa := .seq (.block crEntry) (.seq (decBody c) (.block restore))

/-- The entry of `finish` and `verify`: `(ctx = x0, state = x1, aad_len = x2,
text_len = x3, tag = x4, …)`, with `work` in `w`. -/
def finEntry (w : Reg) : List Instr :=
  save w ++ [mov .x19 w, mov .x20 .x1, mov .x21 .x0, mov .x26 .x2, mov .x27 .x3]

/-- The buffered bytes (of the text, or of the additional data if there is
no text) padded and absorbed, and the tag into `W + o`. -/
def finBody (o : Nat) : Prog isa :=
  .seq (.ite (.zero .x .x27) (.block [imm .x9 15, .logic .and .x .x25 .x26 .x9])
      (.block [imm .x9 15, .logic .and .x .x25 .x27 .x9]))
    (.seq (flush c 16) (tag c o))

/-- `vg_sm4_gcm_stream_finish`, with `work = x5`; `x28` holds `tag`. -/
def streamFinish : Prog isa :=
  .seq (.block (finEntry .x5 ++ [mov .x28 .x4])) (.seq (finBody c 0) (.seq (.block tagOut) (.block restore)))

/-- `vg_sm4_gcm_stream_verify`, with `tag_len = x5` and `work = x6`; `x12`
holds `tag` until `tagIn`. -/
def streamVerify : Prog isa :=
  .seq (.block (finEntry .x6 ++ [mov .x28 .x5, mov .x12 .x4]))
  (.seq tagLenOk
  (.seq (.ite (.zero .x .x9) (.block [imm .x0 0])
      (.seq tagIn (.seq (finBody c uO) (.seq cmp (.block verRet)))))
    (.block restore)))

/-- The entry of `seal` and `open`: `(ctx = x0, nonce = x1, nonce_len = x2,
aad = x3, aad_len = x4, data = x5, len = x6, tag = x7, …)`, with `work` at
`[sp + w]`. The state is at `W + 16`. -/
def oneEntry (w : Nat) : List Instr :=
  ([.ldrSp .x9 w] : List Instr) ++ save .x9 ++
    [mov .x19 .x9, ptr .x20 .x19 16, mov .x21 .x0, .str .x .x3 .x19 aadO,
      .str .x .x4 .x19 alenO, .str .x .x5 .x19 dataO, .str .x .x6 .x19 lenO, mov .x23 .x1,
      mov .x24 .x2, mov .x26 .x2, imm .x27 0]

/-- The additional data absorbed. -/
def oneAad : Prog isa :=
  .seq (.block [.ldr .x .x23 .x19 aadO, .ldr .x .x24 .x19 alenO, imm .x25 0]) (absorbAl c 16)

/-- The arguments of `encBody` and `decAbs`: no text yet. -/
def encPrep : List Instr :=
  [.ldr .x .x9 .x19 alenO, imm .x10 15, .logic .and .x .x25 .x9 .x10, .ldr .x .x26 .x19 lenO,
    imm .x27 0, .ldr .x .x28 .x19 dataO]

/-- The arguments of `finBody`: the lengths. -/
def finPrep : List Instr := [.ldr .x .x26 .x19 alenO, .ldr .x .x27 .x19 lenO]

/-- `vg_sm4_gcm_seal` after its entry. -/
def sealRest : Prog isa :=
  .seq (j0 c)
  (.seq (oneAad c)
  (.seq (.block encPrep)
  (.seq (encBody c)
  (.seq (.block finPrep)
  (.seq (.block [.ldr .x .x28 .x19 tlO])
  (.seq (finBody c 0)
  (.seq (.block tagOut)
    (.block restore))))))))

/-- `vg_sm4_gcm_seal`, with `tag = x7` (kept at `W + 248`) and `work = [sp]`. -/
def «seal» : Prog isa :=
  .seq (.block (oneEntry 0 ++ [.str .x .x7 .x19 tlO, mov .x28 .x7])) (sealRest c)

/-- The text decrypted, from the first counter block. -/
def oneCrypt : Prog isa :=
  .seq (.block [.ldr .x .x23 .x19 dataO, .ldr .x .x24 .x19 lenO, imm .x25 0]) cryptAl

/-- `open` once the tag length is allowed. -/
def openMain : Prog isa :=
  .seq (j0 c)
  (.seq (oneAad c)
  (.seq (.block encPrep)
  (.seq (decAbs c)
  (.seq (.block finPrep)
  (.seq (finBody c uO)
  (.seq (.block [.ldr .x .x28 .x19 tlO])
  (.seq cmp
  (.seq (.block [imm .x27 1, .sub .x .x27 .x27 .x10])
  (.seq (.ite (.zero .x .x27) (.block []) oneCrypt)
    (.block [mov .x0 .x27]))))))))))

/-- The entry of `open`: `oneEntry`, `tag_len` (at `[sp]`) stashed, and `tag`
in `x12`. -/
def openEntry : List Instr :=
  oneEntry 8 ++ ([.ldrSp .x10 0, .str .x .x10 .x19 tlO, mov .x28 .x10, mov .x12 .x7] : List Instr)

/-- `vg_sm4_gcm_open` after its entry. -/
def openRest : Prog isa :=
  .seq tagLenOk
  (.seq (.ite (.zero .x .x9) (.block [imm .x0 0]) (.seq tagIn (openMain c)))
    (.block restore))

/-- `vg_sm4_gcm_open`, with `tag = x7` (in `x12` until `tagIn`),
`tag_len = [sp]` (kept at `W + 248`) and `work = [sp + 8]`. -/
def «open» : Prog isa := .seq (.block openEntry) (openRest c)

end VG.Impl.Sm4Gcm.AArch64
