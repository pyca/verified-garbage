module

public import VerifiedGarbage.Impl.Aes.PPC64LE.ExpandKey
public import VerifiedGarbage.Impl.Aes.PPC64LE.Ctr32
public import VerifiedGarbage.Impl.Gcm.PPC64LE

/-!
# AES-GCM: PPC64LE implementation

The AES-GCM key setup and the start of a streaming encryption or decryption
(`init`, `stream_init`, `stream_aad`, `Spec/Gcm/Contract.lean`), composed of
calls of the verified `vg_aes_expand_key_scratch`, `vg_aes_ctr32` and
`vg_ghash`, as on ARMv7 (`Impl/AesGcm/ARM.lean`). A call (`bl`) stores
nothing in memory and the callees use no stack, so the functions use none
but the frame holding their working space.

## The working space

Every function has a buffer `W` of 2560 bytes (`scratch`):

* `[96, 112)`: a block `T`: a partial block padded with zeros, or the
  lengths block (or `init`'s zero counter block);
* `[128, 240)`: our caller's `r18`–`r31`, and `[240, 248)` our return
  address (a call replaces the link register);
* `[512, 2560)`: the working space of the functions called.

## Registers

`r31` holds `W`, `r30` the streaming state and `r29` the key context
throughout, and `init` keeps the number of rounds in `r28`; the functions
called preserve them (they are nonvolatile). The pieces below (`absorb`,
`flush`, `lens`) take their arguments in `r24` (a pointer), `r25` (a length)
and `r26` (an offset), which the callees also preserve, and `lens` the two
lengths in `r24` and `r26`. `j0` reads the nonce's length from `r18`, which
`stream_init` sets on entry. `r0` and `r3`–`r12` are temporaries.

## The pieces

* `absorb yo`: GHASH, with the accumulator at `r30 + yo` and the partial
  block at `r30 + 32` holding `r26` bytes, absorbs the `r25` bytes at `r24`:
  the partial block filled first (and absorbed if full), then whole blocks,
  then the last bytes buffered.
* `flush yo`: the `r26` buffered bytes padded with zeros, and absorbed.
* `lens yo`: the lengths block of `r24` bytes of additional data and `r26`
  bytes of text, absorbed.
* `j0`: `J₀` for the `r25`-byte nonce at `r24` (GHASH'd with `absorb`,
  `flush` and `lens` unless it is 12 bytes), and the state's accumulator and
  first counter block `inc₃₂(J₀)` (`initState`).

The model has no indexed byte access and branches only on whether a register
is zero: the bytes are copied through advancing pointers, counting down to
zero, and `min (16 - r26, r25)` shifts a difference of small numbers right.
Only the pointers and the lengths can affect timing: the branches are on
those.
-/

@[expose] public section

namespace VG.Impl.AesGcm.PPC64LE

open VG.PPC64LE

/-- `mr d, n` (`or d, n, n`). -/
def mov (d n : Reg) : Instr := .logic .or d n n

/-! ## The working space -/

def tO : Nat := 96
def scrO : Nat := 512
def lrO : Nat := 240
/-- The received tag, padded with zeros, in `verify`. -/
def rO : Nat := 256
/-- The first bytes of the computed tag, padded with zeros, in `verify`. -/
def vO : Nat := 272

/-- Our caller's registers, and where we save them. -/
def saved : List (Reg × Nat) :=
  [(.r18, 128), (.r19, 136), (.r20, 144), (.r21, 152), (.r22, 160), (.r23, 168), (.r24, 176),
   (.r25, 184), (.r26, 192), (.r27, 200), (.r28, 208), (.r29, 216), (.r30, 224), (.r31, 232)]

/-- Saves them and the return address at `b`, and keeps `b` in `r31`. -/
def save (b : Reg) : List Instr :=
  saved.map (fun (r, d) => .store .d r b d) ++
    ([.mflr .r0, .store .d .r0 b lrO, mov .r31 b] : List Instr)

/-- Restores the return address and the registers, through `r12` (a copy of
`W`, as `r31` is restored too). -/
def restore : List Instr :=
  ([mov .r12 .r31, .load .d .r0 .r12 lrO, .mtlr .r0] : List Instr) ++
    saved.map fun (r, d) => .load .d r .r12 d

/-! ## The calls -/

def ctrCall : Prog isa := .call "vg_aes_ctr32" Impl.Aes.PPC64LE.ctr32

def ghCall : Prog isa := .call "vg_ghash" Impl.Gcm.PPC64LE.ghash

def keyCall : Prog isa := .call "vg_aes_expand_key_scratch" Impl.Aes.PPC64LE.expandKey

/-! ## Loops -/

/-- Copies the `r5` (at least 1) bytes at `r3` to `r4`, advancing both. -/
def copyLoop : Prog isa :=
  .loop (.block [.lbz .r0 .r3 0, .stb .r0 .r4 0, .addi .r3 .r3 1, .addi .r4 .r4 1, .subi .r5 .r5 1])
    (.nonzero .d .r5)

/-- XORs the `r5` (at least 1) bytes at `r3` into those at `r4`, advancing both. -/
def xorLoop : Prog isa :=
  .loop (.block [.lbz .r0 .r4 0, .lbz .r6 .r3 0, .logic .xor .r0 .r0 .r6, .stb .r0 .r4 0,
    .addi .r3 .r3 1, .addi .r4 .r4 1, .subi .r5 .r5 1]) (.nonzero .d .r5)

/-- `r5 := min (16 - r26, r25)`: `16 - r26` if `r25 ≥ 16`, and otherwise
whichever the sign of their difference (both being small) says. -/
def minLen : Prog isa :=
  .seq (.block [.li .r5 16, .sub .r5 .r5 .r26, .lsr .d .r6 .r25 4])
    (.ite (.nonzero .d .r6) (.block [])
      (.seq (.block [.sub .r6 .r25 .r5, .lsr .d .r6 .r6 63])
        (.ite (.nonzero .d .r6) (.block [mov .r5 .r25]) (.block []))))

/-! ## GHASH -/

/-- `vg_ghash` of the block at `b + o` into the accumulator at `r30 + yo`. -/
def ghash1 (yo : Nat) (b : Reg) (o : Nat) : Prog isa :=
  .seq (.block [.addi .r3 .r29 240, .addi .r4 .r30 yo, .addi .r5 b o, .li .r6 1, .addi .r7 .r31 scrO])
    ghCall

/-- Before the buffer is absorbed: the buffer filled from `r24` (`r5`
bytes), the arguments advanced, and `r6` zero if the buffer is full. -/
def headPre : Prog isa :=
  .seq minLen
  (.seq (.block [.addi .r4 .r30 32, .add .r4 .r4 .r26, mov .r3 .r24, .add .r24 .r24 .r5,
      .sub .r25 .r25 .r5, .add .r26 .r26 .r5])
  (.seq copyLoop (.block [.subi .r6 .r26 16])))

/-- The buffer filled from `r24`, and absorbed if full. -/
def absorbHead (yo : Nat) : Prog isa :=
  .seq headPre (.ite (.zero .d .r6) (ghash1 yo .r30 32) (.block []))

/-- The whole blocks at `r24` split off: their address in `r5` and number in
`r6`, `r24` and `r25` the rest. -/
def splitWhole : List Instr :=
  [mov .r5 .r24, .lsr .d .r6 .r25 4, .li .r0 15, .logic .and .r8 .r25 .r0, .sub .r9 .r25 .r8,
   .add .r24 .r24 .r9, mov .r25 .r8]

/-- The whole blocks at `r24` absorbed. -/
def absorbWhole (yo : Nat) : Prog isa :=
  .seq (.block splitWhole)
    (.ite (.zero .d .r6) (.block [])
      (.seq (.block [.addi .r3 .r29 240, .addi .r4 .r30 yo, .addi .r7 .r31 scrO]) ghCall))

/-- The last `r25` bytes at `r24` buffered. -/
def absorbTail : Prog isa :=
  .ite (.zero .d .r25) (.block [])
    (.seq (.block [mov .r3 .r24, .addi .r4 .r30 32, mov .r5 .r25]) copyLoop)

/-- The buffer filled first, if it holds bytes. -/
def absorbFill (yo : Nat) : Prog isa :=
  .ite (.zero .d .r26) (.block []) (absorbHead yo)

def absorb (yo : Nat) : Prog isa :=
  .ite (.zero .d .r25) (.block []) (.seq (absorbFill yo) (.seq (absorbWhole yo) absorbTail))

/-- `T` zeroed, and the arguments of the copy of the `r26` buffered bytes to it. -/
def flushPre : List Instr :=
  [.li .r0 0, .store .d .r0 .r31 tO, .store .d .r0 .r31 (tO + 8), .addi .r3 .r30 32,
   .addi .r4 .r31 tO, mov .r5 .r26]

/-- The `r26` buffered bytes, padded with zeros in `T`, absorbed. -/
def flush (yo : Nat) : Prog isa :=
  .ite (.zero .d .r26) (.block []) (.seq (.seq (.block flushPre) copyLoop) (ghash1 yo .r31 tO))

/-- The lengths block of `r24` and `r26` bytes (in bits, big-endian), in `T`. -/
def lensBlock : List Instr :=
  [.lsl .r3 .r24 3, .lsl .r4 .r26 3, .addi .r5 .r31 tO, .li .r6 0, .storeRev .d .r3 .r5 .r6,
   .li .r6 8, .storeRev .d .r4 .r5 .r6]

/-- The lengths block of `r24` and `r26` bytes, absorbed. -/
def lens (yo : Nat) : Prog isa :=
  .seq (.block lensBlock) (ghash1 yo .r31 tO)

/-! ## Counter mode -/

/-- The rest of the keystream block, from byte `r26`, into `r24`. -/
def cryptHead : Prog isa :=
  .seq minLen
  (.seq (.block [.addi .r3 .r30 64, .add .r3 .r3 .r26, mov .r4 .r24, .add .r24 .r24 .r5,
      .sub .r25 .r25 .r5])
    xorLoop)

/-- The whole blocks at `r24` split off: their address in `r6` and number in
`r7`, `r24` and `r25` the rest. -/
def splitCtr : List Instr :=
  [mov .r6 .r24, .lsr .d .r7 .r25 4, .li .r0 15, .logic .and .r8 .r25 .r0, .sub .r9 .r25 .r8,
   .add .r24 .r24 .r9, mov .r25 .r8]

/-- The arguments of `vg_aes_ctr32` but the data and their number: the key
schedule, the rounds, the counter block (at `r30 + c`) and the working
space. -/
def ctrArgs (c : Nat) : List Instr :=
  [mov .r3 .r29, mov .r4 .r28, .addi .r5 .r30 c, .addi .r8 .r31 scrO]

/-- Whole blocks at `r24`, by `vg_aes_ctr32`. -/
def cryptWhole : Prog isa :=
  .seq (.block splitCtr)
    (.ite (.zero .d .r7) (.block []) (.seq (.block (ctrArgs 48)) ctrCall))

/-- The keystream block zeroed, and the arguments of `vg_aes_ctr32` on it. -/
def tailArgs : List Instr :=
  ([.li .r0 0, .store .d .r0 .r30 64, .store .d .r0 .r30 72, .addi .r6 .r30 64, .li .r7 1] :
    List Instr) ++ ctrArgs 48

/-- The last `r25` bytes at `r24`, with a new keystream block. -/
def cryptTail : Prog isa :=
  .ite (.zero .d .r25) (.block [])
    (.seq (.seq (.block tailArgs) ctrCall)
      (.seq (.block [.addi .r3 .r30 64, mov .r4 .r24, mov .r5 .r25]) xorLoop))

/-- The rest of the keystream block first, if the text so far ends within a block. -/
def cryptFill : Prog isa :=
  .ite (.zero .d .r26) (.block []) cryptHead

def crypt : Prog isa :=
  .ite (.zero .d .r25) (.block []) (.seq cryptFill (.seq cryptWhole cryptTail))

/-! ## The tag -/

/-- The accumulator copied to `W + o`, and the arguments of `vg_aes_ctr32` on
it with the counter block `J₀` at the state. -/
def tagArgs (o : Nat) : List Instr :=
  [.load .d .r3 .r30 16, .store .d .r3 .r31 o, .load .d .r3 .r30 24, .store .d .r3 .r31 (o + 8),
   mov .r3 .r29, mov .r4 .r28, mov .r5 .r30, .addi .r6 .r31 o, .li .r7 1, .addi .r8 .r31 scrO]

/-- The tag into `W + o`, after the lengths block of `r24` and `r26` bytes. -/
def tag (o : Nat) : Prog isa :=
  .seq (lens 16) (.seq (.block (tagArgs o)) ctrCall)

/-- The buffered bytes padded and absorbed, and the tag into `W + o`, for
`aad_len` (`r22`) bytes of additional data and `text_len` (`r23`) of text. -/
def finTag (o : Nat) : Prog isa :=
  .seq (.ite (.zero .d .r23) (.block [.li .r0 15, .logic .and .r26 .r22 .r0])
      (.block [.li .r0 15, .logic .and .r26 .r23 .r0]))
  (.seq (flush 16)
  (.seq (.block [mov .r24 .r22, mov .r26 .r23])
    (tag o)))

/-! ## Comparing tags -/

/-- `r25 = 1` if the tag length `r19` is between 4 and 16 bytes, else 0. -/
def tagLenOk : Prog isa :=
  .seq (.block [.li .r25 0, .lsr .d .r0 .r19 2])
    (.ite (.zero .d .r0) (.block [])
      (.seq (.block [.lsr .d .r0 .r19 4])
        (.ite (.zero .d .r0) (.block [.li .r25 1])
          (.seq (.block [.subi .r0 .r19 16])
            (.ite (.zero .d .r0) (.block [.li .r25 1]) (.block []))))))

/-- The `r19` bytes of the received tag (at `r20`), padded with zeros at `W + rO`. -/
def recv : Prog isa :=
  .seq (.block [.li .r0 0, .store .d .r0 .r31 rO, .store .d .r0 .r31 (rO + 8), mov .r3 .r20,
    .addi .r4 .r31 rO, mov .r5 .r19]) copyLoop

/-- `r3 = 1` if the padded tags at `W + vO` and `W + rO` are equal, else 0,
without a branch. -/
def cmpTail : List Instr :=
  [.load .d .r3 .r31 vO, .load .d .r4 .r31 rO, .logic .xor .r3 .r3 .r4, .load .d .r4 .r31 (vO + 8),
   .load .d .r5 .r31 (rO + 8), .logic .xor .r4 .r4 .r5, .logic .or .r3 .r3 .r4, .li .r4 0,
   .sub .r4 .r4 .r3, .logic .or .r3 .r3 .r4, .lsr .d .r3 .r3 63, .li .r4 1, .sub .r3 .r4 .r3]

/-- The first `r19` bytes of the tag at `W + o`, padded with zeros at
`W + vO`, compared with the received one: `r3 = 1` if they are equal. -/
def cmp (o : Nat) : Prog isa :=
  .seq (.block [.li .r0 0, .store .d .r0 .r31 vO, .store .d .r0 .r31 (vO + 8), .addi .r3 .r31 o,
    .addi .r4 .r31 vO, mov .r5 .r19])
    (.seq copyLoop (.block cmpTail))

/-! ## `J₀` -/

/-- The accumulator copied to `W + o`, and the arguments of `vg_aes_ctr32` on
it with the counter block `J₀`. -/
def j012 : List Instr :=
  [.load .w .r3 .r24 0, .load .w .r4 .r24 4, .load .w .r5 .r24 8, .lis .r6 0x0100,
   .store .w .r3 .r30 0, .store .w .r4 .r30 4, .store .w .r5 .r30 8, .store .w .r6 .r30 12]

/-- `J₀` of any other nonce: GHASH of the nonce padded, then of the lengths
block of no additional data and the nonce, from a zero block at the state. -/
def j0hash : Prog isa :=
  .seq (.block [.li .r0 0, .store .d .r0 .r30 0, .store .d .r0 .r30 8, .li .r26 0])
  (.seq (absorb 0)
  (.seq (.block [.li .r0 15, .logic .and .r26 .r18 .r0])
  (.seq (flush 0)
  (.seq (.block [.li .r24 0, mov .r26 .r18])
    (lens 0)))))

/-- The first counter block `inc₃₂(J₀)`, and the accumulator zeroed. -/
def initState : List Instr :=
  [.load .w .r3 .r30 0, .load .w .r4 .r30 4, .load .w .r5 .r30 8, .addi .r7 .r30 12, .li .r8 0,
   .loadRev .w .r6 .r7 .r8, .addi .r6 .r6 1, .store .w .r3 .r30 48, .store .w .r4 .r30 52,
   .store .w .r5 .r30 56, .addi .r7 .r30 60, .storeRev .w .r6 .r7 .r8, .store .d .r8 .r30 16,
   .store .d .r8 .r30 24]

/-- The streaming state for the `r25`-byte nonce at `r24`. -/
def j0 : Prog isa :=
  .seq (.block [.subi .r6 .r25 12]) (.seq (.ite (.zero .d .r6) (.block j012) j0hash) (.block initState))

/-! ## The functions -/

/-- `vg_aes_gcm_init(key = r3, key_len = r4, ctx = r5, scratch = r6)`. -/
def initPre : List Instr :=
  save .r6 ++ ([mov .r29 .r5, .lsr .d .r28 .r4 2, .addi .r28 .r28 6, .addi .r6 .r31 scrO] :
    List Instr)

/-- The hash subkey's block and `T` zeroed, and the arguments of
`vg_aes_ctr32` on them. -/
def initArgs : List Instr :=
  [.li .r0 0, .store .d .r0 .r29 240, .store .d .r0 .r29 248, .store .d .r0 .r31 tO,
   .store .d .r0 .r31 (tO + 8), mov .r3 .r29, mov .r4 .r28, .addi .r5 .r31 tO, .addi .r6 .r29 240,
   .li .r7 1, .addi .r8 .r31 scrO]

def init : Prog isa :=
  .seq (.block initPre)
  (.seq keyCall
  (.seq (.block initArgs) (.seq ctrCall (.block restore))))

/-- `vg_aes_gcm_stream_init(ctx = r3, nonce = r4, nonce_len = r5, state = r6, scratch = r7)`. -/
def streamInitPre : List Instr :=
  save .r7 ++ ([mov .r30 .r6, mov .r29 .r3, mov .r24 .r4, mov .r25 .r5, mov .r18 .r5] : List Instr)

def streamInit : Prog isa :=
  .seq (.block streamInitPre) (.seq j0 (.block restore))

/-- `vg_aes_gcm_stream_aad(ctx = r3, state = r4, aad_len = r5, data = r6, len = r7,
scratch = r8)`. -/
def streamAadPre : List Instr :=
  save .r8 ++ ([mov .r30 .r4, mov .r29 .r3, mov .r24 .r6, mov .r25 .r7, .li .r0 15,
    .logic .and .r26 .r5 .r0] : List Instr)

def streamAad : Prog isa :=
  .seq (.block streamAadPre) (.seq (absorb 16) (.block restore))


/-- The entry of `encrypt` and `decrypt`: `(ctx = r3, rounds = r4, state = r5,
aad_len = r6, text_len = r7, data = r8, len = r9, scratch = r10)`, kept in
`r29`, `r28`, `r30`, `r22`, `r23`, `r20` and `r19`. -/
def cryptEntry : List Instr :=
  save .r10 ++ ([mov .r30 .r5, mov .r29 .r3, mov .r28 .r4, mov .r22 .r6, mov .r23 .r7,
    mov .r20 .r8, mov .r19 .r9] : List Instr)

/-- The arguments of `crypt` or `absorb` for the text: the data, its length,
and the length of the text so far modulo 16. -/
def textArgs : List Instr := [mov .r24 .r20, mov .r25 .r19, .li .r0 15, .logic .and .r26 .r23 .r0]

/-- The additional data padded, before the first text. -/
def firstFlush : Prog isa :=
  .seq (.block [.li .r0 15, .logic .and .r26 .r22 .r0]) (flush 16)

/-- The text (`len` bytes at `data`) absorbed into GHASH. -/
def textAbsorb : Prog isa :=
  .ite (.zero .d .r19) (.block [])
    (.seq (.ite (.zero .d .r23) firstFlush (.block []))
      (.seq (.block textArgs) (absorb 16)))

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncrypt : Prog isa :=
  .seq (.block (cryptEntry ++ textArgs)) (.seq crypt (.seq textAbsorb (.block restore)))

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecrypt : Prog isa :=
  .seq (.block cryptEntry) (.seq textAbsorb (.seq (.block textArgs) (.seq crypt (.block restore))))

/-- The entry of `finish`: `(ctx = r3, rounds = r4, state = r5, aad_len = r6,
text_len = r7, tag = r8, scratch = r9)`, kept in `r29`, `r28`, `r30`, `r22`,
`r23` and `r20`. -/
def finEntry : List Instr :=
  save .r9 ++ ([mov .r30 .r5, mov .r29 .r3, mov .r28 .r4, mov .r22 .r6, mov .r23 .r7, mov .r20 .r8] :
    List Instr)

/-- The tag at `W` copied to `tag` (`r20`). -/
def tagOut : List Instr :=
  [.load .d .r3 .r31 0, .store .d .r3 .r20 0, .load .d .r3 .r31 8, .store .d .r3 .r20 8]

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinish : Prog isa :=
  .seq (.block finEntry) (.seq (finTag 0) (.seq (.block tagOut) (.block restore)))

/-- The entry of `verify`: `(ctx = r3, rounds = r4, state = r5, aad_len = r6,
text_len = r7, tag = r8, tag_len = r9, scratch = r10)`, kept in `r29`,
`r28`, `r30`, `r22`, `r23`, `r20` and `r19`. -/
def verEntry : List Instr :=
  save .r10 ++ ([mov .r30 .r5, mov .r29 .r3, mov .r28 .r4, mov .r22 .r6, mov .r23 .r7, mov .r20 .r8,
    mov .r19 .r9] : List Instr)

/-- `vg_aes_gcm_stream_verify`. -/
def streamVerify : Prog isa :=
  .seq (.block verEntry)
  (.seq tagLenOk
  (.seq (.ite (.zero .d .r25) (.block [.li .r3 0])
      (.seq recv (.seq (finTag 0) (cmp 0))))
    (.block restore)))

/-! ## One shot -/

/-- The entry of `seal` and `open`: `(ctx = r3, rounds = r4, nonce = r5,
nonce_len = r6, aad = r7, aad_len = r8, data = r9, len = r10, tag = [sp + 96],
…, scratch = [sp + off])`, kept in `r29`, `r28`, `r24` (and `r25`, `r18`),
`r21`, `r22`, `r27`, `r23` and `r20`; the state is at `W + 16` (`r30`). -/
def oneEntry (off : Nat) : List Instr :=
  [.addSp .r12 0, .load .d .r12 .r12 off] ++ save .r12 ++
    ([mov .r29 .r3, mov .r28 .r4, .addi .r30 .r31 16, mov .r24 .r5, mov .r25 .r6, mov .r18 .r6,
      mov .r21 .r7, mov .r22 .r8, mov .r27 .r9, mov .r23 .r10, .addSp .r12 0, .load .d .r20 .r12 96] :
      List Instr)

/-- `J₀`, then the additional data absorbed and padded. -/
def oneAad : Prog isa :=
  .seq j0
  (.seq (.block [mov .r24 .r21, mov .r25 .r22, .li .r26 0])
  (.seq (absorb 16)
  (.seq (.block [.li .r0 15, .logic .and .r26 .r22 .r0])
    (flush 16))))

/-- The arguments of `crypt` or `absorb` for the data, from its start. -/
def dataArgs : List Instr := [mov .r24 .r27, mov .r25 .r23, .li .r26 0]

/-- The data encrypted or decrypted, from the first counter block. -/
def oneCrypt : Prog isa := .seq (.block dataArgs) crypt

/-- The data (as ciphertext) absorbed and padded, and the tag into `W + o`. -/
def oneTag (o : Nat) : Prog isa :=
  .seq (.block dataArgs)
  (.seq (absorb 16)
  (.seq (.block [.li .r0 15, .logic .and .r26 .r23 .r0])
  (.seq (flush 16)
  (.seq (.block [mov .r24 .r22, mov .r26 .r23])
    (tag o)))))

/-- The shared entry and return of one-shot seal, with `scratch = [sp + 104]`. -/
def sealWith (textBody : Prog isa) : Prog isa :=
  .seq (.block (oneEntry 104))
    (.seq oneAad (.seq textBody (.seq (.block tagOut) (.block restore))))

/-- `vg_aes_gcm_seal`, with `scratch = [sp + 104]`. -/
def «seal» : Prog isa := sealWith (.seq oneCrypt (oneTag 0))

/-- The entry of `open`, with `tag_len = [sp + 104]` in `r19` and
`scratch = [sp + 112]`. -/
def openEntry : List Instr := oneEntry 112 ++ ([.load .d .r19 .r12 104] : List Instr)

/-- `open` once the tag length is allowed: the nonce's length back in `r25`,
the tag of the ciphertext at `W + 112`, compared with the received one, the
result (`r3`) kept in `r19`, and the data decrypted only if they are equal. -/
def openGood : Prog isa :=
  .seq (.block [mov .r25 .r18])
  (.seq oneAad
  (.seq (oneTag 112)
  (.seq recv
  (.seq (cmp 112)
  (.seq (.block [mov .r19 .r3])
  (.seq (.ite (.zero .d .r19) (.block []) oneCrypt)
    (.block [mov .r3 .r19])))))))

/-- `vg_aes_gcm_open`, with `tag = [sp + 96]`, `tag_len = [sp + 104]` and
`scratch = [sp + 112]`. -/
def «open» : Prog isa :=
  .seq (.block openEntry)
  (.seq tagLenOk
  (.seq (.ite (.zero .d .r25) (.block [.li .r3 0]) openGood)
    (.block restore)))

end VG.Impl.AesGcm.PPC64LE
