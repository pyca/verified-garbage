module

public import VerifiedGarbage.Impl.Aes.PPC64LE.ExpandKey
public import VerifiedGarbage.Impl.Aes.PPC64LE.Ctr32
public import VerifiedGarbage.Impl.Gcm.PPC64LE
public import VerifiedGarbage.Impl.Gather.PPC64LE
public import VerifiedGarbage.Impl.AesCbc.PPC64LE

/-!
# AES-GCM: PPC64LE implementation

The key setup and the streaming functions of `Spec/Gcm/Contract.lean`,
composed of calls of the verified `vg_aes_expand_key_scratch`,
`vg_aes_ctr32(schedule = r3, rounds = r4, counter = r5, data = r6, n = r7, scratch = r8)`
and `vg_ghash(h = r3, y = r4, data = r5, n = r6, scratch = r7)`, as on ARMv7
(`Impl/AesGcm/Arm.lean`). Each takes its working space `W` (2560 bytes) as
its last argument, which a frame on the stack provides
(`Impl/StackScratch/PPC64LE.lean`). A call (`bl`) stores nothing in memory.

## The working space

* `[0, 2048)`: the working space of the functions called;
* `[2048, 2064)`: a block `T`: a partial block padded with zeros, the
  lengths block, or the zero block `init` encrypts;
* `[2064, 2080)`: the tag `verify` computes, and `[2080, 2096)` its first
  `tag_len` bytes padded with zeros;
* `[2096, 2112)`: the received tag padded with zeros;
* `[2112, 2208)`: our caller's `r14`–`r24` and our return address.

## Registers

The nonvolatile registers, which the functions called preserve, hold
throughout: `r14` the working space, `r15` the streaming state, `r16` the
key context, `r17` the number of rounds, `r21` and `r22` the lengths of the
additional data and of the text so far, and `r23` and `r24` the data (or
the tag) and its length. The pieces below take a pointer in `r18`, a length
in `r19` and an offset in `r20`. `r0` and `r3`–`r12` are temporaries.

## The pieces

As on ARMv7:

* `absorb yo`: GHASH, with the accumulator at `r15 + yo` and the partial
  block at `r15 + 32` holding `r20` bytes, absorbs the `r19` bytes at `r18`:
  the partial block filled first (and absorbed if full), then whole blocks,
  then the last bytes buffered.
* `flush yo`: the `r20` buffered bytes padded with zeros, and absorbed.
* `lens yo`: the lengths block of `r21` bytes of additional data and `r22`
  bytes of text, absorbed.
* `crypt`: the `r19` bytes at `r18` XORed with the keystream, `r20` bytes
  into the current keystream block: the rest of that block (at `r15 + 64`),
  then whole blocks with `vg_aes_ctr32` from the counter block at
  `r15 + 48`, then a new keystream block for the last bytes.
* `tag d o`: the lengths block absorbed, and `GHASH ⊕ CIPH_K(J₀)` written to
  `d + o`, with `vg_aes_ctr32` on it with the counter block `J₀` (at `r15`).
* `j0`: `J₀` for the `r19`-byte nonce at `r18` (GHASH'd with `absorb`,
  `flush` and `lens` unless it is 12 bytes), and the state's accumulator and
  first counter block `inc₃₂(J₀)` (`initState`).

Bytes are copied with the gathering's byte loop (`Impl/Gather/PPC64LE.lean`,
`r4` bytes from `r3` to `r9`) and XORed into the text with `xorBytes`. The
model has no flags: the branches are on whether a register is zero, and
`min(16 - r20, r19)` takes `16 - r20` when `r19 ≥ 16` (`r19 >> 4` is not 0)
and otherwise the sign of a difference of two numbers less than 16. Only the
pointers, the lengths, `rounds` and `tag_len` can affect timing: the
branches are on those, and `verify` compares the tags without a branch.
-/

@[expose] public section

namespace VG.Impl.AesGcm.PPC64LE

open VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (mov)

/-! ## The working space -/

def tO : Nat := 2048
def vO : Nat := 2064
def vpO : Nat := 2080
def rO : Nat := 2096

/-- Our caller's registers and our return address (in `r0`), and where we
save them. -/
def saved : List (Reg × Nat) :=
  [(.r0, 2112), (.r15, 2128), (.r16, 2136), (.r17, 2144), (.r18, 2152), (.r19, 2160), (.r20, 2168),
   (.r21, 2176), (.r22, 2184), (.r23, 2192), (.r24, 2200), (.r14, 2120)]

/-- Saves them at `b`, after reading the return address. -/
def save (b : Reg) : List Instr := .mflr .r0 :: saved.map fun (r, d) => .store .d r b d

/-- Restores them from `r14`, which holds `W` (restored last), and the return
address. -/
def restore : List Instr := saved.map (fun (r, d) => .load .d r .r14 d) ++ [.mtlr .r0]

/-! ## The calls -/

def ghCall : Prog isa := .call "vg_ghash" Impl.Gcm.PPC64LE.ghash
def ctrCall : Prog isa := .call "vg_aes_ctr32" Impl.Aes.PPC64LE.ctr32
def ekCall : Prog isa := .call "vg_aes_expand_key_scratch" Impl.Aes.PPC64LE.expandKey

/-! ## Bytes -/

/-- Copies the `r4` (at least 1) bytes at `r3` to `r9`. -/
abbrev copyBytes : Prog isa := Impl.Gather.PPC64LE.copyBytes

/-- XORs the `r4` (at least 1) bytes at `r3` into those at `r9`, advancing both. -/
def xorBytes : Prog isa :=
  .loop (.block [.lbz .r0 .r3 0, .lbz .r5 .r9 0, .logic .xor .r0 .r0 .r5, .stb .r0 .r9 0,
    .addi .r3 .r3 1, .addi .r9 .r9 1, .subi .r4 .r4 1]) (.nonzero .d .r4)

/-- `r4 := min(16 - r20, r19)`, for `1 ≤ r20 ≤ 15`. -/
def minLen : Prog isa :=
  .seq (.block [.li .r4 16, .sub .r4 .r4 .r20, .lsr .d .r5 .r19 4])
    (.ite (.zero .d .r5)
      (.seq (.block [.sub .r5 .r19 .r4, .lsr .d .r5 .r5 63])
        (.ite (.zero .d .r5) (.block []) (.block [mov .r4 .r19])))
      (.block []))

/-! ## GHASH -/

/-- `vg_ghash` of the block at `b + o` into the accumulator at `r15 + yo`. -/
def ghash1 (yo : Nat) (b : Reg) (o : Nat) : Prog isa :=
  .seq (.block [.addi .r3 .r16 240, .addi .r4 .r15 yo, .addi .r5 b o, .li .r6 1, mov .r7 .r14]) ghCall

/-- The buffer filled from `r18` (`r4` bytes), the arguments advanced. -/
def headArgs : List Instr :=
  [.addi .r9 .r15 32, .add .r9 .r9 .r20, mov .r3 .r18, .add .r18 .r18 .r4, .sub .r19 .r19 .r4,
   .add .r20 .r20 .r4]

/-- The buffer filled from `r18`, and absorbed if full. -/
def absorbHead (yo : Nat) : Prog isa :=
  .seq minLen (.seq (.block headArgs) (.seq copyBytes
    (.seq (.block [.subi .r5 .r20 16]) (.ite (.zero .d .r5) (ghash1 yo .r15 32) (.block [])))))

/-- The whole blocks at `r18` split off: their address in `r5` and number in
`r6`; `r18` and `r19` the rest. -/
def splitWhole : List Instr :=
  [.lsr .d .r6 .r19 4, .lsl .r7 .r6 4, mov .r5 .r18, .add .r18 .r18 .r7, .li .r7 15,
   .logic .and .r19 .r19 .r7]

/-- The whole blocks at `r18` absorbed. -/
def absorbWhole (yo : Nat) : Prog isa :=
  .seq (.block splitWhole)
    (.ite (.zero .d .r6) (.block [])
      (.seq (.block [.addi .r3 .r16 240, .addi .r4 .r15 yo, mov .r7 .r14]) ghCall))

/-- The last `r19` bytes at `r18` buffered. -/
def absorbTail : Prog isa :=
  .ite (.zero .d .r19) (.block [])
    (.seq (.block [mov .r3 .r18, .addi .r9 .r15 32, mov .r4 .r19]) copyBytes)

/-- The buffer filled first, if it holds bytes. -/
def absorbFill (yo : Nat) : Prog isa := .ite (.zero .d .r20) (.block []) (absorbHead yo)

def absorb (yo : Nat) : Prog isa :=
  .ite (.zero .d .r19) (.block []) (.seq (absorbFill yo) (.seq (absorbWhole yo) absorbTail))

/-- `T` zeroed, and the arguments of the copy of the `r20` buffered bytes to it. -/
def flushPre : List Instr :=
  [.li .r0 0, .store .d .r0 .r14 tO, .store .d .r0 .r14 (tO + 8), .addi .r3 .r15 32,
   .addi .r9 .r14 tO, mov .r4 .r20]

/-- The `r20` buffered bytes, padded with zeros in `T`, absorbed. -/
def flush (yo : Nat) : Prog isa :=
  .ite (.zero .d .r20) (.block []) (.seq (.block flushPre) (.seq copyBytes (ghash1 yo .r14 tO)))

/-- `[8 r21]₆₄ ‖ [8 r22]₆₄` into `T`, big-endian. -/
def lensPre : List Instr :=
  [.lsl .r5 .r21 3, .lsl .r6 .r22 3, .addi .r9 .r14 tO, .li .r10 0, .li .r11 8,
   .storeRev .d .r5 .r9 .r10, .storeRev .d .r6 .r9 .r11]

/-- The lengths block of `r21` and `r22` bytes, absorbed. -/
def lens (yo : Nat) : Prog isa := .seq (.block lensPre) (ghash1 yo .r14 tO)

/-! ## Counter mode -/

/-- The rest of the keystream block, from byte `r20`, into `r18`. -/
def cryptHead : Prog isa :=
  .seq minLen
    (.seq (.block [.addi .r3 .r15 64, .add .r3 .r3 .r20, mov .r9 .r18, .add .r18 .r18 .r4,
        .sub .r19 .r19 .r4])
      xorBytes)

/-- The whole blocks at `r18` split off: their address in `r6` and number in
`r7`; `r18` and `r19` the rest. -/
def splitCtr : List Instr :=
  [.lsr .d .r7 .r19 4, .lsl .r8 .r7 4, mov .r6 .r18, .add .r18 .r18 .r8, .li .r8 15,
   .logic .and .r19 .r19 .r8]

/-- Whole blocks at `r18`, by `vg_aes_ctr32`. -/
def cryptWhole : Prog isa :=
  .seq (.block splitCtr)
    (.ite (.zero .d .r7) (.block [])
      (.seq (.block [mov .r3 .r16, mov .r4 .r17, .addi .r5 .r15 48, mov .r8 .r14]) ctrCall))

/-- The keystream block zeroed, and the arguments of `vg_aes_ctr32` on it. -/
def tailArgs : List Instr :=
  [.li .r0 0, .store .d .r0 .r15 64, .store .d .r0 .r15 72, mov .r3 .r16, mov .r4 .r17,
   .addi .r5 .r15 48, .addi .r6 .r15 64, .li .r7 1, mov .r8 .r14]

/-- The last `r19` bytes at `r18`, with a new keystream block. -/
def cryptTail : Prog isa :=
  .ite (.zero .d .r19) (.block [])
    (.seq (.seq (.block tailArgs) ctrCall)
      (.seq (.block [.addi .r3 .r15 64, mov .r9 .r18, mov .r4 .r19]) xorBytes))

/-- The rest of the keystream block first, if the text so far ends within a block. -/
def cryptFill : Prog isa := .ite (.zero .d .r20) (.block []) cryptHead

def crypt : Prog isa :=
  .ite (.zero .d .r19) (.block []) (.seq cryptFill (.seq cryptWhole cryptTail))

/-! ## The tag and `J₀` -/

/-- The accumulator copied to `d + o`, and the arguments of `vg_aes_ctr32` on
it with the counter block `J₀`. -/
def tagArgs (d : Reg) (o : Nat) : List Instr :=
  [.load .d .r5 .r15 16, .load .d .r6 .r15 24, .store .d .r5 d o, .store .d .r6 d (o + 8),
   mov .r3 .r16, mov .r4 .r17, mov .r5 .r15, .addi .r6 d o, .li .r7 1, mov .r8 .r14]

/-- The tag into `d + o`. -/
def tag (d : Reg) (o : Nat) : Prog isa := .seq (lens 16) (.seq (.block (tagArgs d o)) ctrCall)

/-- `J₀` of a 12-byte nonce: its 12 bytes and `0x00000001` (big-endian). -/
def j012 : List Instr :=
  [.load .d .r5 .r18 0, .load .w .r6 .r18 8, .lis .r7 0x0100, .store .d .r5 .r15 0,
   .store .w .r6 .r15 8, .store .w .r7 .r15 12]

/-- `J₀` of any other nonce: GHASH of the nonce padded, then of the lengths
block of no additional data and the nonce, from a zero block at the state. -/
def j0hash : Prog isa :=
  .seq (.block [.li .r0 0, .store .d .r0 .r15 0, .store .d .r0 .r15 8, mov .r22 .r19, .li .r20 0])
  (.seq (absorb 0)
  (.seq (.block [.li .r5 15, .logic .and .r20 .r22 .r5])
  (.seq (flush 0)
  (.seq (.block [.li .r21 0])
    (lens 0)))))

/-- The first counter block `inc₃₂(J₀)`, and the accumulator zeroed. -/
def initState : List Instr :=
  [.load .d .r5 .r15 0, .store .d .r5 .r15 48, .load .w .r6 .r15 8, .store .w .r6 .r15 56,
   .li .r7 12, .loadRev .w .r8 .r15 .r7, .addi .r8 .r8 1, .li .r7 60, .storeRev .w .r8 .r15 .r7,
   .li .r0 0, .store .d .r0 .r15 16, .store .d .r0 .r15 24]

/-- The streaming state for the `r19`-byte nonce at `r18`. -/
def j0 : Prog isa :=
  .seq (.block [.subi .r5 .r19 12]) (.seq (.ite (.zero .d .r5) (.block j012) j0hash) (.block initState))

/-! ## Comparing tags -/

/-- `W + o` zeroed (16 bytes) with `r0`. -/
def zero16 (o : Nat) : List Instr := [.li .r0 0, .store .d .r0 .r14 o, .store .d .r0 .r14 (o + 8)]

/-- The first `r24` bytes at `b`, padded with zeros at `W + o`. -/
def pad (b : Reg) (o : Nat) : Prog isa :=
  .seq (.block (zero16 o ++ [mov .r3 b, .addi .r9 .r14 o, mov .r4 .r24])) copyBytes

/-- `r3 = 1` if the padded tags at `W + vpO` and `W + rO` are equal, else 0,
without a branch. -/
def cmpTail : List Instr :=
  [.load .d .r5 .r14 vpO, .load .d .r6 .r14 rO, .logic .xor .r5 .r5 .r6,
   .load .d .r6 .r14 (vpO + 8), .load .d .r7 .r14 (rO + 8), .logic .xor .r6 .r6 .r7,
   .logic .or .r5 .r5 .r6, .li .r6 0, .sub .r6 .r6 .r5, .logic .or .r5 .r5 .r6, .lsr .d .r5 .r5 63,
   .li .r3 1, .sub .r3 .r3 .r5]

/-- The received tag (`r24` bytes at `r23`) and the first `r24` bytes of the
computed one (at `W + vO`), each padded with zeros, compared. -/
def cmp : Prog isa :=
  .seq (pad .r23 rO) (.seq (.seq (.block [.addi .r12 .r14 vO]) (pad .r12 vpO)) (.block cmpTail))

/-- `ok` if `4 ≤ r24 ≤ 16`, else `bad`: `t = r24 - 4` is less than 16
(`t >> 4` is 0, rejecting the wraparound when `r24 < 4`) and then less than
13 (the sign of `t - 13`). -/
def tagLenOk (ok bad : Prog isa) : Prog isa :=
  .seq (.block [.subi .r5 .r24 4, .lsr .d .r6 .r5 4])
    (.ite (.zero .d .r6)
      (.seq (.block [.subi .r6 .r5 13, .lsr .d .r6 .r6 63]) (.ite (.zero .d .r6) bad ok))
      bad)

/-! ## The functions -/

/-- `vg_aes_gcm_init(key = r3, key_len = r4, ctx = r5, scratch = r6)`:
`vg_aes_expand_key_scratch(key, key_len, ctx, W)`. -/
def initPre : List Instr :=
  save .r6 ++ [mov .r14 .r6, mov .r16 .r5, .lsr .d .r17 .r4 2, .addi .r17 .r17 6]

/-- The hash subkey's block and `T` zeroed, and the arguments of
`vg_aes_ctr32` on them. -/
def initArgs : List Instr :=
  [.li .r0 0, .store .d .r0 .r16 240, .store .d .r0 .r16 248, .store .d .r0 .r14 tO,
   .store .d .r0 .r14 (tO + 8), mov .r3 .r16, mov .r4 .r17, .addi .r5 .r14 tO, .addi .r6 .r16 240,
   .li .r7 1, mov .r8 .r14]

def init : Prog isa :=
  .seq (.block initPre) (.seq ekCall (.seq (.block initArgs) (.seq ctrCall (.block restore))))

/-- `vg_aes_gcm_stream_init(ctx = r3, nonce = r4, nonce_len = r5, state = r6, scratch = r7)`. -/
def streamInitPre : List Instr :=
  save .r7 ++ [mov .r14 .r7, mov .r15 .r6, mov .r16 .r3, mov .r18 .r4, mov .r19 .r5]

def streamInit : Prog isa := .seq (.block streamInitPre) (.seq j0 (.block restore))

/-- `vg_aes_gcm_stream_aad(ctx = r3, state = r4, aad_len = r5, data = r6, len = r7, scratch = r8)`. -/
def streamAadPre : List Instr :=
  save .r8 ++ [mov .r14 .r8, mov .r15 .r4, mov .r16 .r3, mov .r18 .r6, mov .r19 .r7, .li .r9 15,
    .logic .and .r20 .r5 .r9]

def streamAad : Prog isa := .seq (.block streamAadPre) (.seq (absorb 16) (.block restore))

/-- The entry of `encrypt` and `decrypt`: `(ctx = r3, rounds = r4, state = r5,
aad_len = r6, text_len = r7, data = r8, len = r9, scratch = r10)`. -/
def cryptEntry : List Instr :=
  save .r10 ++ [mov .r14 .r10, mov .r15 .r5, mov .r16 .r3, mov .r17 .r4, mov .r21 .r6, mov .r22 .r7,
    mov .r23 .r8, mov .r24 .r9]

/-- The arguments of `crypt` or `absorb` for the text: the data, its length,
and the length of the text so far modulo 16. -/
def textArgs : List Instr := [mov .r18 .r23, mov .r19 .r24, .li .r5 15, .logic .and .r20 .r22 .r5]

/-- The additional data padded, before the first text. -/
def firstFlush : Prog isa := .seq (.block [.li .r5 15, .logic .and .r20 .r21 .r5]) (flush 16)

/-- The text (`r24` bytes at `r23`) absorbed into GHASH. -/
def textAbsorb : Prog isa :=
  .ite (.zero .d .r24) (.block [])
    (.seq (.ite (.zero .d .r22) firstFlush (.block [])) (.seq (.block textArgs) (absorb 16)))

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncrypt : Prog isa :=
  .seq (.block (cryptEntry ++ textArgs)) (.seq crypt (.seq textAbsorb (.block restore)))

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecrypt : Prog isa :=
  .seq (.block cryptEntry) (.seq textAbsorb (.seq (.block textArgs) (.seq crypt (.block restore))))

/-- The entry of `finish` and `verify`: `(ctx = r3, rounds = r4, state = r5,
aad_len = r6, text_len = r7, tag = r8, …, work = b)`. -/
def finEntry (b : Reg) : List Instr :=
  save b ++ [mov .r14 b, mov .r15 .r5, mov .r16 .r3, mov .r17 .r4, mov .r21 .r6, mov .r22 .r7,
    mov .r23 .r8]

/-- The buffered bytes padded and absorbed, and the tag into `d + o`. -/
def finTag (d : Reg) (o : Nat) : Prog isa :=
  .seq (.block [mov .r5 .r22])
  (.seq (.ite (.zero .d .r22) (.block [mov .r5 .r21]) (.block []))
  (.seq (.block [.li .r6 15, .logic .and .r20 .r5 .r6])
  (.seq (flush 16)
    (tag d o))))

/-- `vg_aes_gcm_stream_finish`, with `work = r9`: the tag into `tag`. -/
def streamFinish : Prog isa := .seq (.block (finEntry .r9)) (.seq (finTag .r23 0) (.block restore))

/-- `vg_aes_gcm_stream_verify`, with `tag_len = r9` and `work = r10`. -/
def streamVerify : Prog isa :=
  .seq (.block (finEntry .r10 ++ [mov .r24 .r9]))
    (.seq (tagLenOk (.seq (finTag .r14 vO) cmp) (.block [.li .r3 0])) (.block restore))

end VG.Impl.AesGcm.PPC64LE
