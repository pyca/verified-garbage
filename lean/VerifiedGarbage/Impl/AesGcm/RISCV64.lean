module

public import VerifiedGarbage.Impl.Aes.RISCV64.ExpandKey
public import VerifiedGarbage.Impl.AesCtr.RISCV64
public import VerifiedGarbage.Impl.Gcm.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
public import VerifiedGarbage.Impl.Words.RISCV64.Loops

/-!
# AES-GCM: RISC-V implementation

The AES-GCM functions of `Spec/Gcm/Contract.lean`, composed of calls of the
verified `vg_aes_expand_key_scratch`, `vg_aes_ctr32` and `vg_ghash`, as on
PPC64LE (`Impl/AesGcm/PPC64LE.lean`), piece for piece. A call (`call`)
stores nothing in memory; `vg_ghash` uses 2048 bytes of stack below the
stack pointer for its table, the other callees none.

## The working space

Every function has a buffer `W` of 2560 bytes (`scratch`):

* `[0, 16)`: the tag `finish`, `verify` and `seal` compute (which `finish`
  and `seal` then copy to `tag`);
* `[16, 96)`: the streaming state of `seal` and `open`;
* `[96, 112)`: a block `T`: a partial block padded with zeros, or the
  lengths block (or `init`'s zero counter block);
* `[112, 128)`: the tag `open` computes;
* `[128, 224)`: our caller's `s0`–`s11`, `[224, 232)` our return address (a
  call replaces `ra`), and `[232, 240)` and `[240, 248)` the additional
  data and the data of `seal` and `open` (`aadO`, `dataO`);
* `[256, 272)` and `[272, 288)`: the two tags compared, padded with zeros;
* `[512, 2560)`: the working space of the functions called.

## Registers

`s0` holds `W`, `s1` the streaming state and `s2` the key context
throughout, and `s3` the number of rounds in the functions that need it; the
functions called preserve them (they are callee-saved). The pieces below
(`absorb`, `flush`, `crypt`, …) take their arguments in `s4` (a pointer),
`s5` (a length) and `s6` (an offset), which the callees also preserve, and
`lens` the two lengths in `s4` and `s6`. `j0` reads the nonce's length from
`s7`, which `stream_init`, `seal` and `open` set on entry. `s8` holds the
length of the text (or of the received tag), `s9` the text (or the tag),
`s10` the length of the additional data and `s11` the length of the text so
far (or of the data). `a0`–`a7` and `t0`–`t6` are temporaries.

There are fewer callee-saved registers than on PPC64LE, so `seal` and `open`
keep the additional data's and the data's addresses (PPC64LE's `r21` and
`r27`) in `W`, and load them when they need them.

## The pieces

As on PPC64LE (and ARMv7). The model has no indexed byte access and loads
and stores fault unless naturally aligned: the bytes of the caller's buffers
(nonce, additional data, data, tags) are copied a byte at a time, through
advancing pointers, counting down to zero, and the big-endian words GCM
needs (the lengths block, the counter's increment) are stored a byte at a
time. Only the pointers, the lengths, `rounds`, `tag_len` and (for `open`)
whether the tag is right can affect timing: the branches are on those, and
the tags are compared without a branch.
-/

@[expose] public section

namespace VG.Impl.AesGcm.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64 (loadBE32 storeBE copyBytes storeBytes)

/-- `mv d, n` (`addi d, n, 0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-! ## The working space -/

def tO : Nat := 96
def uO : Nat := 112
def scrO : Nat := 512
def raO : Nat := 224
def aadO : Nat := 232
def dataO : Nat := 240
/-- The received tag, padded with zeros. -/
def rO : Nat := 256
/-- The first bytes of the computed tag, padded with zeros. -/
def vO : Nat := 272

/-- Our caller's registers, and where we save them. -/
def saved : List (Reg × Nat) :=
  [(.s0, 128), (.s1, 136), (.s2, 144), (.s3, 152), (.s4, 160), (.s5, 168), (.s6, 176), (.s7, 184),
   (.s8, 192), (.s9, 200), (.s10, 208), (.s11, 216)]

/-- Saves them and the return address at `b`, and keeps `b` in `s0`. -/
def save (b : Reg) : List Instr :=
  saved.map (fun (r, d) => .store .d r b d) ++ ([.store .d .ra b raO, mov .s0 b] : List Instr)

/-- Restores the return address and the registers, through `t1` (a copy of
`W`, as `s0` is restored too). -/
def restore : List Instr :=
  ([mov .t1 .s0, .load .d .ra .t1 raO] : List Instr) ++ saved.map fun (r, d) => .load .d r .t1 d

/-! ## The calls -/

def ctrCall : Prog isa := Impl.AesCtr.RISCV64.ctrCall

def ghCall : Prog isa := .call "vg_ghash" Impl.Gcm.RISCV64.ghash

def keyCall : Prog isa := .call "vg_aes_expand_key_scratch" Impl.Aes.RISCV64.expandKey

/-! ## Loops -/

/-- Copies the `a2` (at least 1) bytes at `a0` to `a1`, advancing both. -/
def copyLoop : Prog isa := Impl.Words.RISCV64.copyLoop .t0 .a0 .a1 .a2

/-- XORs the `a2` (at least 1) bytes at `a0` into those at `a1`, advancing both. -/
def xorLoop : Prog isa :=
  .loop (.block [.load .b .t0 .a1 0, .load .b .a3 .a0 0, .logic .xor .t0 .t0 .a3, .store .b .t0 .a1 0,
    .addi .a0 .a0 1, .addi .a1 .a1 1, .addi .a2 .a2 (-1)]) (.nonzero .a2)

/-- `a2 := min (16 - s6, s5)`: `16 - s6` if `s5 ≥ 16`, and otherwise
whichever the sign of their difference (both being small) says. -/
def minLen : Prog isa :=
  .seq (.block [.li .a2 16, .sub .a2 .a2 .s6, .shift .srl .d .a3 .s5 4])
    (.ite (.nonzero .a3) (.block [])
      (.seq (.block [.sub .a3 .s5 .a2, .shift .srl .d .a3 .a3 63])
        (.ite (.nonzero .a3) (.block [mov .a2 .s5]) (.block []))))

/-! ## GHASH -/

/-- `vg_ghash` of the block at `b + o` into the accumulator at `s1 + yo`. -/
def ghash1 (yo : Nat) (b : Reg) (o : Nat) : Prog isa :=
  .seq (.block [.addi .a0 .s2 240, .addi .a1 .s1 yo, .addi .a2 b o, .li .a3 1, .addi .a4 .s0 scrO])
    ghCall

/-- Before the buffer is absorbed: the buffer filled from `s4` (`a2`
bytes), the arguments advanced, and `a3` zero if the buffer is full. -/
def headPre : Prog isa :=
  .seq minLen
  (.seq (.block [.addi .a1 .s1 32, .add .a1 .a1 .s6, mov .a0 .s4, .add .s4 .s4 .a2,
      .sub .s5 .s5 .a2, .add .s6 .s6 .a2])
  (.seq copyLoop (.block [.addi .a3 .s6 (-16)])))

/-- The buffer filled from `s4`, and absorbed if full. -/
def absorbHead (yo : Nat) : Prog isa :=
  .seq headPre (.ite (.zero .a3) (ghash1 yo .s1 32) (.block []))

/-- The whole blocks at `s4` split off: their address in `a2` and number in
`a3`, `s4` and `s5` the rest. -/
def splitWhole : List Instr :=
  [mov .a2 .s4, .shift .srl .d .a3 .s5 4, .logicImm .and .a5 .s5 15, .sub .a6 .s5 .a5,
   .add .s4 .s4 .a6, mov .s5 .a5]

/-- The whole blocks at `s4` absorbed. -/
def absorbWhole (yo : Nat) : Prog isa :=
  .seq (.block splitWhole)
    (.ite (.zero .a3) (.block [])
      (.seq (.block [.addi .a0 .s2 240, .addi .a1 .s1 yo, .addi .a4 .s0 scrO]) ghCall))

/-- The last `s5` bytes at `s4` buffered. -/
def absorbTail : Prog isa :=
  .ite (.zero .s5) (.block [])
    (.seq (.block [mov .a0 .s4, .addi .a1 .s1 32, mov .a2 .s5]) copyLoop)

/-- The buffer filled first, if it holds bytes. -/
def absorbFill (yo : Nat) : Prog isa :=
  .ite (.zero .s6) (.block []) (absorbHead yo)

def absorb (yo : Nat) : Prog isa :=
  .ite (.zero .s5) (.block []) (.seq (absorbFill yo) (.seq (absorbWhole yo) absorbTail))

/-- `T` zeroed, and the arguments of the copy of the `s6` buffered bytes to it. -/
def flushPre : List Instr :=
  [.li .t0 0, .store .d .t0 .s0 tO, .store .d .t0 .s0 (tO + 8), .addi .a0 .s1 32,
   .addi .a1 .s0 tO, mov .a2 .s6]

/-- The `s6` buffered bytes, padded with zeros in `T`, absorbed. -/
def flush (yo : Nat) : Prog isa :=
  .ite (.zero .s6) (.block []) (.seq (.seq (.block flushPre) copyLoop) (ghash1 yo .s0 tO))

/-- The lengths block of `s4` and `s6` bytes (in bits, big-endian), in `T`. -/
def lensBlock : List Instr :=
  ([.shift .sll .d .a0 .s4 3, .shift .sll .d .a1 .s6 3] : List Instr) ++
    storeBE 8 .a0 .t0 .s0 tO ++ storeBE 8 .a1 .t0 .s0 (tO + 8)

/-- The lengths block of `s4` and `s6` bytes, absorbed. -/
def lens (yo : Nat) : Prog isa :=
  .seq (.block lensBlock) (ghash1 yo .s0 tO)

/-! ## Counter mode -/

/-- The rest of the keystream block, from byte `s6`, into `s4`. -/
def cryptHead : Prog isa :=
  .seq minLen
  (.seq (.block [.addi .a0 .s1 64, .add .a0 .a0 .s6, mov .a1 .s4, .add .s4 .s4 .a2,
      .sub .s5 .s5 .a2])
    xorLoop)

/-- The whole blocks at `s4` split off: their address in `a3` and number in
`a4`, `s4` and `s5` the rest. -/
def splitCtr : List Instr :=
  [mov .a3 .s4, .shift .srl .d .a4 .s5 4, .logicImm .and .a5 .s5 15, .sub .a6 .s5 .a5,
   .add .s4 .s4 .a6, mov .s5 .a5]

/-- The arguments of `vg_aes_ctr32` but the data and their number: the key
schedule, the rounds, the counter block (at `s1 + c`) and the working
space. -/
def ctrArgs (c : Nat) : List Instr :=
  [mov .a0 .s2, mov .a1 .s3, .addi .a2 .s1 c, .addi .a5 .s0 scrO]

/-- Whole blocks at `s4`, by `vg_aes_ctr32`. -/
def cryptWhole : Prog isa :=
  .seq (.block splitCtr)
    (.ite (.zero .a4) (.block []) (.seq (.block (ctrArgs 48)) ctrCall))

/-- The keystream block zeroed, and the arguments of `vg_aes_ctr32` on it. -/
def tailArgs : List Instr :=
  ([.li .t0 0, .store .d .t0 .s1 64, .store .d .t0 .s1 72, .addi .a3 .s1 64, .li .a4 1] :
    List Instr) ++ ctrArgs 48

/-- The last `s5` bytes at `s4`, with a new keystream block. -/
def cryptTail : Prog isa :=
  .ite (.zero .s5) (.block [])
    (.seq (.seq (.block tailArgs) ctrCall)
      (.seq (.block [.addi .a0 .s1 64, mov .a1 .s4, mov .a2 .s5]) xorLoop))

/-- The rest of the keystream block first, if the text so far ends within a block. -/
def cryptFill : Prog isa :=
  .ite (.zero .s6) (.block []) cryptHead

def crypt : Prog isa :=
  .ite (.zero .s5) (.block []) (.seq cryptFill (.seq cryptWhole cryptTail))

/-! ## The tag -/

/-- The accumulator copied to `W + o`, and the arguments of `vg_aes_ctr32` on
it with the counter block `J₀` at the state. -/
def tagArgs (o : Nat) : List Instr :=
  [.load .d .t0 .s1 16, .store .d .t0 .s0 o, .load .d .t0 .s1 24, .store .d .t0 .s0 (o + 8),
   mov .a0 .s2, mov .a1 .s3, mov .a2 .s1, .addi .a3 .s0 o, .li .a4 1, .addi .a5 .s0 scrO]

/-- The tag into `W + o`, after the lengths block of `s4` and `s6` bytes. -/
def tag (o : Nat) : Prog isa :=
  .seq (lens 16) (.seq (.block (tagArgs o)) ctrCall)

/-- The buffered bytes padded and absorbed, and the tag into `W + o`, for
`aad_len` (`s10`) bytes of additional data and `text_len` (`s11`) of text. -/
def finTag (o : Nat) : Prog isa :=
  .seq (.ite (.zero .s11) (.block [.logicImm .and .s6 .s10 15])
      (.block [.logicImm .and .s6 .s11 15]))
  (.seq (flush 16)
  (.seq (.block [mov .s4 .s10, mov .s6 .s11])
    (tag o)))

/-! ## Comparing tags -/

/-- `s5 = 1` if the tag length `s8` is between 4 and 16 bytes, else 0. -/
def tagLenOk : Prog isa :=
  .seq (.block [.li .s5 0, .shift .srl .d .t0 .s8 2])
    (.ite (.zero .t0) (.block [])
      (.seq (.block [.shift .srl .d .t0 .s8 4])
        (.ite (.zero .t0) (.block [.li .s5 1])
          (.seq (.block [.addi .t0 .s8 (-16)])
            (.ite (.zero .t0) (.block [.li .s5 1]) (.block []))))))

/-- The `s8` bytes of the received tag (at `s9`), padded with zeros at `W + rO`. -/
def recv : Prog isa :=
  .seq (.block [.li .t0 0, .store .d .t0 .s0 rO, .store .d .t0 .s0 (rO + 8), mov .a0 .s9,
    .addi .a1 .s0 rO, mov .a2 .s8]) copyLoop

/-- `a0 = 1` if the padded tags at `W + vO` and `W + rO` are equal, else 0,
without a branch. -/
def cmpTail : List Instr :=
  [.load .d .a0 .s0 vO, .load .d .a1 .s0 rO, .logic .xor .a0 .a0 .a1, .load .d .a1 .s0 (vO + 8),
   .load .d .a2 .s0 (rO + 8), .logic .xor .a1 .a1 .a2, .logic .or .a0 .a0 .a1, .li .a1 0,
   .sub .a1 .a1 .a0, .logic .or .a0 .a0 .a1, .shift .srl .d .a0 .a0 63, .li .a1 1, .sub .a0 .a1 .a0]

/-- The first `s8` bytes of the tag at `W + o`, padded with zeros at
`W + vO`, compared with the received one: `a0 = 1` if they are equal. -/
def cmp (o : Nat) : Prog isa :=
  .seq (.block [.li .t0 0, .store .d .t0 .s0 vO, .store .d .t0 .s0 (vO + 8), .addi .a0 .s0 o,
    .addi .a1 .s0 vO, mov .a2 .s8])
    (.seq copyLoop (.block cmpTail))

/-! ## `J₀` -/

/-- `J₀ = IV ‖ 0³¹ ‖ 1` of a 12-byte nonce, at the state. -/
def j012 : List Instr := copyBytes .t0 .s4 .s1 0 0 12 ++ storeBytes .t0 .s1 12 [0, 0, 0, 1]

/-- `J₀` of any other nonce: GHASH of the nonce padded, then of the lengths
block of no additional data and the nonce, from a zero block at the state. -/
def j0hash : Prog isa :=
  .seq (.block [.li .t0 0, .store .d .t0 .s1 0, .store .d .t0 .s1 8, .li .s6 0])
  (.seq (absorb 0)
  (.seq (.block [.logicImm .and .s6 .s7 15])
  (.seq (flush 0)
  (.seq (.block [.li .s4 0, mov .s6 .s7])
    (lens 0)))))

/-- The first counter block `inc₃₂(J₀)`, and the accumulator zeroed. -/
def initState : List Instr :=
  ([.load .d .t0 .s1 0, .store .d .t0 .s1 48, .load .w .t0 .s1 8, .store .w .t0 .s1 56] :
    List Instr) ++ loadBE32 .a0 .t0 .s1 12 ++ ([.addi .a0 .a0 1] : List Instr) ++
    storeBE 4 .a0 .t0 .s1 60 ++
    ([.li .t0 0, .store .d .t0 .s1 16, .store .d .t0 .s1 24] : List Instr)

/-- The streaming state for the `s5`-byte nonce at `s4`. -/
def j0 : Prog isa :=
  .seq (.block [.addi .a2 .s5 (-12)]) (.seq (.ite (.zero .a2) (.block j012) j0hash) (.block initState))

/-! ## The functions -/

/-- `vg_aes_gcm_init(key = a0, key_len = a1, ctx = a2, scratch = a3)`. -/
def initPre : List Instr :=
  save .a3 ++ ([mov .s2 .a2, .shift .srl .d .s3 .a1 2, .addi .s3 .s3 6, .addi .a3 .s0 scrO] :
    List Instr)

/-- The hash subkey's block and `T` zeroed, and the arguments of
`vg_aes_ctr32` on them. -/
def initArgs : List Instr :=
  [.li .t0 0, .store .d .t0 .s2 240, .store .d .t0 .s2 248, .store .d .t0 .s0 tO,
   .store .d .t0 .s0 (tO + 8), mov .a0 .s2, mov .a1 .s3, .addi .a2 .s0 tO, .addi .a3 .s2 240,
   .li .a4 1, .addi .a5 .s0 scrO]

def init : Prog isa :=
  .seq (.block initPre)
  (.seq keyCall
  (.seq (.block initArgs) (.seq ctrCall (.block restore))))

/-- `vg_aes_gcm_stream_init(ctx = a0, nonce = a1, nonce_len = a2, state = a3, scratch = a4)`. -/
def streamInitPre : List Instr :=
  save .a4 ++ ([mov .s1 .a3, mov .s2 .a0, mov .s4 .a1, mov .s5 .a2, mov .s7 .a2] : List Instr)

def streamInit : Prog isa :=
  .seq (.block streamInitPre) (.seq j0 (.block restore))

/-- `vg_aes_gcm_stream_aad(ctx = a0, state = a1, aad_len = a2, data = a3, len = a4,
scratch = a5)`. -/
def streamAadPre : List Instr :=
  save .a5 ++ ([mov .s1 .a1, mov .s2 .a0, mov .s4 .a3, mov .s5 .a4, .logicImm .and .s6 .a2 15] :
    List Instr)

def streamAad : Prog isa :=
  .seq (.block streamAadPre) (.seq (absorb 16) (.block restore))

/-- The entry of `encrypt` and `decrypt`: `(ctx = a0, rounds = a1, state = a2,
aad_len = a3, text_len = a4, data = a5, len = a6, scratch = a7)`, kept in
`s2`, `s3`, `s1`, `s10`, `s11`, `s9` and `s8`. -/
def cryptEntry : List Instr :=
  save .a7 ++ ([mov .s1 .a2, mov .s2 .a0, mov .s3 .a1, mov .s10 .a3, mov .s11 .a4, mov .s9 .a5,
    mov .s8 .a6] : List Instr)

/-- The arguments of `crypt` or `absorb` for the text: the data, its length,
and the length of the text so far modulo 16. -/
def textArgs : List Instr := [mov .s4 .s9, mov .s5 .s8, .logicImm .and .s6 .s11 15]

/-- The additional data padded, before the first text. -/
def firstFlush : Prog isa :=
  .seq (.block [.logicImm .and .s6 .s10 15]) (flush 16)

/-- The text (`len` bytes at `data`) absorbed into GHASH. -/
def textAbsorb : Prog isa :=
  .ite (.zero .s8) (.block [])
    (.seq (.ite (.zero .s11) firstFlush (.block []))
      (.seq (.block textArgs) (absorb 16)))

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncrypt : Prog isa :=
  .seq (.block (cryptEntry ++ textArgs)) (.seq crypt (.seq textAbsorb (.block restore)))

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecrypt : Prog isa :=
  .seq (.block cryptEntry) (.seq textAbsorb (.seq (.block textArgs) (.seq crypt (.block restore))))

/-- The entry of `finish`: `(ctx = a0, rounds = a1, state = a2, aad_len = a3,
text_len = a4, tag = a5, scratch = a6)`, kept in `s2`, `s3`, `s1`, `s10`,
`s11` and `s9`. -/
def finEntry : List Instr :=
  save .a6 ++ ([mov .s1 .a2, mov .s2 .a0, mov .s3 .a1, mov .s10 .a3, mov .s11 .a4, mov .s9 .a5] :
    List Instr)

/-- The tag at `W` copied to `tag` (`s9`). -/
def tagOut : List Instr := copyBytes .t0 .s0 .s9 0 0 16

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinish : Prog isa :=
  .seq (.block finEntry) (.seq (finTag 0) (.seq (.block tagOut) (.block restore)))

/-- The entry of `verify`: `(ctx = a0, rounds = a1, state = a2, aad_len = a3,
text_len = a4, tag = a5, tag_len = a6, scratch = a7)`, kept in `s2`, `s3`,
`s1`, `s10`, `s11`, `s9` and `s8`. -/
def verEntry : List Instr :=
  save .a7 ++ ([mov .s1 .a2, mov .s2 .a0, mov .s3 .a1, mov .s10 .a3, mov .s11 .a4, mov .s9 .a5,
    mov .s8 .a6] : List Instr)

/-- `vg_aes_gcm_stream_verify`. -/
def streamVerify : Prog isa :=
  .seq (.block verEntry)
  (.seq tagLenOk
  (.seq (.ite (.zero .s5) (.block [.li .a0 0])
      (.seq recv (.seq (finTag 0) (cmp 0))))
    (.block restore)))

/-! ## One shot -/

/-- The entry of `seal` and `open`: `(ctx = a0, rounds = a1, nonce = a2,
nonce_len = a3, aad = a4, aad_len = a5, data = a6, len = a7, tag = [sp], …,
scratch = [sp + off])`, kept in `s2`, `s3`, `s4` (and `s5`, `s7`), `W + aadO`,
`s10`, `W + dataO`, `s11` and `s9`; the state is at `W + 16` (`s1`). -/
def oneEntry (off : Nat) : List Instr :=
  [.addSp .t1 0, .load .d .t1 .t1 off] ++ save .t1 ++
    ([mov .s2 .a0, mov .s3 .a1, .addi .s1 .s0 16, mov .s4 .a2, mov .s5 .a3, mov .s7 .a3,
      .store .d .a4 .s0 aadO, mov .s10 .a5, .store .d .a6 .s0 dataO, mov .s11 .a7, .addSp .t1 0,
      .load .d .s9 .t1 0] : List Instr)

/-- `J₀`, then the additional data absorbed and padded. -/
def oneAad : Prog isa :=
  .seq j0
  (.seq (.block [.load .d .s4 .s0 aadO, mov .s5 .s10, .li .s6 0])
  (.seq (absorb 16)
  (.seq (.block [.logicImm .and .s6 .s10 15])
    (flush 16))))

/-- The arguments of `crypt` or `absorb` for the data, from its start. -/
def dataArgs : List Instr := [.load .d .s4 .s0 dataO, mov .s5 .s11, .li .s6 0]

/-- The data encrypted or decrypted, from the first counter block. -/
def oneCrypt : Prog isa := .seq (.block dataArgs) crypt

/-- The data (as ciphertext) absorbed and padded, and the tag into `W + o`. -/
def oneTag (o : Nat) : Prog isa :=
  .seq (.block dataArgs)
  (.seq (absorb 16)
  (.seq (.block [.logicImm .and .s6 .s11 15])
  (.seq (flush 16)
  (.seq (.block [mov .s4 .s10, mov .s6 .s11])
    (tag o)))))

/-- `vg_aes_gcm_seal`, with `tag = [sp]` and `scratch = [sp + 8]`. -/
def «seal» : Prog isa :=
  .seq (.block (oneEntry 8))
    (.seq oneAad (.seq oneCrypt (.seq (oneTag 0) (.seq (.block tagOut) (.block restore)))))

/-- The entry of `open`, with `tag_len = [sp + 8]` in `s8` and
`scratch = [sp + 16]`. -/
def openEntry : List Instr := oneEntry 16 ++ ([.load .d .s8 .t1 8] : List Instr)

/-- `open` once the tag length is allowed: the nonce's length back in `s5`,
the tag of the ciphertext at `W + 112`, compared with the received one, the
result (`a0`) kept in `s8`, and the data decrypted only if they are equal. -/
def openGood : Prog isa :=
  .seq (.block [mov .s5 .s7])
  (.seq oneAad
  (.seq (oneTag 112)
  (.seq recv
  (.seq (cmp 112)
  (.seq (.block [mov .s8 .a0])
  (.seq (.ite (.zero .s8) (.block []) oneCrypt)
    (.block [mov .a0 .s8])))))))

/-- `vg_aes_gcm_open`, with `tag = [sp]`, `tag_len = [sp + 8]` and
`scratch = [sp + 16]`. -/
def «open» : Prog isa :=
  .seq (.block openEntry)
  (.seq tagLenOk
  (.seq (.ite (.zero .s5) (.block [.li .a0 0]) openGood)
    (.block restore)))

end VG.Impl.AesGcm.RISCV64
