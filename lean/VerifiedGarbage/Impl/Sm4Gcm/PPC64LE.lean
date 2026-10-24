module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Ctr32
public import VerifiedGarbage.Impl.Sm4.PPC64LE.ExpandKey

/-!
# SM4-GCM: PPC64LE implementation

The SM4-GCM functions of `Spec/Sm4/Gcm/Contract.lean`: AES-GCM's code
(`Impl/AesGcm/PPC64LE.lean`, whose description of the working space, the
registers and the pieces applies here too), with SM4's key context and
functions. `vg_sm4_gcm_stream_init` and `vg_sm4_gcm_stream_aad`, which read
only the hash subkey, are AES-GCM's functions themselves.

* The key context is SM4's 128-byte schedule, then, at AES-GCM's offset, the
  hash subkey: `H` is at `ctx + 240`, where AES-GCM's GHASH pieces read it.
* SM4's counter mode (`Impl.Sm4.PPC64LE.ctr32`, `vg_sm4_ctr32`'s code
  before its frame: `schedule = r3, counter = r4, data = r5, n = r6,
  scratch = r7`) and key expansion (`Impl.Sm4.PPC64LE.expandKey`:
  `key = r3, schedule = r4, scratch = r5`) are inlined, with their working
  space `X` of 3264 bytes, the argument after `W` (in a frame of its own: a
  frame is less than a page, too small for both), kept in `r28`. They
  preserve the nonvolatile registers and the link register, as calls would,
  and need no stack, so the functions use none but the frames holding `W`
  and `X`.
* There is no number of rounds: the arguments of every function but
  `stream_init` and `stream_aad` are one register earlier than AES-GCM's.
-/

@[expose] public section

namespace VG.Impl.Sm4Gcm.PPC64LE

open VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov tO save restore cryptFill splitWhole lens flush absorb tagLenOk recv cmp
  j0 textArgs textAbsorb tagOut oneAad dataArgs)

/-! ## Counter mode -/

/-- The arguments of SM4's counter mode but the data and their number: the key
schedule, the counter block (at `r30 + c`) and the working space. -/
def ctrArgs (c : Nat) : List Instr :=
  [mov .r3 .r29, .addi .r4 .r30 c, mov .r7 .r28]

/-- Whole blocks at `r24`, by SM4's counter mode, from the counter block at
`r30 + 48`: `splitWhole` leaves their address in `r5` and number in `r6`. -/
def cryptWhole : Prog isa :=
  .seq (.block splitWhole)
    (.ite (.zero .d .r6) (.block []) (.seq (.block (ctrArgs 48)) Impl.Sm4.PPC64LE.ctr32))

/-- The keystream block zeroed, and the arguments of SM4's counter mode on it. -/
def tailArgs : List Instr :=
  ([.li .r0 0, .store .d .r0 .r30 64, .store .d .r0 .r30 72, .addi .r5 .r30 64, .li .r6 1] :
    List Instr) ++ ctrArgs 48

/-- The last `r25` bytes at `r24`, with a new keystream block. -/
def cryptTail : Prog isa :=
  .ite (.zero .d .r25) (.block [])
    (.seq (.seq (.block tailArgs) Impl.Sm4.PPC64LE.ctr32)
      (.seq (.block [.addi .r3 .r30 64, mov .r4 .r24, mov .r5 .r25]) Impl.AesGcm.PPC64LE.xorLoop))

def crypt : Prog isa :=
  .ite (.zero .d .r25) (.block []) (.seq cryptFill (.seq cryptWhole cryptTail))

/-! ## The tag -/

/-- The accumulator copied to `W + o`, and the arguments of SM4's counter mode
on it with the counter block `J₀` at the state. -/
def tagArgs (o : Nat) : List Instr :=
  [.load .d .r3 .r30 16, .store .d .r3 .r31 o, .load .d .r3 .r30 24, .store .d .r3 .r31 (o + 8),
   mov .r3 .r29, mov .r4 .r30, .addi .r5 .r31 o, .li .r6 1, mov .r7 .r28]

/-- The tag into `W + o`, after the lengths block of `r24` and `r26` bytes. -/
def tag (o : Nat) : Prog isa :=
  .seq (lens 16) (.seq (.block (tagArgs o)) Impl.Sm4.PPC64LE.ctr32)

/-- The buffered bytes padded and absorbed, and the tag into `W + o`, for
`aad_len` (`r22`) bytes of additional data and `text_len` (`r23`) of text. -/
def finTag (o : Nat) : Prog isa :=
  .seq (.ite (.zero .d .r23) (.block [.li .r0 15, .logic .and .r26 .r22 .r0])
      (.block [.li .r0 15, .logic .and .r26 .r23 .r0]))
  (.seq (flush 16)
  (.seq (.block [mov .r24 .r22, mov .r26 .r23])
    (tag o)))

/-! ## The functions -/

/-- `vg_sm4_gcm_init(key = r3, ctx = r4, scratch = r5, sm4 = r6)`: the key
schedule is written to the context, with the key and the context already in
key expansion's argument registers. -/
def initPre : List Instr :=
  save .r5 ++ ([mov .r29 .r4, mov .r28 .r6, mov .r5 .r6] : List Instr)

/-- The hash subkey's block and `T` zeroed, and the arguments of SM4's counter
mode on them. -/
def initArgs : List Instr :=
  [.li .r0 0, .store .d .r0 .r29 240, .store .d .r0 .r29 248, .store .d .r0 .r31 tO,
   .store .d .r0 .r31 (tO + 8), mov .r3 .r29, .addi .r4 .r31 tO, .addi .r5 .r29 240, .li .r6 1,
   mov .r7 .r28]

def init : Prog isa :=
  .seq (.block initPre)
  (.seq Impl.Sm4.PPC64LE.expandKey
  (.seq (.block initArgs) (.seq Impl.Sm4.PPC64LE.ctr32 (.block restore))))

/-- The entry of `encrypt` and `decrypt`: `(ctx = r3, state = r4, aad_len = r5,
text_len = r6, data = r7, len = r8, scratch = r9, sm4 = r10)`, kept in `r29`,
`r30`, `r22`, `r23`, `r20`, `r19` and `r28`. -/
def cryptEntry : List Instr :=
  save .r9 ++ ([mov .r30 .r4, mov .r29 .r3, mov .r22 .r5, mov .r23 .r6, mov .r20 .r7, mov .r19 .r8,
    mov .r28 .r10] : List Instr)

/-- `vg_sm4_gcm_stream_encrypt`. -/
def streamEncrypt : Prog isa :=
  .seq (.block (cryptEntry ++ textArgs)) (.seq crypt (.seq textAbsorb (.block restore)))

/-- `vg_sm4_gcm_stream_decrypt`. -/
def streamDecrypt : Prog isa :=
  .seq (.block cryptEntry) (.seq textAbsorb (.seq (.block textArgs) (.seq crypt (.block restore))))

/-- The entry of `finish`: `(ctx = r3, state = r4, aad_len = r5, text_len = r6,
tag = r7, scratch = r8, sm4 = r9)`, kept in `r29`, `r30`, `r22`, `r23`, `r20`
and `r28`. -/
def finEntry : List Instr :=
  save .r8 ++ ([mov .r30 .r4, mov .r29 .r3, mov .r22 .r5, mov .r23 .r6, mov .r20 .r7, mov .r28 .r9] :
    List Instr)

/-- `vg_sm4_gcm_stream_finish`. -/
def streamFinish : Prog isa :=
  .seq (.block finEntry) (.seq (finTag 0) (.seq (.block tagOut) (.block restore)))

/-- The entry of `verify`: `(ctx = r3, state = r4, aad_len = r5, text_len = r6,
tag = r7, tag_len = r8, scratch = r9, sm4 = r10)`, kept in `r29`, `r30`,
`r22`, `r23`, `r20`, `r19` and `r28`. -/
def verEntry : List Instr :=
  save .r9 ++ ([mov .r30 .r4, mov .r29 .r3, mov .r22 .r5, mov .r23 .r6, mov .r20 .r7, mov .r19 .r8,
    mov .r28 .r10] : List Instr)

/-- `vg_sm4_gcm_stream_verify`. -/
def streamVerify : Prog isa :=
  .seq (.block verEntry)
  (.seq tagLenOk
  (.seq (.ite (.zero .d .r25) (.block [.li .r3 0])
      (.seq recv (.seq (finTag 0) (cmp 0))))
    (.block restore)))

/-! ## One shot -/

/-- The entry of `seal` and `open`: `(ctx = r3, nonce = r4, nonce_len = r5,
aad = r6, aad_len = r7, data = r8, len = r9, tag = r10, …, scratch =
[sp + off], sm4 = [sp + off + 8])`, kept in `r29`, `r24` (and `r25`, `r18`),
`r21`, `r22`, `r27`, `r23`, `r20` and `r28`; the state is at `W + 16`
(`r30`). -/
def oneEntry (off : Nat) : List Instr :=
  [.addSp .r12 0, .load .d .r12 .r12 off] ++ save .r12 ++
    ([mov .r29 .r3, .addi .r30 .r31 16, mov .r24 .r4, mov .r25 .r5, mov .r18 .r5, mov .r21 .r6,
      mov .r22 .r7, mov .r27 .r8, mov .r23 .r9, mov .r20 .r10, .addSp .r12 0, .load .d .r28 .r12 (off + 8)] :
      List Instr)

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

/-- `vg_sm4_gcm_seal`, with `scratch = [sp + 96]` and `sm4 = [sp + 104]`. -/
def «seal» : Prog isa :=
  .seq (.block (oneEntry 96))
    (.seq oneAad (.seq oneCrypt (.seq (oneTag 0) (.seq (.block tagOut) (.block restore)))))

/-- The entry of `open`, with `tag_len = [sp + 96]` in `r19`,
`scratch = [sp + 104]` and `sm4 = [sp + 112]`. -/
def openEntry : List Instr := oneEntry 104 ++ ([.addSp .r12 0, .load .d .r19 .r12 96] : List Instr)

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

/-- `vg_sm4_gcm_open`, with `tag = r10`, `tag_len = [sp + 96]`,
`scratch = [sp + 104]` and `sm4 = [sp + 112]`. -/
def «open» : Prog isa :=
  .seq (.block openEntry)
  (.seq tagLenOk
  (.seq (.ite (.zero .d .r25) (.block [.li .r3 0]) openGood)
    (.block restore)))

end VG.Impl.Sm4Gcm.PPC64LE
