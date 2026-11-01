module

public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.Sm4.RISCV64.Modes
public import VerifiedGarbage.Impl.Sm4.RISCV64.ExpandKey
public import VerifiedGarbage.Impl.StackScratch.RISCV64

/-!
# SM4-GCM: RISC-V implementation

The SM4-GCM functions of `Spec/Sm4/Gcm/Contract.lean`: AES-GCM's code
(`Impl/AesGcm/RISCV64.lean`, whose description of the working space, the
registers and the pieces applies here too), with SM4's key context and
functions, as on PPC64LE (`Impl/Sm4Gcm/PPC64LE.lean`).
`vg_sm4_gcm_stream_init` and `vg_sm4_gcm_stream_aad`, which read only the
hash subkey, are AES-GCM's functions themselves.

* The key context is SM4's 128-byte schedule, then, at AES-GCM's offset, the
  hash subkey: `H` is at `ctx + 240`, where AES-GCM's GHASH pieces read it.
* SM4's counter mode and key expansion are calls of the verified
  `vg_sm4_ctr32` (`schedule = a0, counter = a1, data = a2, n = a3`) and
  `vg_sm4_expand_key` (`key = a0, schedule = a1`), each with its working
  space in a frame of its own below the stack pointer (3232 and 3168 bytes),
  so they need no part of `W`. They preserve the callee-saved registers, as
  `vg_ghash` does.
* There is no number of rounds: the arguments of every function but
  `stream_init` and `stream_aad` are one register earlier than AES-GCM's,
  and `s3` is unused.
-/

@[expose] public section

namespace VG.Impl.Sm4Gcm.RISCV64

open VG.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov tO aadO dataO save restore cryptFill splitCtr lens flush absorb tagLenOk
  recv cmp j0 textArgs textAbsorb tagOut oneAad dataArgs xorLoop)

/-- A call of `vg_sm4_ctr32`. -/
def ctrCall : Prog isa := .call "vg_sm4_ctr32" Impl.Sm4.RISCV64.ctr32

/-- A call of `vg_sm4_expand_key`, in its frame. -/
def keyCall : Prog isa :=
  .call "vg_sm4_expand_key" (Impl.StackScratch.RISCV64.withStackScratchWiped 3168 .a2 396 Impl.Sm4.RISCV64.expandKey)

/-! ## Counter mode -/

/-- The arguments of `vg_sm4_ctr32`: the key schedule, the counter block (at
`s1 + c`), and the blocks and their number, which `splitCtr` (or `tailArgs`)
leaves in `a3` and `a4`. -/
def ctrArgs (c : Nat) : List Instr :=
  [mov .a0 .s2, .addi .a1 .s1 c, mov .a2 .a3, mov .a3 .a4]

/-- Whole blocks at `s4`, by `vg_sm4_ctr32`. -/
def cryptWhole : Prog isa :=
  .seq (.block splitCtr)
    (.ite (.zero .a4) (.block []) (.seq (.block (ctrArgs 48)) ctrCall))

/-- The keystream block zeroed, and the arguments of `vg_sm4_ctr32` on it. -/
def tailArgs : List Instr :=
  ([.li .t0 0, .store .d .t0 .s1 64, .store .d .t0 .s1 72, .addi .a3 .s1 64, .li .a4 1] :
    List Instr) ++ ctrArgs 48

/-- The last `s5` bytes at `s4`, with a new keystream block. -/
def cryptTail : Prog isa :=
  .ite (.zero .s5) (.block [])
    (.seq (.seq (.block tailArgs) ctrCall)
      (.seq (.block [.addi .a0 .s1 64, mov .a1 .s4, mov .a2 .s5]) xorLoop))

def crypt : Prog isa :=
  .ite (.zero .s5) (.block []) (.seq cryptFill (.seq cryptWhole cryptTail))

/-! ## The tag -/

/-- The accumulator copied to `W + o`, and the arguments of `vg_sm4_ctr32` on
it with the counter block `J₀` at the state. -/
def tagArgs (o : Nat) : List Instr :=
  [.load .d .t0 .s1 16, .store .d .t0 .s0 o, .load .d .t0 .s1 24, .store .d .t0 .s0 (o + 8),
   mov .a0 .s2, mov .a1 .s1, .addi .a2 .s0 o, .li .a3 1]

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

/-! ## The functions -/

/-- `vg_sm4_gcm_init(key = a0, ctx = a1, scratch = a2)`: the key schedule is
written to the context, with the key and the context already in key
expansion's argument registers. -/
def initPre : List Instr :=
  save .a2 ++ ([mov .s2 .a1] : List Instr)

/-- The hash subkey's block and `T` zeroed, and the arguments of
`vg_sm4_ctr32` on them. -/
def initArgs : List Instr :=
  [.li .t0 0, .store .d .t0 .s2 240, .store .d .t0 .s2 248, .store .d .t0 .s0 tO,
   .store .d .t0 .s0 (tO + 8), mov .a0 .s2, .addi .a1 .s0 tO, .addi .a2 .s2 240, .li .a3 1]

def init : Prog isa :=
  .seq (.block initPre)
  (.seq keyCall
  (.seq (.block initArgs) (.seq ctrCall (.block restore))))

/-- The entry of `encrypt` and `decrypt`: `(ctx = a0, state = a1, aad_len = a2,
text_len = a3, data = a4, len = a5, scratch = a6)`, kept in `s2`, `s1`,
`s10`, `s11`, `s9` and `s8`. -/
def cryptEntry : List Instr :=
  save .a6 ++ ([mov .s1 .a1, mov .s2 .a0, mov .s10 .a2, mov .s11 .a3, mov .s9 .a4, mov .s8 .a5] :
    List Instr)

/-- `vg_sm4_gcm_stream_encrypt`. -/
def streamEncrypt : Prog isa :=
  .seq (.block (cryptEntry ++ textArgs)) (.seq crypt (.seq textAbsorb (.block restore)))

/-- `vg_sm4_gcm_stream_decrypt`. -/
def streamDecrypt : Prog isa :=
  .seq (.block cryptEntry) (.seq textAbsorb (.seq (.block textArgs) (.seq crypt (.block restore))))

/-- The entry of `finish`: `(ctx = a0, state = a1, aad_len = a2, text_len = a3,
tag = a4, scratch = a5)`, kept in `s2`, `s1`, `s10`, `s11` and `s9`. -/
def finEntry : List Instr :=
  save .a5 ++ ([mov .s1 .a1, mov .s2 .a0, mov .s10 .a2, mov .s11 .a3, mov .s9 .a4] : List Instr)

/-- `vg_sm4_gcm_stream_finish`. -/
def streamFinish : Prog isa :=
  .seq (.block finEntry) (.seq (finTag 0) (.seq (.block tagOut) (.block restore)))

/-- The entry of `verify`: `(ctx = a0, state = a1, aad_len = a2, text_len = a3,
tag = a4, tag_len = a5, scratch = a6)`, kept in `s2`, `s1`, `s10`, `s11`,
`s9` and `s8`. -/
def verEntry : List Instr :=
  save .a6 ++ ([mov .s1 .a1, mov .s2 .a0, mov .s10 .a2, mov .s11 .a3, mov .s9 .a4, mov .s8 .a5] :
    List Instr)

/-- `vg_sm4_gcm_stream_verify`. -/
def streamVerify : Prog isa :=
  .seq (.block verEntry)
  (.seq tagLenOk
  (.seq (.ite (.zero .s5) (.block [.li .a0 0])
      (.seq recv (.seq (finTag 0) (cmp 0))))
    (.block restore)))

/-! ## One shot -/

/-- The entry of `seal` and `open`: `(ctx = a0, nonce = a1, nonce_len = a2,
aad = a3, aad_len = a4, data = a5, len = a6, tag = a7, …, scratch =
[sp + off])`, kept in `s2`, `s4` (and `s5`, `s7`), `W + aadO`, `s10`,
`W + dataO`, `s11` and `s9`; the state is at `W + 16` (`s1`). -/
def oneEntry (off : Nat) : List Instr :=
  [.addSp .t1 0, .load .d .t1 .t1 off] ++ save .t1 ++
    ([mov .s2 .a0, .addi .s1 .s0 16, mov .s4 .a1, mov .s5 .a2, mov .s7 .a2, .store .d .a3 .s0 aadO,
      mov .s10 .a4, .store .d .a5 .s0 dataO, mov .s11 .a6, mov .s9 .a7] : List Instr)

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

/-- `vg_sm4_gcm_seal`, with `scratch = [sp]`. -/
def «seal» : Prog isa :=
  .seq (.block (oneEntry 0))
    (.seq oneAad (.seq oneCrypt (.seq (oneTag 0) (.seq (.block tagOut) (.block restore)))))

/-- The entry of `open`, with `tag_len = [sp]` in `s8` and `scratch = [sp + 8]`. -/
def openEntry : List Instr := oneEntry 8 ++ ([.addSp .t1 0, .load .d .s8 .t1 0] : List Instr)

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

/-- `vg_sm4_gcm_open`, with `tag = a7`, `tag_len = [sp]` and `scratch = [sp + 8]`. -/
def «open» : Prog isa :=
  .seq (.block openEntry)
  (.seq tagLenOk
  (.seq (.ite (.zero .s5) (.block [.li .a0 0]) openGood)
    (.block restore)))

end VG.Impl.Sm4Gcm.RISCV64
