module
public import VerifiedGarbage.Impl.AesGcm.X86
public import VerifiedGarbage.Impl.Sm4.X86.Ctr32
public import VerifiedGarbage.Impl.Sm4.X86.ExpandKey
public import VerifiedGarbage.Impl.StackScratch.X86

/-!
# SM4-GCM: x86 (32-bit) implementation

The SM4-GCM functions of `Spec/Sm4/Gcm/Contract.lean`, cdecl (every argument
on the stack), composed of calls of the verified `vg_sm4_expand_key`,
`vg_sm4_ctr32` and `vg_ghash`, as AES-GCM's (`Impl/AesGcm/X86.lean`), with
whose working space, registers and pieces they share everything that does
not encrypt: SM4-GCM's key context has AES-GCM's layout, the hash subkey at
`ctx + 240`, so the pieces that only hash (`absorb`, `flush`, `lens`, `j0`,
`firstFlush`, `textAbsorb`, `oneAad`), compare tags (`recv`, `cmp`,
`tagLenOk`), copy them (`tagOut`) or XOR the rest of a keystream block
(`cryptHead`) are AES-GCM's, and so are `vg_sm4_gcm_stream_init` and
`vg_sm4_gcm_stream_aad`, which only hash. They take AES-GCM's callees
(`Callees`), of which they call only `vg_ghash` (`gh`).

What differs:

* the cipher is `vg_sm4_ctr32(schedule, counter, data, n)`, whose schedule is
  the key context's first 128 bytes and whose working space is on its own
  stack, below its return address, and the key schedule is
  `vg_sm4_expand_key(key, schedule)`'s: so `crypt` and `tag` call them with
  these four arguments (`ctrCall`), and `init` with the key context's
  address as the schedule's (`keyCall`). A call of `vg_sm4_ctr32` uses 1536
  bytes of stack with its arguments and return address, one of
  `vg_sm4_expand_key` 1460;
* there is no number of rounds, so the functions that encrypt take their
  arguments at other positions (`cryptEntry`, `finEntry`, `oneEntry`), and
  the working space `W + 512` on goes only to `vg_ghash`.

Only the pointers, the lengths, `tag_len` and (for `open`) whether the tag
is right can affect timing, as for AES-GCM.
-/

@[expose] public section

namespace VG.Impl.Sm4Gcm.X86

open VG.X86
open VG.Impl.AesGcm.X86 (Fn Callees at_ imm slot argOp keep zero4 restore entry splitWhole xorLoop minLen
  cryptHead lens absorb flush recv cmp tagLenOk tagOut setText textAbsorb oneAad setData
  tO uO ctxO alO ahO xlO xhO dataO lenO aadO nlO zO tpO tglO auxO stO dO nO bO)

/-- `vg_sm4_ctr32`, as registered (`Artifacts/Sm4Gcm/X86.lean`): its
working space in a frame of its own. -/
def ctrFn : Fn :=
  ⟨"vg_sm4_ctr32", Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ctr32⟩

/-- `vg_sm4_expand_key`, as registered (`Artifacts/Sm4/X86.lean`). -/
def keyFn : Fn :=
  ⟨"vg_sm4_expand_key", Impl.StackScratch.X86.withStackScratchWiped 1448 2 358 Impl.Sm4.X86.expandKey⟩

/-! ## Calls -/

/-- `vg_sm4_ctr32(eax, edx, ebx, edi)`. -/
def ctrCall : Prog isa :=
  .frame (.push [.edi, .ebx, .edx, .eax]) (.call ctrFn.name ctrFn.code) (.pop .eax 4)

/-- `vg_sm4_expand_key(eax, edx)`. -/
def keyCall : Prog isa :=
  .frame (.push [.edx, .eax]) (.call keyFn.name keyFn.code) (.pop .eax 2)

/-! ## Counter mode -/

/-- The arguments of `vg_sm4_ctr32` but the data and their number (`ebx`,
`edi`): the key schedule and the counter block at `esi + 48`. -/
def ctrArgs : List Instr :=
  [.mov .eax (slot ctxO), .mov .edx (.reg .esi), .alu .add .edx (imm 48)]

/-- Whole blocks at `dO`, by `vg_sm4_ctr32`. -/
def cryptWhole : Prog isa :=
  .seq (.block splitWhole)
    (.ite .e (.block []) (.seq (.block ctrArgs) ctrCall))

/-- The last `nO` bytes at `dO`, with a new keystream block. -/
def cryptTail : Prog isa :=
  .seq (.block [.mov .eax (slot nO), .alu .test .eax (.reg .eax)])
    (.ite .e (.block [])
      (.seq (.block (([.mov .eax (imm 0), .store (at_ .esi 64) .eax, .store (at_ .esi 68) .eax,
          .store (at_ .esi 72) .eax, .store (at_ .esi 76) .eax, .mov .ebx (.reg .esi), .alu .add .ebx (imm 64),
          .mov .edi (imm 1)] : List Instr) ++ ctrArgs))
      (.seq ctrCall
      (.seq (.block [.mov .edi (slot dO), .mov .edx (.reg .esi), .alu .add .edx (imm 64), .mov .ecx (slot nO)])
        xorLoop))))

/-- The `nO` bytes at `dO` XORed with the keystream, `bO` bytes into the
current keystream block (AES-GCM's `crypt`). -/
def crypt : Prog isa :=
  .seq (.block [.mov .eax (slot nO), .alu .test .eax (.reg .eax)])
    (.ite .e (.block [])
      (.seq (.block [.mov .eax (slot bO), .alu .test .eax (.reg .eax)])
      (.seq (.ite .e (.block []) cryptHead)
      (.seq cryptWhole cryptTail))))

section
variable (c : Callees)

/-! ## The tag -/

/-- The tag into `W + o`, for the lengths kept at `W + al`, …: the lengths
block absorbed, and `GHASH ⊕ CIPH_K(J₀)`, with `vg_sm4_ctr32` on it with the
counter block `J₀` (at `esi`). -/
def tag (o al ah tl th : Nat) : Prog isa :=
  .seq (lens c 16 al ah tl th)
  (.seq (.block [.mov .eax (.mem (at_ .esi 16)), .mov .ecx (.mem (at_ .esi 20)), .mov .edx (.mem (at_ .esi 24)),
      .mov .ebx (.mem (at_ .esi 28)), .store (at_ .ebp o) .eax, .store (at_ .ebp (o + 4)) .ecx,
      .store (at_ .ebp (o + 8)) .edx, .store (at_ .ebp (o + 12)) .ebx, .mov .ebx (.reg .ebp),
      .alu .add .ebx (imm o), .mov .edi (imm 1), .mov .eax (slot ctxO), .mov .edx (.reg .esi)])
    ctrCall)

/-! ## The functions -/

/-- `vg_sm4_gcm_init(key, ctx, scratch)`: the key schedule into the key
context's first 128 bytes, then `H = CIPH_K(0¹²⁸)` into its last 16, the
encryption of a zero block at `ctx + 240` from a zero counter block at
`W + 96`. -/
def init : Prog isa :=
  .seq (entry 2 [.mov .esi (argOp 1), .mov .eax (argOp 0), .mov .edx (.reg .esi)])
  (.seq keyCall
  (.seq (.block (([.mov .eax (imm 0), .store (at_ .esi 240) .eax, .store (at_ .esi 244) .eax,
      .store (at_ .esi 248) .eax, .store (at_ .esi 252) .eax] : List Instr) ++ zero4 tO ++
      ([.mov .eax (.reg .esi), .mov .edx (.reg .ebp), .alu .add .edx (imm tO),
        .mov .ebx (.reg .esi), .alu .add .ebx (imm 240), .mov .edi (imm 1)] : List Instr)))
  (.seq ctrCall
    (.block restore))))

/-- The entry of `encrypt` and `decrypt`: `(ctx, state, aad_len (2 words),
text_len (2 words), data, len, scratch)`. -/
def cryptEntry : Prog isa :=
  entry 8 (([.mov .esi (argOp 1)] : List Instr) ++ keep 0 ctxO ++ keep 2 alO ++ keep 3 ahO ++
    keep 4 xlO ++ keep 5 xhO ++ keep 6 dataO ++ keep 7 lenO)

/-- `vg_sm4_gcm_stream_encrypt`. -/
def streamEncrypt : Prog isa :=
  .seq cryptEntry (.seq (.block setText) (.seq crypt (.seq (textAbsorb c) (.block restore))))

/-- `vg_sm4_gcm_stream_decrypt`. -/
def streamDecrypt : Prog isa :=
  .seq cryptEntry (.seq (textAbsorb c) (.seq (.block setText) (.seq crypt (.block restore))))

/-- The entry of `finish` and `verify`: `(ctx, state, aad_len (2 words),
text_len (2 words), tag, …)`, with `W` the stack argument `w`, and `rest`. -/
def finEntry (w : Nat) (rest : List Instr) : Prog isa :=
  entry w (([.mov .esi (argOp 1)] : List Instr) ++ keep 0 ctxO ++ keep 2 alO ++ keep 3 ahO ++
    keep 4 xlO ++ keep 5 xhO ++ rest)

/-- The buffered bytes padded and absorbed, and the tag into `W + o`
(AES-GCM's `finTag`, with `tag`). -/
def finTag (o : Nat) : Prog isa :=
  .seq (.block [.mov .eax (slot xlO), .mov .ecx (slot alO), .mov .edx (slot xlO), .alu .or .edx (slot xhO)])
  (.seq (.ite .e (.block [.mov .eax (.reg .ecx)]) (.block []))
  (.seq (.block [.alu .and .eax (imm 15), .store (at_ .ebp bO) .eax])
  (.seq (flush c 16) (tag c o alO ahO xlO xhO))))

/-- `vg_sm4_gcm_stream_finish(ctx, state, aad_len, text_len, tag, work)`. -/
def streamFinish : Prog isa :=
  .seq (finEntry 7 (keep 6 tpO)) (.seq (finTag c 0) (.seq (tagOut 0) (.block restore)))

/-- `vg_sm4_gcm_stream_verify(ctx, state, aad_len, text_len, tag, tag_len, work)`. -/
def streamVerify : Prog isa :=
  .seq (finEntry 8 (keep 6 tpO ++ keep 7 tglO))
  (.seq tagLenOk
  (.seq (.ite .e (.block [.mov .eax (imm 0)])
      (.seq recv (.seq (finTag c 0) (cmp 0))))
    (.block restore)))

/-- The entry of `seal` and `open`: `(ctx, nonce, nonce_len, aad, aad_len,
data, len, tag, …)`, with `W` the stack argument `w`, and `rest`. The state
is at `W + 16`. -/
def oneEntry (w : Nat) (rest : List Instr) : Prog isa :=
  entry w (([.mov .esi (.reg .ebp), .alu .add .esi (imm stO)] : List Instr) ++ keep 0 ctxO ++ keep 1 dO ++
    keep 2 nO ++ keep 2 nlO ++ keep 3 aadO ++ keep 4 alO ++ keep 5 dataO ++ keep 6 lenO ++ rest ++
    ([.mov .eax (imm 0), .store (at_ .ebp zO) .eax] : List Instr))

/-- The data (as ciphertext) absorbed and padded, and the tag into `W + o`
(AES-GCM's `oneTag`, with `tag`). -/
def oneTag (o : Nat) : Prog isa :=
  .seq (.block setData)
  (.seq (absorb c 16)
  (.seq (.block [.mov .eax (slot lenO), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax])
  (.seq (flush c 16) (tag c o alO zO lenO zO))))

/-- The data encrypted or decrypted, from the first counter block. -/
def oneCrypt : Prog isa := .seq (.block setData) crypt

/-- `vg_sm4_gcm_seal(ctx, nonce, nonce_len, aad, aad_len, data, len, tag, work)`. -/
def «seal» : Prog isa :=
  .seq (oneEntry 8 (keep 7 tpO))
    (.seq (oneAad c) (.seq oneCrypt (.seq (oneTag c 0) (.seq (tagOut 0) (.block restore)))))

/-- `vg_sm4_gcm_open(ctx, nonce, nonce_len, aad, aad_len, data, len, tag, tag_len, work)`. -/
def «open» : Prog isa :=
  .seq (oneEntry 9 (keep 7 tpO ++ keep 8 tglO))
  (.seq tagLenOk
  (.seq (.ite .e (.block [.mov .eax (imm 0)])
      (.seq (oneAad c)
      (.seq (oneTag c uO)
      (.seq recv
      (.seq (cmp uO)
      (.seq (.block [.store (at_ .ebp auxO) .eax, .alu .test .eax (.reg .eax)])
      (.seq (.ite .e (.block []) oneCrypt)
        (.block [.mov .eax (slot auxO)]))))))))
    (.block restore)))

end

end VG.Impl.Sm4Gcm.X86
