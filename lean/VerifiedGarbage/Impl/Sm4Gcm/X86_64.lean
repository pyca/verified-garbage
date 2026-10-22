module
public import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Impl.Sm4.X86_64.Ctr32
public import VerifiedGarbage.Impl.Sm4.X86_64.ExpandKey
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-!
# SM4-GCM: x86-64 implementation

The SM4-GCM functions of `Spec/Sm4/Gcm/Contract.lean`, composed of calls of
the verified `vg_sm4_expand_key`, `vg_sm4_ctr32` and `vg_ghash`, as AES-GCM's
(`Impl/AesGcm/X86_64.lean`), with whose working space, registers and pieces
they share everything that does not encrypt: SM4-GCM's key context has
AES-GCM's layout, the hash subkey at `ctx + 240`, so the pieces that only
hash (`absorb`, `flush`, `lens`, `j0`, …), compare tags (`recv`, `cmp`) or
copy them (`tagOut`) are AES-GCM's, and so are `vg_sm4_gcm_stream_init` and
`vg_sm4_gcm_stream_aad`, which only hash. They take AES-GCM's callees
(`Callees`), of which they call only `vg_ghash` (`gh`).

What differs:

* the cipher is `vg_sm4_ctr32(schedule = rdi, counter = rsi, data = rdx,
  n = rcx)`, whose schedule is the key context's first 128 bytes (at `r13`)
  and whose working space is on its own stack, and the key schedule is
  `vg_sm4_expand_key(key = rdi, schedule = rsi)`'s: so `crypt` and `tag`
  call them with these arguments (`cryptWhole`, `cryptTail`, `tag`), and
  `init` with the key context's address as the schedule's;
* there is no number of rounds, so the functions that encrypt take their
  arguments in different registers (`cryptEntry`, `finEntry`, `oneEntry`);
* `seal` and `open` encrypt or decrypt and absorb the data in two passes, with
  `crypt` and `absorb` (AES-GCM's interleave them in one call of
  `vg_aes_gcm_encrypt_blocks`), and `open` decrypts only once the tag is
  right, so the data stays as it was otherwise without being encrypted
  again; likewise `stream_encrypt` and `stream_decrypt` (`streamText`).

Only the pointers, the lengths, `tag_len` and (for `open`) whether the tag is
right can affect timing, as for AES-GCM.
-/

@[expose] public section

namespace VG.Impl.Sm4Gcm.X86_64

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (Fn Callees at_ imm ptr save restore splitWhole xorLoop minLen cryptHead
  absorb absorbPad lens j0 recv cmp tagOut tagLenOk partWith firstFlush streamLoad oneAad
  stO tO uO alenO tlenO dataO lenO auxO tlO aadO tagPO)

/-- `vg_sm4_ctr32`, as registered (`Artifacts/Sm4Gcm/X86_64.lean`): its
working space in a frame of its own. -/
def ctrFn : Fn :=
  ⟨"vg_sm4_ctr32", Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ctr32⟩

/-- `vg_sm4_expand_key`, as registered (`Artifacts/Sm4/X86_64.lean`). -/
def keyFn : Fn :=
  ⟨"vg_sm4_expand_key", Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rdx 392 Impl.Sm4.X86_64.expandKey⟩

variable (c : Callees)

/-! ## Counter mode -/

/-- Whole blocks at `r12`, by `vg_sm4_ctr32` from the counter block at `r14 + 48`. -/
def cryptWhole : Prog isa :=
  .seq (.block (splitWhole .rdx .rcx ++ ([.alu .test .rcx (.reg .rcx)] : List Instr)))
    (.ite .e (.block [])
      (.seq (.block (([.mov .rdi (.reg .r13)] : List Instr) ++ ptr .rsi .r14 48))
        (.call ctrFn.name ctrFn.code)))

/-- The last `rbp` bytes at `r12`, with a new keystream block. -/
def cryptTail : Prog isa :=
  .seq (.block [.alu .test .rbp (.reg .rbp)])
    (.ite .e (.block [])
      (.seq (.block (([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax,
          .mov .rdi (.reg .r13)] : List Instr) ++ ptr .rsi .r14 48 ++ ptr .rdx .r14 64 ++
          ([.mov32 .rcx (imm 1)] : List Instr)))
      (.seq (.call ctrFn.name ctrFn.code)
        (.seq (.block (([.mov .rdi (.reg .r12)] : List Instr) ++ ptr .rsi .r14 64 ++
          ([.mov .rcx (.reg .rbp)] : List Instr))) xorLoop))))

/-- The `rbp` bytes at `r12` XORed with the keystream, `rbx` bytes into the
current keystream block (AES-GCM's `crypt`). -/
def crypt : Prog isa :=
  .seq (.block [.alu .test .rbp (.reg .rbp)])
    (.ite .e (.block [])
      (.seq (.block [.alu .test .rbx (.reg .rbx)])
      (.seq (.ite .e (.block []) cryptHead)
      (.seq cryptWhole cryptTail))))

/-- `crypt` from the start of a keystream block (`rbx = 0`). -/
def cryptAl : Prog isa := .seq cryptWhole cryptTail

/-! ## The tag -/

/-- The tag into `W + o`: the lengths block absorbed, and `GHASH ⊕ CIPH_K(J₀)`,
with `vg_sm4_ctr32` on it with the counter block `J₀` (at `r14`). -/
def tag (o : Nat) : Prog isa :=
  .seq (lens c 16)
  (.seq (.block (([.mov .rax (.mem (at_ .r14 16)), .store (at_ .r15 o) .rax, .mov .rax (.mem (at_ .r14 24)),
      .store (at_ .r15 (o + 8)) .rax, .mov .rdi (.reg .r13), .mov .rsi (.reg .r14)] : List Instr) ++
      ptr .rdx .r15 o ++ ([.mov32 .rcx (imm 1)] : List Instr)))
    (.call ctrFn.name ctrFn.code))

/-! ## The functions -/

/-- `vg_sm4_gcm_init(key = rdi, ctx = rsi, scratch = rdx)`: the key schedule
into the key context's first 128 bytes, then `H = CIPH_K(0¹²⁸)` into its
last 16, the encryption of a zero block at `ctx + 240` from a zero counter
block at `W + 96`. -/
def init : Prog isa :=
  .seq (.block (save .rdx ++ ([.mov .r15 (.reg .rdx), .mov .r13 (.reg .rsi)] : List Instr)))
  (.seq (.call keyFn.name keyFn.code)
  (.seq (.block (([.mov32 .rax (imm 0), .store (at_ .r13 240) .rax, .store (at_ .r13 248) .rax,
      .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax, .mov .rdi (.reg .r13)] : List Instr) ++
      ptr .rsi .r15 tO ++ ptr .rdx .r13 240 ++ ([.mov32 .rcx (imm 1)] : List Instr)))
  (.seq (.call ctrFn.name ctrFn.code)
    (.block restore))))

/-- The entry of `encrypt` and `decrypt`: `(ctx = rdi, state = rsi,
aad_len = rdx, text_len = rcx, data = r8, len = r9, scratch = [rsp + 8])`. -/
def cryptEntry : List Instr :=
  ([.mov .rax (.mem (at_ .rsp 8))] : List Instr) ++ save .rax ++
    ([.mov .r15 (.reg .rax), .mov .r14 (.reg .rsi), .mov .r13 (.reg .rdi),
      .store (at_ .r15 alenO) .rdx, .store (at_ .r15 tlenO) .rcx, .store (at_ .r15 dataO) .r8,
      .mov .rbp (.reg .r9), .store (at_ .r15 lenO) .rbp, .mov .r12 (.reg .r8), .mov .rbx (.reg .rcx),
      .alu .and .rbx (imm 15)] : List Instr)

/-- The text of `encrypt` (`enc`) or `decrypt`: if there is any, the
additional data padded first if there is no text yet, then `crypt` and
`absorb` over it: encrypting absorbs after `crypt`, decrypting before. -/
def streamText (enc : Bool) : Prog isa :=
  .seq (.block [.alu .test .rbp (.reg .rbp)])
    (.ite .e (.block [])
      (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.seq (.ite .e (firstFlush c) (.block []))
      (.seq (.block streamLoad)
        (partWith enc (crypt) (absorb c 16))))))

/-- `vg_sm4_gcm_stream_encrypt`. -/
def streamEncrypt : Prog isa :=
  .seq (.block cryptEntry) (.seq (streamText c true) (.block restore))

/-- `vg_sm4_gcm_stream_decrypt`. -/
def streamDecrypt : Prog isa :=
  .seq (.block cryptEntry) (.seq (streamText c false) (.block restore))

/-- The buffered bytes padded and absorbed, and the tag into `W + o`
(AES-GCM's `finTag`, with `tag`). -/
def finTag (o : Nat) : Prog isa :=
  .seq (.block [.mov .rbx (.mem (at_ .r15 tlenO)), .mov .rax (.mem (at_ .r15 alenO)),
      .alu .test .rbx (.reg .rbx)])
  (.seq (.ite .e (.block [.mov .rbx (.reg .rax)]) (.block []))
  (.seq (.block [.alu .and .rbx (imm 15)])
  (.seq (Impl.AesGcm.X86_64.flush c 16)
  (.seq (.block [.mov .rbx (.mem (at_ .r15 alenO)), .mov .rbp (.mem (at_ .r15 tlenO))])
    (tag c o)))))

/-- The entry of `finish` and `verify`: `(ctx = rdi, state = rsi, aad_len = rdx,
text_len = rcx)`, with `W` at `w`. -/
def finEntry (w : Reg) : List Instr :=
  save w ++ ([.mov .r15 (.reg w), .mov .r14 (.reg .rsi), .mov .r13 (.reg .rdi),
    .store (at_ .r15 alenO) .rdx, .store (at_ .r15 tlenO) .rcx] : List Instr)

/-- `vg_sm4_gcm_stream_finish(ctx = rdi, state = rsi, aad_len = rdx,
text_len = rcx, tag = r8, work = r9)`: the tag computed at `W` and copied to
`tag`. -/
def streamFinish : Prog isa :=
  .seq (.block (finEntry .r9 ++ ([.store (at_ .r15 tagPO) .r8] : List Instr)))
    (.seq (.seq (finTag c 0) (.block (tagOut (at_ .r15 tagPO)))) (.block restore))

/-- `vg_sm4_gcm_stream_verify(ctx = rdi, state = rsi, aad_len = rdx,
text_len = rcx, tag = r8, tag_len = r9, work = [rsp + 8])`. -/
def streamVerify : Prog isa :=
  .seq (.block (([.mov .rax (.mem (at_ .rsp 8))] : List Instr) ++ finEntry .rax ++
      ([.mov .rbx (.reg .r9), .store (at_ .r15 tlO) .rbx, .mov .rsi (.reg .r8)] : List Instr)))
  (.seq tagLenOk
  (.seq (.ite .e (.block [.mov32 .rax (imm 0)])
      (.seq recv
      (.seq (finTag c 0)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))])
        (cmp 0)))))
    (.block restore)))

/-- The entry of `seal` and `open`: `(ctx = rdi, nonce = rsi, nonce_len = rdx,
aad = rcx, aad_len = r8, data = r9, len = [rsp + 8], tag = [rsp + 16])`, and
`work` at `[rsp + wo]`. The state is at `W + 16`; the length is kept at
`lenO` and at `tlenO`, as the text's. -/
def oneEntry (wo : Nat) : List Instr :=
  ([.mov .rax (.mem (at_ .rsp wo))] : List Instr) ++ save .rax ++
    ([.mov .r15 (.reg .rax)] : List Instr) ++ ptr .r14 .r15 stO ++
    ([.mov .r13 (.reg .rdi), .store (at_ .r15 aadO) .rcx, .store (at_ .r15 alenO) .r8,
      .store (at_ .r15 dataO) .r9, .mov .rax (.mem (at_ .rsp 8)), .store (at_ .r15 lenO) .rax,
      .store (at_ .r15 tlenO) .rax, .mov .r12 (.reg .rsi), .mov .rbp (.reg .rdx)] : List Instr)

/-- The data encrypted or decrypted, from the first counter block. -/
def oneCrypt : Prog isa :=
  .seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)])
    cryptAl

/-- The data (as ciphertext) absorbed and padded, and the tag into `W + o`. -/
def oneTag (o : Nat) : Prog isa :=
  .seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)])
  (.seq (absorbPad c 16)
  (.seq (.block [.mov .rbx (.mem (at_ .r15 alenO)), .mov .rbp (.mem (at_ .r15 tlenO))])
    (tag c o)))

/-- `vg_sm4_gcm_seal`, with `work = [rsp + 24]`: `J₀` and the additional
data, the data encrypted, then absorbed, and the tag computed at `W` and
copied to `tag`. -/
def «seal» : Prog isa :=
  .seq (.block (oneEntry 24)) (.seq (oneAad c) (.seq oneCrypt
    (.seq (.seq (oneTag c 0) (.block (tagOut (at_ .rsp 16)))) (.block restore))))

/-- `vg_sm4_gcm_open`, with `tag_len = [rsp + 24]` and `work = [rsp + 32]`:
`J₀` and the additional data, the data absorbed and the tag computed at
`W + 112`, compared with the received one, and the data decrypted if they
are equal. -/
def «open» : Prog isa :=
  .seq (.block (oneEntry 32 ++ ([.mov .rbx (.mem (at_ .rsp 24)), .store (at_ .r15 tlO) .rbx] : List Instr)))
  (.seq tagLenOk
  (.seq (.ite .e (.block [.mov32 .rax (imm 0)])
      (.seq (oneAad c)
      (.seq (oneTag c uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 16))])
      (.seq recv
      (.seq (cmp uO)
      (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
      (.seq (.ite .e (.block []) oneCrypt)
        (.block [.mov .rax (.mem (at_ .r15 auxO))])))))))))
    (.block restore)))

end VG.Impl.Sm4Gcm.X86_64
