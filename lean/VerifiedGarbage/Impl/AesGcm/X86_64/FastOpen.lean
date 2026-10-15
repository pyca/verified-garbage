module

public import VerifiedGarbage.Impl.AesGcm.X86_64.Fast

/-!
# AES-GCM on x86-64: `open`'s path for TLS records

`vg_aes_gcm_open_prepared` with a prepared key context
(`VG.Spec.Gcm.PreparedPowersRepr`) takes a path of its own for the records of
TLS too long for the short path: a 12-byte nonce and at most 16 bytes of
additional data (`Fast.cond`). It is the other instances' body
(`Short.openLong`) with no call but `oneBlocks`' and, when the tags differ,
`oneUndo`'s: the additional data absorbed with the prepared `H'` (`Fast.aad`),
and the tag (`tagP`) as `Short.finishP` computes `seal`'s, of the
ciphertext: `H'` and `H'²` loaded from the context, the keystream of `J₀`
and of the counter block in two lanes of `zmm5`, `J₀` incremented (where
`oneUndo` takes the first counter block, as `oneTag`'s call of
`vg_aes_ctr32` leaves it), the bytes left copied (not encrypted) to `G[0]`,
and the tag at `W + uO`.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.FastOpen

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm Callees copyLoop recv cmp oneBlocks oneUndo oneCrypt lenO tlO auxO uO)

/-- `J₀`, at the state's start, incremented: its last word, big-endian. -/
def incJ : List Instr :=
  [.mov32 .rsi (.mem (at_ .r14 12)), .bswap32 .rsi, .alu32 .add .rsi (imm 1), .bswap32 .rsi,
    .store32 (at_ .r14 12) .rsi]

/-- The tag of the ciphertext at `W + uO`, without calls, with `J₀`
incremented once its keystream is computed. -/
def tagP : Prog isa :=
  .seq (.block Short.finPowP)
  (.seq Short.finKs
  (.seq (.block incJ)
  (.seq (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .test .rax (.reg .rax)])
  (.ite .e (.block (Short.finLens ++ Short.finGh1 ++ Short.tagK uO))
      (.seq (.block Short.finTextArgs) (.seq copyLoop (.block (Short.finLens ++ Short.finGh2 ++ Short.tagK uO))))))))

variable (c : Callees)

/-- After the entry and `tagLenOk`: `Short.openLong` with `Fast.aad` and
`tagP`. -/
def run : Prog isa :=
  .seq Fast.aad
  (.seq (oneBlocks c.dec)
  (.seq tagP
  (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))])
  (.seq recv
  (.seq (cmp uO)
  (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
  (.seq (.ite .e (oneUndo c) (oneCrypt c))
    (.block [.mov .rax (.mem (at_ .r15 auxO))]))))))))

/-- `run`'s part after the additional data, a word lower, calling `f`, the
decryption function given the block index (`vg_aes_gcm_decrypt_blocks_prepared_iv96`),
for which the word above `scratch` holds the index: the received tag's
address is then 8 bytes further from `rsp`. -/
def bodyI (f : Fn) : Prog isa :=
  .seq (oneBlocks f)
  (.seq tagP
  (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 32))])
  (.seq recv
  (.seq (cmp uO)
  (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
  (.seq (.ite .e (oneUndo c) (oneCrypt c))
    (.block [.mov .rax (.mem (at_ .r15 auxO))])))))))

/-- `run` calling `f`, given the block index: the index of the first counter
block, 2 for a 12-byte nonce, pushed in a frame of one word around the rest
(`bodyI`), whose call passes it above `scratch`. -/
def runI (f : Fn) : Prog isa :=
  .seq Fast.aad
  (.seq (.block [.mov32 .rax (imm 2)])
    (.frame (.push [.rax]) (bodyI c f) (.pop .r10 1)))

/-- `Fast.cond`, then this path, or `other`: `runI` if the decryption function
given the block index `fi` is there, `run` otherwise. -/
def sel (fi : Option Fn) (other : Prog isa) : Prog isa :=
  .seq Fast.cond (.ite .e other (match fi with | some f => runI c f | none => run c))

end VG.Impl.AesGcm.X86_64.FastOpen
