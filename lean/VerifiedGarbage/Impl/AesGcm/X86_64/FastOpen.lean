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
and the tag at `W + uO`. If the tags match, the bytes left are decrypted with
the keystream of the counter block computed with `J₀`'s (`tailK`), without
`oneCrypt`'s call.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.FastOpen

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr Callees copyLoop xorLoop recv cmp oneBlocks oneUndo lenO dataO tlO auxO uO
  oneEntry tagLenOk restore)

/-- `J₀`, at the state's start, incremented: its last word, big-endian. -/
def incJ : List Instr :=
  [.mov32 .rsi (.mem (at_ .r14 12)), .bswap32 .rsi, .alu32 .add .rsi (imm 1), .bswap32 .rsi,
    .store32 (at_ .r14 12) .rsi]

/-- `rax` the number of bytes left, and `test rax, rax`. -/
def lenTest : List Instr :=
  [.mov .rax (.mem (at_ .r15 lenO)), .alu .test .rax (.reg .rax)]

/-- The tag of the ciphertext at `W + uO`, without calls, with `J₀`
incremented once its keystream is computed, by `ks` (`Short.finKs` on
512-bit registers, `Short.finKsA` on 128-bit ones). The blocks `GHASH` reads
from memory, the bytes left copied to `G[0]` and the lengths block, are
stored before the keystream, so that they have reached the cache when they
are loaded back: a load of a block written in smaller stores waits for them. -/
def tagP (ks : Prog isa := Short.finKs) : Prog isa :=
  .seq (.block Short.finPowP)
  (.seq (.block lenTest)
  (.seq (.ite .e (.block Short.finLens)
      (.seq (.block Short.finTextArgs) (.seq copyLoop (.block Short.finLens))))
  (.seq ks
  (.seq (.block incJ)
  (.seq (.block lenTest)
  (.ite .e (.block (Short.finGh1 ++ Short.tagK uO)) (.block (Short.finGh2 ++ Short.tagK uO))))))))

/-- The bytes left (`rcx`, fewer than 16, at the data kept) decrypted with
`K[1]`, the keystream of the counter block, which `tagP` computed: where
`oneCrypt` encrypts the counter block again with a call of `vg_aes_ctr32`. -/
def tailK : Prog isa :=
  .seq (.block [.mov .rcx (.mem (at_ .r15 lenO)), .alu .test .rcx (.reg .rcx)])
    (.ite .e (.block [])
      (.seq (.block (([.mov .rdi (.mem (at_ .r15 dataO))] : List Instr) ++ ptr .rsi .r15 (Short.kO + 16)))
        xorLoop))

variable (c : Callees)

/-- After the entry and `tagLenOk`: `Short.openLong` with `Fast.aad`,
`tagP ks` and `tailK`. -/
def run (ks : Prog isa := Short.finKs) : Prog isa :=
  .seq Fast.aad
  (.seq (oneBlocks c.dec)
  (.seq (tagP ks)
  (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))])
  (.seq recv
  (.seq (cmp uO)
  (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
  (.seq (.ite .e (oneUndo c) tailK)
    (.block [.mov .rax (.mem (at_ .r15 auxO))]))))))))

/-- `Fast.cond any`, then this path, or `other`. -/
def sel (other : Prog isa) (ks : Prog isa := Short.finKs) (any : Bool := false) : Prog isa :=
  .seq (Fast.cond any) (.ite .e other (run c ks))

/-- `vg_aes_gcm_open`'s frame, as `Impl.AesGcm.X86_64.open` and
`Short.open` have it, around `lng` for an allowed tag length: for the
256-bit VAES instances, which have no short path, `sel` with the 128-bit
keystream `Short.finKsA`. -/
def openFin (lng : Prog isa) : Prog isa :=
  .seq (.block (oneEntry 40 ++ ([.mov .rbx (.mem (at_ .rsp 32)), .store (at_ .r15 tlO) .rbx] : List Instr)))
  (.seq tagLenOk
  (.seq (.ite .e (.block [.mov32 .rax (imm 0)]) lng)
    (.block restore)))

end VG.Impl.AesGcm.X86_64.FastOpen
