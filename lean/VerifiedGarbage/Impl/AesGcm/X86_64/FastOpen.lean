module

public import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
public import VerifiedGarbage.Impl.AesGcm.X86_64.OpenSplit

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
open VG.Impl.AesGcm.X86_64 (at_ imm ptr Callees Fn copyLoop xorLoopG recv cmp oneBlocks oneUndo lenO dataO tlO auxO uO
  tlenO oneEntry tagLenOk restore openRun oneAad oneTag oneCryptG)

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

/-- Where `tailKG` reads and writes the `rcx` bytes left: in place, at the
data kept (`rdi`); out of place (`to`), from the data kept (`rbx`, at `src`)
to the end of `dst` (`rdi = dst + (len - rcx)`, `dst` at `[rsp + 8]` and
`len` at `tlenO`), as `oneCryptBlk` puts them. -/
def tailArgs (to : Bool) : List Instr :=
  if to then [.mov .rdi (.mem (at_ .rsp 8)), .mov .rax (.mem (at_ .r15 tlenO)), .alu .sub .rax (.reg .rcx),
    .alu .add .rdi (.reg .rax), .mov .rbx (.mem (at_ .r15 dataO))]
  else [.mov .rdi (.mem (at_ .r15 dataO))]

/-- The bytes left (`rcx`, fewer than 16, at the data kept) decrypted with
`K[1]`, the keystream of the counter block, which `tagP` computed: where
`oneCrypt` encrypts the counter block again with a call of `vg_aes_ctr32`.
In place, or out of place (`to`) to the end of `dst` (`tailArgs`). -/
def tailKG (to : Bool) : Prog isa :=
  .seq (.block [.mov .rcx (.mem (at_ .r15 lenO)), .alu .test .rcx (.reg .rcx)])
    (.ite .e (.block [])
      (.seq (.block (tailArgs to ++ ptr .rsi .r15 (Short.kO + 16))) (xorLoopG to)))

/-- `tailKG` in place. -/
abbrev tailK : Prog isa := tailKG false

variable (c : Callees)

/-- After the entry and `tagLenOk`: `Short.openLong` with `Fast.aad`,
`tagP ks` and `tailK`. -/
def run (ks : Prog isa := Short.finKs) : Prog isa :=
  openRun Fast.aad (oneBlocks c.dec) (tagP ks) (oneUndo c) tailK

/-- `run` out of place, as `OpenSplit.openSplit` is `open`'s body out of
place: the whole blocks decrypted from `src` to `dst` by `fToDec`
(`OpenSplit.mid`), nothing done if the tags differ (the caller zeroes `dst`),
and the bytes left decrypted to the end of `dst` if they match
(`tailKG true`). -/
def runTo (fToDec : Fn) (ks : Prog isa := Short.finKs) : Prog isa :=
  openRun Fast.aad (OpenSplit.mid fToDec) (tagP ks) (.block []) (tailKG true)

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

/-- `vg_aes_gcm_open_split_prepared`: `OpenSplit.openSplit`'s entry and end
around `selTo`, which takes `runTo` for the inputs `Fast.cond any` takes and
`OpenSplit.openSplit`'s body for the others. -/
def openSplit (fToDec : Fn) (ks : Prog isa := Short.finKs) (any : Bool := false) : Prog isa :=
  .seq (.block OpenSplit.entry)
  (.seq tagLenOk
  (.seq (.ite .e (.block [.mov32 .rax (imm 0)])
      (.seq (Fast.cond any)
        (.ite .e (openRun (oneAad c) (OpenSplit.mid fToDec) (oneTag c uO) (.block []) (oneCryptG c true))
          (runTo fToDec ks))))
    (.block restore)))

end VG.Impl.AesGcm.X86_64.FastOpen
