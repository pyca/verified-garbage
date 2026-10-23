module

public import VerifiedGarbage.Impl.AesGcm.AArch64
public import VerifiedGarbage.Impl.Gcm.AArch64.Pmull
public import VerifiedGarbage.Impl.AesGcm.AArch64.Tail

/-!
# AES-GCM on AArch64: `seal`'s path for TLS records

`vg_aes_gcm_seal` takes a path of its own for the records of TLS: a 12-byte
nonce and at most 16 bytes of additional data (`cond`, which depends only on
the lengths). Where `sealRest` calls `vg_ghash` six times, each call
computing `H' = H · x⁻¹` from `H` again, this path computes `H'` once
(`hPrime`, with `vg_ghash_aes`'s instructions: `Impl.Gcm.AArch64.Pmull`) and
multiplies the blocks of the additional data, of the last bytes of the
ciphertext and of the lengths by it in registers (`mulT`), each padded with
zeros in `T`; only the whole blocks of the ciphertext are hashed by a call.
It needs PMULL (Rust's `aes` feature), so only the variants with it take it.
-/

@[expose] public section

namespace VG.Impl.AesGcm.AArch64.Fast

open VG.AArch64
open VG.Impl.Gcm.AArch64.Pmull (A Y C tReg sReg consts mul loadRev)

/-- Where `H'` is kept across the call of `vg_ghash`, and its halves swapped
after it, in the working space. -/
def hO : Nat := 288

/-- `x10 = 0` if the path applies: a 12-byte nonce (`x24`) and at most 16
bytes of additional data (`x5`). -/
def cond : Prog isa :=
  .seq (.block [imm .x10 0, .lsr .x .x9 .x5 4])
  (.seq (.ite (.zero .x .x9) (.block [])
      (.seq (.block [.subImm .x .x9 .x5 16]) (.ite (.zero .x .x9) (.block []) (.block [imm .x10 1]))))
  (.seq (.block [.subImm .x .x9 .x24 12]) (.ite (.zero .x .x9) (.block []) (.block [imm .x10 1]))))

/-- `H'` (`v16`) and its halves swapped (`v24`) from `H` at `x0`, and the
reduction constant (`v1`), as `vg_ghash_aes`'s prologue computes them. -/
def key : List Instr :=
  loadRev A .x0 0 ++ consts ++ mul (sReg 1) A (sReg 2) (tReg 2) ++
    ([.vop (.ext (tReg 1) (sReg 1) (sReg 1) 8)] : List Instr)

/-- `H'` and its halves swapped kept at `W + hO`, and `Y = 0`. -/
def keep : List Instr := [.strq (tReg 1) .x19 hO, .strq (sReg 1) .x19 (hO + 16), .vop (.movi0 Y)]

/-- `key` from `H` at `ctx + 240`, then `keep`. -/
def hPrime : List Instr := ([ptr .x0 .x21 240] : List Instr) ++ key ++ keep

/-- `H'`, its halves swapped and the reduction constant again, after the call. -/
def hReload : List Instr :=
  [.ldrq (tReg 1) .x19 hO, .ldrq (sReg 1) .x19 (hO + 16), .movz .x .x5 0xc200 3, .vop (.dup .d2 C .x5)]

/-- `T` zeroed. -/
def zeroT : List Instr := [imm .x9 0, .str .x .x9 .x19 tO, .str .x .x9 .x19 (tO + 8)]

/-- `Y ← mul(Y ⊕ T, H')`. -/
def mulT : List Instr :=
  loadRev A .x19 tO ++ ([.vop (.logic .eor A A Y)] : List Instr) ++ mul Y A (sReg 1) (tReg 1)

/-- The `x13` bytes at `x12` (if any) padded with zeros in `T`, and absorbed. -/
def padMul : Prog isa :=
  .ite (.zero .x .x13) (.block [])
    (.seq (.block (zeroT ++ [ptr .x11 .x19 tO])) (.seq copy (.block mulT)))

/-- `padMul` for the last bytes of the text (`x26` bytes), if there are any:
from the 16 bytes that end it (`Tail.padVec`) if it is at least a block long. -/
def padMulT : Prog isa :=
  .ite (.zero .x .x13) (.block [])
    (.seq (.block [.lsr .x .x9 .x26 4]) (.ite (.zero .x .x9) padMul (.block Tail.padVec)))

/-- The accumulator stored at `x20 + 16`, as `vg_ghash` keeps it. -/
def storeY : List Instr := [.vop (.rev .rev64b Y Y), .strq Y .x20 16]

/-- `J₀` of the 12-byte nonce, the first counter block, `H'`, and the
additional data (`x4`, `x5`) absorbed; the data and its length (`x6`, `x7`)
kept in `x23` and `x26`. -/
def front : Prog isa :=
  .seq (.block (j012 ++ ([mov .x25 .x5, mov .x27 .x4, mov .x23 .x6, mov .x26 .x7] : List Instr) ++
      initState ++ hPrime ++ ([mov .x13 .x25, mov .x12 .x27] : List Instr)))
    (.seq padMul (.block storeY))

/-- The lengths block `[8 alen]₆₄ ‖ [8 len]₆₄` in `T` (the length of the text
in `x26`), absorbed, the accumulator stored, and the arguments for the tag at
`W + o`. -/
def lensTagAt (o : Nat) : List Instr :=
  ([.ldr .x .x10 .x19 alenO, .lsl .x .x9 .x10 3, .rev .x9 .x9, .str .x .x9 .x19 tO, .lsl .x .x9 .x26 3,
    .rev .x9 .x9, .str .x .x9 .x19 (tO + 8)] : List Instr) ++ mulT ++ storeY ++ tagSeg o

/-- `lensTagAt`, with the tag at `W`. -/
def lensTag : List Instr := lensTagAt 0

variable (c : Callees)

/-- After the entry: `front`, the text (at `x27`, of `x26` bytes) encrypted,
its whole blocks hashed by `cl` (a call of `vg_ghash`, with its arguments
set), its last bytes and the lengths absorbed, and the tag, to `x28`. -/
def runWithP (cl : Prog isa) : Prog isa :=
  .seq (front)
  (.seq (.block [mov .x27 .x23, mov .x24 .x26, imm .x25 0])
  (.seq (Tail.cryptAlT c)
  (.seq (.block ([mov .x23 .x27, mov .x24 .x26] ++ absSeg2 16))
  (.seq cl
  (.seq (.block (hReload ++ loadRev Y .x20 16 ++ [mov .x13 .x24, mov .x12 .x23]))
  (.seq padMulT
  (.seq (.block lensTag)
  (.seq (ctrCall c)
  (.seq (.block tagOut)
    (.block restore))))))))))

/-- `runWithP`, hashing the whole blocks by a call of `gh`. -/
def runWith (gh : Fn) : Prog isa := runWithP c (.call gh.name gh.code)

/-- `runWith`, hashing the whole blocks with `vg_ghash`. -/
def run : Prog isa := runWith c c.gh

/-- `vg_aes_gcm_seal` with this path: the entry, `cond`, then `run` or `sealRest`. -/
def «seal» : Prog isa :=
  .seq (.block (oneEntry 8 ++ stashArg 0))
    (.seq cond (.ite (.zero .x .x10) (run c) (sealRest c)))

/-- `seal`, with `work` at `sp + k` and the whole blocks of this path hashed
by `cl`. -/
def sealWithE (k : Nat) (cl : Prog isa) : Prog isa :=
  .seq (.block (oneEntry k ++ stashArg 0))
    (.seq cond (.ite (.zero .x .x10) (runWithP c cl) (sealRest c)))

/-- `seal`, with the whole blocks of this path hashed by `gh`: for
`vg_aes_gcm_seal_prepared`, `vg_ghash_prepared`, which reads the powers of
`H` from the prepared context instead of computing them (`sealRest` reads
only the first 256 bytes of the context, as in `seal`). -/
def sealWith (gh : Fn) : Prog isa := sealWithE c 8 (.call gh.name gh.code)

/-! ## `open` -/

/-- `oneCrypt` with `Tail.cryptAlT`. -/
def oneCryptT : Prog isa :=
  .seq (.block [.ldr .x .x23 .x19 dataO, .ldr .x .x24 .x19 lenO, imm .x25 0]) (Tail.cryptAlT c)

/-- `open`'s path for TLS records, once the tag length is allowed and the
received tag is at `W`: `front`; the whole blocks of the ciphertext (`x26`
bytes at `x23`) hashed by `gh`; its last bytes and the lengths absorbed; the
tag to `W + uO` (`uO`, as `openMain`), compared with the received one (the
tag length still in `x28`, which nothing here writes); and the text
decrypted only if they are equal, `x0` then 1 and else 0. -/
def openRunWithP (cl : Prog isa) : Prog isa :=
  .seq front
  (.seq (.block ([mov .x24 .x26, imm .x25 0] ++ absSeg2 16))
  (.seq cl
  (.seq (.block (hReload ++ loadRev Y .x20 16 ++ [mov .x13 .x24, mov .x12 .x23]))
  (.seq padMulT
  (.seq (.block (lensTagAt uO))
  (.seq (ctrCall c)
  (.seq cmp
  (.seq (.block [imm .x27 1, .sub .x .x27 .x27 .x10])
  (.seq (.ite (.zero .x .x27) (.block []) (oneCryptT c))
    (.block [mov .x0 .x27]))))))))))

/-- `openRunWithP`, hashing the whole blocks by a call of `gh`. -/
def openRunWith (gh : Fn) : Prog isa := openRunWithP c (.call gh.name gh.code)

/-- `openRest`, with `openRunWithP` for `openMain`. -/
def openFastP (cl : Prog isa) : Prog isa :=
  .seq tagLenOk
  (.seq (.ite (.zero .x .x9) (.block [imm .x0 0]) (.seq tagIn (openRunWithP c cl)))
    (.block restore))

/-- `openFastP`, hashing by a call of `gh`. -/
def openFast (gh : Fn) : Prog isa := openFastP c (.call gh.name gh.code)

/-- `vg_aes_gcm_open` with this path, with `work` at `sp + k`: the entry,
`cond`, then `openFastP` or `openRest`; the ciphertext's whole blocks hashed
by `cl`. -/
def openWithE (k : Nat) (cl : Prog isa) : Prog isa :=
  .seq (.block (oneEntry k ++ stashArg 8 ++ ([.ldrSp .x12 0] : List Instr)))
    (.seq cond (.ite (.zero .x .x10) (openFastP c cl) (openRest c)))

/-- `vg_aes_gcm_open` with this path: the entry, `cond`, then `openFast` or
`openRest`; the ciphertext's whole blocks hashed by `gh`. -/
def openWith (gh : Fn) : Prog isa := openWithE c 16 (.call gh.name gh.code)

/-- `vg_aes_gcm_open` with this path, hashing with `vg_ghash`. -/
def «open» : Prog isa := openWith c c.gh

/-! ## With the powers in their own buffer

`vg_aes_gcm_seal_with_powers` and `vg_aes_gcm_open_with_powers` take one more
stack argument, `pw`, after the others, so `work` is one slot further. On the
path for TLS records, `gh` (`vg_ghash_with_powers`) takes `pw` in `x5`, read
from its stack slot just before the call, unless one block or none is left
to hash, which `vg_ghash` does faster; the other paths never read it. -/

/-- The call of `gh` with `pw`, the stack argument at `sp + k`, in `x5`. -/
def pwCall (k : Nat) (gh : Fn) : Prog isa := .seq (.block [.ldrSp .x5 k]) (.call gh.name gh.code)

/-- The call of `vg_ghash` (`c.gh`) for at most one block (`x3`), which
needs no powers, else `pwCall k gh`. -/
def pwSel (k : Nat) (gh : Fn) : Prog isa :=
  .seq (.block [.lsr .x .x9 .x3 1]) (.ite (.zero .x .x9) (.call c.gh.name c.gh.code) (pwCall k gh))

/-- `vg_aes_gcm_seal_with_powers`: `tag`, `pw`, then `work` on the stack. -/
def sealWithPw (gh : Fn) : Prog isa := sealWithE c 16 (pwSel c 8 gh)

/-- `vg_aes_gcm_open_with_powers`: `tag`, `tag_len`, `pw`, then `work` on the stack. -/
def openWithPw (gh : Fn) : Prog isa := openWithE c 24 (pwSel c 16 gh)

end VG.Impl.AesGcm.AArch64.Fast
