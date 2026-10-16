module

public import VerifiedGarbage.Impl.AesGcm.AArch64
public import VerifiedGarbage.Impl.Gcm.AArch64.Pmull

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
bytes of additional data (at `W + 224`, in `x11`). -/
def cond : Prog isa :=
  .seq (.block [imm .x10 0, .ldr .x .x11 .x19 alenO, .lsr .x .x9 .x11 4])
  (.seq (.ite (.zero .x .x9) (.block [])
      (.seq (.block [.subImm .x .x9 .x11 16]) (.ite (.zero .x .x9) (.block []) (.block [imm .x10 1]))))
  (.seq (.block [.subImm .x .x9 .x24 12]) (.ite (.zero .x .x9) (.block []) (.block [imm .x10 1]))))

/-- `H'` (`v16`) and its halves swapped (`v24`) from `H` at `ctx + 240`, the
reduction constant (`v1`), both kept at `W + hO`, and `Y = 0`. -/
def hPrime : List Instr :=
  ([ptr .x0 .x21 240] : List Instr) ++ loadRev A .x0 0 ++ consts ++ mul (sReg 1) A (sReg 2) (tReg 2) ++
    ([.vop (.ext (tReg 1) (sReg 1) (sReg 1) 8), .strq (tReg 1) .x19 hO, .strq (sReg 1) .x19 (hO + 16),
      .vop (.movi0 Y)] : List Instr)

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

/-- The accumulator stored at `x20 + 16`, as `vg_ghash` keeps it. -/
def storeY : List Instr := [.vop (.rev .rev64b Y Y), .strq Y .x20 16]

/-- `J₀` of the 12-byte nonce, the first counter block, `H'`, and the
additional data absorbed. -/
def front : Prog isa :=
  .seq (.block (j012 ++ initState ++ hPrime ++ [.ldr .x .x13 .x19 alenO, .ldr .x .x12 .x19 aadO]))
    (.seq padMul (.block storeY))

/-- The lengths block `[8 alen]₆₄ ‖ [8 len]₆₄` in `T`, absorbed, the
accumulator stored, and the arguments for the tag at `W`. -/
def lensTag : List Instr :=
  ([.ldr .x .x26 .x19 alenO, .ldr .x .x27 .x19 lenO, .lsl .x .x9 .x26 3, .rev .x9 .x9,
    .str .x .x9 .x19 tO, .lsl .x .x9 .x27 3, .rev .x9 .x9, .str .x .x9 .x19 (tO + 8)] : List Instr) ++
  mulT ++ storeY ++ ([.ldr .x .x28 .x19 tlO] : List Instr) ++ tagSeg 0

variable (c : Callees)

/-- After the entry: `front`, the text encrypted, its whole blocks hashed by
`vg_ghash`, its last bytes and the lengths absorbed, and the tag. -/
def run : Prog isa :=
  .seq (front)
  (.seq (.block [.ldr .x .x23 .x19 dataO, .ldr .x .x24 .x19 lenO, imm .x25 0])
  (.seq (cryptAl c)
  (.seq (.block ([.ldr .x .x23 .x19 dataO, .ldr .x .x24 .x19 lenO] ++ absSeg2 16))
  (.seq (ghCall c)
  (.seq (.block (hReload ++ loadRev Y .x20 16 ++ [mov .x13 .x24, mov .x12 .x23]))
  (.seq padMul
  (.seq (.block lensTag)
  (.seq (ctrCall c)
    (.block (tagOut ++ restore))))))))))

/-- `vg_aes_gcm_seal` with this path: the entry, `cond`, then `run` or `sealRest`. -/
def «seal» : Prog isa :=
  .seq (.block (oneEntry 8 ++ stashArg 0))
    (.seq cond (.ite (.zero .x .x10) (run c) (sealRest c)))

end VG.Impl.AesGcm.AArch64.Fast
