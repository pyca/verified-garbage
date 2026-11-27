module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Loops
public import VerifiedGarbage.Impl.Words.RISCV64.CopyFast

/-!
# HKDF (RFC 5869) on RISC-V, with HMAC through a table

Three functions, each with HMAC over the hash function of the table `hmac`
of the interface `Hmac` (`Spec/HmacTable.lean`), whose functions they call
indirectly (`tcall`, with the table in `s6`: its word `j` into `t1`, then
`jalr ra, 0(t1)`): HMAC's `init` (word 0), the streaming `update` (word 1)
and HMAC's `finalize` (word 2). The digest length `D` and HMAC's block size
`B` are the table's words of data 4 and 5, which the code loads into `s7`
and `s8` where it needs them, and the code computes the lengths and counts
it passes from them (all public): nothing in the code depends on the hash
function but those two words and the table's functions.

* `vg_hkdf_extract(salt = a0, salt_len = a1, ikm = a2, ikm_len = a3,
  prk = a4, prk_len = a5, hmac = a6)` (`extract`): `init` with the salt as
  the key, into the inner and outer states in its frame; `update` with the
  input keying material; `finalize`, which writes the MAC, `PRK`, to `prk`.
* `vg_hkdf_key(prk = a0, prk_len = a1, key = a2, hmac = a3)` (`key`):
  `init` with `PRK` as the key, into the states at `key` and `key + 192`.
* `vg_hkdf_expand(key = a0, info = a1, info_len = a2, out = a3,
  out_len = a4, hmac = a5)` (`expand`): unless `out_len` is 0, for each
  block `T(i)` (`block`): the inner state at `key` made the working state in
  its frame, by copying its first 64 bytes (`copyAny`: a doubleword at a
  time if `key` is aligned, else a byte at a time): the inner state holds a
  whole block of key, so its hash value, at most 64 bytes, is all of it that
  matters;
  `update` with `T(i - 1)` (the `s9` bytes at `T` in the frame: none for
  the first block, `D` after), then with `info`, then with the counter `i`
  (a byte, kept in `s0`); `finalize` with the outer state at `key + 192`,
  which writes `T(i)` to the frame; and its first `min(D, rem)` bytes,
  `rem` the bytes of `out` still to write, copied to `out` (`copyLoop`).
  `key` is only read.

Each runs in a frame (`alloc`) holding our caller's registers it uses
(`ra`, then `s0`–`s10` for `expand`'s and `extract`'s, `s6` for `key`'s);
our variables live in callee-saved registers, which the functions we call
save and restore. The functions we call use the stack below the frame.
Every address depends only on the pointers and `D`.
-/

@[expose] public section

namespace VG.Impl.Hkdf.RISCV64

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (mov)
open VG.Impl.Ecdsa.Rfc6979.RISCV64 (Fns tcall)

/-- Our caller's registers `extract` and `expand` save, and where, at the
start of the frame. -/
def saved : List (Reg × Nat) :=
  [(.ra, 0), (.s0, 8), (.s1, 16), (.s2, 24), (.s3, 32), (.s4, 40), (.s5, 48), (.s6, 56), (.s7, 64),
    (.s8, 72), (.s9, 80), (.s10, 88)]

/-- Where we restore them from, in order (`s1`, the base, last). -/
def restList : List (Reg × Nat) :=
  [(.ra, 0), (.s0, 8), (.s2, 24), (.s3, 32), (.s4, 40), (.s5, 48), (.s6, 56), (.s7, 64), (.s8, 72),
    (.s9, 80), (.s10, 88), (.s1, 16)]

/-- Our caller's registers into the frame, which `s1` then holds. -/
def save : List Instr := .addSp .t0 0 :: (saved.map fun (r, d) => .store .d r .t0 d) ++ [mov .s1 .t0]

/-- Restore our caller's registers. -/
def restore : List Instr := restList.map fun (r, d) => .load .d r .s1 d

/-- `D` and `B`, the table's words of data 4 and 5, into `s7` and `s8` (the
table in `s6`). -/
def loadDB : List Instr := [.load .d .s7 .s6 32, .load .d .s8 .s6 40]

/-! ## HKDF-Extract -/

/-! Where things are in `extract`'s frame: the save area, then HMAC's inner
and outer states (192 bytes each). -/
def xIn : Nat := 96
def xOut : Nat := 288
/-- `extract`'s frame's size. -/
def xFr : Nat := 480

/-- `extract`'s prologue: our caller's registers saved; `ikm` and its length
in `s3` and `s4`, `prk` in `s2`, the table in `s6`, `D` and `B` in `s7` and
`s8`; then `init`'s arguments: the states, and the salt as the key. -/
def extractPro : List Instr :=
  save ++ [mov .s3 .a2, mov .s4 .a3, mov .s2 .a4, mov .s6 .a6] ++ loadDB ++
    [mov .a2 .a0, mov .a3 .a1, .addi .a0 .s1 xIn, .addi .a1 .s1 xOut]

/-- `update`'s arguments: the inner state, which holds `B` bytes, and the
input keying material. -/
def extractUpd : List Instr := [.addi .a0 .s1 xIn, mov .a1 .s8, mov .a2 .s3, mov .a3 .s4]

/-- `finalize`'s arguments: the states, the `B + ikm_len` bytes the inner one
holds, and `prk`. -/
def extractFin : List Instr := [.addi .a0 .s1 xIn, .addi .a1 .s1 xOut, .add .a2 .s8 .s4, mov .a3 .s2]

/-- The frame's body of `vg_hkdf_extract`, whose table's functions may be
`f`'s. -/
def extractMain (f : Fns) : Prog isa :=
  .seq (.block extractPro)
  (.seq (tcall 0 f.init)
  (.seq (.block extractUpd)
  (.seq (tcall 1 f.upd)
  (.seq (.block extractFin)
  (.seq (tcall 2 f.fin)
    (.block restore))))))

/-- `vg_hkdf_extract`. -/
def extract (f : Fns) : Prog isa := .frame (.alloc xFr) (extractMain f) (.free xFr)

/-! ## Keying HMAC -/

/-- `key`'s frame's size: `ra` and `s6`. -/
def kFr : Nat := 16

/-- `key`'s prologue: `ra` and `s6` saved, the table in `s6`; then `init`'s
arguments: the states at `key` and `key + 192`, and `PRK` as the key. -/
def keyPro : List Instr :=
  [.addSp .t0 0, .store .d .ra .t0 0, .store .d .s6 .t0 8, mov .s6 .a3, mov .t2 .a0, mov .t3 .a1,
    mov .a0 .a2, .addi .a1 .a2 192, mov .a2 .t2, mov .a3 .t3]

/-- `ra` and `s6` restored. -/
def keyEpi : List Instr := [.addSp .t0 0, .load .d .ra .t0 0, .load .d .s6 .t0 8]

/-- The frame's body of `vg_hkdf_key`, whose table's `init` may be `f`'s. -/
def keyMain (f : Fns) : Prog isa :=
  .seq (.block keyPro) (.seq (tcall 0 f.init) (.block keyEpi))

/-- `vg_hkdf_key`. -/
def key (f : Fns) : Prog isa := .frame (.alloc kFr) (keyMain f) (.free kFr)

/-! ## HKDF-Expand -/

/-! Where things are in `expand`'s frame: the save area, the working state
(192 bytes), `T(i)` (64 bytes) and the counter's byte. -/
def eW : Nat := 96
def eT : Nat := 288
def eC : Nat := 352
/-- `expand`'s frame's size. -/
def eFr : Nat := 368

/-- `expand`'s prologue: our caller's registers saved; `key` in `s10`,
`info` and its length in `s3` and `s4`, `out` in `s2`, the bytes of `out`
left in `s5`, the table in `s6`, `D` and `B` in `s7` and `s8`, the length of
`T(i - 1)` (none yet) in `s9` and the counter `i = 1` in `s0`. -/
def expandPro : List Instr :=
  save ++ [mov .s10 .a0, mov .s3 .a1, mov .s4 .a2, mov .s2 .a3, mov .s5 .a4, mov .s6 .a5] ++ loadDB ++
    [.li .s9 0, .li .s0 1]

/-- The copy's arguments: the inner state at `key` in `a4`, the working state
in `a5`, and the 64 bytes to copy in `a6`. -/
def copyArgs : List Instr := [mov .a4 .s10, .addi .a5 .s1 eW, .li .a6 64]

/-- `update`'s arguments for `T(i - 1)`: the working state, which holds `B`
bytes, and the `s9` bytes at `T`. -/
def updT : List Instr := [.addi .a0 .s1 eW, mov .a1 .s8, .addi .a2 .s1 eT, mov .a3 .s9]

/-- `update`'s arguments for `info`: the working state, which holds
`B + s9` bytes. -/
def updI : List Instr := [.addi .a0 .s1 eW, .add .a1 .s8 .s9, mov .a2 .s3, mov .a3 .s4]

/-- The counter's byte stored; `update`'s arguments for it: the working
state, which holds `B + s9 + info_len` bytes, and the byte. -/
def updC : List Instr :=
  [.store .b .s0 .s1 eC, .addi .a0 .s1 eW, .add .a1 .s8 .s9, .add .a1 .a1 .s4, .addi .a2 .s1 eC,
    .li .a3 1]

/-- `finalize`'s arguments: the working state, which holds
`B + s9 + info_len + 1` bytes, the outer state at `key + 192`, and `T`. -/
def finT : List Instr :=
  [.addi .a0 .s1 eW, .addi .a1 .s10 192, .add .a2 .s8 .s9, .add .a2 .a2 .s4, .addi .a2 .a2 1,
    .addi .a3 .s1 eT]

/-- The copy's arguments: `a6 = min(D, rem)` (`rem + ((D - rem) & -(D < rem))`,
the bytes of `out` left in `s5`), `T` in `a4` and `out` in `a5`; and `rem`
less those bytes. -/
def outArgs : List Instr :=
  [.sub .t2 .s7 .s5, .sltu .t3 .s7 .s5, .li .t4 0, .sub .t3 .t4 .t3, .logic .and .t2 .t2 .t3,
    .add .a6 .s5 .t2, .addi .a4 .s1 eT, mov .a5 .s2, .sub .s5 .s5 .a6]

/-- After the copy: `out` past the bytes written (where the copy left `a5`),
`T(i)`'s `D` bytes the next block's `T(i - 1)`, and the next counter. -/
def nextBlock : List Instr := [mov .s2 .a5, mov .s9 .s7, .addi .s0 .s0 1]

/-- One block `T(i)`, whose table's functions may be `f`'s: `T(i)` into the
frame, its first `min(D, rem)` bytes to `out`. -/
def block (f : Fns) : Prog isa :=
  .seq (.seq (.block copyArgs) (Words.RISCV64.copyAny .t0 .a4 .a5 .a6))
  (.seq (.seq (.block updT) (tcall 1 f.upd))
  (.seq (.seq (.block updI) (tcall 1 f.upd))
  (.seq (.seq (.block updC) (tcall 1 f.upd))
  (.seq (.seq (.block finT) (tcall 2 f.fin))
  (.seq (.block outArgs)
  (.seq (Words.RISCV64.copyLoop .t1 .a4 .a5 .a6)
    (.block nextBlock)))))))

/-- The frame's body of `vg_hkdf_expand`, whose table's functions may be
`f`'s: the blocks while bytes of `out` are left. -/
def expandMain (f : Fns) : Prog isa :=
  .seq (.block expandPro)
  (.seq (.ite (.nonzero .s5) (.loop (block f) (.nonzero .s5)) (.block []))
    (.block restore))

/-- `vg_hkdf_expand`. -/
def expand (f : Fns) : Prog isa := .frame (.alloc eFr) (expandMain f) (.free eFr)

end VG.Impl.Hkdf.RISCV64
