module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.AArch64

/-!
# HKDF (RFC 5869) on AArch64, with HMAC through a table

Three functions, each with HMAC over the hash function of the table `hmac`
of the interface `Hmac` (`Spec/HmacTable.lean`), whose functions they call
indirectly (`tcall`: the table's word `j` into `x16`, then `blr x16`):
HMAC's `init` for a key of any length (word 0), the streaming `update`
(word 1) and HMAC's `finalize` (word 2), each with its working space in
`x4`. The digest length `D` and HMAC's block size `B` are the table's words
of data 4 and 5, which the code loads where it needs them: nothing in the
code depends on the hash function but those two words and the table's
functions.

* `vg_hkdf_key(prk = x0, prk_len = x1, key = x2, hmac = x3)` (`key`):
  `init` with `PRK` as the key, into the states at `key` and `key + 192`,
  with its working space in the frame.
* `vg_hkdf_extract(salt = x0, salt_len = x1, ikm = x2, ikm_len = x3,
  prk = x4, prk_len = x5, hmac = x6)` (`extract`): `init` with the salt as
  the key, into the inner and outer states in the frame; `update` with the
  input keying material; `finalize`, which writes `PRK` to `prk`.
* `vg_hkdf_expand(key = x0, info = x1, info_len = x2, out = x3,
  out_len = x4, hmac = x5)` (`expand`): unless `out_len` is 0, for each
  block `T(i)` (`block`): the inner state at `key` made the working state in
  the frame, by copying its first 64 bytes (`copyW`): the inner state holds
  a whole block of key, so its hash value, at most 64 bytes, is all of it
  that matters; `update` with `T(i - 1)` (the `x26` bytes at `T` in the
  frame: none for the first block, `D` after), then with `info`, then with
  the counter `i` (a byte, kept in `x25`); `finalize` with the outer state
  at `key + 192`, which writes `T(i)` to the frame; and its first
  `min(D, rem)` bytes (`csel`, with no branch), `rem` the bytes of `out`
  still to write (in `x23`), copied to `out` (in `x22`) a byte at a time
  (`Cfg.cpLoop`). `key` is only read.

Each pushes its return address `x30` (the calls replace it), then runs in a
frame (`alloc`) holding our caller's registers it uses, at its start, and
the working space of the functions it calls (`8 W` bytes for `update` and
`finalize`, `8 (W + S)` for `init`); our variables live in callee-saved
registers, which the functions we call keep. The functions we call use the
16 bytes below the frame. Every address depends only on the pointers and
`D`, and every branch only on lengths.
-/

@[expose] public section

namespace VG.Impl.Hkdf.AArch64

open VG.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)

/-- `d ← n`. -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- The working space the table's functions get: `init`'s for a key of any
length, the most (SHA-512's `W + S` words). -/
def work : Nat := 3408

/-- The indirect call of the table's function `j`, among `ts`, with the
table in `t`: its word `j` into `x16`, then `blr x16`. -/
def tcall (t : Reg) (j : Nat) (ts : List (String × Prog isa)) : Prog isa :=
  .seq (.block [.ldr .x .x16 t (8 * j)]) (Code.icalls (.blr .x16) ts)

/-- `B`, the table's word of data 5, into `d`. -/
def ldB (t d : Reg) : Instr := .ldr .x d t 40

/-- `D`, the table's word of data 4, into `d`. -/
def ldD (t d : Reg) : Instr := .ldr .x d t 32

/-- `c` in a frame of `n` bytes, the return address pushed around it. -/
def framed (n : Nat) (c : Prog isa) : Prog isa :=
  .frame (.push .x30) (.frame (.alloc n) c (.free n)) (.pop .x30)

/-! ## Keying HMAC -/

/-- `key`'s frame: the working space. -/
def kFr : Nat := work

/-- `init`'s arguments: the states at `key` and `key + 192`, `PRK` as the
key, the working space; and its address, the table's word 0, in `x16`. -/
def keyArgs : List Instr :=
  [.ldr .x .x16 .x3 0, mov .x3 .x1, mov .x9 .x0, mov .x0 .x2, .addImm .x .x1 .x2 192, mov .x2 .x9,
    .addSp .x4 0]

/-- The frame's body of `vg_hkdf_key`, whose table's `init` may be `f`'s. -/
def keyMain (f : Fns) : Prog isa := .seq (.block keyArgs) (Code.icalls (.blr .x16) f.init)

/-- `vg_hkdf_key`. -/
def key (f : Fns) : Prog isa := framed kFr (keyMain f)

/-! ## HKDF-Extract -/

/-- Our caller's registers `extract` uses, and where in its frame. -/
def xSaved : List (Reg × Nat) := [(.x19, 0), (.x20, 8), (.x21, 16), (.x22, 24)]

/-! Where things are in `extract`'s frame: our caller's `x19`–`x22`, then
HMAC's inner and outer states (192 bytes each), then the working space. -/
def xIn : Nat := 32
def xOut : Nat := 224
def xWork : Nat := 416
/-- `extract`'s frame's size. -/
def xFr : Nat := xWork + work

/-- Our caller's registers `l` saved at the frame's start, through `x9`. -/
def saveRegs (l : List (Reg × Nat)) : List Instr := .addSp .x9 0 :: l.map fun (r, d) => .str .x r .x9 d

/-- Our caller's registers `l` restored from the frame's start, through `x9`. -/
def restoreRegs (l : List (Reg × Nat)) : List Instr := .addSp .x9 0 :: l.map fun (r, d) => .ldr .x r .x9 d

/-- `extract`'s prologue: our caller's registers saved; `ikm` and its length
in `x19` and `x20`, `prk` in `x21`, the table in `x22`; then `init`'s
arguments: the salt as the key, the states, the working space. -/
def extractPro : List Instr :=
  saveRegs xSaved ++
    [mov .x19 .x2, mov .x20 .x3, mov .x21 .x4, mov .x22 .x6, mov .x2 .x0, mov .x3 .x1, .addSp .x0 xIn,
      .addSp .x1 xOut, .addSp .x4 xWork]

/-- `update`'s arguments: the inner state, which holds `B` bytes, the input
keying material, the working space. -/
def extractUpd : List Instr := [.addSp .x0 xIn, ldB .x22 .x1, mov .x2 .x19, mov .x3 .x20, .addSp .x4 xWork]

/-- `finalize`'s arguments: the states, the `B + ikm_len` bytes the inner one
holds, `prk`, the working space. -/
def extractFin : List Instr :=
  [.addSp .x0 xIn, .addSp .x1 xOut, ldB .x22 .x2, .add .x .x2 .x2 .x20, mov .x3 .x21, .addSp .x4 xWork]

/-- Our caller's registers restored. -/
def extractEpi : List Instr := restoreRegs xSaved

/-- The frame's body of `vg_hkdf_extract`, whose table's functions may be
`f`'s. -/
def extractMain (f : Fns) : Prog isa :=
  .seq (.block extractPro)
  (.seq (tcall .x22 0 f.init)
  (.seq (.block extractUpd)
  (.seq (tcall .x22 1 f.upd)
  (.seq (.block extractFin)
  (.seq (tcall .x22 2 f.fin)
    (.block extractEpi))))))

/-- `vg_hkdf_extract`. -/
def extract (f : Fns) : Prog isa := framed xFr (extractMain f)

/-! ## HKDF-Expand -/

/-- Our caller's registers `expand` uses, and where in its frame. -/
def eSaved : List (Reg × Nat) :=
  [(.x19, 0), (.x20, 8), (.x21, 16), (.x22, 24), (.x23, 32), (.x24, 40), (.x25, 48), (.x26, 56)]

/-! Where things are in `expand`'s frame: our caller's `x19`–`x26`, the
working state (192 bytes), `T(i)` (64 bytes), the counter's byte (in 16
bytes), then the working space of `update` and `finalize`. -/
def eW : Nat := 64
def eT : Nat := 256
def eC : Nat := 320
def eWork : Nat := 336
/-- `expand`'s frame's size: the working space of `update` and `finalize`
is at most 1872 bytes. -/
def eFr : Nat := eWork + 1872

/-- `expand`'s prologue: our caller's registers saved; `key` in `x19`,
`info` and its length in `x20` and `x21`, `out` in `x22`, the bytes of `out`
left in `x23`, the table in `x24`, the counter `i = 1` in `x25` and the
length of `T(i - 1)` (none yet) in `x26`. -/
def expandPro : List Instr :=
  saveRegs eSaved ++
    [mov .x19 .x0, mov .x20 .x1, mov .x21 .x2, mov .x22 .x3, mov .x23 .x4, mov .x24 .x5,
      .movz .x .x25 1 0, .movz .x .x26 0 0]

/-- The inner state's first 64 bytes at `key` to the working state, a word at
a time through `x9`. -/
def copyW : List Instr :=
  (List.range 8).flatMap fun j => [.ldr .x .x9 .x19 (8 * j), .strSp .x9 (eW + 8 * j)]

/-- `update`'s arguments for `T(i - 1)`: the working state, which holds `B`
bytes, the `x26` bytes at `T`, the working space. -/
def updT : List Instr := [.addSp .x0 eW, ldB .x24 .x1, .addSp .x2 eT, mov .x3 .x26, .addSp .x4 eWork]

/-- `update`'s arguments for `info`: the working state, which holds
`B + x26` bytes. -/
def updI : List Instr :=
  [.addSp .x0 eW, ldB .x24 .x1, .add .x .x1 .x1 .x26, mov .x2 .x20, mov .x3 .x21, .addSp .x4 eWork]

/-- The counter's byte stored; `update`'s arguments for it: the working
state, which holds `B + x26 + info_len` bytes, and the byte. -/
def updC : List Instr :=
  [.addSp .x2 eC, .strb .x25 .x2 0, .addSp .x0 eW, ldB .x24 .x1, .add .x .x1 .x1 .x26,
    .add .x .x1 .x1 .x21, .movz .x .x3 1 0, .addSp .x4 eWork]

/-- `finalize`'s arguments: the working state, which holds
`B + x26 + info_len + 1` bytes, the outer state at `key + 192`, `T`, the
working space. -/
def finT : List Instr :=
  [.addSp .x0 eW, .addImm .x .x1 .x19 192, ldB .x24 .x2, .add .x .x2 .x2 .x26, .add .x .x2 .x2 .x21,
    .addImm .x .x2 .x2 1, .addSp .x3 eT, .addSp .x4 eWork]

/-- The bytes of `T(i)` to copy, `min(D, rem)`, into `x14` and the copy's
count `x13`: `D`, or `rem` if it is less (`subs` sets C, no borrow, when
`rem ≥ D`); `T` in `x11` and `out` in `x12`. -/
def outArgs : List Instr :=
  [ldD .x24 .x14, .subs .x .x9 .x23 .x14, .cselc .x .x14 .x14 .x23 .hs, mov .x13 .x14, .addSp .x11 eT,
    mov .x12 .x22]

/-- After the copy: `out` past the bytes written, `rem` less them, `T(i)`'s
`D` bytes the next block's `T(i - 1)`, the next counter. -/
def nextBlock : List Instr :=
  [.add .x .x22 .x22 .x14, .sub .x .x23 .x23 .x14, ldD .x24 .x26, .addImm .x .x25 .x25 1]

/-- One block `T(i)`, whose table's functions may be `f`'s. -/
def block (f : Fns) : Prog isa :=
  .seq (.block copyW)
  (.seq (.seq (.block updT) (tcall .x24 1 f.upd))
  (.seq (.seq (.block updI) (tcall .x24 1 f.upd))
  (.seq (.seq (.block updC) (tcall .x24 1 f.upd))
  (.seq (.seq (.block finT) (tcall .x24 2 f.fin))
  (.seq (.block outArgs)
  (.seq Impl.Ecdsa.Rfc6979.AArch64.Cfg.cpLoop
    (.block nextBlock)))))))

/-- Our caller's registers restored. -/
def expandEpi : List Instr := restoreRegs eSaved

/-- The frame's body of `vg_hkdf_expand`, whose table's functions may be
`f`'s: the blocks while bytes of `out` are left. -/
def expandMain (f : Fns) : Prog isa :=
  .seq (.block expandPro)
  (.seq (.ite (.nonzero .x .x23) (.loop (block f) (.nonzero .x .x23)) (.block []))
    (.block expandEpi))

/-- `vg_hkdf_expand`. -/
def expand (f : Fns) : Prog isa := framed eFr (expandMain f)

end VG.Impl.Hkdf.AArch64
