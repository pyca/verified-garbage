module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.Arm

/-!
# HKDF (RFC 5869) on 32-bit ARM, with HMAC through a table

Three functions, as on AArch64 (`Impl/Hkdf/AArch64.lean`), each with HMAC
over the hash function of the table `hmac` of the interface `Hmac`
(`Spec/HmacTable.lean`), whose functions they call indirectly (`tcall`: the
table's word `j` into `lr`, then `blx lr`, in a frame pushing the call's
stack arguments, as deterministic ECDSA calls them,
`Impl/Ecdsa/Rfc6979/Arm.lean`): HMAC's `init` for a key of any length (word
0, its working space pushed with `push {r12, lr}`), the streaming `update`
(word 1, its data, their length and its working space pushed with
`push {r1, r7, r10, r12}`) and HMAC's `finalize` (word 2, the MAC's place
and its working space pushed with `push {r10, r12}`), so that the stack
pointer stays 8-byte aligned. The digest length `D` and HMAC's block size
`B` are the table's words of data 4 and 5 (at `hmac + 16` and `hmac + 20`),
which the code loads where it needs them: nothing in the code depends on the
hash function but those two words and the table's functions.

* `vg_hkdf_key(prk = r0, prk_len = r1, key = r2, hmac = r3)` (`key`):
  `init` with `PRK` as the key, into the states at `key` and `key + 192`,
  with its working space in the frame.
* `vg_hkdf_extract(salt = r0, salt_len = r1, ikm = r2, ikm_len = r3,
  prk = [sp], prk_len = [sp + 4], hmac = [sp + 8])` (`extract`): `init`
  with the salt as the key, into the inner and outer states in the frame;
  `update` with the input keying material; `finalize`, which writes `PRK` to
  `prk`.
* `vg_hkdf_expand(key = r0, info = r1, info_len = r2, out = r3,
  out_len = [sp], hmac = [sp + 4])` (`expand`): unless `out_len` is 0, for
  each block `T(i)` (`block`): the inner state at `key` (192 bytes) copied to
  the working state in the frame (`copyLoop`, a byte at a time); `update`
  with `T(i - 1)` (none for the first block, `D` bytes after: the length is
  a word of the frame), then with `info`, then with the counter `i` (a byte,
  the low one of a word of the frame); `finalize` with the outer state at
  `key + 192`, which writes `T(i)` to the frame; and its first `min(D, rem)`
  bytes (chosen with no branch, from the carry of `D - rem`), `rem` the bytes
  of `out` still to write (in `r9`), copied to `out` (in `r8`) by
  `copyLoop`. `key` is only read.

Each runs in a frame (`alloc`) holding our caller's registers it uses and
our return address, which the calls replace, and the working space of the
functions it calls (`8 W` bytes for `update` and `finalize`, `8 (W + S)`
for `init`); our variables live in callee-saved registers, which the
functions we call keep. The calls use the 32 bytes below the frame. Each
block of straight-line code starts by putting the frame's base in `r12`
(`add r12, sp, #0`), from which it forms every address in the frame and
reads the stack arguments. Every address depends only on the pointers and
`D`, and every branch only on lengths.
-/

@[expose] public section

namespace VG.Impl.Hkdf.Arm

open VG.Arm
open VG.Impl.Ecdsa.Rfc6979.Arm (Fns tD tB)
open VG.Impl.AesGcm.Arm (copyLoop addI imm)

/-- The working space the table's functions get: `init`'s for a key of any
length, the most (SHA-512's `W + S` words). -/
def work : Nat := 3408

/-- The indirect call of the table's function `j`, among `ts`, with the
table in `t`: its word `j` into `lr`, then `blx lr`, in a frame pushing
`rs` (its stack arguments) and popping `n` bytes, the first into `r`. -/
def tcall (t : Reg) (j : Nat) (ts : List (String × Prog isa)) (rs : List Reg) (r : Reg) (n : Nat) : Prog isa :=
  .seq (.block [.ldr .lr t (4 * j)]) (.frame (.push rs) (Code.icalls (.blx .lr) ts) (.pop r n))

/-- The table's `update`, in the frame of its stack arguments. -/
def callUpd (t : Reg) (f : Fns) : Prog isa := tcall t 1 f.upd [.r1, .r7, .r10, .r12] .r1 16

/-- The table's HMAC `finalize`, in the frame of its stack arguments. -/
def callFin (t : Reg) (f : Fns) : Prog isa := tcall t 2 f.fin [.r10, .r12] .r12 8

/-- Our caller's registers `l` saved at the frame's start, through `r12`,
the frame's base. -/
def saveRegs (l : List (Reg × Nat)) : List Instr := .addSp .r12 0 :: l.map fun (r, d) => .str r .r12 d

/-- Our caller's registers `l` restored from the frame's start, through `r12`. -/
def restoreRegs (l : List (Reg × Nat)) : List Instr := .addSp .r12 0 :: l.map fun (r, d) => .ldr r .r12 d

/-! ## Keying HMAC -/

/-- `key`'s frame: the working space, then our return address. -/
def kLr : Nat := work
def kFr : Nat := 3424

/-- Our return address saved; `init`'s arguments: the states at `key` and
`key + 192`, `PRK` as the key, the working space (the frame's base, `r12`);
and its address, the table's word 0, in `lr`. -/
def keyArgs : List Instr :=
  [.addSp .r12 0, .str .lr .r12 kLr, .ldr .lr .r3 0, .mov .r3 (.reg .r1), .mov .r1 (.reg .r0), .mov .r0 (.reg .r2),
    .mov .r2 (.reg .r1), addI .r1 .r0 192]

/-- Our return address restored. -/
def keyEpi : List Instr := [.addSp .r12 0, .ldr .lr .r12 kLr]

/-- The frame's body of `vg_hkdf_key`, whose table's `init` may be `f`'s. -/
def keyMain (f : Fns) : Prog isa :=
  .seq (.block keyArgs)
  (.seq (.frame (.push [.r12, .lr]) (Code.icalls (.blx .lr) f.init) (.pop .r12 8))
    (.block keyEpi))

/-- `vg_hkdf_key`. -/
def key (f : Fns) : Prog isa := .frame (.alloc kFr) (keyMain f) (.free kFr)

/-! ## HKDF-Extract -/

/-- Our caller's registers `extract` uses, and our return address, and where
in its frame. -/
def xSaved : List (Reg × Nat) := [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r10, 16), (.lr, 20)]

/-! Where things are in `extract`'s frame: the saved registers, then HMAC's
inner and outer states (192 bytes each), then the working space. -/
def xIn : Nat := 32
def xOut : Nat := 224
def xWork : Nat := 416
/-- `extract`'s frame's size. -/
def xFr : Nat := xWork + work

/-- `extract`'s prologue: our caller's registers saved; `ikm` and its length
in `r4` and `r7`, `prk` (`[sp]` on entry, past the frame) in `r6`, the
table (`[sp + 8]`) in `r5`; then `init`'s arguments: the states, the salt as the key, the
working space. -/
def extractPro : List Instr :=
  saveRegs xSaved ++
    [.mov .r4 (.reg .r2), .mov .r7 (.reg .r3), .ldr .r6 .r12 xFr, .ldr .r5 .r12 (xFr + 8), .mov .r2 (.reg .r0),
      .mov .r3 (.reg .r1), addI .r0 .r12 xIn, addI .r1 .r12 xOut, addI .r12 .r12 xWork]

/-- `update`'s arguments: the inner state, the input keying material (`r1`,
`r7`), the `B` bytes the inner state holds (`r3:r2`), the working space
(`r10`). -/
def extractUpd : List Instr :=
  [.addSp .r12 0, addI .r0 .r12 xIn, .mov .r1 (.reg .r4), .ldr .r2 .r5 tB, .mov .r3 (imm 0), addI .r10 .r12 xWork]

/-- `finalize`'s arguments: the states, the `B + ikm_len` bytes the inner one
holds, `prk` (`r10`), the working space (`r12`). -/
def extractFin : List Instr :=
  [.addSp .r12 0, addI .r0 .r12 xIn, addI .r1 .r12 xOut, .ldr .r2 .r5 tB, .dp .add .r2 .r2 (.reg .r7),
    .mov .r3 (imm 0), .mov .r10 (.reg .r6), addI .r12 .r12 xWork]

/-- Our caller's registers and our return address restored. -/
def extractEpi : List Instr := restoreRegs xSaved

/-- The frame's body of `vg_hkdf_extract`, whose table's functions may be
`f`'s. -/
def extractMain (f : Fns) : Prog isa :=
  .seq (.block extractPro)
  (.seq (tcall .r5 0 f.init [.r12, .lr] .r12 8)
  (.seq (.block extractUpd)
  (.seq (callUpd .r5 f)
  (.seq (.block extractFin)
  (.seq (callFin .r5 f)
    (.block extractEpi))))))

/-- `vg_hkdf_extract`. -/
def extract (f : Fns) : Prog isa := .frame (.alloc xFr) (extractMain f) (.free xFr)

/-! ## HKDF-Expand -/

/-- Our caller's registers `expand` uses, and our return address, and where
in its frame. -/
def eSaved : List (Reg × Nat) :=
  [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20), (.r10, 24), (.r11, 28), (.lr, 32)]

/-! Where things are in `expand`'s frame: the saved registers, the counter
`i` (a word, whose low byte `update` reads), the length of `T(i - 1)`,
`T(i)` (64 bytes), the working state (192 bytes), then the working space of
`update` and `finalize`. -/
def eC : Nat := 40
def eL : Nat := 44
def eT : Nat := 48
def eW : Nat := 112
def eWork : Nat := 304
/-- `expand`'s frame's size: the working space of `update` and `finalize`
is at most 1872 bytes. -/
def eFr : Nat := eWork + 1872

/-- `expand`'s prologue: our caller's registers saved; `key` in `r4`, `info`
and its length in `r5` and `r6`, `out` in `r8`, the bytes of `out` left
(`out_len`, `[sp]` on entry) in `r9`, the table (`[sp + 4]`) in `r11`, the
counter `i = 1` and the length of `T(i - 1)` (none yet) in the frame; `Z`
set iff `out_len` is 0. -/
def expandPro : List Instr :=
  saveRegs eSaved ++
    [.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2), .mov .r8 (.reg .r3), .ldr .r9 .r12 eFr,
      .ldr .r11 .r12 (eFr + 4), .mov .r0 (imm 1), .str .r0 .r12 eC, .mov .r0 (imm 0), .str .r0 .r12 eL,
      .cmp .r9 (imm 0)]

/-- The copy of the inner state at `key`, its 192 bytes, to the working
state: `copyLoop`'s arguments. -/
def copyW : List Instr := [.addSp .r12 0, .mov .r1 (.reg .r4), addI .r2 .r12 eW, .mov .r3 (imm 192)]

/-- `update`'s arguments for `T(i - 1)`: the working state, which holds `B`
bytes, the bytes at `T` of the length the frame holds. -/
def updT : List Instr :=
  [.addSp .r12 0, addI .r0 .r12 eW, addI .r1 .r12 eT, .ldr .r7 .r12 eL, .ldr .r2 .r11 tB, .mov .r3 (imm 0),
    addI .r10 .r12 eWork]

/-- `update`'s arguments for `info`: the working state, which holds
`B + |T(i - 1)|` bytes. -/
def updI : List Instr :=
  [.addSp .r12 0, addI .r0 .r12 eW, .mov .r1 (.reg .r5), .mov .r7 (.reg .r6), .ldr .r2 .r11 tB, .ldr .r3 .r12 eL,
    .dp .add .r2 .r2 (.reg .r3), .mov .r3 (imm 0), addI .r10 .r12 eWork]

/-- `update`'s arguments for the counter's byte: the working state, which
holds `B + |T(i - 1)| + info_len` bytes. -/
def updC : List Instr :=
  [.addSp .r12 0, addI .r0 .r12 eW, addI .r1 .r12 eC, .mov .r7 (imm 1), .ldr .r2 .r11 tB, .ldr .r3 .r12 eL,
    .dp .add .r2 .r2 (.reg .r3), .dp .add .r2 .r2 (.reg .r6), .mov .r3 (imm 0), addI .r10 .r12 eWork]

/-- `finalize`'s arguments: the working state, which holds
`B + |T(i - 1)| + info_len + 1` bytes, the outer state at `key + 192`, `T`
(`r10`), the working space (`r12`). -/
def finT : List Instr :=
  [.addSp .r12 0, addI .r0 .r12 eW, addI .r1 .r4 192, .ldr .r2 .r11 tB, .ldr .r3 .r12 eL,
    .dp .add .r2 .r2 (.reg .r3), .dp .add .r2 .r2 (.reg .r6), addI .r2 .r2 1, .mov .r3 (imm 0),
    addI .r10 .r12 eT, addI .r12 .r12 eWork]

/-- The bytes of `T(i)` to copy, `min(D, rem)`, into `r3` (`copyLoop`'s
count) and `r7`: `rem + ((D - rem) & mask)`, the mask all ones iff
`D < rem` (`subs` clears C, borrowing, iff `D < rem`); `T` in `r1` and
`out` in `r2`. -/
def outArgs : List Instr :=
  [.addSp .r12 0, .ldr .r3 .r11 tD, .subs .r0 .r3 (.reg .r9), .mov .r1 (imm 0), .adc .r1 .r1 (imm 0),
    .dp .sub .r1 .r1 (imm 1), .dp .and .r0 .r0 (.reg .r1), .dp .add .r3 .r9 (.reg .r0), .mov .r7 (.reg .r3),
    addI .r1 .r12 eT, .mov .r2 (.reg .r8)]

/-- After the copy: `out` past the bytes written, `rem` less them, `T(i)`'s
`D` bytes the next block's `T(i - 1)`, the next counter; `Z` set iff no
bytes of `out` are left. -/
def nextBlock : List Instr :=
  [.addSp .r12 0, .dp .add .r8 .r8 (.reg .r7), .dp .sub .r9 .r9 (.reg .r7), .ldr .r0 .r11 tD, .str .r0 .r12 eL,
    .ldr .r0 .r12 eC, addI .r0 .r0 1, .str .r0 .r12 eC, .cmp .r9 (imm 0)]

/-- One block `T(i)`, whose table's functions may be `f`'s. -/
def block (f : Fns) : Prog isa :=
  .seq (.block copyW)
  (.seq copyLoop
  (.seq (.block updT)
  (.seq (callUpd .r11 f)
  (.seq (.block updI)
  (.seq (callUpd .r11 f)
  (.seq (.block updC)
  (.seq (callUpd .r11 f)
  (.seq (.block finT)
  (.seq (callFin .r11 f)
  (.seq (.block outArgs)
  (.seq copyLoop
    (.block nextBlock))))))))))))

/-- Our caller's registers and our return address restored. -/
def expandEpi : List Instr := restoreRegs eSaved

/-- The frame's body of `vg_hkdf_expand`, whose table's functions may be
`f`'s: the blocks while bytes of `out` are left. -/
def expandMain (f : Fns) : Prog isa :=
  .seq (.block expandPro)
  (.seq (.ite .eq (.block []) (.loop (block f) .ne))
    (.block expandEpi))

/-- `vg_hkdf_expand`. -/
def expand (f : Fns) : Prog isa := .frame (.alloc eFr) (expandMain f) (.free eFr)

end VG.Impl.Hkdf.Arm
