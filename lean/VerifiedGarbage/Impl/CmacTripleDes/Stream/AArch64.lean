module

public import VerifiedGarbage.Impl.CmacTripleDes.AArch64

/-!
# Streaming TDEA-CMAC: AArch64 implementation

`vg_cmac_triple_des_stream_init(state = x0, key = x1, key_len = x2, scratch = x3)`,
`vg_cmac_triple_des_absorb(state = x0, count = x1, data = x2, len = x3, scratch = x4)`
and `vg_cmac_triple_des_finish(state = x0, count = x1, out = x2, scratch = x3)`
(see `VG.Spec.Cmac.tdesStreamInitContract` and the others), built, as on
x86-64 (`Impl/CmacTripleDes/Stream/X86_64.lean`), from the code of
`vg_cmac_triple_des_init`, `vg_cmac_triple_des_update` and
`vg_cmac_triple_des_finalize` (`Impl/CmacTripleDes/AArch64.lean`), inline:
each takes its arguments in the registers of its own signature and its
640-byte working space in `scratch`, keeps our caller's callee-saved
registers and leaves `x30`, the return address, alone.

The state (`VG.Spec.Cmac.tdesRepr`) is the key schedule (bytes 0–383), the
subkeys (384–399), the chaining value (400–407) and the bytes held back
(408–415). The scratch buffer: `[0, 640)` is the working space of the code
inlined, and `absorb` keeps our caller's callee-saved registers in
`[640, 680)`.

* `stream_init` zeroes the chaining value, and runs `init` with the state
  as its `out`.
* `absorb` keeps the state (`x19`), the data left (`x21`, `x22` bytes), the
  scratch buffer (`x23`) and the bytes of whole blocks chained by the second
  run of `update` (`x20`) across the runs, as AES-CMAC's does
  (`Impl/CmacAes/Stream/AArch64.lean`), with 8-byte blocks.
* `finish` copies the chaining value to `out`, and runs `finalize` with the
  state as its key, `out` as its state and the `h` bytes held back as the
  last bytes.

The model has no flags to branch on: the branches are `cbz`/`cbnz`, and
`min(len, 8 - h)` is `min(min(len, 8), 8 - h)`, the first by whether
`len >> 3` is 0, the second by the sign of a difference of two numbers of at
most 8. Only the pointers, the key length, `count` and `len` can affect
timing: the branches are on them, and so are the number of bytes copied and
of blocks chained.
-/

@[expose] public section

namespace VG.Impl.CmacTripleDes.Stream.AArch64

open VG.AArch64
open VG.Impl.CmacTripleDes.AArch64 (mov)

/-! ## `vg_cmac_triple_des_stream_init` -/

/-- The chaining value zeroed, and the arguments of
`init(key = x0, key_len = x1, out = x2, scratch = x3)`. -/
def initPre : List Instr :=
  [.movz .x .x9 0 0, .str .x .x9 .x0 400, mov .x9 .x0, mov .x0 .x1, mov .x1 .x2, mov .x2 .x9]

def streamInit : Prog isa := .seq (.block initPre) Impl.CmacTripleDes.AArch64.init

/-! ## Copying bytes -/

/-- The `x8` bytes at `x7` (none if `x8` is 0) copied to `x6`, a byte at a time. -/
def copy : Prog isa := .ite (.zero .x .x8) (.block []) Impl.CmacTripleDes.AArch64.copy

/-! ## `vg_cmac_triple_des_absorb` -/

/-- The registers saved in the scratch buffer, and where (`x23`, the base of
the restore, last). -/
def saved : List (Reg × Nat) := [(.x19, 640), (.x20, 648), (.x21, 656), (.x22, 664), (.x23, 672)]

/-- Saves the registers and keeps the arguments in them. -/
def save : List Instr :=
  saved.map (fun (r, d) => .str .x r .x4 d) ++ [mov .x19 .x0, mov .x21 .x2, mov .x22 .x3, mov .x23 .x4]

/-- The number of bytes held back for `count` (`x1`), in `x9`. -/
def held : Prog isa :=
  .ite (.zero .x .x1) (.block [.movz .x .x9 0 0])
    (.block [.subImm .x .x9 .x1 1, .movz .x .x10 7 0, .logic .and .x .x9 .x9 .x10, .addImm .x .x9 .x9 1])

/-- `min(len, 8)` in `x10`. -/
def clamp : Prog isa :=
  .seq (.block [.lsr .x .x10 .x22 3])
    (.ite (.zero .x .x10) (.block [mov .x10 .x22]) (.block [.movz .x .x10 8 0]))

/-- `f = min(len, 8 - h)` in `x8` and `x10`, the destination `state + 408 + h`
in `x6` and the source in `x7`. -/
def fill : Prog isa :=
  .seq clamp
    (.seq (.block [.movz .x .x8 8 0, .sub .x .x8 .x8 .x9, .sub .x .x11 .x10 .x8, .lsr .x .x11 .x11 63])
      (.seq (.ite (.zero .x .x11) (.block []) (.block [mov .x8 .x10]))
        (.block [mov .x10 .x8, .add .x .x6 .x19 .x9, .addImm .x .x6 .x6 408, mov .x7 .x21])))

/-- The data advanced past the `f` bytes copied; one block to chain (`x3`)
if data is left, else none; and the other arguments of
`update(schedule = x0, state = x1, data = x2, n = x3, scratch = x4)` for the
block held back. -/
def chain1 : Prog isa :=
  .seq (.block [.add .x .x21 .x21 .x10, .sub .x .x22 .x22 .x10, .movz .x .x3 0 0])
    (.seq (.ite (.zero .x .x22) (.block []) (.block [.movz .x .x3 1 0]))
      (.block [mov .x0 .x19, .addImm .x .x1 .x19 400, .addImm .x .x2 .x19 408, mov .x4 .x23]))

/-- `8 nb` in `x20` for the `nb` whole blocks of the data left but its last
1 to 8 bytes (none if no data is left), and the arguments of `update` for
them. -/
def chain2 : Prog isa :=
  .seq (.block [.movz .x .x20 0 0])
    (.seq (.ite (.zero .x .x22) (.block [])
        (.block [.subImm .x .x20 .x22 1, .movz .x .x9 7 0, .logic .and .x .x9 .x20 .x9,
          .sub .x .x20 .x20 .x9]))
      (.block [.lsr .x .x3 .x20 3, mov .x0 .x19, .addImm .x .x1 .x19 400, mov .x2 .x21, mov .x4 .x23]))

/-- The data advanced past the blocks chained, and the arguments of the
copy of the rest to the start of the bytes held back. -/
def rest : List Instr :=
  [.add .x .x21 .x21 .x20, .sub .x .x22 .x22 .x20, .addImm .x .x6 .x19 408, mov .x7 .x21, mov .x8 .x22]

/-- Restores the registers, with `x23` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .ldr .x r .x23 d

/-- Everything before the first run of `update`. -/
def absorbPre : Prog isa := .seq (.block save) (.seq held (.seq fill (.seq copy chain1)))

/-- Everything after the second. -/
def absorbPost : Prog isa := .seq (.block rest) (.seq copy (.block restore))

/-- Up to the first run of `update`, and that run. -/
def absorb₁ : Prog isa := .seq absorbPre Impl.CmacTripleDes.AArch64.update

/-- The second run of `update`, with its arguments. -/
def absorb₂ : Prog isa := .seq chain2 Impl.CmacTripleDes.AArch64.update

def absorb : Prog isa := .seq absorb₁ (.seq absorb₂ absorbPost)

/-! ## `vg_cmac_triple_des_finish` -/

/-- The chaining value copied to `out`, and the arguments of
`finalize(key = x0, state = x1, last = x2, last_len = x3, scratch = x4)` but
`last_len`, which is `count` in `x3` so far. -/
def finishPre : List Instr :=
  [.ldr .x .x9 .x0 400, .str .x .x9 .x2 0, mov .x4 .x3, mov .x3 .x1, mov .x1 .x2, .addImm .x .x2 .x0 408]

/-- `last_len`: the number of bytes held back for `count` (in `x3`). -/
def lastLen : Prog isa :=
  .ite (.zero .x .x3) (.block [])
    (.block [.subImm .x .x3 .x3 1, .movz .x .x9 7 0, .logic .and .x .x3 .x3 .x9, .addImm .x .x3 .x3 1])

/-- Everything before `finalize`. -/
def finPre : Prog isa := .seq (.block finishPre) lastLen

def finish : Prog isa := .seq finPre Impl.CmacTripleDes.AArch64.finalize

end VG.Impl.CmacTripleDes.Stream.AArch64
