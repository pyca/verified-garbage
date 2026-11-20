module

public import VerifiedGarbage.Impl.CmacAes.AArch64.Callee
public import VerifiedGarbage.Impl.CmacAes.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64.Union
public import VerifiedGarbage.Impl.StackScratch.AArch64

/-!
# Streaming AES-CMAC: AArch64 implementation

`vg_cmac_aes_init(state = x0, key = x1, key_len = x2, scratch = x3)`,
`vg_cmac_aes_absorb(state = x0, rounds = x1, count = x2, data = x3, len = x4, scratch = x5)`
and `vg_cmac_aes_finish(state = x0, rounds = x1, count = x2, out = x3, scratch = x4)`
(see `VG.Spec.Cmac.aesInitContract` and the others), composed of calls of
the verified `vg_aes_expand_key_scratch`, `vg_cmac_aes_subkeys`, `vg_cmac_aes_update`
and `vg_cmac_aes_finalize`. Initialization and finalization are generic
over AES (`Ctr32`, its `ExpandKey`, and their symbol suffix). Absorption is
generic over whole-block CMAC chaining (`Update`), so a specialized chaining
loop reaches streaming callers without changing their buffering proof.

The state (`VG.Spec.Cmac.Repr`) is the key schedule (bytes 0–239), the
subkeys (240–271), the chaining value (272–287) and the bytes held back
(288–303), so bytes 0–271 are `vg_cmac_aes_finalize`'s `key`. The scratch
buffer of `init` holds our caller's callee-saved registers and our return
address `x30` in `[0, 32)` and the working space of the functions called
after it, from `initWOff`; `finish`'s holds the registers in `[0, 16)` and
the working space from `finWOff`. The working space is as large as the
implementations called need (`Ctr32Impl.scratch`), so the code does not
depend on its size. `absorb`'s (`64 + n` bytes, for a
chaining implementation that needs `n`): `[8, 64)` holds the registers and
`[64, 64 + n)` is the working space of the function called. A call (`bl`)
stores nothing in memory, so no stack is used.

* `init` expands the key into the state, derives the subkeys after it and
  zeroes the chaining value, keeping the state (`x19`), the scratch buffer
  (`x20`) and the rounds (`x21`) across the calls.
* `absorb` keeps the state (`x19`), the rounds (`x20`), the data left
  (`x21`, `x22` bytes), the scratch buffer (`x23`) and the bytes of whole
  blocks chained by the second call (`x24`) across the calls. With `h`
  bytes held back (`count` modulo 16, but 16 for a multiple of 16 and 0 for
  the empty message), it copies `f = min(len, 16 - h)` bytes after them. If
  data is left (the block held back is whole and not the last), it chains
  that block, then the whole blocks of what is left but its last 1 to 16
  bytes, which it copies to the start of the bytes held back. With no data
  left, the two calls chain no blocks and the second copy copies nothing,
  so the code has no branch around a call.
* `finish` copies the chaining value to `out` and calls
  `vg_cmac_aes_finalize` with the state as its key, `out` as its state and
  the `h` bytes held back as the last bytes, keeping only the scratch buffer
  (in `x19`) across the call.

The model has no flags to branch on: the branches are `cbz`/`cbnz`, and
`min(len, 16 - h)` is `min(min(len, 16), 16 - h)`, the first by whether
`len >> 4` is 0, the second by the sign of a difference of two numbers of at
most 16. Only the pointers, the key length, `count` and `len` can affect
timing: the branches are on them, and so are the number of bytes copied and
of blocks chained.
-/

@[expose] public section

namespace VG.Impl.CmacAes.Stream.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (Ctr32 ExpandKey)
open VG.Impl.CmacAes.AArch64 (mov)

/-! ## `vg_cmac_aes_init` -/

/-- The registers saved in the scratch buffer, and where. -/
def initSaved : List (Reg × Nat) := [(.x19, 0), (.x20, 8), (.x21, 16), (.x30, 24)]

/-- The offset of the working space of the functions `init` calls. -/
def initWOff : Nat := 32

/-- Saves the registers, keeps the state in `x19`, the scratch buffer in
`x20` and the rounds (`key_len / 4 + 6`) in `x21`, and sets up the arguments
of `vg_aes_expand_key_scratch(key = x0, key_len = x1, schedule = x2, scratch = x3)`. -/
def initPre : List Instr :=
  initSaved.map (fun (r, d) => .str .x r .x3 d) ++
  [mov .x19 .x0, mov .x20 .x3, .lsr .x .x21 .x2 2, .addImm .x .x21 .x21 6, mov .x0 .x1, mov .x1 .x2,
   mov .x2 .x19, .addImm .x .x3 .x3 initWOff]

/-- The arguments of `vg_cmac_aes_subkeys(schedule = x0, rounds = x1, subkeys = x2, scratch = x3)`. -/
def initMid : List Instr := [mov .x0 .x19, mov .x1 .x21, .addImm .x .x2 .x19 240, .addImm .x .x3 .x20 initWOff]

/-- The chaining value zeroed, and the registers restored (`x20` last). -/
def initPost : List Instr :=
  [.movz .x .x9 0 0, .str .x .x9 .x19 272, .str .x .x9 .x19 280, .ldr .x .x30 .x20 24,
   .ldr .x .x19 .x20 0, .ldr .x .x21 .x20 16, .ldr .x .x20 .x20 8]

def init (e : ExpandKey) (c : Ctr32) (sfx : String) : Prog isa :=
  .seq (.block initPre)
    (.seq (.call e.name e.code)
      (.seq (.block initMid) (.seq (.call ("vg_cmac_aes_subkeys" ++ sfx) (Impl.CmacAes.AArch64.subkeys c))
        (.block initPost))))

/-! ## Copying bytes -/

/-- The `x8` bytes at `x7` (none if `x8` is 0) copied to `x6`, a byte at a time. -/
def copy : Prog isa := .ite (.zero .x .x8) (.block []) Impl.CmacAes.AArch64.copy

/-! ## `vg_cmac_aes_absorb` -/

/-- The registers saved in the scratch buffer, and where (`x23`, the base of
the restore, last). -/
def saved : List (Reg × Nat) :=
  [(.x19, 8), (.x20, 16), (.x21, 24), (.x22, 32), (.x24, 40), (.x30, 48), (.x23, 56)]

/-- Saves the registers and keeps the arguments in them. -/
def save : List Instr :=
  saved.map (fun (r, d) => .str .x r .x5 d) ++
  [mov .x19 .x0, mov .x20 .x1, mov .x21 .x3, mov .x22 .x4, mov .x23 .x5]

/-- The number of bytes held back for `count` (`x2`), in `x9`. -/
def held : Prog isa :=
  .ite (.zero .x .x2) (.block [.movz .x .x9 0 0])
    (.block [.subImm .x .x9 .x2 1, .movz .x .x10 15 0, .logic .and .x .x9 .x9 .x10, .addImm .x .x9 .x9 1])

/-- `min(len, 16)` in `x10`. -/
def clamp : Prog isa :=
  .seq (.block [.lsr .x .x10 .x22 4])
    (.ite (.zero .x .x10) (.block [mov .x10 .x22]) (.block [.movz .x .x10 16 0]))

/-- `f = min(len, 16 - h)` in `x8` and `x10`, the destination `state + 288 + h`
in `x6` and the source in `x7`. -/
def fill : Prog isa :=
  .seq clamp
    (.seq (.block [.movz .x .x8 16 0, .sub .x .x8 .x8 .x9, .sub .x .x11 .x10 .x8, .lsr .x .x11 .x11 63])
      (.seq (.ite (.zero .x .x11) (.block []) (.block [mov .x8 .x10]))
        (.block [mov .x10 .x8, .add .x .x6 .x19 .x9, .addImm .x .x6 .x6 288, mov .x7 .x21])))

/-- The data advanced past the `f` bytes copied; one block to chain (`x4`)
if data is left, else none; and the other arguments of
`vg_cmac_aes_update(schedule = x0, rounds = x1, state = x2, data = x3, n = x4, scratch = x5)`
for the block held back. -/
def chain1 : Prog isa :=
  .seq (.block [.add .x .x21 .x21 .x10, .sub .x .x22 .x22 .x10, .movz .x .x4 0 0])
    (.seq (.ite (.zero .x .x22) (.block []) (.block [.movz .x .x4 1 0]))
      (.block [mov .x0 .x19, mov .x1 .x20, .addImm .x .x2 .x19 272, .addImm .x .x3 .x19 288,
        .addImm .x .x5 .x23 64]))

/-- `16 nb` in `x24` for the `nb` whole blocks of the data left but its last
1 to 16 bytes (none if no data is left), and the arguments of
`vg_cmac_aes_update` for them. -/
def chain2 : Prog isa :=
  .seq (.block [.movz .x .x24 0 0])
    (.seq (.ite (.zero .x .x22) (.block [])
        (.block [.subImm .x .x24 .x22 1, .movz .x .x9 15 0, .logic .and .x .x9 .x24 .x9,
          .sub .x .x24 .x24 .x9]))
      (.block [.lsr .x .x4 .x24 4, mov .x0 .x19, mov .x1 .x20, .addImm .x .x2 .x19 272, mov .x3 .x21,
        .addImm .x .x5 .x23 64]))

/-- The data advanced past the blocks chained, and the arguments of the
copy of the rest to the start of the bytes held back. -/
def rest : List Instr :=
  [.add .x .x21 .x21 .x24, .sub .x .x22 .x22 .x24, .addImm .x .x6 .x19 288, mov .x7 .x21, mov .x8 .x22]

/-- Restores the registers, with `x23` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .ldr .x r .x23 d

/-- Everything before the first call. -/
def absorbPre : Prog isa := .seq (.block save) (.seq held (.seq fill (.seq copy chain1)))

/-- Everything after the second call. -/
def absorbPost : Prog isa := .seq (.block rest) (.seq copy (.block restore))

def absorb (u : Impl.CmacAes.AArch64.Update) : Prog isa :=
  .seq absorbPre
    (.seq (.call u.name u.code)
      (.seq chain2 (.seq (.call u.name u.code) absorbPost)))

/-! ## `vg_cmac_aes_finish` -/

/-- The offset of the working space of the function `finish` calls. -/
def finWOff : Nat := 16

/-- The chaining value copied to `out`, `x19` and `x30` saved and the scratch
buffer kept in `x19`, and the arguments of
`vg_cmac_aes_finalize(key = x0, rounds = x1, state = x2, last = x3, last_len = x4, scratch = x5)`
but `last_len`, which is `count` in `x4` so far. -/
def finishPre : List Instr :=
  [.ldr .x .x9 .x0 272, .str .x .x9 .x3 0, .ldr .x .x9 .x0 280, .str .x .x9 .x3 8,
   .str .x .x19 .x4 0, .str .x .x30 .x4 8, mov .x19 .x4, .addImm .x .x5 .x4 finWOff, mov .x4 .x2, mov .x2 .x3,
   .addImm .x .x3 .x0 288]

/-- `last_len`: the number of bytes held back for `count` (in `x4`). -/
def lastLen : Prog isa :=
  .ite (.zero .x .x4) (.block [])
    (.block [.subImm .x .x4 .x4 1, .movz .x .x9 15 0, .logic .and .x .x4 .x4 .x9, .addImm .x .x4 .x4 1])

/-- Everything before the call. -/
def finPre : Prog isa := .seq (.block finishPre) lastLen

/-- The registers restored. -/
def finishPost : List Instr := [.ldr .x .x30 .x19 8, .ldr .x .x19 .x19 0]

def finish (c : Ctr32) (sfx : String) : Prog isa :=
  .seq finPre (.seq (.call ("vg_cmac_aes_finalize" ++ sfx) (Impl.CmacAes.AArch64.finalize c))
    (.block finishPost))

/-! ## The functions, as emitted

Each function is its code with its working space in a frame on the stack,
sized to what the functions it calls need, then its cleanup
(`Impl.Residue.AArch64.scrubAll`): the registers it writes that the calling
convention does not preserve are cleared and that stack is zeroed, so that it
returns without secret residue. The registers are those its own
instructions write, stated here, and those the functions it calls state
they write (`clear`). -/

namespace Fn

open VG.Impl.Residue.AArch64 (Clear scrubAll)

/-- The registers `vg_cmac_aes_init`'s own instructions write. -/
def initOwn : Clear := ⟨[.x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11, .x12, .x16, .x17], [], []⟩

/-- The working space of `vg_cmac_aes_init` over an implementation that needs
`scratch` bytes: the 512 bytes of the key expansion, or what
`vg_cmac_aes_subkeys` needs (`128 + scratch`), if more. -/
def initWork (scratch : Nat) : Nat := if scratch = 0 then 512 else 2176

/-- `vg_cmac_aes_init`. -/
def init (e : ExpandKey) (c : Ctr32) (sfx : String) : Prog isa :=
  scrubAll (32 + initWork c.scratch) 0 ((initOwn.union e.clear).union c.clear)
    (Impl.StackScratch.AArch64.withStackScratch (32 + initWork c.scratch) .x3 (Stream.AArch64.init e c sfx))

/-- The registers `vg_cmac_aes_absorb`'s own instructions write. -/
def absorbOwn : Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x16, .x17], [], []⟩

/-- `vg_cmac_aes_absorb`, with the working space `u` needs. -/
def absorb (u : Impl.CmacAes.AArch64.Update) : Prog isa :=
  scrubAll (64 + u.scratch) 0 (absorbOwn.union u.clear)
    (Impl.StackScratch.AArch64.withStackScratch (64 + u.scratch) .x5 (Stream.AArch64.absorb u))

/-- The registers `vg_cmac_aes_finish`'s own instructions write. -/
def finishOwn : Clear := ⟨[.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x16, .x17], [], []⟩

/-- The working space of `vg_cmac_aes_finish` over an implementation that
needs `scratch` bytes: what `vg_cmac_aes_finalize` needs. -/
def finishWork (scratch : Nat) : Nat := 128 + scratch

/-- `vg_cmac_aes_finish`. -/
def finish (c : Ctr32) (sfx : String) : Prog isa :=
  scrubAll (16 + finishWork c.scratch) 0 (finishOwn.union c.clear)
    (Impl.StackScratch.AArch64.withStackScratch (16 + finishWork c.scratch) .x4 (Stream.AArch64.finish c sfx))

end Fn

end VG.Impl.CmacAes.Stream.AArch64
