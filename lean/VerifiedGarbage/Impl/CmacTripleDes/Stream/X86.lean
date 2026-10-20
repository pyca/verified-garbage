module

public import VerifiedGarbage.Impl.CmacTripleDes.X86

/-!
# Streaming TDEA-CMAC: x86 (32-bit) implementation

`vg_cmac_triple_des_stream_init(state, key, key_len, scratch)`,
`vg_cmac_triple_des_absorb(state, count, data, len, scratch)` and
`vg_cmac_triple_des_finish(state, count, out, scratch)` (see
`VG.Spec.Cmac.tdesStreamInitContract` and the others), every argument on
the stack (cdecl; `count` takes two slots, its low word first), built, as
on x86-64 (`Impl/CmacTripleDes/Stream/X86_64.lean`), from the code of
`vg_cmac_triple_des_init`, `vg_cmac_triple_des_update` and
`vg_cmac_triple_des_finalize` (`Impl/CmacTripleDes/X86.lean`), inline. That
code reads its arguments from the stack, `[esp + 4]` on: each run is in a
frame that pushes them (from registers, the last first) and a word in the
return address's place, popped (into `eax`) after it. The code keeps our
caller's callee-saved registers, and its working space is the first 640
bytes of ours.

The state (`VG.Spec.Cmac.tdesRepr`) is the key schedule (bytes 0–383), the
subkeys (384–399), the chaining value (400–407) and the bytes held back
(408–415).

* `stream_init` keeps `ebx` in the chaining value's place while it runs
  `init` with the state as its `out`, then zeroes the chaining value.
* `absorb` and `finish` keep our caller's `ebx`, `esi`, `edi` and `ebp` in
  `[640, 656)` of their working space (688 bytes), and reload everything
  else from their own stack arguments after each run, as AES-CMAC's do
  (`Impl/CmacAes/Stream/X86.lean`): `absorb` keeps the number of bytes of
  data consumed in `ebp`. With `h` bytes held back (`count` modulo 8, but 8
  for a multiple of 8 and 0 for the empty message), `absorb` copies
  `f = min(len, 8 - h)` bytes after them; if data is left, it chains that
  block, then the whole blocks of what is left but its last 1 to 8 bytes,
  which it copies to the start of the bytes held back. With no data left,
  the two runs chain no blocks and the last copy copies nothing.
* `finish` copies the chaining value to `out`, and runs `finalize` with the
  state as its key, `out` as its state and the `h` bytes held back as the
  last bytes.

Only the pointers, the key length, `count` and `len` can affect timing: the
branches are on them, and so are the number of bytes copied and of blocks
chained.
-/

@[expose] public section

namespace VG.Impl.CmacTripleDes.Stream.X86

open VG.X86
open VG.Impl.CmacTripleDes.X86 (at_)

/-- The stack argument `i`, `[esp + 4 + 4 i]`. -/
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

/-- Our caller's callee-saved registers, and where they are saved in the
scratch buffer. -/
def saved : List (Reg × Nat) := [(.ebx, 640), (.esi, 644), (.edi, 648), (.ebp, 652)]

/-- Save them, with the scratch buffer in `eax`. -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .eax d) r

/-- Restore them, with the scratch buffer (the stack argument `i`) loaded into `eax`. -/
def restore (i : Nat) : List Instr := .mov .eax (.mem (argOp i)) :: saved.map fun (r, d) => .mov r (.mem (at_ .eax d))

/-- The loop's body: one byte from `[esi]` to `[edi]`, advancing both, with
`ecx` bytes left. -/
def copyBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .store8 (at_ .edi 0) .al, .alu .add .esi (.imm 1), .alu .add .edi (.imm 1),
   .alu .sub .ecx (.imm 1)]

/-- The `ecx` bytes at `esi` copied to `edi` (none if `ecx` is 0). -/
def copy : Prog isa :=
  .seq (.block [.alu .test .ecx (.reg .ecx)]) (.ite .e (.block []) (.loop (.block copyBody) .ne))

/-- `count`'s low word (the stack argument 1) in `r`; ZF set if `count` is 0. -/
def count0 (r : Reg) : List Instr := [.mov r (.mem (argOp 1)), .mov .ecx (.mem (argOp 2)), .alu .or .ecx (.reg r)]

/-- The number of bytes held back for `count`, in `r`, from `count0 r`. -/
def held (r : Reg) : Prog isa :=
  .ite .e (.block []) (.block [.alu .sub r (.imm 1), .alu .and r (.imm 7), .alu .add r (.imm 1)])

/-- The number of bytes held back for `count`, in `r` (`ecx` clobbered). -/
def countHeld (r : Reg) : Prog isa := .seq (.block (count0 r)) (held r)

/-! ## `vg_cmac_triple_des_stream_init` -/

/-- `ebx` kept in the chaining value's place, and the arguments of
`init(key = ebx, key_len = ecx, out = eax, scratch = edx)`. -/
def initPre : List Instr :=
  [.mov .eax (.mem (argOp 0)), .store (at_ .eax 400) .ebx, .mov .ebx (.mem (argOp 1)), .mov .ecx (.mem (argOp 2)),
   .mov .edx (.mem (argOp 3))]

/-- A run of `init` in the frame of its arguments (and `esi` in the return
address's place). -/
def initFrame : Prog isa := .frame (.push [.edx, .eax, .ecx, .ebx, .esi]) Impl.CmacTripleDes.X86.init (.pop .eax 5)

/-- `ebx` restored, and the chaining value zeroed. -/
def initPost : List Instr :=
  [.mov .eax (.mem (argOp 0)), .mov .ebx (.mem (at_ .eax 400)), .mov .ecx (.imm 0), .store (at_ .eax 400) .ecx,
   .store (at_ .eax 404) .ecx]

def streamInit : Prog isa := .seq (.block initPre) (.seq initFrame (.block initPost))

/-! ## `vg_cmac_triple_des_absorb` -/

/-- Saves the registers. -/
def absSave : List Instr := [.mov .eax (.mem (argOp 5))] ++ save

/-- `f = min(len, 8 - h)` (`h` in `eax`) in `ecx` and `ebp`, the data in
`esi` and the destination `state + 408 + h` in `edi`. -/
def fill : Prog isa :=
  .seq (.block [.mov .ecx (.imm 8), .alu .sub .ecx (.reg .eax), .mov .edx (.mem (argOp 4)),
      .alu .cmp .edx (.reg .ecx)])
    (.seq (.ite .b (.block [.mov .ecx (.reg .edx)]) (.block []))
      (.block [.mov .ebp (.reg .ecx), .mov .esi (.mem (argOp 3)), .mov .edi (.mem (argOp 0)),
        .alu .add .edi (.imm 408), .alu .add .edi (.reg .eax)]))

/-- The arguments of `update(schedule = eax, state = edx, data = ebx, n = esi,
scratch = edi)` for the block held back: `n = 1` if data is left, else 0. -/
def chain1 : Prog isa :=
  .seq (.block [.mov .esi (.imm 0), .mov .edx (.mem (argOp 4)), .alu .sub .edx (.reg .ebp)])
    (.seq (.ite .e (.block []) (.block [.mov .esi (.imm 1)]))
      (.block [.mov .eax (.mem (argOp 0)), .mov .edx (.reg .eax), .alu .add .edx (.imm 400),
        .mov .ebx (.reg .eax), .alu .add .ebx (.imm 408), .mov .edi (.mem (argOp 5))]))

/-- A run of `update` in the frame of its arguments (and `ecx` in the return
address's place). -/
def updFrame : Prog isa :=
  .frame (.push [.edi, .esi, .ebx, .edx, .eax, .ecx]) Impl.CmacTripleDes.X86.update (.pop .eax 6)

/-- `8 nb` in `ecx` for the `nb` whole blocks of the data left but its last
1 to 8 bytes (none if no data is left), `ebp` advanced past them, and the
arguments of `update` for them: the data left, at `data + f` (with no data
left, the bytes held back, which it reads none of, as `data + f` may be the
end of the address space). -/
def chain2 : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0), .mov .ebx (.mem (argOp 0)), .alu .add .ebx (.imm 408),
      .mov .edx (.mem (argOp 4)), .alu .sub .edx (.reg .ebp)])
    (.seq (.ite .e (.block [])
        (.block [.mov .ecx (.reg .edx), .alu .sub .ecx (.imm 1), .mov .eax (.reg .ecx), .alu .and .eax (.imm 7),
          .alu .sub .ecx (.reg .eax), .mov .ebx (.mem (argOp 3)), .alu .add .ebx (.reg .ebp)]))
      (.block [.mov .esi (.reg .ecx), .shift .shr .esi 3, .alu .add .ebp (.reg .ecx), .mov .eax (.mem (argOp 0)),
        .mov .edx (.reg .eax), .alu .add .edx (.imm 400), .mov .edi (.mem (argOp 5))]))

/-- The arguments of the copy of the rest to the start of the bytes held back. -/
def rest : List Instr :=
  [.mov .esi (.mem (argOp 3)), .alu .add .esi (.reg .ebp), .mov .edi (.mem (argOp 0)), .alu .add .edi (.imm 408),
   .mov .ecx (.mem (argOp 4)), .alu .sub .ecx (.reg .ebp)]

/-- Everything before the first run of `update`. -/
def absorbPre : Prog isa := .seq (.block absSave) (.seq (countHeld .eax) (.seq fill (.seq copy chain1)))

/-- Everything after the second. -/
def absorbPost : Prog isa := .seq (.block rest) (.seq copy (.block (restore 5)))

def absorb : Prog isa :=
  .seq absorbPre (.seq updFrame (.seq chain2 (.seq updFrame absorbPost)))

/-! ## `vg_cmac_triple_des_finish` -/

/-- Saves the registers, and sets up the copy of the chaining value to `out`. -/
def finSave : List Instr :=
  [.mov .eax (.mem (argOp 4))] ++ save ++ [.mov .esi (.mem (argOp 0)), .alu .add .esi (.imm 400),
    .mov .edi (.mem (argOp 3)), .mov .ecx (.imm 8)]

/-- The arguments of `finalize(key = eax, state = edx, last = ebx,
last_len = esi, scratch = edi)` but `last_len`: the state as the key, `out`
as the state, and the bytes held back. -/
def finArgs : List Instr :=
  [.mov .eax (.mem (argOp 0)), .mov .edx (.mem (argOp 3)), .mov .ebx (.reg .eax), .alu .add .ebx (.imm 408),
   .mov .edi (.mem (argOp 4))]

/-- Everything before `finalize`. -/
def finPre : Prog isa :=
  .seq (.block finSave) (.seq copy (.seq (countHeld .esi) (.block finArgs)))

/-- A run of `finalize` in the frame of its arguments (and `ecx` in the
return address's place). -/
def finFrame : Prog isa :=
  .frame (.push [.edi, .esi, .ebx, .edx, .eax, .ecx]) Impl.CmacTripleDes.X86.finalize (.pop .eax 6)

def finish : Prog isa := .seq finPre (.seq finFrame (.block (restore 4)))

end VG.Impl.CmacTripleDes.Stream.X86
