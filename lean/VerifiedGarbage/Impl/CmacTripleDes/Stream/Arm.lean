module

public import VerifiedGarbage.Impl.CmacTripleDes.Arm

/-!
# Streaming TDEA-CMAC: 32-bit ARM implementation

`vg_cmac_triple_des_stream_init(state = r0, key = r1, key_len = r2, scratch = r3)`,
`vg_cmac_triple_des_absorb(state = r0, count = r2:r3, data = [sp], len = [sp, #4], scratch = [sp, #8])`
and `vg_cmac_triple_des_finish(state = r0, count = r2:r3, out = [sp], scratch = [sp, #4])`
(see `VG.Spec.Cmac.tdesStreamInitContract` and the others), built, as on
x86-64 (`Impl/CmacTripleDes/Stream/X86_64.lean`), from the code of
`vg_cmac_triple_des_init`, `vg_cmac_triple_des_update` and
`vg_cmac_triple_des_finalize` (`Impl/CmacTripleDes/Arm.lean`), inline: each
takes its arguments in `r0`–`r3` and its 640-byte working space in `r3`
(`init`) or as its stack argument (`update`, `finalize`), keeps our caller's
callee-saved registers and leaves `lr`, the return address, alone. A frame
pushes the working space's address for `update` and `finalize`
(`push {rA}`), and its pop loads `rA` back, so `absorb` and `finish` use 4
bytes of stack.

The state (`VG.Spec.Cmac.tdesRepr`) is the key schedule (bytes 0–383), the
subkeys (384–399), the chaining value (400–407) and the bytes held back
(408–415). The scratch buffer: `[0, 640)` is the working space of the code
inlined, and `absorb` keeps our caller's callee-saved registers in
`[640, 660)`.

* `stream_init` zeroes the chaining value, and runs `init` with the state
  as its `out`.
* `absorb` keeps the state (`r4`), the data left (`r6`, `r7` bytes), the
  bytes of whole blocks chained by the second run of `update` (`r8`) and the
  scratch buffer (`r10`) across the runs, as AES-CMAC's does
  (`Impl/CmacAes/Stream/Arm.lean`), with 8-byte blocks: with `h` bytes held
  back (`((count_lo - 1) & 7) + 1` if `count_lo | count_hi` is not 0), it
  copies `f = min(len, 8 - h)` bytes after them; if data is left, it chains
  that block, then the whole blocks of what is left but its last 1 to 8
  bytes, which it copies to the start of the bytes held back. With no data
  left, the two runs chain no blocks (the second from the state, as the
  data may then end at the end of the address space) and the second copy
  copies nothing.
* `finish` copies the chaining value to `out`, and runs `finalize` with the
  state as its key, `out` as its state and the `h` bytes held back as the
  last bytes.

The model has no register-offset addressing: bytes are copied through
advancing pointers, counting down with `subs`, and `min(len, 8 - h)` is
computed with shifts tested by `cmp`. Only the pointers, the key length,
`count` and `len` can affect timing: the branches are on them, and so are
the number of bytes copied and of blocks chained.
-/

@[expose] public section

namespace VG.Impl.CmacTripleDes.Stream.Arm

open VG.Arm
open VG.Impl.CmacTripleDes.Arm (mov)

/-! ## `vg_cmac_triple_des_stream_init` -/

/-- The chaining value zeroed, and the arguments of
`init(key = r0, key_len = r1, out = r2, scratch = r3)`. -/
def initPre : List Instr :=
  [.mov .r12 (.imm 0), .str .r12 .r0 400, .str .r12 .r0 404, mov .r12 .r0, mov .r0 .r1, mov .r1 .r2,
   mov .r2 .r12]

def streamInit : Prog isa := .seq (.block initPre) Impl.CmacTripleDes.Arm.init

/-! ## Copying bytes -/

/-- The loop's body: one byte from `[r6]` to `[r2]`, advancing both, with
`r1` bytes left. -/
def copyBody : List Instr :=
  [.ldrb .r12 .r6 0, .strb .r12 .r2 0, .dp .add .r6 .r6 (.imm 1), .dp .add .r2 .r2 (.imm 1),
   .subs .r1 .r1 (.imm 1)]

/-- The `r1` bytes at `r6` (none if `r1` is 0) copied to `r2`, advancing
both, and taken off the data left (`r7`). -/
def copy : Prog isa :=
  .seq (.block [.dp .sub .r7 .r7 (.reg .r1), .cmp .r1 (.imm 0)])
    (.ite .eq (.block []) (.loop (.block copyBody) .ne))

/-! ## `vg_cmac_triple_des_absorb` -/

/-- The registers saved in the scratch buffer, and where (`r10`, the base of
the restore, last). -/
def saved : List (Reg × Nat) := [(.r4, 640), (.r6, 644), (.r7, 648), (.r8, 652), (.r10, 656)]

/-- Saves them, with the scratch buffer (the third stack argument) in `r12`,
and keeps the arguments in registers. -/
def save : List Instr :=
  .ldrSp .r12 8 :: saved.map (fun (r, d) => .str r .r12 d) ++
  [mov .r4 .r0, .ldrSp .r6 0, .ldrSp .r7 4, mov .r10 .r12]

/-- The number of bytes held back for `count` (`r2:r3`), in `r0`. -/
def held : Prog isa :=
  .seq (.block [.dp .sub .r0 .r2 (.imm 1), .dp .and .r0 .r0 (.imm 7), .dp .add .r0 .r0 (.imm 1),
      .dp .orr .r12 .r2 (.reg .r3), .cmp .r12 (.imm 0)])
    (.ite .eq (.block [.mov .r0 (.imm 0)]) (.block []))

/-- `f = min(len, 8 - h)` in `r1`: `8 - h`, or `len` if `len < 8` and
`len + h < 8`; and the destination `state + 408 + h` in `r2`. -/
def fill : Prog isa :=
  .seq (.block [.mov .r1 (.imm 8), .dp .sub .r1 .r1 (.reg .r0), .mov .r12 (.shifted .r7 .lsr 3),
      .cmp .r12 (.imm 0)])
    (.seq (.ite .eq
        (.seq (.block [.dp .add .r12 .r7 (.reg .r0), .mov .r12 (.shifted .r12 .lsr 3), .cmp .r12 (.imm 0)])
          (.ite .eq (.block [mov .r1 .r7]) (.block [])))
        (.block []))
      (.block [.dp .add .r2 .r4 (.reg .r0), .dp .add .r2 .r2 (.imm 408)]))

/-- One block to chain (`r3`) if data is left, else none; and the other
arguments of `update(schedule = r0, state = r1, data = r2, n = r3,
scratch = [sp])` for the block held back. -/
def chain1 : Prog isa :=
  .seq (.block [.mov .r3 (.imm 0), .cmp .r7 (.imm 0)])
    (.seq (.ite .eq (.block []) (.block [.mov .r3 (.imm 1)]))
      (.block [mov .r0 .r4, .dp .add .r1 .r4 (.imm 400), .dp .add .r2 .r4 (.imm 408)]))

/-- A run of `update`, with the scratch buffer in `r10` pushed as its stack
argument, and `r10` popped. -/
def updFrame : Prog isa := .frame (.push [.r10]) Impl.CmacTripleDes.Arm.update (.pop .r10 4)

/-- `nb` in `r3` and `8 nb` in `r8` for the `nb` whole blocks of the data
left but its last 1 to 8 bytes (none if no data is left, then at the
state), and the arguments of `update` for them. -/
def chain2 : Prog isa :=
  .seq (.block [.cmp .r7 (.imm 0)])
    (.seq (.ite .eq (.block [.mov .r3 (.imm 0), .mov .r8 (.imm 0), mov .r2 .r4])
        (.block [.dp .sub .r3 .r7 (.imm 1), .mov .r3 (.shifted .r3 .lsr 3), .mov .r8 (.shifted .r3 .lsl 3),
          mov .r2 .r6]))
      (.block [mov .r0 .r4, .dp .add .r1 .r4 (.imm 400)]))

/-- The data advanced past the blocks chained, and the arguments of the
copy of the rest to the start of the bytes held back. -/
def rest : List Instr :=
  [.dp .add .r6 .r6 (.reg .r8), .dp .sub .r7 .r7 (.reg .r8), mov .r1 .r7, .dp .add .r2 .r4 (.imm 408)]

/-- Restores the registers, with `r10` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .ldr r .r10 d

/-- Everything before the first run of `update`. -/
def absorbPre : Prog isa := .seq (.block save) (.seq held (.seq fill (.seq copy chain1)))

/-- Everything after the second. -/
def absorbPost : Prog isa := .seq (.block rest) (.seq copy (.block restore))

def absorb : Prog isa :=
  .seq absorbPre (.seq updFrame (.seq chain2 (.seq updFrame absorbPost)))

/-! ## `vg_cmac_triple_des_finish` -/

/-- The chaining value copied to `out` (in `r1`), the arguments of
`finalize(key = r0, state = r1, last = r2, last_len = r3, scratch = [sp])`
but `last_len`, which is the number of bytes held back for `count`
(`r2:r3`) but for the empty message so far; Z is set if `count` is 0. -/
def finishPre : List Instr :=
  [.ldrSp .r1 0, .ldr .r12 .r0 400, .str .r12 .r1 0, .ldr .r12 .r0 404, .str .r12 .r1 4,
   .dp .orr .r12 .r2 (.reg .r3), .dp .sub .r3 .r2 (.imm 1), .dp .and .r3 .r3 (.imm 7),
   .dp .add .r3 .r3 (.imm 1), .dp .add .r2 .r0 (.imm 408), .cmp .r12 (.imm 0)]

/-- `last_len`: none for the empty message. -/
def lastLen : Prog isa := .ite .eq (.block [.mov .r3 (.imm 0)]) (.block [])

/-- The scratch buffer (the second stack argument) in `r12`. -/
def finArgs : List Instr := [.ldrSp .r12 4]

/-- Everything before `finalize`. -/
def finPre : Prog isa := .seq (.block finishPre) (.seq lastLen (.block finArgs))

/-- A run of `finalize`, with the scratch buffer in `r12` pushed as its
stack argument, and `r12` popped. -/
def finFrame : Prog isa := .frame (.push [.r12]) Impl.CmacTripleDes.Arm.finalize (.pop .r12 4)

def finish : Prog isa := .seq finPre finFrame

end VG.Impl.CmacTripleDes.Stream.Arm
