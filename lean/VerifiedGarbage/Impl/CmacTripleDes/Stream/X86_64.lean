module

public import VerifiedGarbage.Impl.CmacTripleDes.X86_64

/-!
# Streaming TDEA-CMAC: x86-64 implementation

`vg_cmac_triple_des_stream_init(state = rdi, key = rsi, key_len = rdx, scratch = rcx)`,
`vg_cmac_triple_des_absorb(state = rdi, count = rsi, data = rdx, len = rcx, scratch = r8)`
and `vg_cmac_triple_des_finish(state = rdi, count = rsi, out = rdx, scratch = rcx)`
(see `VG.Spec.Cmac.tdesStreamInitContract` and the others), built from the
code of `vg_cmac_triple_des_init`, `vg_cmac_triple_des_update` and
`vg_cmac_triple_des_finalize` (`Impl/CmacTripleDes/X86_64.lean`), inline:
each takes its arguments in the registers of its own signature and its
640-byte working space in `scratch`, and keeps our caller's callee-saved
registers.

The state (`VG.Spec.Cmac.tdesRepr`) is the key schedule (bytes 0–383), the
subkeys (384–399), the chaining value (400–407) and the bytes held back
(408–415), so bytes 0–399 are `finalize`'s `key`, as `init` writes them.
The scratch buffer: `[0, 640)` is the working space of the code inlined,
and `absorb` keeps our caller's callee-saved registers in `[640, 680)`.

* `stream_init` zeroes the chaining value, and runs `init` with the state
  as its `out`.
* `absorb` keeps the state (`rbx`), the data left (`r13`, `r14` bytes) and
  the scratch buffer (`r15`) across the two runs of `update`. With `h` bytes
  held back (`count` modulo 8, but 8 for a multiple of 8 and 0 for the empty
  message), it copies `f = min(len, 8 - h)` bytes after them. If data is
  left (the block held back is whole and not the last), it chains that
  block, then the whole blocks of what is left but its last 1 to 8 bytes,
  which it copies to the start of the bytes held back. With no data left,
  the two runs chain no blocks and the second copy copies nothing, so the
  code has no branch around them.
* `finish` copies the chaining value to `out`, and runs `finalize` with the
  state as its key, `out` as its state and the `h` bytes held back as the
  last bytes.

Only the pointers, the key length, `count` and `len` can affect timing: the
branches are on them, and so are the number of bytes copied and of blocks
chained.
-/

@[expose] public section

namespace VG.Impl.CmacTripleDes.Stream.X86_64

open VG.X86_64
open VG.Impl.CmacTripleDes.X86_64 (at_)

/-! ## `vg_cmac_triple_des_stream_init` -/

/-- The chaining value zeroed, and the arguments of
`init(key = rdi, key_len = rsi, out = rdx, scratch = rcx)`. -/
def initPre : List Instr :=
  [.mov32 .rax (.imm 0), .store (at_ .rdi 400) .rax, .mov .rax (.reg .rdi), .mov .rdi (.reg .rsi),
   .mov .rsi (.reg .rdx), .mov .rdx (.reg .rax)]

def streamInit : Prog isa := .seq (.block initPre) Impl.CmacTripleDes.X86_64.init

/-! ## Copying bytes -/

/-- `[r13 + r10]` and `[rdx + r10]`. -/
def srcByte : MemOp := { base := .r13, index := some .r10 }
def dstByte : MemOp := { base := .rdx, index := some .r10 }

/-- The loop's body: one byte from `[r13 + r10]` to `[rdx + r10]`. -/
def copyBody : List Instr :=
  [.movzx8 .rax srcByte, .store8 dstByte .rax, .alu .add .r10 (.imm 1), .alu .cmp .r10 (.reg .rcx)]

/-- The `rcx` bytes at `r13` (none if `rcx` is 0) copied to `rdx`. -/
def copy : Prog isa :=
  .seq (.block [.mov32 .r10 (.imm 0), .alu .test .rcx (.reg .rcx)])
    (.ite .e (.block []) (.loop (.block copyBody) .ne))

/-! ## `vg_cmac_triple_des_absorb` -/

/-- Our caller's callee-saved registers that `absorb` uses, and their
offsets in the scratch buffer. -/
def saved : List (Reg × Nat) := [(.rbx, 640), (.r12, 648), (.r13, 656), (.r14, 664), (.r15, 672)]

/-- Saves the registers and keeps the arguments in them; ZF is set if
`count` is 0. -/
def save : List Instr :=
  saved.map (fun (r, d) => .store (at_ .r8 d) r) ++
  [.mov .rbx (.reg .rdi), .mov .r13 (.reg .rdx), .mov .r14 (.reg .rcx), .mov .r15 (.reg .r8),
   .alu .test .rsi (.reg .rsi)]

/-- The number of bytes held back for `count` (`rsi`, ZF set if it is 0), in `rax`. -/
def held : Prog isa :=
  .ite .e (.block [.mov32 .rax (.imm 0)])
    (.block [.mov .rax (.reg .rsi), .alu .sub .rax (.imm 1), .alu .and .rax (.imm 7),
      .alu .add .rax (.imm 1)])

/-- `f = min(len, 8 - h)` in `rcx`, and the destination `state + 408 + h` in `rdx`. -/
def fill : Prog isa :=
  .seq (.block [.mov32 .rcx (.imm 8), .alu .sub .rcx (.reg .rax), .alu .cmp .r14 (.reg .rcx)])
    (.seq (.ite .b (.block [.mov .rcx (.reg .r14)]) (.block []))
      (.block [.mov .rdx (.reg .rbx), .alu .add .rdx (.imm 408), .alu .add .rdx (.reg .rax)]))

/-- The data advanced past the `f` bytes copied; one block to chain (`rcx`)
if data is left, else none; and the other arguments of
`update(schedule = rdi, state = rsi, data = rdx, n = rcx, scratch = r8)`
for the block held back. -/
def chain1 : Prog isa :=
  .seq (.block [.alu .add .r13 (.reg .rcx), .alu .sub .r14 (.reg .rcx), .mov32 .rcx (.imm 0)])
    (.seq (.ite .e (.block []) (.block [.mov32 .rcx (.imm 1)]))
      (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbx), .alu .add .rsi (.imm 400),
        .mov .rdx (.reg .rbx), .alu .add .rdx (.imm 408), .mov .r8 (.reg .r15)]))

/-- `8 nb` in `r12` for the `nb` whole blocks of the data left but its last
1 to 8 bytes (none if no data is left), and the arguments of `update` for
them. -/
def chain2 : Prog isa :=
  .seq (.block [.mov32 .r12 (.imm 0), .alu .test .r14 (.reg .r14)])
    (.seq (.ite .e (.block [])
        (.block [.mov .r12 (.reg .r14), .alu .sub .r12 (.imm 1), .mov .rax (.reg .r12),
          .alu .and .rax (.imm 7), .alu .sub .r12 (.reg .rax)]))
      (.block [.mov .rcx (.reg .r12), .shift .shr .rcx 3, .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbx),
        .alu .add .rsi (.imm 400), .mov .rdx (.reg .r13), .mov .r8 (.reg .r15)]))

/-- The data advanced past the blocks chained, and the arguments of the
copy of the rest to the start of the bytes held back. -/
def rest : List Instr :=
  [.alu .add .r13 (.reg .r12), .alu .sub .r14 (.reg .r12), .mov .rdx (.reg .rbx),
   .alu .add .rdx (.imm 408), .mov .rcx (.reg .r14)]

/-- Restores the registers, with `r15` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r15 d))

/-- Everything before the first run of `update`. -/
def absorbPre : Prog isa := .seq (.block save) (.seq held (.seq fill (.seq copy chain1)))

/-- Everything after the second. -/
def absorbPost : Prog isa := .seq (.block rest) (.seq copy (.block restore))

/-- Up to the first run of `update`, and that run. -/
def absorb₁ : Prog isa := .seq absorbPre Impl.CmacTripleDes.X86_64.update

/-- The rest. -/
def absorb₂ : Prog isa := .seq chain2 (.seq Impl.CmacTripleDes.X86_64.update absorbPost)

def absorb : Prog isa := .seq absorb₁ absorb₂

/-! ## `vg_cmac_triple_des_finish` -/

/-- The chaining value copied to `out`, and the arguments of
`finalize(key = rdi, state = rsi, last = rdx, last_len = rcx, scratch = r8)`
but `last_len`; ZF set if `count` is 0. -/
def finishPre : List Instr :=
  [.mov .rax (.mem (at_ .rdi 400)), .store (at_ .rdx 0) .rax, .mov .r8 (.reg .rcx), .mov .rcx (.reg .rsi),
   .mov .rsi (.reg .rdx), .mov .rdx (.reg .rdi), .alu .add .rdx (.imm 408), .alu .test .rcx (.reg .rcx)]

/-- `last_len`: the number of bytes held back for `count` (in `rcx`). -/
def lastLen : Prog isa :=
  .ite .e (.block [])
    (.block [.alu .sub .rcx (.imm 1), .alu .and .rcx (.imm 7), .alu .add .rcx (.imm 1)])

/-- Everything before `finalize`. -/
def finPre : Prog isa := .seq (.block finishPre) lastLen

def finish : Prog isa := .seq finPre Impl.CmacTripleDes.X86_64.finalize

end VG.Impl.CmacTripleDes.Stream.X86_64
