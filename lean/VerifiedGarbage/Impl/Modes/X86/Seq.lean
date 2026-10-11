import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Impl.Modes.Ops

/-!
# Block cipher modes on x86 (32-bit), for any block cipher with blocks of 8 or 16 bytes

`seq core mode`: a mode of operation over a block cipher's *core* (`Core`),
the code that encrypts a batch of `G` blocks of `bw` 32-bit words in a buffer
of the scratch buffer. The core is inlined. The functions take, cdecl (every
argument on the stack, `[esp + 4]` the first on entry), the key, the
initialization vector (or chaining value), the data, its length in steps
(blocks, or bytes for CFB8) and the scratch buffer:
`f(key, iv, data, n, scratch)`.

The scratch buffer's address is in `sb` (`edi`) throughout; its first
`core.slots` 4-byte slots are the core's, the next 10 the mode's: the
callee-saved registers (`savedSlot`), the data pointer and the steps left
(`dSlot`, `nSlot`), and the mode's chaining value or input block, `bw`
words (`chnSlot`). The core keeps only `sb` and `esp`, so everything else the
mode needs lives in its slots.

Every mode here processes one step at a time (`Mode`), in three *areas*:
the step's data (`dat`, at `esi`), the chaining value (`chn`) and the
core's first block (`buf`). A step is `pre` (copies and XORs among the
areas, words or bytes: `Op`), `core.crypt` (which enciphers `buf`), and
`post`; the data pointer and the steps left are loaded into `esi` and
`ebp` before `pre` and before `post`, since the core uses every register,
and stored back after `post`, which advances them.

* The callee-saved registers are saved in their slots, the IV is copied to
  the chaining value, `core.prepare` makes the key ready, and the data
  pointer and `n` go to their slots.
* Each step: `pre`, `crypt`, `post`, and on.
* If the mode returns its chaining value (`ivOut`), it is copied back to the
  IV, and the registers are restored.

Only the pointers and `n` are public: no address or branch depends on the
key, the IV or the data. Each step's stores through `esi` make the analysis
of constant time forget what the scratch buffer holds, so the data pointer
and the steps left are stored again, from registers, at the end of each step
(and after `prepare`).
-/

namespace VG.Impl.Modes.X86

open VG.X86
open VG.Impl.Modes

/-- The scratch buffer's base register. -/
def sb : Reg := .edi

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- Stack argument `i` (cdecl, on entry to the function). -/
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

def slotAt (k : Nat) : MemOp := at_ sb (4 * k)

/-- A block cipher's core for the modes: with the scratch buffer of `total`
slots at `sb`, `prepare` makes the key, given by the stack arguments, ready
in the core's slots `[0, slots)`, and `crypt` replaces the `G` blocks of
`bw` words of the buffer at slot `buf` with their encryptions. Both keep
`sb` and `esp`, and may use `stack` bytes below `esp`. A mode keeps its own
slots in `[slots, total)`. -/
structure Core where
  prepare : Prog isa
  crypt : Prog isa
  slots : Nat
  total : Nat
  buf : Nat
  G : Nat
  bw : Nat
  stack : Nat := 0

namespace Core

variable (c : Core)

def savedRegs : List Reg := [.ebx, .esi, .edi, .ebp]

def savedSlot (i : Nat) : Nat := c.slots + i
def dSlot : Nat := c.slots + 4
def nSlot : Nat := c.slots + 5
def chnSlot : Nat := c.slots + 6

/-- Base register and displacement of an area. -/
def loc : Loc → Reg × Nat
  | .dat => (.esi, 0)
  | .chn => (sb, 4 * c.chnSlot)
  | .buf => (sb, 4 * c.buf)

def opAt (l : Loc) (off : Nat) : MemOp := at_ (c.loc l).1 ((c.loc l).2 + off)

/-- An operation's code, through `eax` (and `ecx` for a byte XOR). -/
def opCode (o : Op) : List Instr :=
  if o.wide then
    ([.mov .eax (.mem (c.opAt o.src o.sOff))] : List Instr) ++
      (match o.xr with
       | none => []
       | some (l, off) => [.alu .xor .eax (.mem (c.opAt l off))]) ++
      [.store (c.opAt o.dst o.dOff) .eax]
  else
    ([.movzx8 .eax (c.opAt o.src o.sOff)] : List Instr) ++
      (match o.xr with
       | none => []
       | some (l, off) => [.movzx8 .ecx (c.opAt l off), .alu .xor .eax (.reg .ecx)]) ++
      [.store8 (c.opAt o.dst o.dOff) .al]

def opsCode (os : List Op) : List Instr := os.flatMap c.opCode

/-! ## The function -/

/-- The scratch buffer (argument 4) to `sb`, the callee-saved registers to
their slots first. -/
def entry : List Instr :=
  ([.mov .eax (.mem (argOp 4))] : List Instr) ++
    (List.range 4).map (fun i => .store (at_ .eax (4 * c.savedSlot i)) (savedRegs.getD i .ebx)) ++
    [.mov sb (.reg .eax)]

/-- The IV (argument 1, at `esi`, as the data area) to the chaining value. -/
def ivIn : List Instr := ([.mov .esi (.mem (argOp 1))] : List Instr) ++ c.opsCode (copyBlk c.bw .chn .dat)

/-- The data pointer and `n` (arguments 2 and 3) to their slots; ZF is set
if `n = 0`. -/
def args : List Instr :=
  [.mov .eax (.mem (argOp 2)), .store (slotAt c.dSlot) .eax, .mov .eax (.mem (argOp 3)),
   .store (slotAt c.nSlot) .eax, .alu .test .eax (.reg .eax)]

/-- The data pointer and the steps left to `esi` and `ebp`. -/
def load : List Instr := [.mov .esi (.mem (slotAt c.dSlot)), .mov .ebp (.mem (slotAt c.nSlot))]

/-- On by `step` bytes, one step fewer (ZF set when none is left), both
stored back. -/
def advance (step : Nat) : List Instr :=
  [.alu .add .esi (.imm (BitVec.ofNat 32 step)), .alu .sub .ebp (.imm 1), .store (slotAt c.dSlot) .esi,
   .store (slotAt c.nSlot) .ebp]

/-- One step. -/
def body (m : Mode) : Prog isa :=
  .seq (.block (c.load ++ c.opsCode m.pre)) (.seq c.crypt
    (.block (c.load ++ c.opsCode m.post ++ c.advance m.step)))

/-- The chaining value back to the IV (argument 1, at `esi`, as the data
area). -/
def ivBack : List Instr := ([.mov .esi (.mem (argOp 1))] : List Instr) ++ c.opsCode (copyBlk c.bw .dat .chn)

/-- The callee-saved registers restored (`sb` last). -/
def restore : List Instr :=
  [.mov .ebx (.mem (slotAt (c.savedSlot 0))), .mov .esi (.mem (slotAt (c.savedSlot 1))),
   .mov .ebp (.mem (slotAt (c.savedSlot 3))), .mov sb (.mem (slotAt (c.savedSlot 2)))]

/-- The whole function. -/
def seq (m : Mode) : Prog isa :=
  .seq (.block (c.entry ++ c.ivIn)) (.seq c.prepare (.seq (.block c.args)
    (.seq (.ite .e (.block []) (.loop (c.body m) .ne))
      (.block ((if m.ivOut then c.ivBack else []) ++ c.restore)))))

end Core

end VG.Impl.Modes.X86
