module

public import VerifiedGarbage.Impl.Modes.Ops
public import VerifiedGarbage.Impl.Modes.RISCV64.Counter
public import VerifiedGarbage.Impl.Words.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Frame
public import VerifiedGarbage.Impl.Words.RISCV64.Loops
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Block cipher modes on RISC-V, for any block cipher with blocks of 8 or 16 bytes

`seq core mode`: a mode of operation over a block cipher's *core* (`Core`),
the code that encrypts a batch of `G` blocks of `bw` 32-bit words in a buffer
of the mode's frame. The core is inlined. The function is
`f(key = a0, iv = a1, data = a2, n = a3)`: the key is a single argument
(the schedule's address), which the mode leaves in `a0` for the core.

The mode runs in a frame of `total` 8-byte slots on the stack
(`bigFrame`), 16-byte aligned, whose base is in `sb` (`s4`) throughout:
its first four slots hold the caller's `s1`–`s4` (`savedSlot`), the next
two the mode's chaining value or input block (`chnSlot`, `bw` words), and
the rest are the core's (from `coreSlot`; its buffer at slot `buf`). The
core may access the frame a word or a doubleword at a time; the IV and the
data may be anywhere, so the mode accesses them a byte at a time. The
analysis of constant time takes memory for secret, so the mode keeps what
it addresses or counts in registers that the core keeps (`s1`–`s4`): the
IV's address in `s1`, the data pointer in `s2`, the steps left in `s3`.
The frame is zeroed before it is freed (`wipe`): it may hold the core's copy
of the key.

Every mode here processes one step at a time (`Mode`), in three *areas*:
the step's data (`dat`, at `s2`), the chaining value (`chn`) and the
core's first block (`buf`). A step is `pre` (copies and XORs among the
areas, words or bytes, and the counters' increments: `Op`, through `t0`,
`t1` and `t2`), `core.crypt` (which enciphers `buf`), `post`, and the data
pointer and the steps left advanced.

* The caller's `s1`–`s4` are saved in their slots, the IV is copied to the
  chaining value, and `core.prepare` makes the key ready.
* Each step: `pre`, `crypt`, `post`, and on.
* If the mode returns its chaining value (`ivOut`), it is copied back to the
  IV; the caller's registers are restored, and the frame zeroed.

Only the pointers and `n` are public: no address or branch depends on the
key, the IV or the data.
-/

@[expose] public section

namespace VG.Impl.Modes.RISCV64

open VG.RISCV64
open VG.Impl.Modes
open VG.Impl.Words.RISCV64 (loadLE32 storeLE32 bigFrame fillLoop)

/-- `mv d, n` (`addi d, n, 0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- The frame's base register. -/
def sb : Reg := .s4

/-- The first of the core's slots: the mode's take six. -/
def coreSlot : Nat := 6

/-- A block cipher's core for the modes: with the frame of `total` 8-byte
slots at `sb` and the key's argument in `a0`, `prepare` makes the key ready
in the core's slots `[coreSlot, total)`, and `crypt` replaces the `G`
blocks of `bw` words of the buffer at slot `buf` with their encryptions.
Both keep the stack pointer, `a0`, `ra` and the registers the caller
expects preserved (among them `s1`–`s4`, the mode's). -/
structure Core where
  prepare : Prog isa
  crypt : Prog isa
  total : Nat
  buf : Nat
  G : Nat
  bw : Nat

namespace Core

variable (c : Core)

/-- The registers the mode saves for its caller, in their slots' order. -/
def savedRegs : List Reg := [.s1, .s2, .s3, .s4]

def savedSlot (i : Nat) : Nat := i
def chnSlot : Nat := 4

/-- The frame's bytes. -/
def frameBytes : Nat := 8 * c.total

/-- Base register and displacement of an area. -/
def loc : Loc → Reg × Nat
  | .dat => (.s2, 0)
  | .chn => (sb, 8 * chnSlot)
  | .buf => (sb, 8 * c.buf)

/-- An operation's code, through `t0`, `t1` and `t2`: a word is read and
written a byte at a time (`loadLE32`, `storeLE32`), its sources before its
destination. -/
def opCode (o : Op) : List Instr :=
  if o.inc then incAt (c.loc o.dst).1 ((c.loc o.dst).2 + o.dOff)
  else if o.inc32 then inc32At (c.loc o.dst).1 ((c.loc o.dst).2 + o.dOff)
  else if o.wide then
    loadLE32 .t0 .t2 (c.loc o.src).1 ((c.loc o.src).2 + o.sOff) ++
      (match o.xr with
       | none => []
       | some (l, off) => loadLE32 .t1 .t2 (c.loc l).1 ((c.loc l).2 + off) ++ [.logic .xor .t0 .t0 .t1]) ++
      storeLE32 .t0 .t2 (c.loc o.dst).1 ((c.loc o.dst).2 + o.dOff)
  else
    ([.load .b .t0 (c.loc o.src).1 ((c.loc o.src).2 + o.sOff)] : List Instr) ++
      (match o.xr with
       | none => []
       | some (l, off) => [.load .b .t1 (c.loc l).1 ((c.loc l).2 + off), .logic .xor .t0 .t0 .t1]) ++
      [.store .b .t0 (c.loc o.dst).1 ((c.loc o.dst).2 + o.dOff)]

def opsCode (os : List Op) : List Instr := os.flatMap c.opCode

/-! ## The function -/

/-- The caller's `s1`–`s4` to their slots (through `t0`, the frame's base);
the frame's base to `sb`, the IV's address to `s1` (and to `s2`, as the
data area), `n` to `s3`. -/
def entry : List Instr :=
  (.addSp .t0 0 :: (List.range 4).map (fun i => .store .d (savedRegs.getD i .s1) .t0 (8 * savedSlot i))) ++
    [mov sb .t0, mov .s1 .a1, mov .s2 .a1, mov .s3 .a3]

/-- The IV (at `s2`, as the data area) to the chaining value, and the
data's address (in `a2`) to `s2`. -/
def ivIn : List Instr := c.opsCode (copyBlk c.bw .chn .dat) ++ [mov .s2 .a2]

/-- On by `step` bytes, one step fewer. -/
def advance (step : Nat) : List Instr := [.addi .s2 .s2 step, .addi .s3 .s3 (-1)]

/-- One step. -/
def body (m : Mode) : Prog isa :=
  .seq (.block (c.opsCode m.pre)) (.seq c.crypt (.block (c.opsCode m.post ++ advance m.step)))

/-- The chaining value back to the IV (at `s1`, moved to `s2` as the data
area). -/
def ivBack : List Instr := mov .s2 .s1 :: c.opsCode (copyBlk c.bw .dat .chn)

/-- The caller's `s1`–`s4` restored, through `t3`. -/
def restore : List Instr :=
  mov .t3 sb :: (List.range 4).map (fun i => .load .d (savedRegs.getD i .s1) .t3 (8 * savedSlot i))

/-- Zero the frame (at `t3`), a doubleword at a time. -/
def wipe : Prog isa :=
  .seq (.block [.li .t0 0, mov .t1 .t3, .li .t2 c.total]) (fillLoop .t0 .t1 .t2)

/-- The whole function. -/
def seq (m : Mode) : Prog isa :=
  bigFrame c.frameBytes (.seq (.block (entry ++ c.ivIn)) (.seq c.prepare
    (.seq (.ite (.zero .s3) (.block []) (.loop (c.body m) (.nonzero .s3)))
      (.seq (.block ((if m.ivOut then c.ivBack else []) ++ restore)) c.wipe))))

end Core

end VG.Impl.Modes.RISCV64
