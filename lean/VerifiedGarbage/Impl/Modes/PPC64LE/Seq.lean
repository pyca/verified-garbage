module

public import VerifiedGarbage.Impl.Modes.Ops
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Block cipher modes on PPC64LE, for any block cipher with blocks of 8 or 16 bytes

`seq core mode`: a mode of operation over a block cipher's *core* (`Core`),
the code that encrypts a batch of `G` blocks of `bw` 32-bit words in a buffer
of the scratch buffer. The core is inlined (it may call the cipher's own
function). The function is
`f(key = r3, iv = r4, data = r5, n = r6, scratch = r7)`: the key is a single
argument (the schedule's address), which the mode leaves in `r3` for the core.

The scratch buffer's address is in `sb` (`r5`) throughout; its first
`core.slots` 8-byte slots are the core's, the next 6 the mode's: the
caller's `r29`–`r31` and the return address (`savedSlot`), and the mode's
chaining value or input block, `bw` words (`chnSlot`). The analysis of
constant time takes memory for secret, so the mode keeps what it addresses
or counts in registers that the core keeps (`r3`, `r5`, `r29`–`r31`): the
IV's address in `r29`, the steps left in `r30`, and the data pointer in
`r31`.

Every mode here processes one step at a time (`Mode`), in three *areas*:
the step's data (`dat`, at `r31`), the chaining value (`chn`) and the
core's first block (`buf`). A step is `pre` (copies and XORs among the
areas, words or bytes: `Op`, through `r8` and `r9`), `core.crypt` (which
enciphers `buf`), `post`, and the data pointer and the steps left
advanced.

* The caller's registers and the return address are saved in their slots,
  the IV is copied to the chaining value, and `core.prepare` makes the key
  ready.
* Each step: `pre`, `crypt`, `post`, and on.
* If the mode returns its chaining value (`ivOut`), it is copied back to the
  IV, and the registers and the return address are restored.

Only the pointers and `n` are public: no address or branch depends on the
key, the IV or the data.
-/

@[expose] public section

namespace VG.Impl.Modes.PPC64LE

open VG.PPC64LE
open VG.Impl.Modes

/-- The scratch buffer's base register. -/
def sb : Reg := .r5

/-- `mr d, n` (`or d, n, n`). -/
def mov (d n : Reg) : Instr := .logic .or d n n

/-- A block cipher's core for the modes: with the scratch buffer of `total`
8-byte slots at `sb` and the key's argument in `r3`, `prepare` makes the key
ready in the core's slots `[0, slots)`, and `crypt` replaces the `G` blocks
of `bw` words of the buffer at slot `buf` with their encryptions. Both keep
`r3`, `sb` and `r29`–`r31`. A mode keeps its own slots in `[slots, total)`. -/
structure Core where
  prepare : Prog isa
  crypt : Prog isa
  slots : Nat
  total : Nat
  buf : Nat
  G : Nat
  bw : Nat

namespace Core

variable (c : Core)

/-- The registers the mode saves for its caller, in their slots' order. -/
def savedRegs : List Reg := [.r29, .r30, .r31]

def savedSlot (i : Nat) : Nat := c.slots + i
/-- The return address's slot. -/
def lrSlot : Nat := c.slots + 3
def chnSlot : Nat := c.slots + 4

/-- Base register and displacement of an area. -/
def loc : Loc → Reg × Nat
  | .dat => (.r31, 0)
  | .chn => (sb, 8 * c.chnSlot)
  | .buf => (sb, 8 * c.buf)

/-- An operation's code, through `r8` (and `r9` for an XOR). The modes here
neither increment counters nor use a step's words otherwise. -/
def opCode (o : Op) : List Instr :=
  if o.inc || o.inc32 then [] else
  if o.wide then
    ([.load .w .r8 (c.loc o.src).1 ((c.loc o.src).2 + o.sOff)] : List Instr) ++
      (match o.xr with
       | none => []
       | some (l, off) => [.load .w .r9 (c.loc l).1 ((c.loc l).2 + off), .logic .xor .r8 .r8 .r9]) ++
      [.store .w .r8 (c.loc o.dst).1 ((c.loc o.dst).2 + o.dOff)]
  else
    ([.lbz .r8 (c.loc o.src).1 ((c.loc o.src).2 + o.sOff)] : List Instr) ++
      (match o.xr with
       | none => []
       | some (l, off) => [.lbz .r9 (c.loc l).1 ((c.loc l).2 + off), .logic .xor .r8 .r8 .r9]) ++
      [.stb .r8 (c.loc o.dst).1 ((c.loc o.dst).2 + o.dOff)]

def opsCode (os : List Op) : List Instr := os.flatMap c.opCode

/-! ## The function -/

/-- The return address and the caller's `r29`–`r31` to their slots (of the
scratch buffer, at `r7`); the IV's address to `r29` (and to `r31`, as the
data area), `n` to `r30`, the data's address to `r6`, and the scratch
buffer's to `sb`. -/
def entry : List Instr :=
  ([.mflr .r0, .store .d .r0 .r7 (8 * c.lrSlot)] : List Instr) ++
    (List.range 3).map (fun i => .store .d (savedRegs.getD i .r29) .r7 (8 * c.savedSlot i)) ++
    [mov .r29 .r4, mov .r30 .r6, mov .r31 .r4, mov .r6 .r5, mov sb .r7]

/-- The IV (at `r31`, as the data area) to the chaining value, and the
data's address (in `r6`) to `r31`. -/
def ivIn : List Instr := c.opsCode (copyBlk c.bw .chn .dat) ++ [mov .r31 .r6]

/-- On by `step` bytes, one step fewer. -/
def advance (step : Nat) : List Instr := [.addi .r31 .r31 step, .subi .r30 .r30 1]

/-- One step. -/
def body (m : Mode) : Prog isa :=
  .seq (.block (c.opsCode m.pre)) (.seq c.crypt (.block (c.opsCode m.post ++ advance m.step)))

/-- The chaining value back to the IV (at `r29`, moved to `r31` as the data
area). -/
def ivBack : List Instr := mov .r31 .r29 :: c.opsCode (copyBlk c.bw .dat .chn)

/-- The caller's `r29`–`r31` and the return address restored. -/
def restore : List Instr :=
  (List.range 3).map (fun i => .load .d (savedRegs.getD i .r29) sb (8 * c.savedSlot i)) ++
    [.load .d .r0 sb (8 * c.lrSlot), .mtlr .r0]

/-- The whole function. -/
def seq (m : Mode) : Prog isa :=
  .seq (.block (c.entry ++ c.ivIn)) (.seq c.prepare
    (.seq (.ite (.zero .d .r30) (.block []) (.loop (c.body m) (.nonzero .d .r30)))
      (.block ((if m.ivOut then c.ivBack else []) ++ c.restore))))

end Core

end VG.Impl.Modes.PPC64LE
