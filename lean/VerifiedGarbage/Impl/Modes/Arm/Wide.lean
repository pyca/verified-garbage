module

public import VerifiedGarbage.Impl.Modes.Arm.CbcChained
public import VerifiedGarbage.Impl.Modes.Arm.Ctr
public import VerifiedGarbage.Impl.StackScratch.Arm

/-!
# Block cipher modes on ARMv7, a group of blocks at a time

`seqW core mode wide lgs wb`: `seq core mode` (`Seq.lean`), which first takes
the blocks in groups, for a mode whose blocks can be enciphered
independently (CTR, CBC decryption, CFB decryption) and a core that takes
no working space. A core's ECB function takes a number of blocks, and costs
about as much on one block as on a group, so a group costs one call where
`seq` makes one a block.

The groups are of `2 ^ lg` blocks for each `lg` of `lgs` in turn (`wlevel`):
each level takes the groups of `2 ^ lg` of the blocks the levels before it
left (while `r7 >> lg` is not zero), and `seq`'s loop, one block at a time,
takes what the last level leaves. So a message costs a call for each group
of the largest size and one for each power of two in the number of blocks
left after them.

A group (`wbody`) works on its `G` data blocks `D₀ … D_{G-1}` (at `r6`), on
`G` blocks `W₀ … W_{G-1}` of a buffer of `wb` bytes that `wide` reserves on
the stack around the levels (at `sp`, whose address is in `r12` between the
calls: `wbuf`) and zeroes after them, and on the chaining block `O` and the
spare block `T` of `seq`'s scratch buffer (`WBlk`): the mode's operations on
them before the call (`WMode.pre`), the call of the core on the `G` blocks
of the buffer or of the data (`WMode.onW`), and the operations after it
(`WMode.post`). A wide mode leaves the data, `O` and `T` as `G` steps of
its mode one block at a time do:

* `ctrW`: `Wⱼ := O`, `O := inc(O)` for each `j`; the cipher on `W`; then
  `Dⱼ ⊕= Wⱼ`, and `T := W_{G-1}`.
* `cbcDecW`: `Wⱼ := Dⱼ` (the ciphertext blocks); the inverse cipher on `D`;
  then `D₀ ⊕= O`, `Dⱼ ⊕= Wⱼ₋₁`, and `O := T := W_{G-1}`.
* `cfbDecW`: `W₀ := O`, `Wⱼ := Dⱼ₋₁`, `O := T := D_{G-1}`; the cipher on
  `W`; then `Dⱼ ⊕= Wⱼ`.

The branches are on `r7`, the number of blocks left, alone, which is
public, as in `seq`.
-/

@[expose] public section

namespace VG.Impl.Modes.Arm

open VG.Arm

/-- The blocks a group works on: data block `j` (at `r6`), block `j` of the
buffer on the stack (at `r12`), the chaining block and the spare block (in
the scratch buffer). -/
inductive WBlk | d (j : Nat) | w (j : Nat) | o | t
  deriving DecidableEq, Repr

/-- A block operation of a group: `inc` steps the chaining block as a
counter, `copy x y` stores block `y` in block `x`, `xor x y` XORs block `y`
into block `x`. -/
inductive WOp
  | inc
  | copy (x y : WBlk)
  | xor (x y : WBlk)
  deriving DecidableEq, Repr

/-- A mode, a group of `G` blocks at a time: the operations before the call,
whether the cipher is applied to the buffer's blocks (or the data's), and
the operations after it. -/
structure WMode where
  pre : Nat → List WOp
  onW : Bool
  post : Nat → List WOp

namespace Core

variable (c : Core)

/-- Where a block of a group is: its base register and offset. -/
def wbase : WBlk → Reg × Nat
  | .d j => (.r6, c.bs * j)
  | .w j => (.r12, c.bs * j)
  | .o => (.r8, oOff)
  | .t => (.r8, oOff + c.bs)

/-- A block operation of a group, a word at a time. -/
def wopCode : WOp → List Instr
  | .inc => incAt .r8 oOff
  | .copy x y => (List.range c.bw).flatMap (copyWord (c.wbase x).1 (c.wbase y).1 (c.wbase x).2 (c.wbase y).2)
  | .xor x y => (List.range c.bw).flatMap (xorWord (c.wbase x).1 (c.wbase y).1 (c.wbase x).2 (c.wbase y).2)

/-- A list of block operations of a group. -/
def wopsCode (ops : List WOp) : List Instr := ops.flatMap c.wopCode

/-- The buffer's address, the stack pointer, to `r12`. -/
def wbuf : List Instr := [.addSp .r12 0]

/-- The arguments of the call on a group of `G` blocks: the schedule, the
number of rounds (if any), the buffer's or the data's blocks, `n = G`, and
the constant argument (if any). -/
def wcallArgs (onW : Bool) (G : Nat) : List Instr :=
  mov .r0 .r4 :: ((if c.rounds then [mov .r1 .r11] else []) ++
    [mov c.dReg (if onW then .r12 else .r6), .mov c.nReg (.imm (BitVec.ofNat 32 G))]) ++ c.arg3Code

/-- Z is set if no group of `2 ^ lg` blocks is left. -/
def groupsLeft (lg : Nat) : List Instr := [.mov .r9 (.shifted .r7 .lsr lg), .cmp .r9 (.imm 0)]

/-- On to the next group, and whether one is left. -/
def wadvance (lg : Nat) : List Instr :=
  [.dp .add .r6 .r6 (.imm (BitVec.ofNat 32 (c.bs * 2 ^ lg))),
   .dp .sub .r7 .r7 (.imm (BitVec.ofNat 32 (2 ^ lg)))] ++ groupsLeft lg

/-- One group of `2 ^ lg` blocks. -/
def wbody (wm : WMode) (lg : Nat) : Prog isa :=
  .seq (.block wbuf) (.seq (.block (c.wopsCode (wm.pre (2 ^ lg)) ++ c.wcallArgs wm.onW (2 ^ lg)))
    (.seq (.call c.name c.code) (.seq (.block wbuf)
      (.block (c.wopsCode (wm.post (2 ^ lg)) ++ c.wadvance lg)))))

/-- The groups of `2 ^ lg` blocks, while one is left. -/
def wlevel (wm : WMode) (lg : Nat) : Prog isa :=
  .seq (.block (groupsLeft lg)) (.ite .eq (.block []) (.loop (c.wbody wm lg) .ne))

/-- The groups of `2 ^ lg` blocks for each `lg` of `lgs` in turn. -/
def wlevels (wm : WMode) : List Nat → Prog isa
  | [] => .block []
  | lg :: lgs => .seq (c.wlevel wm lg) (wlevels wm lgs)

/-- The levels, with the buffer of `wb` bytes on the stack, zeroed after
them. -/
def wide (wm : WMode) (lgs : List Nat) (wb : Nat) : Prog isa :=
  .frame (.alloc wb) (.seq (c.wlevels wm lgs)
    (.seq (.block wbuf) (.block (.mov .r2 (.imm 0) :: Impl.StackScratch.Arm.wipeStores (wb / 4))))) (.free wb)

/-- The whole function: the groups, then the blocks left one at a time. -/
def seqW (m : Mode) (wm : WMode) (lgs : List Nat) (wb : Nat) : Prog isa :=
  .seq (.block (c.save ++ c.setup)) (.seq (c.wide wm lgs wb) (.seq (.block [.cmp .r7 (.imm 0)])
    (.seq (.ite .eq (.block []) (.loop (c.body m) .ne)) (.block (c.finish m ++ restore)))))

end Core

/-- The levels of the groups of a cipher of 16-byte blocks: of 8, of 4 and
of 2 blocks. -/
def wideLevels : List Nat := [3, 2, 1]

/-- The size of their buffer: 8 blocks of 16 bytes. -/
def wideBuf : Nat := 128

/-- `seqW`, in groups of 8, of 4 and of 2 blocks of 16 bytes. -/
def Core.seq8 (c : Core) (m : Mode) (wm : WMode) : Prog isa := c.seqW m wm wideLevels wideBuf

/-! ## The modes -/

/-- CTR (`ctr`), a group at a time. -/
def ctrW : WMode where
  pre G := (List.range G).flatMap fun j => [.copy (.w j) .o, .inc]
  onW := true
  post G := (List.range G).map (fun j => .xor (.d j) (.w j)) ++ [.copy .t (.w (G - 1))]

/-- CBC decryption (`cbcDecChained`), a group at a time. -/
def cbcDecW : WMode where
  pre G := (List.range G).map fun j => .copy (.w j) (.d j)
  onW := false
  post G := .xor (.d 0) .o :: (List.range (G - 1)).map (fun j => .xor (.d (j + 1)) (.w j)) ++
    [.copy .o (.w (G - 1)), .copy .t (.w (G - 1))]

/-- CFB decryption (`cfbDec`), a group at a time. -/
def cfbDecW : WMode where
  pre G := .copy (.w 0) .o :: (List.range (G - 1)).map (fun j => .copy (.w (j + 1)) (.d j)) ++
    [.copy .o (.d (G - 1)), .copy .t (.d (G - 1))]
  onW := true
  post G := (List.range G).map fun j => .xor (.d j) (.w j)

end VG.Impl.Modes.Arm
