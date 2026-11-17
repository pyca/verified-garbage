module

public import VerifiedGarbage.Impl.AesCbc.Arm

/-!
# AES's modes on ARMv7, a group of blocks at a time

`wholeG frame gm lgs body`: `whole body` (`Impl/AesCbc/Arm.lean`), which
first takes the blocks in groups, for a mode whose blocks can be enciphered
independently (CBC decryption, CFB decryption, XTS). AES's block functions
take a number of blocks: they bitslice the round keys once a call and
encipher two blocks at a time, so a call on one block costs as much as one
on two, and the round keys again. A group costs one call.

The groups are of `2 ^ lg` blocks for each `lg` of `lgs` in turn (`gLevel`):
each level takes the groups of `2 ^ lg` of the blocks the levels before it
left (while `r8 >> lg` is not zero), and `whole`'s loop, one block at a time,
takes what the last level leaves.

A group (`gBody`) works on its `G` data blocks `D₀ … D_{G-1}` (at `r7`), on
`G` blocks `W₀ … W_{G-1}` of the scratch buffer, after the registers `save`
keeps there (at `r10 + wOff`: the buffer has room for five), and on the
chaining value `IV` (at `r6`): the mode's operations on them before the call
(`GMode.pre`), the call of the block function on the `G` blocks of the buffer
or of the data (`GMode.onW`), and the operations after it (`GMode.post`). The
operations move blocks as `whole`'s bodies do, through `r12` and `lr`. A
mode's groups leave the data and the chaining value as `G` runs of its body
do:

* `cbcDecG`: `Wⱼ := Dⱼ` (the ciphertext blocks); the inverse cipher on `D`;
  then `D₀ ⊕= IV`, `Dⱼ ⊕= Wⱼ₋₁`, and `IV := W_{G-1}`.
* `cfbDecG`: `W₀ := IV`, `Wⱼ := Dⱼ₋₁`, `IV := D_{G-1}`; the cipher on `W`;
  then `Dⱼ ⊕= Wⱼ`.

The registers are `whole`'s, and the stack: a group uses the 8 bytes its
call pushes. The branches are on `r8`, the number of blocks left, alone,
which is public.
-/

@[expose] public section

namespace VG.Impl.AesCbc.Arm

open VG.Arm
open VG.Impl.CmacAes.Arm (mov save setup restore xor4)

/-- The offset of the groups' buffer in the scratch buffer. -/
def wOff : Nat := 2096

/-- The blocks a group works on: data block `j` (at `r7`), block `j` of the
buffer (in the scratch buffer), and the chaining value (at `r6`). -/
inductive GBlk | d (j : Nat) | w (j : Nat) | iv
  deriving DecidableEq, Repr

/-- Where a block is: its base register and offset. -/
def GBlk.base : GBlk → Reg × Nat
  | .d j => (.r7, 16 * j)
  | .w j => (.r10, wOff + 16 * j)
  | .iv => (.r6, 0)

/-- A block operation of a group: `copy x y` stores block `y` in block `x`,
`xor x y` XORs block `y` into block `x`. -/
inductive GOp
  | copy (x y : GBlk)
  | xor (x y : GBlk)
  deriving DecidableEq, Repr

/-- A block operation, a word at a time: a copy is a zeroed block XORed with
the source. -/
def GOp.code : GOp → List Instr
  | .copy x y => zero4 x.base.1 x.base.2 ++ xor4 x.base.1 y.base.1 x.base.1 x.base.2 y.base.2 x.base.2
  | .xor x y => xor4 x.base.1 y.base.1 x.base.1 x.base.2 y.base.2 x.base.2

/-- A list of block operations. -/
def opsCode (ops : List GOp) : List Instr := ops.flatMap GOp.code

/-- A mode, a group of `G` blocks at a time: the operations before the call,
whether the cipher is applied to the buffer's blocks (or the data's), and
the operations after it. -/
structure GMode where
  pre : Nat → List GOp
  onW : Bool
  post : Nat → List GOp

/-- The address of the blocks of the call: the buffer's, or the data's. -/
def gTarget (onW : Bool) : Instr :=
  if onW then .dp .add .r2 .r10 (.imm (BitVec.ofNat 32 wOff)) else mov .r2 .r7

/-- The arguments of the block function on a group of `G` blocks: the
schedule, the rounds, the blocks, `n = G`, and the working space. -/
def gArgs (onW : Bool) (G : Nat) : List Instr :=
  [mov .r0 .r4, mov .r1 .r5, gTarget onW, .mov .r3 (.imm (BitVec.ofNat 32 G)), mov .r12 .r10]

/-- Z is set if no group of `2 ^ lg` blocks is left. -/
def groupsLeft (lg : Nat) : List Instr := [.mov .r12 (.shifted .r8 .lsr lg), .cmp .r12 (.imm 0)]

/-- On to the next group, and whether one is left. -/
def gAdvance (lg : Nat) : List Instr :=
  [.dp .add .r7 .r7 (.imm (BitVec.ofNat 32 (16 * 2 ^ lg))),
   .dp .sub .r8 .r8 (.imm (BitVec.ofNat 32 (2 ^ lg)))] ++ groupsLeft lg

/-- One group of `2 ^ lg` blocks, through the call `frame` of a block
function. -/
def gBody (frame : Prog isa) (gm : GMode) (lg : Nat) : Prog isa :=
  .seq (.block (opsCode (gm.pre (2 ^ lg)) ++ gArgs gm.onW (2 ^ lg)))
    (.seq frame (.block (opsCode (gm.post (2 ^ lg)) ++ gAdvance lg)))

/-- The groups of `2 ^ lg` blocks, while one is left. -/
def gLevel (frame : Prog isa) (gm : GMode) (lg : Nat) : Prog isa :=
  .seq (.block (groupsLeft lg)) (.ite .eq (.block []) (.loop (gBody frame gm lg) .ne))

/-- The groups of `2 ^ lg` blocks for each `lg` of `lgs` in turn. -/
def gLevels (frame : Prog isa) (gm : GMode) : List Nat → Prog isa
  | [] => .block []
  | lg :: lgs => .seq (gLevel frame gm lg) (gLevels frame gm lgs)

/-- The registers saved and the arguments set up, the groups, `body` run
once for each block left, and the registers restored. -/
def wholeG (frame : Prog isa) (gm : GMode) (lgs : List Nat) (body : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup)) (.seq (gLevels frame gm lgs) (.seq (.block [.cmp .r8 (.imm 0)])
    (.seq (.ite .eq (.block []) (.loop body .ne)) (.block restore))))

/-- The levels of the groups: of 4 and of 2 blocks. -/
def groupLevels : List Nat := [2, 1]

/-! ## The modes -/

/-- CBC decryption (`decBody`), a group at a time. -/
def cbcDecG : GMode where
  pre G := (List.range G).map fun j => .copy (.w j) (.d j)
  onW := false
  post G := .xor (.d 0) .iv :: (List.range (G - 1)).map (fun j => .xor (.d (j + 1)) (.w j)) ++
    [.copy .iv (.w (G - 1))]

/-- CFB decryption with `s = b` (`Impl/AesCfb/Arm.lean`), a group at a time. -/
def cfbDecG : GMode where
  pre G := .copy (.w 0) .iv :: (List.range (G - 1)).map (fun j => .copy (.w (j + 1)) (.d j)) ++
    [.copy .iv (.d (G - 1))]
  onW := true
  post G := (List.range G).map fun j => .xor (.d j) (.w j)

/-- `vg_aes_cbc_decrypt`: the groups, then `decBody` for the blocks left. -/
def decryptG : Prog isa := wholeG decFrame cbcDecG groupLevels decBody

end VG.Impl.AesCbc.Arm
