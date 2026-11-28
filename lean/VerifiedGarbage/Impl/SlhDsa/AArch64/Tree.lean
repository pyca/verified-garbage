module

public import VerifiedGarbage.Impl.SlhDsa.AArch64.Wots

/-!
# SLH-DSA (SHAKE) on AArch64: the heights of a tree

`levels(scratch = x0, nodes = x1, count = x2, z₀ = x3, auth = x4, idx = x5)`,
with the variables 0 to 3 of frame 3 set by the caller (`capBase`,
`adrsBase`, `type`, `kp`, `setParams`), as on x86-64
(`Impl/SlhDsa/X86_64/Tree.lean`): from the `count = 2^h` nodes of height
`z₀` at `nodes`, `n` bytes each, it computes those of each height up to
`z₀ + h`, the nodes of each written over the first of those of the height
below (so the node of height `z₀ + h` is the first), and for each height `z`
from `z₀` to `z₀ + h - 1` the authentication path's node of `idx` at height
`z`: the node whose index in its tree is `⌊idx / 2^z⌋ ⊕ 1`, the nodes at
`nodes` having the indices `⌊capBase / 2^z⌋ + i` in their tree: the node of
the height whose index it is, if one is, is XORed into the path's node at
`auth + (z - z₀)·n`, which the caller zeroes first.

Node `j` of height `z + 1` is `H(PK.seed, ADRS, node 2j ‖ node 2j + 1)` for
the address of the caller's layer and tree in the lanes `A`, with the type
`type` (`TREE` for XMSS, `FORS_TREE` for FORS), the key pair address `kp`,
the tree height `z + 1` and the tree index `⌊adrsBase / 2^(z+1)⌋ + j`.

The node of `idx` is selected with masks from all the nodes of the height,
so `idx` (and `kp`, `capBase`, `adrsBase`, `type`) affect no branch and no
address: they are only read into the data of the masks and the addresses.
The model has no shift by a register, so the code keeps `⌊idx / 2^z⌋`,
`⌊capBase / 2^z⌋` and `⌊adrsBase / 2^(z+1)⌋` in registers, shifted right by
`z₀` first (a loop of `z₀` steps, a public count) and by one at each height.
The nodes are computed four at a time, a last group computing lanes past the
height's nodes, which nothing reads (the caller leaves room for 8 nodes past
them).

Registers: `x19` = `scratch`, `x20` = `nodes`, `x21` = the path's node,
`x22` = the height `z`, `x23` = the number of nodes at height `z`, `x24` =
the node or group, `x25` = `⌊idx / 2^z⌋`, `x26` = `⌊capBase / 2^z⌋`, `x27` =
`⌊adrsBase / 2^(z+1)⌋`: callee-saved registers, which `thash4` keeps, saved
in frame 3 with `x30`. The sibling is `x13` during the scan.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.AArch64.Tree

open VG.AArch64
open VG.Impl.SlhDsa.AArch64.Thash4 (mov)

variable (L : Layout) (t4name : String) (t4 : Prog isa)

/-- The offset of variable `i` of frame 3 in `scratch`. -/
def var (i : Nat) : Nat := Layout.oVar 3 i

/-- The registers saved in frame 3. -/
def saved : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x30]

def pro : List Instr :=
  saveRegs 3 .x0 saved ++ [mov .x19 .x0, mov .x20 .x1, mov .x23 .x2, mov .x22 .x3, mov .x21 .x4,
    mov .x25 .x5, .ldr .x .x26 .x19 (var 0), .ldr .x .x27 .x19 (var 1), .lsr .x .x27 .x27 1]

/-- The three shifted values shifted right by `z₀` (`x22`): `z₀` steps of one. -/
def align : Prog isa :=
  .ite (.zero .x .x22) (.block [])
    (.seq (.block [mov .x9 .x22])
      (.loop (.block [.lsr .x .x25 .x25 1, .lsr .x .x26 .x26 1, .lsr .x .x27 .x27 1, .subImm .x .x9 .x9 1])
        (.nonzero .x .x9)))

/-- The sibling `⌊idx / 2^z⌋ ⊕ 1`, and the scan from node 0 (at `x10`). -/
def scanInit : List Instr :=
  [.movz .x .x9 1 0, .logic .eor .x .x13 .x25 .x9, .movz .x .x24 0 0, mov .x10 .x20]

/-- Node `i` (`x24`, at `x10`) XORed into the authentication path's node
under the mask of `⌊capBase / 2^z⌋ + i = sibling`; then `i + 1`, with
`x9 = 0` after the last. -/
def scanBody : List Instr :=
  [.add .x .x11 .x26 .x24, .logic .eor .x .x11 .x11 .x13] ++ maskZero .x11 .x12 ++
  (List.range (L.n / 8)).flatMap (fun w =>
    [.ldr .x .x12 .x10 (8 * w), .logic .and .x .x12 .x12 .x11, .ldr .x .x14 .x21 (8 * w),
      .logic .eor .x .x14 .x14 .x12, .str .x .x14 .x21 (8 * w)]) ++
  [.addImm .x .x10 .x10 L.n, .addImm .x .x24 .x24 1, .sub .x .x9 .x24 .x23]

/-- Lane `k`'s address for node `j + k` of height `z + 1` (`x10` = `z + 1`,
`x11` = `⌊adrsBase / 2^(z+1)⌋ + j`), and its message, nodes `2(j + k)` and
`2(j + k) + 1` (from `x12`). -/
def nodeLane (k : Nat) : List Instr :=
  [.ldr .w .x13 .x19 (var 2)] ++ setFieldR .x19 (Layout.laneA k + L.adrsOff + 16) .x13 ++
    [.ldr .w .x13 .x19 (var 3)] ++ setFieldR .x19 (Layout.laneA k + L.adrsOff + 20) .x13 ++
    setFieldR .x19 (Layout.laneA k + L.adrsOff + 24) .x10 ++
    [.addImm .x .x13 .x11 k] ++ setFieldR .x19 (Layout.laneA k + L.adrsOff + 28) .x13 ++
    copyWords .x19 (Layout.laneA k + L.msgOff) .x12 (2 * L.n * k) (2 * L.n / 8)

/-- The lanes of nodes `j` to `j + 3` (`j` in `x24`) of height `z + 1`. -/
def levelLanes : List Instr :=
  [.addImm .x .x10 .x22 1, .add .x .x11 .x27 .x24, mov .x12 .x24] ++ mulN L.n .x12 .x13 ++
    [.add .x .x12 .x12 .x12, .add .x .x12 .x12 .x20] ++ (List.range 4).flatMap (nodeLane L)

/-- The outputs of the four `H`s to nodes `j` to `j + 3`; then `j + 4`,
with `x9 = 1` while it is below the height's number of nodes. -/
def levelOut : List Instr :=
  [mov .x10 .x24] ++ mulN L.n .x10 .x11 ++ [.add .x .x10 .x10 .x20] ++
    (List.range 4).flatMap (fun k => copyWords .x10 (L.n * k) .x19 (Layout.laneA k + L.msgOff) (L.n / 8)) ++
    [.addImm .x .x24 .x24 4, .sub .x .x9 .x24 .x23, .lsr .x .x9 .x9 63]

/-- Nodes `j` to `j + 3` of height `z + 1`: the lanes, four `H`s, the outputs. -/
def levelBody : Prog isa :=
  .seq (.block (levelLanes L)) (.seq (thashCall L t4name t4 Layout.oA Layout.strideA (3 * L.n + 32)) (.block (levelOut L)))

/-- After the scan: the number of nodes halved, and the level from node 0. -/
def halve : List Instr := [.lsr .x .x23 .x23 1, .movz .x .x24 0 0]

/-- After the level: the next node of the path, `z + 1` and the shifted
values with it; `x9 = 0` once a single node is left. -/
def nextHeight : List Instr :=
  [.addImm .x .x21 .x21 L.n, .addImm .x .x22 .x22 1, .lsr .x .x25 .x25 1, .lsr .x .x26 .x26 1,
    .lsr .x .x27 .x27 1, .subImm .x .x9 .x23 1]

/-- Height `z`: the scan, then the nodes of height `z + 1`. -/
def heightBody : Prog isa :=
  .seq (.block scanInit)
    (.seq (.loop (.block (scanBody L)) (.nonzero .x .x9))
      (.seq (.block halve) (.seq (.loop (levelBody L t4name t4) (.nonzero .x .x9)) (.block (nextHeight L)))))

/-- `levels`, calling the `thash4` named `t4name`, whose code is `t4`. -/
def levels : Prog isa :=
  .seq (.block pro) (.seq align (.seq (.loop (heightBody L t4name t4) (.nonzero .x .x9)) (.block (restoreRegs 3 saved))))

/-- A parameter of `levels`: a register or an immediate. -/
inductive Src
  | reg (r : Reg)
  | imm (v : Nat)

/-- `x9 ← s`. -/
def Src.mov : Src → List Instr
  | .reg r => [Thash4.mov .x9 r]
  | .imm v => movV .x9 v

/-- The caller's setting of the parameters of `levels` in frame 3:
`capBase`, `adrsBase`, `type` and `kp`, through `x9`. -/
def setParams (capBase adrsBase type kp : Src) : List Instr :=
  capBase.mov ++ [.str .x .x9 .x19 (var 0)] ++ adrsBase.mov ++ [.str .x .x9 .x19 (var 1)] ++
    type.mov ++ [.str .x .x9 .x19 (var 2)] ++ kp.mov ++ [.str .x .x9 .x19 (var 3)]

end VG.Impl.SlhDsa.AArch64.Tree
