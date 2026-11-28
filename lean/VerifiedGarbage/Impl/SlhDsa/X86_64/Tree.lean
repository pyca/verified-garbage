module

public import VerifiedGarbage.Impl.SlhDsa.X86_64.Wots

/-!
# SLH-DSA (SHAKE) on x86-64: the heights of a tree

`levels(scratch = rdi, nodes = rsi, count = rdx, z₀ = rcx, auth = r8, idx = r9)`,
with the variables 5 to 8 of frame 4 set by the caller (`capBase`,
`adrsBase`, `type`, `kp`, `setParams`): from the `count = 2^h` nodes of
height `z₀` at `nodes`, `n` bytes each, it computes those of each height up
to `z₀ + h`, the nodes of each written over the first of those of the height
below (so the node of height `z₀ + h` is the first), and for each height `z`
from `z₀` to `z₀ + h - 1` the authentication path's node of `idx` at height
`z`: the node whose index in its tree is `⌊idx / 2^z⌋ ⊕ 1`, the nodes at
`nodes` having the indices `⌊capBase / 2^z⌋ + i` in their tree: the node of
the height whose index it is, if one is, is XORed into the path's node at
`auth + (z - z₀)·n`, which the caller zeroes first (FORS's subtrees each have
the nodes of some of a path's heights).

Node `j` of height `z + 1` is `H(PK.seed, ADRS, node 2j ‖ node 2j + 1)` for
the address of the caller's layer and tree in the lanes `A`, with the type
`type` (`TREE` for XMSS, `FORS_TREE` for FORS), the key pair address `kp`,
the tree height `z + 1` and the tree index `⌊adrsBase / 2^(z+1)⌋ + j`: for an
XMSS tree, `capBase = adrsBase = 0`; for FORS's tree `t` and the subtree
whose first leaf is leaf `u` of the tree, `capBase = u` and
`adrsBase = t·2^a + u` (the leaves of all `k` trees are numbered in one
sequence, Algorithm 15).

The node of `idx` is selected with masks from all the nodes of the height,
so `idx` (and `kp`, `capBase`, `adrsBase`, `type`) affect no branch and no
address: they are only read from memory into the data of the masks and the
addresses. Everything that does, the pointers, the height, the number of
nodes and the node's index, is kept in callee-saved registers, which
`thash4` keeps. The nodes are computed four at a time, a last group
computing lanes past the height's nodes, which nothing reads (the caller
leaves room for 8 nodes past them).

Registers: `rbx` = `scratch`, `r12` = `nodes`, `r13` = the path's node,
`r14` = the height `z`, `r15` = the number of nodes at height `z`, `rbp` =
the node or group; variables of frame 4: 0 `idx`, 3 the sibling.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.X86_64.Tree

open VG.X86_64
open VG.Impl.Sha3.X86_64 (at_)

variable (L : Layout) (t4name : String) (t4 : Prog isa)

/-- Variable `i` of frame 4. -/
def var (i : Nat) : MemOp := at_ .rbx (Layout.oVar 4 i)

open VG.Impl.SlhDsa.X86_64.Wots (mulN)

def pro : List Instr :=
  saveRegs 4 .rdi ++ [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r15 (.reg .rdx), .mov .r14 (.reg .rcx),
    .mov .r13 (.reg .r8), .store (var 0) .r9]

/-- The sibling `⌊idx / 2^z⌋ ⊕ 1`, and the scan from node 0. -/
def scanInit : List Instr :=
  [.mov .rcx (.reg .r14), .mov .rax (.mem (var 0)), .shiftCl .shr .rax, .alu .xor .rax (.imm 1), .store (var 3) .rax,
    .mov32 .rbp (.imm 0)]

/-- Node `i` (`rbp`) XORed into the authentication path's node under the
mask of `⌊capBase / 2^z⌋ + i = sibling`; then `i + 1`, setting ZF after the
last. -/
def scanBody : List Instr :=
  [.mov .rax (.mem (var 5)), .mov .rcx (.reg .r14), .shiftCl .shr .rax, .alu .add .rax (.reg .rbp),
    .alu .xor .rax (.mem (var 3)), .alu .sub .rax (.imm 1), .shift .shr .rax 63, .mov32 .rdi (.imm 0),
    .alu .sub .rdi (.reg .rax), .mov .rdx (.reg .rbp)] ++
  mulN L.n .rdx .rcx ++ [.alu .add .rdx (.reg .r12)] ++
  (List.range (L.n / 8)).flatMap (fun w =>
    [.mov .rax (.mem (at_ .rdx (8 * w))), .alu .and .rax (.reg .rdi), .alu .xor .rax (.mem (at_ .r13 (8 * w))),
      .store (at_ .r13 (8 * w)) .rax]) ++
  [.alu .add .rbp (.imm 1), .alu .cmp .rbp (.reg .r15)]

/-- Lane `k`'s address for node `j + k` of height `z + 1` (`r10` = `z + 1`,
`r9` = `⌊adrsBase / 2^(z+1)⌋ + j`), and its message, nodes `2(j + k)` and
`2(j + k) + 1` (from `rsi`). -/
def nodeLane (k : Nat) : List Instr :=
  [.mov .rdx (.mem (var 7))] ++ setFieldR .rbx (Layout.laneA k + L.adrsOff + 16) .rdx ++
    [.mov .rdx (.mem (var 8))] ++ setFieldR .rbx (Layout.laneA k + L.adrsOff + 20) .rdx ++
    setFieldR .rbx (Layout.laneA k + L.adrsOff + 24) .r10 ++
    [.mov .r11 (.reg .r9), .alu .add .r11 (.imm (BitVec.ofNat 32 k))] ++
    setFieldR .rbx (Layout.laneA k + L.adrsOff + 28) .r11 ++
    copyWords .rbx (Layout.laneA k + L.msgOff) .rsi (2 * L.n * k) (2 * L.n / 8)

/-- The lanes of nodes `j` to `j + 3` (`j` in `rbp`) of height `z + 1`. -/
def levelLanes : List Instr :=
  [.mov .r10 (.reg .r14), .alu .add .r10 (.imm 1), .mov .r9 (.mem (var 6)), .mov .rcx (.reg .r10),
    .shiftCl .shr .r9, .alu .add .r9 (.reg .rbp), .mov .rsi (.reg .rbp)] ++ mulN L.n .rsi .rcx ++
    [.alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .r12)] ++ (List.range 4).flatMap (nodeLane L)

/-- The outputs of the four `H`s to nodes `j` to `j + 3`; then `j + 4`,
setting CF while it is below the height's number of nodes. -/
def levelOut : List Instr :=
  [.mov .rdx (.reg .rbp)] ++ mulN L.n .rdx .rcx ++ [.alu .add .rdx (.reg .r12)] ++
    (List.range 4).flatMap (fun k => copyWords .rdx (L.n * k) .rbx (Layout.laneA k + L.msgOff) (L.n / 8)) ++
    [.alu .add .rbp (.imm 4), .alu .cmp .rbp (.reg .r15)]

/-- Nodes `j` to `j + 3` of height `z + 1`: the lanes, four `H`s, the outputs. -/
def levelBody : Prog isa :=
  .seq (.block (levelLanes L)) (.seq (thashCall L t4name t4 Layout.oA Layout.strideA (3 * L.n + 32)) (.block (levelOut L)))

/-- After the scan: the number of nodes halved, and the level from node 0. -/
def halve : List Instr := [.shift .shr .r15 1, .mov32 .rbp (.imm 0)]

/-- After the level: the next node of the path and `z + 1`; ZF set once a
single node is left. -/
def nextHeight : List Instr :=
  [.alu .add .r13 (.imm (BitVec.ofNat 32 L.n)), .alu .add .r14 (.imm 1), .alu .cmp .r15 (.imm 1)]

/-- Height `z`: the scan, then the nodes of height `z + 1`. -/
def heightBody : Prog isa :=
  .seq (.block scanInit)
    (.seq (.loop (.block (scanBody L)) .ne)
      (.seq (.block halve) (.seq (.loop (levelBody L t4name t4) .b) (.block (nextHeight L)))))

/-- `levels`, calling the `thash4` named `t4name`, whose code is `t4`. -/
def levels : Prog isa :=
  .seq (.block pro) (.seq (.loop (heightBody L t4name t4) .ne) (.block (restoreRegs 4)))

/-- The caller's setting of the parameters of `levels` in frame 4:
`capBase`, `adrsBase`, `type` and `kp` from `src`s (each a register, an
immediate or memory), through `rax`. -/
def setParams (capBase adrsBase type kp : Src) : List Instr :=
  [.mov .rax capBase, .store (var 5) .rax, .mov .rax adrsBase, .store (var 6) .rax,
    .mov .rax type, .store (var 7) .rax, .mov .rax kp, .store (var 8) .rax]

end VG.Impl.SlhDsa.X86_64.Tree
