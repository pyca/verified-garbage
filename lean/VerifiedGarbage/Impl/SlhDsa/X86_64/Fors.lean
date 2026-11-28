module

public import VerifiedGarbage.Impl.SlhDsa.X86_64.Tree

/-!
# SLH-DSA (SHAKE) on x86-64: FORS

`forsSign(scratch = rdi, sig = rsi, kp = rdx)` writes the FORS signature
(`fors_sign`, Algorithm 16) of the message digest `md` at `oDigest` to the
`k(1 + a)·n` bytes at `sig`, and the FORS public key it gives
(`fors_pkFromSig`, Algorithm 17), `T_k` of the `k` roots
(`forsPkFromSig_forsSign`), to the `n` bytes at `oMsg`, for the key pair `kp`
of the tree whose layer (0) and tree addresses, and `PK.seed`, the caller has
put in the lanes `A` and `B`. It reads `⌈k·a / 8⌉ + 2` bytes of the digest.

It computes the `k` indices `base_2b(md, a, k)` to `oFidx` (`indices`: index
`t` is bits `t·a` to `t·a + a - 1` of `md`, most significant first, of the
three bytes from byte `⌊t·a / 8⌋`). Each tree `t` is computed as `U = 2^(a-s)`
subtrees of height `s = min(a, 9)`, so that the nodes of one fit at `oN`:
for each, its leaves four at a time, each `F` of the private key value
`PRF(PK.seed, SK.seed, ADRS)` (`fors_skGen` and `fors_node`, Algorithms 14
and 15), the private key value of the tree's index XORed into the
signature's under a mask; then its heights (`levels`), its root to the
subtree roots at `oRoots`; then, if `U > 1`, the heights of the tree over the
subtree roots, copied to `oN`. Every node of the authentication path is in one of them,
which XORs it into the signature's, zeroed before the tree. The root goes to
lane 0 of the lanes `B`, as the `t`-th string of `T_k`'s message; after the
last tree, its address gets the type `FORS_ROOTS` and `T_k` gives the public
key.

Registers: `rbx` = `scratch`, `r12` = `kp`, `r13` = the tree's index,
`r14` = `sig`, `r15` = the public key (`oMsg`), `rbp` = `md`; variables (frame 2): 0 the tree
`t`, 1 its signature, 2 the subtree's first leaf `u·2^s`, 3 the leaf `j` of
the subtree, 4 `t·2^a`.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.X86_64.Fors

open VG.X86_64
open VG.Impl.Sha3.X86_64 (at_)

variable (L : Layout) (a k : Nat) (t4name levelsName : String) (t4 : Prog isa)

/-- The height of the subtrees. -/
def s : Nat := min a 9

/-- Variable `i` of frame 2. -/
def var (i : Nat) : MemOp := at_ .rbx (Layout.oVar 2 i)

def pro : List Instr :=
  saveRegs 2 .rdi ++ [.mov .rbx (.reg .rdi), .mov .r14 (.reg .rsi), .mov .r12 (.reg .rdx), .mov .rbp (.reg .rdi),
    .alu .add .rbp (.imm (BitVec.ofNat 32 Layout.oDigest)), .mov .r15 (.reg .rdi),
    .alu .add .r15 (.imm (BitVec.ofNat 32 Layout.oMsg))]

/-- Index `t`: bits `t·a` to `t·a + a - 1` of `md`. -/
def index (t : Nat) : List Instr :=
  let o := t * a / 8
  [.movzx8 .rax (at_ .rbp o), .shift .shl .rax 16, .movzx8 .rcx (at_ .rbp (o + 1)), .shift .shl .rcx 8,
    .alu .or .rax (.reg .rcx), .movzx8 .rcx (at_ .rbp (o + 2)), .alu .or .rax (.reg .rcx),
    .shift .shr .rax (24 - t * a % 8 - a), .alu .and .rax (.imm (BitVec.ofNat 32 (2 ^ a - 1))),
    .store (at_ .rbx (Layout.oFidx + 8 * t)) .rax]

/-- The indices, then tree 0 with its signature at `sig`. -/
def indices : List Instr :=
  (List.range k).flatMap (index a) ++
    [.mov32 .rax (.imm 0), .store (var 0) .rax, .store (var 4) .rax, .store (var 1) .r14]

/-- Lane `k'`'s address for leaf `j + k'` of the subtree (`r11` its index in
the sequence of all trees' leaves) with the type `ty`. -/
def leafAdrs (ty : Nat) (k' : Nat) : List Instr :=
  setField .rbx (Layout.laneA k' + L.adrsOff + 16) ty ++ setFieldR .rbx (Layout.laneA k' + L.adrsOff + 20) .r12 ++
    setField .rbx (Layout.laneA k' + L.adrsOff + 24) 0 ++
    [.mov .r11 (.reg .r10), .alu .add .r11 (.imm (BitVec.ofNat 32 k'))] ++
    setFieldR .rbx (Layout.laneA k' + L.adrsOff + 28) .r11

/-- Lane `k'`'s private key value XORed into the signature's (at `rsi`)
under the mask of `u·2^s + j + k' = index` (`rdx` = `u·2^s + j`). -/
def captureSk (k' : Nat) : List Instr :=
  [.mov .rax (.reg .rdx), .alu .add .rax (.imm (BitVec.ofNat 32 k')), .alu .xor .rax (.reg .r13),
    .alu .sub .rax (.imm 1), .shift .shr .rax 63, .mov32 .rdi (.imm 0), .alu .sub .rdi (.reg .rax)] ++
  (List.range (L.n / 8)).flatMap fun w =>
    [.mov .rax (.mem (at_ .rbx (Layout.laneA k' + L.msgOff + 8 * w))), .alu .and .rax (.reg .rdi),
      .alu .xor .rax (.mem (at_ .rsi (8 * w))), .store (at_ .rsi (8 * w)) .rax]

/-- Four leaves `j` to `j + 3` of the subtree: the private key values, their
capture, the leaves to the nodes; then `j + 4`, setting CF while below `2^s`. -/
def leafBody : Prog isa :=
  .seq (.block ([.mov .r10 (.mem (var 4)), .alu .add .r10 (.mem (var 2)), .alu .add .r10 (.mem (var 3))] ++
      (List.range 4).flatMap (fun k' => leafAdrs L 6 k' ++
        copyWords .rbx (Layout.laneA k' + L.msgOff) .rbx Layout.oSkSeed (L.n / 8))))
    (.seq (thashCall L t4name t4 Layout.oA Layout.strideA (2 * L.n + 32))
      (.seq (.block ([.mov .rsi (.mem (var 1)), .mov .rdx (.mem (var 2)), .alu .add .rdx (.mem (var 3))] ++
          (List.range 4).flatMap (captureSk L) ++
          (List.range 4).flatMap (fun k' => setField .rbx (Layout.laneA k' + L.adrsOff + 16) 3)))
        (.seq (thashCall L t4name t4 Layout.oA Layout.strideA (2 * L.n + 32))
          (.block ([.mov .rdx (.mem (var 3))] ++ Wots.mulN L.n .rdx .rcx ++ [.alu .add .rdx (.reg .rbx)] ++
            (List.range 4).flatMap (fun k' =>
              copyWords .rdx (Layout.oN + L.n * k') .rbx (Layout.laneA k' + L.msgOff) (L.n / 8)) ++
            [.mov .rax (.mem (var 3)), .alu .add .rax (.imm 4), .store (var 3) .rax,
              .alu .cmp .rax (.imm (BitVec.ofNat 32 (2 ^ s a)))])))))

/-- The heights of the subtree from `u·2^s` (`levels` from its `2^s` leaves),
its root to the subtree roots. -/
def subtreeHeights : Prog isa :=
  .seq (.block ([.mov .r10 (.mem (var 1)), .alu .add .r10 (.imm (BitVec.ofNat 32 L.n)),
      .mov .rcx (.mem (var 4)), .alu .add .rcx (.mem (var 2))] ++
      Tree.setParams (.mem (var 2)) (.reg .rcx) (.imm 3) (.reg .r12) ++
      [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 Layout.oN)),
        .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ s a))), .mov32 .rcx (.imm 0),
        .mov .r8 (.reg .r10), .mov .r9 (.reg .r13)]))
    (.seq (.call levelsName (Tree.levels L t4name t4))
      (.block ([.mov .rdx (.mem (var 2)), .shift .shr .rdx (s a)] ++ Wots.mulN L.n .rdx .rcx ++
        [.alu .add .rdx (.reg .rbx)] ++ copyWords .rdx Layout.oRoots .rbx Layout.oN (L.n / 8))))

/-- A subtree: its leaves, its heights; then the next, setting ZF after the
last. -/
def subtreeBody : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .store (var 3) .rax])
    (.seq (.loop (leafBody L a t4name t4) .b)
      (.seq (subtreeHeights L a t4name levelsName t4)
        (.block [.mov .rax (.mem (var 2)), .alu .add .rax (.imm (BitVec.ofNat 32 (2 ^ s a))), .store (var 2) .rax,
          .alu .cmp .rax (.imm (BitVec.ofNat 32 (2 ^ a)))])))

/-- Where the tree's root is after `topHeights`' heights: the first node, or
the first subtree root if there is one subtree. -/
def rootOff : Nat := if s a < a then Layout.oN else Layout.oRoots

/-- The heights above the subtrees (`levels` from the `2^(a-s)` subtree
roots, for `a > s`, copied to the nodes, where `levels` has room for the 8
nodes past them), and the tree's root to lane 0 of the lanes `B`. -/
def topHeights : Prog isa :=
  .seq (if s a < a then
      .seq (.block (copyWords .rbx Layout.oN .rbx Layout.oRoots (2 ^ (a - s a) * L.n / 8) ++
          [.mov .r10 (.mem (var 1)), .alu .add .r10 (.imm (BitVec.ofNat 32 (L.n + s a * L.n)))] ++
          Tree.setParams (.imm 0) (.mem (var 4)) (.imm 3) (.reg .r12) ++
          [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 Layout.oN)),
            .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ (a - s a)))), .mov32 .rcx (.imm (BitVec.ofNat 32 (s a))),
            .mov .r8 (.reg .r10), .mov .r9 (.reg .r13)]))
        (.call levelsName (Tree.levels L t4name t4))
    else .block [])
    (.block ([.mov .rdx (.mem (var 0))] ++ Wots.mulN L.n .rdx .rcx ++ [.alu .add .rdx (.reg .rbx)] ++
      copyWords .rdx (Layout.laneB 0 + L.msgOff) .rbx (rootOff a) (L.n / 8)))

/-- `[rbx + 8 r + oFidx]`: index `r`. -/
def fidxR (r : Reg) : MemOp := { base := .rbx, index := some r, scale := 8, disp := (Layout.oFidx : Int) }

/-- `[rbx + 8 rax + oFidx]`: index `rax`. -/
def fidx : MemOp := fidxR .rax

/-- Tree `t`: its index, its signature zeroed, its subtrees and the heights
above them; then `t + 1`, setting ZF after the last. -/
def treeBody : Prog isa :=
  .seq (.block ([.mov .rax (.mem (var 0)), .mov .r13 (.mem fidx), .mov .rsi (.mem (var 1)), .mov32 .rax (.imm 0)] ++
      (List.range ((a + 1) * L.n / 8)).map (fun w => .store (at_ .rsi (8 * w)) .rax) ++ [.store (var 2) .rax]))
    (.seq (.loop (subtreeBody L a t4name levelsName t4) .ne)
      (.seq (topHeights L a t4name levelsName t4)
        (.block [.mov .rax (.mem (var 1)), .alu .add .rax (.imm (BitVec.ofNat 32 ((a + 1) * L.n))),
          .store (var 1) .rax, .mov .rax (.mem (var 4)), .alu .add .rax (.imm (BitVec.ofNat 32 (2 ^ a))),
          .store (var 4) .rax, .mov .rax (.mem (var 0)), .alu .add .rax (.imm 1), .store (var 0) .rax,
          .alu .cmp .rax (.imm (BitVec.ofNat 32 k))])))

/-- `T_k` of the roots, with the type `FORS_ROOTS`, to `pk`. -/
def pkFors : Prog isa :=
  .seq (.block (setField .rbx (Layout.laneB 0 + L.adrsOff + 16) 4 ++ setFieldR .rbx (Layout.laneB 0 + L.adrsOff + 20) .r12 ++
      setField .rbx (Layout.laneB 0 + L.adrsOff + 24) 0 ++ setField .rbx (Layout.laneB 0 + L.adrsOff + 28) 0))
    (.seq (thashCall L t4name t4 Layout.oB Layout.strideB (L.n + 32 + k * L.n))
      (.block (copyWords .r15 0 .rbx (Layout.laneB 0 + L.msgOff) (L.n / 8))))

/-- `forsSign` for the FORS parameters `a` and `k`. -/
def forsSign : Prog isa :=
  .seq (.block (pro ++ indices a k))
    (.seq (.loop (treeBody L a k t4name levelsName t4) .ne)
      (.seq (pkFors L k t4name t4) (.block (restoreRegs 2))))

end VG.Impl.SlhDsa.X86_64.Fors
