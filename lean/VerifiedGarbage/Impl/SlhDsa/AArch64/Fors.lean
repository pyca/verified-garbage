module

public import VerifiedGarbage.Impl.SlhDsa.AArch64.Tree

/-!
# SLH-DSA (SHAKE) on AArch64: FORS

`forsSign(scratch = x0, sig = x1, kp = x2)`, as on x86-64
(`Impl/SlhDsa/X86_64/Fors.lean`): it writes the FORS signature
(`fors_sign`, Algorithm 16) of the message digest `md` at `oDigest` to the
`k(1 + a)·n` bytes at `sig`, and the FORS public key it gives
(`fors_pkFromSig`, Algorithm 17), `T_k` of the `k` roots, to the `n` bytes at
`oMsg`, for the key pair `kp` of the tree whose layer (0) and tree
addresses, and `PK.seed`, the caller has put in the lanes `A` and `B`. It
reads `⌈k·a / 8⌉ + 2` bytes of the digest.

It computes the `k` indices `base_2b(md, a, k)` to `oFidx` (`indices`: index
`t` is bits `t·a` to `t·a + a - 1` of `md`, most significant first, of the
three bytes from byte `⌊t·a / 8⌋`). Each tree `t` is computed as `U = 2^(a-s)`
subtrees of height `s = min(a, 9)`, so that the nodes of one fit at `oN`:
for each, its leaves four at a time, each `F` of the private key value
`PRF(PK.seed, SK.seed, ADRS)` (`fors_skGen` and `fors_node`, Algorithms 14
and 15), the private key value of the tree's index XORed into the
signature's under a mask; then its heights (`levels`), its root to the
subtree roots at `oRoots`; then, if `U > 1`, the heights of the tree over the
subtree roots, copied to `oN`. Every node of the authentication path is in
one of them, which XORs it into the signature's, zeroed before the tree. The
root goes to lane 0 of the lanes `B`, as the `t`-th string of `T_k`'s
message; after the last tree, its address gets the type `FORS_ROOTS` and
`T_k` gives the public key.

Registers (callee-saved, saved in frame 2 with `x30`): `x19` = `scratch`,
`x20` = `kp`, `x21` = the tree's index (secret: read from `oFidx`, it
reaches only masks), `x23` = the tree `t`, `x24` = its signature, `x25` =
the subtree's first leaf `u·2^s`, `x26` = the leaf `j` of the subtree, `x27`
= `t·2^a`: the public ones are those x86-64 keeps in frame 2.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.AArch64.Fors

open VG.AArch64
open VG.Impl.SlhDsa.AArch64.Thash4 (mov)

variable (L : Layout) (a k : Nat) (t4name levelsName : String) (t4 : Prog isa)

/-- The height of the subtrees. -/
def s : Nat := min a 9

/-- The registers saved in frame 2. -/
def saved : List Reg := [.x19, .x20, .x21, .x23, .x24, .x25, .x26, .x27, .x30]

def pro : List Instr := saveRegs 2 .x0 saved ++ [mov .x19 .x0, mov .x24 .x1, mov .x20 .x2]

/-- Index `t`: bits `t·a` to `t·a + a - 1` of `md`. -/
def index (t : Nat) : List Instr :=
  let o := Layout.oDigest + t * a / 8
  [.ldrb .x9 .x19 o, .lsl .x .x9 .x9 16, .ldrb .x10 .x19 (o + 1), .lsl .x .x10 .x10 8,
    .logic .orr .x .x9 .x9 .x10, .ldrb .x10 .x19 (o + 2), .logic .orr .x .x9 .x9 .x10,
    .lsr .x .x9 .x9 (24 - t * a % 8 - a), .movz .x .x10 (BitVec.ofNat 16 (2 ^ a - 1)) 0,
    .logic .and .x .x9 .x9 .x10, .str .x .x9 .x19 (Layout.oFidx + 8 * t)]

/-- The indices. -/
def indices : List Instr := (List.range k).flatMap (index a)

/-- Lane `k'`'s address for leaf `j + k'` of the subtree (`x10` its index in
the sequence of all trees' leaves) with the type `ty`. -/
def leafAdrs (ty : Nat) (k' : Nat) : List Instr :=
  setField .x19 (Layout.laneA k' + L.adrsOff + 16) ty ++ setFieldR .x19 (Layout.laneA k' + L.adrsOff + 20) .x20 ++
    setField .x19 (Layout.laneA k' + L.adrsOff + 24) 0 ++ [.addImm .x .x11 .x10 k'] ++
    setFieldR .x19 (Layout.laneA k' + L.adrsOff + 28) .x11

/-- Lane `k'`'s private key value XORed into the signature's (at `x24`)
under the mask of `u·2^s + j + k' = index` (`x11` = `u·2^s + j`). -/
def captureSk (k' : Nat) : List Instr :=
  [.addImm .x .x12 .x11 k', .logic .eor .x .x12 .x12 .x21] ++ maskZero .x12 .x13 ++
  (List.range (L.n / 8)).flatMap fun w =>
    [.ldr .x .x13 .x19 (Layout.laneA k' + L.msgOff + 8 * w), .logic .and .x .x13 .x13 .x12,
      .ldr .x .x14 .x24 (8 * w), .logic .eor .x .x14 .x14 .x13, .str .x .x14 .x24 (8 * w)]

/-- Four leaves `j` to `j + 3` of the subtree: the private key values, their
capture, the leaves to the nodes; then `j + 4`, with `x9 = 0` after the
last. -/
def leafBody : Prog isa :=
  .seq (.block ([.add .x .x10 .x27 .x25, .add .x .x10 .x10 .x26] ++
      (List.range 4).flatMap (fun k' => leafAdrs L 6 k' ++
        copyWords .x19 (Layout.laneA k' + L.msgOff) .x19 Layout.oSkSeed (L.n / 8))))
    (.seq (thashCall L t4name t4 Layout.oA Layout.strideA (2 * L.n + 32))
      (.seq (.block ([.add .x .x11 .x25 .x26] ++ (List.range 4).flatMap (captureSk L) ++
          (List.range 4).flatMap (fun k' => setField .x19 (Layout.laneA k' + L.adrsOff + 16) 3)))
        (.seq (thashCall L t4name t4 Layout.oA Layout.strideA (2 * L.n + 32))
          (.block ([mov .x10 .x26] ++ mulN L.n .x10 .x11 ++ [.add .x .x10 .x10 .x19] ++
            (List.range 4).flatMap (fun k' =>
              copyWords .x10 (Layout.oN + L.n * k') .x19 (Layout.laneA k' + L.msgOff) (L.n / 8)) ++
            [.addImm .x .x26 .x26 4, .subImm .x .x9 .x26 (2 ^ s a)])))))

/-- The heights of the subtree from `u·2^s` (`levels` from its `2^s` leaves),
its root to the subtree roots. -/
def subtreeHeights : Prog isa :=
  .seq (.block ([.addImm .x .x10 .x24 L.n, .add .x .x11 .x27 .x25] ++
      Tree.setParams (.reg .x25) (.reg .x11) (.imm 3) (.reg .x20) ++
      [mov .x0 .x19] ++ lea .x1 .x19 Layout.oN ++ movV .x2 (2 ^ s a) ++
      [.movz .x .x3 0 0, mov .x4 .x10, mov .x5 .x21]))
    (.seq (.call levelsName (Tree.levels L t4name t4))
      (.block ([.lsr .x .x10 .x25 (s a)] ++ mulN L.n .x10 .x11 ++ [.add .x .x10 .x10 .x19] ++
        copyWords .x10 Layout.oRoots .x19 Layout.oN (L.n / 8))))

/-- A subtree: its leaves, its heights; then the next, with `x9 = 0` after
the last. -/
def subtreeBody : Prog isa :=
  .seq (.block [.movz .x .x26 0 0])
    (.seq (.loop (leafBody L a t4name t4) (.nonzero .x .x9))
      (.seq (subtreeHeights L a t4name levelsName t4)
        (.block ([.addImm .x .x25 .x25 (2 ^ s a)] ++ movV .x10 (2 ^ a) ++ [.sub .x .x9 .x25 .x10]))))

/-- Where the tree's root is after `topHeights`' heights: the first node, or
the first subtree root if there is one subtree. -/
def rootOff : Nat := if s a < a then Layout.oN else Layout.oRoots

/-- The heights above the subtrees (`levels` from the `2^(a-s)` subtree
roots, for `a > s`, copied to the nodes, where `levels` has room for the 8
nodes past them), and the tree's root to lane 0 of the lanes `B`. -/
def topHeights : Prog isa :=
  .seq (if s a < a then
      .seq (.block (copyWords .x19 Layout.oN .x19 Layout.oRoots (2 ^ (a - s a) * L.n / 8) ++
          [.addImm .x .x10 .x24 (L.n + s a * L.n)] ++
          Tree.setParams (.imm 0) (.reg .x27) (.imm 3) (.reg .x20) ++
          [mov .x0 .x19] ++ lea .x1 .x19 Layout.oN ++ movV .x2 (2 ^ (a - s a)) ++
          [.movz .x .x3 (BitVec.ofNat 16 (s a)) 0, mov .x4 .x10, mov .x5 .x21]))
        (.call levelsName (Tree.levels L t4name t4))
    else .block [])
    (.block ([mov .x10 .x23] ++ mulN L.n .x10 .x11 ++ [.add .x .x10 .x10 .x19] ++
      copyWords .x10 (Layout.laneB 0 + L.msgOff) .x19 (rootOff a) (L.n / 8)))

/-- Tree `t`: its index, its signature zeroed, its subtrees and the heights
above them; then `t + 1`, with `x9 = 0` after the last. -/
def treeBody : Prog isa :=
  .seq (.block ([.lsl .x .x9 .x23 3, .add .x .x9 .x9 .x19, .ldr .x .x21 .x9 Layout.oFidx] ++
      zeroWords .x24 0 ((a + 1) * L.n / 8) ++ [.movz .x .x25 0 0]))
    (.seq (.loop (subtreeBody L a t4name levelsName t4) (.nonzero .x .x9))
      (.seq (topHeights L a t4name levelsName t4)
        (.block ([.addImm .x .x24 .x24 ((a + 1) * L.n)] ++ movV .x10 (2 ^ a) ++
          [.add .x .x27 .x27 .x10, .addImm .x .x23 .x23 1, .subImm .x .x9 .x23 k]))))

/-- `T_k` of the roots, with the type `FORS_ROOTS`, to `pk` (`oMsg`). -/
def pkFors : Prog isa :=
  .seq (.block (setField .x19 (Layout.laneB 0 + L.adrsOff + 16) 4 ++
      setFieldR .x19 (Layout.laneB 0 + L.adrsOff + 20) .x20 ++
      setField .x19 (Layout.laneB 0 + L.adrsOff + 24) 0 ++ setField .x19 (Layout.laneB 0 + L.adrsOff + 28) 0))
    (.seq (thashCall L t4name t4 Layout.oB Layout.strideB (L.n + 32 + k * L.n))
      (.block (copyWords .x19 Layout.oMsg .x19 (Layout.laneB 0 + L.msgOff) (L.n / 8))))

/-- `forsSign` for the FORS parameters `a` and `k`. -/
def forsSign : Prog isa :=
  .seq (.block (pro ++ indices a k ++ [.movz .x .x23 0 0, .movz .x .x27 0 0]))
    (.seq (.loop (treeBody L a k t4name levelsName t4) (.nonzero .x .x9))
      (.seq (pkFors L k t4name t4) (.block (restoreRegs 2 saved))))

end VG.Impl.SlhDsa.AArch64.Fors
