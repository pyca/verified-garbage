module

public import VerifiedGarbage.Impl.SlhDsa.AArch64.Shake

/-!
# SLH-DSA (SHAKE) on AArch64: verification

As on x86-64 (`Impl/SlhDsa/X86_64/Verify.lean`). Every input of
verification is public, so its code may branch on them.

* `forsPk(scratch = x0, sig = x1, kp = x2)` writes the FORS public key the
  FORS signature at `sig` of the message digest `md` at `oDigest` gives
  (`fors_pkFromSig`, Algorithm 17) to the `n` bytes at `oMsg`, for the
  key pair `kp` of the tree whose layer and tree addresses, and `PK.seed`,
  the caller has put in the lanes. It computes the indices (`Fors.indices`),
  then the roots of four trees at a time (a last group repeats the last
  tree): each lane the leaf `F` of its private key value, then `a` `H`s up its
  authentication path, the node first or second as the index's bit says;
  each root to lane 0 of `B`, and `T_k` of them (`Fors.pkFors`).
* `xmssPk(scratch = x0, idx = x1, sig = x2)` writes the root the XMSS
  signature at `sig` of the `n` bytes at `oMsg` by the key pair `idx` gives
  (`xmss_pkFromSig`, Algorithm 11) to `oMsg`: the digits of
  `msg` (`Xmss.digits`), the ends of its WOTS⁺ chains four at a time (a last
  group repeats the last chain), each lane running from step `digit` to 14,
  its value put back after every earlier step of the group (`wots_pkFromSig`,
  Algorithm 8); `T_len` of them in lane 0 of `B`; then `h′` `H`s up the
  authentication path, in lane 0 of `A`.
* `verify(pk = x0, msg = x1, msg_len = x2, ctx = x3, ctx_len = x4,
  sig = x5, sig_len = x6, scratch = x7) -> w0` (`slh_verify`, Algorithm 24,
  and `slh_verify_internal`, Algorithm 20): 0 at once if `ctx_len ≥ 256` or
  `sig_len` is not the length of a signature; otherwise, as signing, the
  digest, `forsPk`, then `xmssPk` for each layer, and 1 if the last root is
  `PK.root`, 0 if not (computed without a branch).

The model has no shift by a register, so each lane's index in its tree, at
the height being computed, is kept in a register and shifted by one at each
height: in `forsPk`, `x24`–`x27` for the four lanes; in `xmssPk`, `x26`.

Registers (callee-saved, saved with `x30`): `forsPk` (frame 2): `x19` =
`scratch`, `x20` = `kp`, `x21` = `sig`, `x22` = the first tree of the group,
`x23` = the height, `x24`–`x27` the lanes' indices; `xmssPk` (frame 1): `x19`
= `scratch`, `x20` = `idx`, `x21` = `sig`, `x22` = the first chain of the
group, `x23` = the step, `x24` = the first step of the group, `x25` = the
height, `x26` = `⌊idx / 2^z⌋`; `verify` (at `oTop`): as signing's, with
`sig` in `x24`.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.AArch64.Verify

open VG.AArch64
open VG.Impl.SlhDsa.AArch64.Thash4 (mov)
open VG.Spec.SlhDsa (Params)
open VG.Impl.SlhDsa.AArch64.Shake (Fns hashM' parseIdx treeLanes seedLanes xmssCode layout topSaved)

variable (p : Params) (f : Fns)

/-! ## `forsPk` -/

section Fors

/-- The registers saved in frame 2. -/
def fsaved : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x30]

def fpro : List Instr := saveRegs 2 .x0 fsaved ++ [mov .x19 .x0, mov .x21 .x1, mov .x20 .x2]

/-- Lane `k`'s index register. -/
def idxReg (k' : Nat) : Reg := [Reg.x24, .x25, .x26, .x27].getD k' .x24

/-- Lane `k`'s tree `t = min(t₀ + k, k - 1)` in `x10`. -/
def treeT (k' : Nat) : List Instr :=
  [.addImm .x .x10 .x22 k'] ++ movV .x13 (p.k - 1) ++
  -- `x13 = 1` iff `t > k - 1`, i.e. `t ≥ k` (only in a last group); then
  -- `t ← t - x13·(t - (k - 1))`, `t - (k - 1)` being at most 3
  [.sub .x .x13 .x13 .x10, .lsr .x .x13 .x13 63, .subImm .x .x14 .x10 (p.k - 1), .movz .x .x15 0 0,
    .sub .x .x15 .x15 .x13, .logic .and .x .x14 .x14 .x15, .sub .x .x10 .x10 .x14]

/-- The signature of lane `k`'s tree in `x12`: `sig + t·(a + 1)·n`. -/
def treeSig : List Instr := movV .x13 ((p.a + 1) * p.n) ++ [.mul .x .x12 .x10 .x13, .add .x .x12 .x12 .x21]

/-- The leaves: each lane's index `t·2^a + index` (to its register), its
address (type `FORS_TREE`, `kp`, height 0, tree index its leaf), its
message the private key value, one `F`. -/
def forsLeaves : Prog isa :=
  .seq (.block ((List.range 4).flatMap fun k' => treeT p k' ++
      [.lsl .x .x11 .x10 3, .add .x .x11 .x11 .x19, .ldr .x .x11 .x11 Layout.oFidx, .lsl .x .x13 .x10 p.a,
        .add .x (idxReg k') .x11 .x13] ++ treeSig p ++
      setField .x19 (Layout.laneA k' + (layout p).adrsOff + 16) 3 ++
      setFieldR .x19 (Layout.laneA k' + (layout p).adrsOff + 20) .x20 ++
      setField .x19 (Layout.laneA k' + (layout p).adrsOff + 24) 0 ++
      setFieldR .x19 (Layout.laneA k' + (layout p).adrsOff + 28) (idxReg k') ++
      copyWords .x19 (Layout.laneA k' + (layout p).msgOff) .x12 0 (p.n / 8)))
    (thashCall (layout p) f.t4name f.t4 Layout.oA Layout.strideA (2 * p.n + 32))

/-- Lane `k`'s message at height `z` (`x23`): its node, and the
authentication path's node `z` (at `x12 + n + z·n`), in the order the bit of
its index says; and its address's height `z + 1` and tree index, its index
shifted by one. -/
def forsUpLane (k' : Nat) : Prog isa :=
  .seq (.block (treeT p k' ++ treeSig p ++ [mov .x13 .x23] ++ mulN p.n .x13 .x14 ++
      [.add .x .x12 .x12 .x13, .addImm .x .x12 .x12 p.n, .movz .x .x9 1 0, .logic .and .x .x9 (idxReg k') .x9]))
    (.seq (.ite (.zero .x .x9)
        (.block (copyWords .x19 (Layout.laneA k' + (layout p).msgOff + p.n) .x12 0 (p.n / 8)))
        (.block (copyWords .x19 (Layout.laneA k' + (layout p).msgOff + p.n) .x19 (Layout.laneA k' + (layout p).msgOff) (p.n / 8) ++
          copyWords .x19 (Layout.laneA k' + (layout p).msgOff) .x12 0 (p.n / 8))))
      (.block ([.lsr .x (idxReg k') (idxReg k') 1, .addImm .x .x10 .x23 1] ++
        setFieldR .x19 (Layout.laneA k' + (layout p).adrsOff + 24) .x10 ++
        setFieldR .x19 (Layout.laneA k' + (layout p).adrsOff + 28) (idxReg k'))))

/-- Height `z` of the group: the lanes, four `H`s; then `z + 1`, with
`x9 = 0` after the last. -/
def forsUp : Prog isa :=
  .seq (forsUpLane p 0) (.seq (forsUpLane p 1) (.seq (forsUpLane p 2) (.seq (forsUpLane p 3)
    (.seq (thashCall (layout p) f.t4name f.t4 Layout.oA Layout.strideA (3 * p.n + 32))
      (.block [.addImm .x .x23 .x23 1, .subImm .x .x9 .x23 p.a])))))

/-- A group of four trees: the leaves, the heights, each lane's root to lane
0 of `B` at `t·n`; then `t₀ + 4`, with `x9 = 1` while it is below `k`. -/
def forsGroup : Prog isa :=
  .seq (forsLeaves p f)
    (.seq (.block [.movz .x .x23 0 0])
      (.seq (.loop (forsUp p f) (.nonzero .x .x9))
        (.block ((List.range 4).flatMap (fun k' => treeT p k' ++ [mov .x11 .x10] ++ mulN p.n .x11 .x13 ++
            [.add .x .x11 .x11 .x19] ++
            copyWords .x11 (Layout.laneB 0 + (layout p).msgOff) .x19 (Layout.laneA k' + (layout p).msgOff) (p.n / 8)) ++
          [.addImm .x .x22 .x22 4, .subImm .x .x9 .x22 p.k, .lsr .x .x9 .x9 63]))))

/-- `forsPk` for `p`. -/
def forsPk : Prog isa :=
  .seq (.block (fpro ++ Fors.indices p.a p.k ++ [.movz .x .x22 0 0]))
    (.seq (.loop (forsGroup p f) (.nonzero .x .x9))
      (.seq (Fors.pkFors (layout p) p.k f.t4name f.t4) (.block (restoreRegs 2 fsaved))))

end Fors

/-! ## `xmssPk` -/

section Xmss

/-- The registers saved in frame 1. -/
def xsaved : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x30]

def xpro : List Instr := saveRegs 1 .x0 xsaved ++ [mov .x19 .x0, mov .x20 .x1, mov .x21 .x2]

/-- Lane `k`'s chain `c = min(c₀ + k, len - 1)` in `x10` and its digit in `x11`. -/
def chainOf (k' : Nat) : List Instr :=
  [.addImm .x .x10 .x22 k', .movz .x .x13 (BitVec.ofNat 16 (p.len - 1)) 0, .sub .x .x13 .x13 .x10,
    .lsr .x .x13 .x13 63, .subImm .x .x14 .x10 (p.len - 1), .movz .x .x15 0 0, .sub .x .x15 .x15 .x13,
    .logic .and .x .x14 .x14 .x15, .sub .x .x10 .x10 .x14,
    .add .x .x11 .x19 .x10, .ldrb .x11 .x11 Layout.oDigits]

/-- `x12 ← sig + c·n`, chain `c`'s signature value. -/
def chainSig : List Instr := [mov .x12 .x10] ++ mulN p.n .x12 .x13 ++ [.add .x .x12 .x12 .x21]

/-- The group's lanes: address (type `WOTS_HASH`, key pair `idx`, chain `c`),
message chain `c`'s signature value; the group's first step, the least of
its digits, to `x24`. -/
def chainLanes : List Instr :=
  [.movz .x .x24 15 0] ++
  (List.range 4).flatMap fun k' => chainOf p k' ++
    setField .x19 (Layout.laneA k' + (layout p).adrsOff + 16) 0 ++
    setFieldR .x19 (Layout.laneA k' + (layout p).adrsOff + 20) .x20 ++
    setFieldR .x19 (Layout.laneA k' + (layout p).adrsOff + 24) .x10 ++ chainSig p ++
    copyWords .x19 (Layout.laneA k' + (layout p).msgOff) .x12 0 (p.n / 8) ++
    -- `x24 ← min(x24, digit)`
    [.sub .x .x13 .x24 .x11, .lsr .x .x13 .x13 63, .movz .x .x15 0 0, .sub .x .x15 .x15 .x13,
      .logic .eor .x .x13 .x11 .x24, .logic .and .x .x13 .x13 .x15, .logic .eor .x .x24 .x13 .x11]

/-- After step `j` (`x23`) of the group, each lane whose digit is above `j`
gets its signature value back. -/
def restoreLane (k' : Nat) : Prog isa :=
  .seq (.block (chainOf p k' ++ [.sub .x .x13 .x23 .x11, .lsr .x .x13 .x13 63]))
    (.ite (.zero .x .x13) (.block [])
      (.block (chainSig p ++ copyWords .x19 (Layout.laneA k' + (layout p).msgOff) .x12 0 (p.n / 8))))

/-- Step `j` of the group: the hash addresses `j`, four `F`s, the lanes not
yet started put back; then `j + 1`, with `x9 = 0` after step 14. -/
def stepBody : Prog isa :=
  .seq (.block ((List.range 4).flatMap fun k' => setFieldR .x19 (Layout.laneA k' + (layout p).adrsOff + 28) .x23))
    (.seq (thashCall (layout p) f.t4name f.t4 Layout.oA Layout.strideA (2 * p.n + 32))
      (.seq (restoreLane p 0) (.seq (restoreLane p 1) (.seq (restoreLane p 2) (.seq (restoreLane p 3)
        (.block [.addImm .x .x23 .x23 1, .subImm .x .x9 .x23 15]))))))

/-- A group of four chains: the lanes, the steps from the least digit, the
ends to lane 0 of `B` at `c·n`; then `c₀ + 4`, with `x9 = 1` while it is
below `len`. -/
def chainGroup : Prog isa :=
  .seq (.block (chainLanes p))
    (.seq (.block [mov .x23 .x24, .subImm .x .x9 .x24 15])
      (.seq (.ite (.zero .x .x9) (.block []) (.loop (stepBody p f) (.nonzero .x .x9)))
        (.block ((List.range 4).flatMap (fun k' => chainOf p k' ++ [mov .x12 .x10] ++ mulN p.n .x12 .x13 ++
            [.add .x .x12 .x12 .x19] ++
            copyWords .x12 (Layout.laneB 0 + (layout p).msgOff) .x19 (Layout.laneA k' + (layout p).msgOff) (p.n / 8)) ++
          [.addImm .x .x22 .x22 4, .subImm .x .x9 .x22 p.len, .lsr .x .x9 .x9 63]))))

/-- The WOTS⁺ public key, `T_len` of the ends in lane 0 of `B` (type
`WOTS_PK`, key pair `idx`), to lane 0 of `A`'s message. -/
def wotsPk : Prog isa :=
  .seq (.block (setField .x19 (Layout.laneB 0 + (layout p).adrsOff + 16) 1 ++
      setFieldR .x19 (Layout.laneB 0 + (layout p).adrsOff + 20) .x20 ++
      setField .x19 (Layout.laneB 0 + (layout p).adrsOff + 24) 0 ++
      setField .x19 (Layout.laneB 0 + (layout p).adrsOff + 28) 0))
    (.seq (thashCall (layout p) f.t4name f.t4 Layout.oB Layout.strideB (p.n + 32 + p.len * p.n))
      (.block (copyWords .x19 (Layout.laneA 0 + (layout p).msgOff) .x19 (Layout.laneB 0 + (layout p).msgOff) (p.n / 8))))

/-- Height `z` (`x25`) of the path, in lane 0 of `A`: the node and the
authentication path's node `z` in the order bit `z` of `idx` (bit 0 of
`x26`) says, the address (type `TREE`, height `z + 1`, index
`⌊idx / 2^(z+1)⌋`), one `H`; then `z + 1`, with `x9 = 0` after the last. -/
def pathBody : Prog isa :=
  .seq (.block ([mov .x12 .x25] ++ mulN p.n .x12 .x13 ++
      [.add .x .x12 .x12 .x21, .addImm .x .x12 .x12 (p.len * p.n), .movz .x .x9 1 0, .logic .and .x .x9 .x26 .x9]))
    (.seq (.ite (.zero .x .x9)
        (.block (copyWords .x19 (Layout.laneA 0 + (layout p).msgOff + p.n) .x12 0 (p.n / 8)))
        (.block (copyWords .x19 (Layout.laneA 0 + (layout p).msgOff + p.n) .x19 (Layout.laneA 0 + (layout p).msgOff) (p.n / 8) ++
          copyWords .x19 (Layout.laneA 0 + (layout p).msgOff) .x12 0 (p.n / 8))))
      (.seq (.block (setField .x19 (Layout.laneA 0 + (layout p).adrsOff + 16) 2 ++
          setField .x19 (Layout.laneA 0 + (layout p).adrsOff + 20) 0 ++
          [.addImm .x .x10 .x25 1] ++ setFieldR .x19 (Layout.laneA 0 + (layout p).adrsOff + 24) .x10 ++
          [.lsr .x .x26 .x26 1] ++ setFieldR .x19 (Layout.laneA 0 + (layout p).adrsOff + 28) .x26))
        (.seq (thashCall (layout p) f.t4name f.t4 Layout.oA Layout.strideA (3 * p.n + 32))
          (.block [.addImm .x .x25 .x25 1, .subImm .x .x9 .x25 p.hp]))))

/-- `xmssPk` for `p`. -/
def xmssPk : Prog isa :=
  .seq (.block (xpro ++ Xmss.digits (layout p) ++ [.movz .x .x22 0 0]))
    (.seq (.loop (chainGroup p f) (.nonzero .x .x9))
      (.seq (wotsPk p f)
        (.seq (.block [.movz .x .x25 0 0, mov .x26 .x20])
          (.seq (.loop (pathBody p f) (.nonzero .x .x9))
            (.block (copyWords .x19 Layout.oMsg .x19 (Layout.laneA 0 + (layout p).msgOff) (p.n / 8) ++
              restoreRegs 1 xsaved))))))

end Xmss

/-! ## `verify` -/

/-- The internal functions `verify` calls besides `Fns`'s. -/
structure VFns where
  forsPkName : String
  xmssPkName : String

/-- Their names for the parameter set named `set` (`128s`, …) and the
variant whose suffix is `sfx`, as `Shake.Fns.ofVariant`'s. -/
def VFns.ofVariant (set sfx : String) : VFns where
  forsPkName := s!"vg_slhdsa_shake_forspk_{set}{sfx}"
  xmssPkName := s!"vg_slhdsa_shake_xmsspk_{set}{sfx}"

variable (g : VFns)

/-- One layer `j` (`x21`): the lanes' addresses, `xmssPk` of the next
XMSS signature (`x20`) and `oMsg` to `oMsg`; then the next layer's
indices, with `x9 = 0` after the last. -/
def layerBody : Prog isa :=
  .seq (.block (treeLanes p .x21 .x22 ++ [mov .x0 .x19, mov .x1 .x23, mov .x2 .x20]))
    (.seq (.call g.xmssPkName (xmssPk p f))
      (.block ([.addImm .x .x20 .x20 p.xmssSigLen] ++ movV .x11 (2 ^ p.hp - 1) ++
        [.logic .and .x .x23 .x22 .x11, .lsr .x .x22 .x22 p.hp, .addImm .x .x21 .x21 1,
          .subImm .x .x9 .x21 p.d])))

/-- `w0 ← 1` if the root at `oMsg` is `PK.root`, else 0, without a branch:
`x9` the OR of the words' differences, `x0 = 1 - ((x9 ∨ -x9) ≫ 63)`. -/
def compareRoot : List Instr :=
  .movz .x .x9 0 0 :: (List.range (p.n / 8)).flatMap (fun w =>
    [.ldr .x .x10 .x19 (Layout.oMsg + 8 * w), .ldr .x .x11 .x19 (Layout.oPkRoot + 8 * w),
      .logic .eor .x .x10 .x10 .x11, .logic .orr .x .x9 .x9 .x10]) ++
  [.movz .x .x10 0 0, .sub .x .x10 .x10 .x9, .logic .orr .x .x10 .x10 .x9, .lsr .x .x10 .x10 63,
    .movz .x .x11 1 0, .sub .x .x9 .x11 .x10]

/-- The body: the arguments kept, the keys, the digest, the lanes (after
the digest, as the sponge functions may write the working space past their
state up to lane 0 of `A`), `forsPk`, the hypertree and the comparison. -/
def verifyBody : Prog isa :=
  .seq (.block (saveRegsAt Layout.oTop .x7 topSaved ++
      [mov .x19 .x7, mov .x20 .x1, mov .x21 .x2, mov .x22 .x3, mov .x23 .x4, mov .x24 .x5,
        .movz .x .x9 0 0, .strb .x9 .x19 Layout.oHdr, .strb .x23 .x19 (Layout.oHdr + 1)] ++
      (List.range 2).flatMap (fun c => copyWords .x19 (Layout.oPkSeed + 32 * c) .x0 (p.n * c) (p.n / 8))))
    (.seq (hashM' p f [.reg .x24, .scr Layout.oPkSeed, .scr Layout.oPkRoot] (.scr Layout.oDigest) p.m)
      (.seq (.block (seedLanes p ++ parseIdx p ++ [.movz .x .x10 0 0] ++ treeLanes p .x10 .x22 ++
          [mov .x0 .x19, .addImm .x .x1 .x24 p.n, mov .x2 .x23]))
        (.seq (.call g.forsPkName (forsPk p f))
          (.seq (.block ([.movz .x .x21 0 0] ++ lea .x20 .x24 (p.n + p.forsSigLen)))
            (.seq (.loop (layerBody p f g) (.nonzero .x .x9))
              (.block (compareRoot p ++ restoreRegsAt Layout.oTop topSaved ++ [mov .x0 .x9])))))))

/-- `verify` for `p`: 0 if `ctx_len ≥ 256` or `sig_len ≠ sigLen`, else the body. -/
def verify : Prog isa :=
  .seq (.block ([.lsr .x .x9 .x4 8] ++ movV .x10 p.sigLen ++ [.sub .x .x10 .x6 .x10, .logic .orr .x .x9 .x9 .x10]))
    (.ite (.nonzero .x .x9) (.block [.movz .x .x0 0 0]) (verifyBody p f g))

end VG.Impl.SlhDsa.AArch64.Verify
