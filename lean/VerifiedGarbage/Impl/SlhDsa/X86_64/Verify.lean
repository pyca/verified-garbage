module

public import VerifiedGarbage.Impl.SlhDsa.X86_64.Shake

/-!
# SLH-DSA (SHAKE) on x86-64: verification

Every input of verification is public, so its code may branch on them.

* `forsPk(scratch = rdi, sig = rsi, kp = rdx)` writes the FORS public key the
  FORS signature at `sig` of the message digest `md` at `oDigest` gives
  (`fors_pkFromSig`, Algorithm 17) to the `n` bytes at `oMsg`, for the
  key pair `kp` of the tree whose layer and tree addresses, and `PK.seed`,
  the caller has put in the lanes. It computes the indices (`Fors.indices`),
  then the roots of four trees at a time (a last group repeats the last
  tree): each lane the leaf `F` of its private key value, then `a` `H`s up its
  authentication path, the node first or second as the index's bit says;
  each root to lane 0 of `B`, and `T_k` of them (`Fors.pkFors`).
* `xmssPk(scratch = rdi, idx = rsi, sig = rdx)` writes the root the XMSS
  signature at `sig` of the `n` bytes at `oMsg` by the key pair `idx` gives
  (`xmss_pkFromSig`, Algorithm 11) to `oMsg`: the digits of
  `msg` (`Xmss.digits`), the ends of its WOTS⁺ chains four at a time (a last
  group repeats the last chain), each lane running from step `digit` to 14,
  its value put back after every earlier step of the group (`wots_pkFromSig`,
  Algorithm 8); `T_len` of them in lane 0 of `B`; then `h′` `H`s up the
  authentication path, in lane 0 of `A`.
* `verify(pk = rdi, msg = rsi, msg_len = rdx, ctx = rcx, ctx_len = r8,
  sig = r9, sig_len = [rsp + 8], scratch = [rsp + 16]) -> eax` (`slh_verify`,
  Algorithm 24, and `slh_verify_internal`, Algorithm 20): 0 at once if
  `ctx_len ≥ 256` or `sig_len` is not the length of a signature; otherwise,
  in a frame as signing's, the digest, `forsPk`, then `xmssPk` for each layer,
  and 1 if the last root is `PK.root`, 0 if not.

Variables: `forsPk` frame 2 (0 the first tree of the group, 1 the height),
`xmssPk` frame 1 (0 the first chain of the group, 1 the step, 2 the first
step of the group, 3 the height); `verify` saves the callee-saved registers
where key generation does, at `oKgSave`, and keeps its variables after them
(`vvar`), past every part of `scratch` the functions it calls may change.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.X86_64.Verify

open VG.X86_64
open VG.Impl.Sha3.X86_64 (at_)
open VG.Spec.SlhDsa (Params)
open VG.Impl.SlhDsa.X86_64.Shake (Fns stk Arg callA hashM' parseIdx treeLanes seedLanes rcTable xmssCode layout)

variable (p : Params) (f : Fns)

/-! ## `forsPk` -/

section Fors
open VG.Impl.SlhDsa.X86_64.Fors (var)

/-- Lane `k`'s tree `t = min(t₀ + k, k - 1)` in `r10`, its index's leaf
`t·2^a + index` in `r11`, and the signature of the tree at `rsi`. -/
def treeOf (k' : Nat) : List Instr :=
  [.mov .r10 (.mem (var 0)), .alu .add .r10 (.imm (BitVec.ofNat 32 k')), .alu .cmp .r10 (.imm (BitVec.ofNat 32 p.k))] ++
  -- `t ≥ k` only in a last group: `t ← k - 1`
  [.mov32 .rax (.imm (BitVec.ofNat 32 (p.k - 1))), .alu .sub .rax (.reg .r10), .shift .shr .rax 63,
    -- rax = 1 iff t > k - 1, i.e. t ≥ k; t ← t - rax·(t - (k - 1)): t - (k-1) is at most 3
    .mov .rcx (.reg .r10), .alu .sub .rcx (.imm (BitVec.ofNat 32 (p.k - 1))), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
    .alu .and .rcx (.reg .rdx), .alu .sub .r10 (.reg .rcx),
    .mov .r11 (.mem (Fors.fidxR .r10)), .mov .rax (.reg .r10), .shift .shl .rax p.a, .alu .add .r11 (.reg .rax),
    .mov .rsi (.reg .r10)] ++ Wots.mulN p.n .rsi .rax ++ [.mov .rax (.reg .rsi)] ++
    -- `(a + 1)·n·t`: `n·t` times `a + 1`, by additions
    (List.range p.a).map (fun _ => .alu .add .rsi (.reg .rax)) ++ [.alu .add .rsi (.reg .r14)]

/-- The leaves: each lane's address (type `FORS_TREE`, `kp`, height 0, tree
index its leaf), its message the private key value, one `F`. -/
def forsLeaves : Prog isa :=
  .seq (.block ((List.range 4).flatMap fun k' => treeOf p k' ++
      setField .rbx (Layout.laneA k' + (layout p).adrsOff + 16) 3 ++ setFieldR .rbx (Layout.laneA k' + (layout p).adrsOff + 20) .r12 ++
      setField .rbx (Layout.laneA k' + (layout p).adrsOff + 24) 0 ++ setFieldR .rbx (Layout.laneA k' + (layout p).adrsOff + 28) .r11 ++
      copyWords .rbx (Layout.laneA k' + (layout p).msgOff) .rsi 0 (p.n / 8)))
    (thashCall (layout p) f.t4name f.t4 Layout.oA Layout.strideA (2 * p.n + 32))

/-- Lane `k`'s message at height `z` (variable 1): its node, and the
authentication path's node `z` (at `rsi + n + z·n`), in the order the bit `z`
of its index says; and its address's height `z + 1` and tree index
`⌊leaf / 2^(z+1)⌋`. -/
def forsUpLane (k' : Nat) : Prog isa :=
  .seq (.block (treeOf p k' ++ [.mov .rcx (.mem (var 1)), .mov .rax (.reg .r11), .shiftCl .shr .rax,
      .mov .rdx (.mem (var 1))] ++ Wots.mulN p.n .rdx .rcx ++ [.alu .add .rsi (.reg .rdx), .alu .add .rsi (.imm (BitVec.ofNat 32 p.n)),
      .alu .and .rax (.imm 1)]))
    (.seq (.ite .e
        (.block (copyWords .rbx (Layout.laneA k' + (layout p).msgOff + p.n) .rsi 0 (p.n / 8)))
        (.block (copyWords .rbx (Layout.laneA k' + (layout p).msgOff + p.n) .rbx (Layout.laneA k' + (layout p).msgOff) (p.n / 8) ++
          copyWords .rbx (Layout.laneA k' + (layout p).msgOff) .rsi 0 (p.n / 8))))
      (.block ([.mov .r10 (.mem (var 1)), .alu .add .r10 (.imm 1)] ++
        setFieldR .rbx (Layout.laneA k' + (layout p).adrsOff + 24) .r10 ++
        [.mov .rcx (.reg .r10), .shiftCl .shr .r11] ++ setFieldR .rbx (Layout.laneA k' + (layout p).adrsOff + 28) .r11)))

/-- Height `z` of the group: the lanes, four `H`s; then `z + 1`, setting ZF
after the last. -/
def forsUp : Prog isa :=
  .seq (forsUpLane p 0) (.seq (forsUpLane p 1) (.seq (forsUpLane p 2) (.seq (forsUpLane p 3)
    (.seq (thashCall (layout p) f.t4name f.t4 Layout.oA Layout.strideA (3 * p.n + 32))
      (.block [.mov .rax (.mem (var 1)), .alu .add .rax (.imm 1), .store (var 1) .rax,
        .alu .cmp .rax (.imm (BitVec.ofNat 32 p.a))])))))

/-- A group of four trees: the leaves, the heights, each lane's root to lane
0 of `B` at `t·n`; then `t₀ + 4`, setting CF while below `k`. -/
def forsGroup : Prog isa :=
  .seq (forsLeaves p f)
    (.seq (.block [.mov32 .rax (.imm 0), .store (var 1) .rax])
      (.seq (.loop (forsUp p f) .ne)
        (.block ((List.range 4).flatMap (fun k' => treeOf p k' ++ [.mov .rdx (.reg .r10)] ++ Wots.mulN p.n .rdx .rcx ++
            [.alu .add .rdx (.reg .rbx)] ++
            copyWords .rdx (Layout.laneB 0 + (layout p).msgOff) .rbx (Layout.laneA k' + (layout p).msgOff) (p.n / 8)) ++
          [.mov .rax (.mem (var 0)), .alu .add .rax (.imm 4), .store (var 0) .rax,
            .alu .cmp .rax (.imm (BitVec.ofNat 32 p.k))]))))

/-- `forsPk` for `p`. -/
def forsPk : Prog isa :=
  .seq (.block (Fors.pro ++ Fors.indices p.a p.k))
    (.seq (.loop (forsGroup p f) .b)
      (.seq (Fors.pkFors (layout p) p.k f.t4name f.t4) (.block (restoreRegs 2))))

end Fors

/-! ## `xmssPk` -/

section Xmss

/-- Variable `i` of frame 1. -/
def xv (i : Nat) : MemOp := at_ .rbx (Layout.oVar 1 i)

def xpro : List Instr :=
  saveRegs 1 .rdi ++ [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx), .mov .r15 (.reg .rdi),
    .alu .add .r15 (.imm (BitVec.ofNat 32 Layout.oMsg)), .mov .r14 (.reg .r15)]

/-- Lane `k`'s chain `c = min(c₀ + k, len - 1)` in `r10` and its digit in `r11`. -/
def chainOf (k' : Nat) : List Instr :=
  [.mov .r10 (.mem (xv 0)), .alu .add .r10 (.imm (BitVec.ofNat 32 k')),
    .mov32 .rax (.imm (BitVec.ofNat 32 (p.len - 1))), .alu .sub .rax (.reg .r10), .shift .shr .rax 63,
    .mov .rcx (.reg .r10), .alu .sub .rcx (.imm (BitVec.ofNat 32 (p.len - 1))), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
    .alu .and .rcx (.reg .rdx), .alu .sub .r10 (.reg .rcx),
    .movzx8 .r11 { base := .rbx, index := some .r10, scale := 1, disp := (Layout.oDigits : Int) }]

/-- `rsi ← sig + c·n`, chain `c`'s signature value. -/
def chainSig : List Instr := [.mov .rsi (.reg .r10)] ++ Wots.mulN p.n .rsi .rax ++ [.alu .add .rsi (.reg .r13)]

/-- The group's lanes: address (type `WOTS_HASH`, key pair `idx`, chain `c`),
message chain `c`'s signature value; the group's first step, the least of
its digits, to variable 2. -/
def chainLanes : List Instr :=
  [.mov32 .rax (.imm 15), .store (xv 2) .rax] ++
  (List.range 4).flatMap fun k' => chainOf p k' ++
    setField .rbx (Layout.laneA k' + (layout p).adrsOff + 16) 0 ++ setFieldR .rbx (Layout.laneA k' + (layout p).adrsOff + 20) .r12 ++
    setFieldR .rbx (Layout.laneA k' + (layout p).adrsOff + 24) .r10 ++ chainSig p ++
    copyWords .rbx (Layout.laneA k' + (layout p).msgOff) .rsi 0 (p.n / 8) ++
    -- variable 2 ← min(variable 2, digit)
    [.mov .rax (.mem (xv 2)), .alu .sub .rax (.reg .r11), .shift .shr .rax 63, .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
      .mov .rax (.reg .r11), .alu .xor .rax (.mem (xv 2)), .alu .and .rax (.reg .rdx), .alu .xor .rax (.reg .r11),
      .store (xv 2) .rax]

/-- After step `j` (variable 1) of the group, each lane whose digit is above
`j` gets its signature value back. -/
def restoreLane (k' : Nat) : Prog isa :=
  .seq (.block (chainOf p k' ++ [.alu .cmp .r11 (.mem (xv 1))]))
    (.ite .e (.block []) (.ite .b (.block [])
      (.block (chainSig p ++ copyWords .rbx (Layout.laneA k' + (layout p).msgOff) .rsi 0 (p.n / 8)))))

/-- Step `j` of the group: the hash addresses `j`, four `F`s, the lanes not
yet started put back; then `j + 1`, setting ZF after step 14. -/
def stepBody : Prog isa :=
  .seq (.block (.mov .r10 (.mem (xv 1)) :: (List.range 4).flatMap fun k' =>
      setFieldR .rbx (Layout.laneA k' + (layout p).adrsOff + 28) .r10))
    (.seq (thashCall (layout p) f.t4name f.t4 Layout.oA Layout.strideA (2 * p.n + 32))
      (.seq (restoreLane p 0) (.seq (restoreLane p 1) (.seq (restoreLane p 2) (.seq (restoreLane p 3)
        (.block [.mov .rax (.mem (xv 1)), .alu .add .rax (.imm 1), .store (xv 1) .rax, .alu .cmp .rax (.imm 15)]))))))

/-- A group of four chains: the lanes, the steps from the least digit, the
ends to lane 0 of `B` at `c·n`; then `c₀ + 4`, setting CF while below `len`. -/
def chainGroup : Prog isa :=
  .seq (.block (chainLanes p))
    (.seq (.block [.mov .rax (.mem (xv 2)), .store (xv 1) .rax, .alu .cmp .rax (.imm 15)])
      (.seq (.ite .b (.loop (stepBody p f) .ne) (.block []))
        (.block ((List.range 4).flatMap (fun k' => chainOf p k' ++ [.mov .rdx (.reg .r10)] ++ Wots.mulN p.n .rdx .rcx ++
            [.alu .add .rdx (.reg .rbx)] ++
            copyWords .rdx (Layout.laneB 0 + (layout p).msgOff) .rbx (Layout.laneA k' + (layout p).msgOff) (p.n / 8)) ++
          [.mov .rax (.mem (xv 0)), .alu .add .rax (.imm 4), .store (xv 0) .rax,
            .alu .cmp .rax (.imm (BitVec.ofNat 32 p.len))]))))

/-- The WOTS⁺ public key, `T_len` of the ends in lane 0 of `B` (type
`WOTS_PK`, key pair `idx`), to lane 0 of `A`'s message. -/
def wotsPk : Prog isa :=
  .seq (.block (setField .rbx (Layout.laneB 0 + (layout p).adrsOff + 16) 1 ++
      setFieldR .rbx (Layout.laneB 0 + (layout p).adrsOff + 20) .r12 ++
      setField .rbx (Layout.laneB 0 + (layout p).adrsOff + 24) 0 ++ setField .rbx (Layout.laneB 0 + (layout p).adrsOff + 28) 0))
    (.seq (thashCall (layout p) f.t4name f.t4 Layout.oB Layout.strideB (p.n + 32 + p.len * p.n))
      (.block (copyWords .rbx (Layout.laneA 0 + (layout p).msgOff) .rbx (Layout.laneB 0 + (layout p).msgOff) (p.n / 8))))

/-- Height `z` (variable 3) of the path, in lane 0 of `A`: the node and the
authentication path's node `z` in the order bit `z` of `idx` says, the
address (type `TREE`, height `z + 1`, index `⌊idx / 2^(z+1)⌋`), one `H`; then
`z + 1`, setting ZF after the last. -/
def pathBody : Prog isa :=
  .seq (.block ([.mov .rcx (.mem (xv 3)), .mov .rax (.reg .r12), .shiftCl .shr .rax, .mov .rsi (.reg .rcx)] ++
      Wots.mulN p.n .rsi .rdx ++ [.alu .add .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (p.len * p.n))),
        .alu .and .rax (.imm 1)]))
    (.seq (.ite .e
        (.block (copyWords .rbx (Layout.laneA 0 + (layout p).msgOff + p.n) .rsi 0 (p.n / 8)))
        (.block (copyWords .rbx (Layout.laneA 0 + (layout p).msgOff + p.n) .rbx (Layout.laneA 0 + (layout p).msgOff) (p.n / 8) ++
          copyWords .rbx (Layout.laneA 0 + (layout p).msgOff) .rsi 0 (p.n / 8))))
      (.seq (.block (setField .rbx (Layout.laneA 0 + (layout p).adrsOff + 16) 2 ++ setField .rbx (Layout.laneA 0 + (layout p).adrsOff + 20) 0 ++
          [.mov .r10 (.mem (xv 3)), .alu .add .r10 (.imm 1)] ++ setFieldR .rbx (Layout.laneA 0 + (layout p).adrsOff + 24) .r10 ++
          [.mov .rcx (.reg .r10), .mov .r11 (.reg .r12), .shiftCl .shr .r11] ++
          setFieldR .rbx (Layout.laneA 0 + (layout p).adrsOff + 28) .r11))
        (.seq (thashCall (layout p) f.t4name f.t4 Layout.oA Layout.strideA (3 * p.n + 32))
          (.block [.mov .rax (.mem (xv 3)), .alu .add .rax (.imm 1), .store (xv 3) .rax,
            .alu .cmp .rax (.imm (BitVec.ofNat 32 p.hp))]))))

/-- `xmssPk` for `p`. -/
def xmssPk : Prog isa :=
  .seq (.block (xpro ++ Xmss.digits (layout p) ++ [.mov32 .rax (.imm 0), .store (xv 0) .rax]))
    (.seq (.loop (chainGroup p f) .b)
      (.seq (wotsPk p f)
        (.seq (.block [.mov32 .rax (.imm 0), .store (xv 3) .rax])
          (.seq (.loop (pathBody p f) .ne)
            (.block (copyWords .r14 0 .rbx (Layout.laneA 0 + (layout p).msgOff) (p.n / 8) ++ restoreRegs 1))))))

end Xmss

/-! ## `verify` -/

/-- The internal functions `verify` calls besides `Fns`'s. -/
structure VFns where
  forsPkName : String
  xmssPkName : String

/-- Their names for the parameter set named `set` (`128s`, …) and the
variant of `thash4` whose suffix is `sfx`, as `Shake.Fns.ofVariant`'s. -/
def VFns.ofVariant (set sfx : String) : VFns where
  forsPkName := s!"vg_slhdsa_shake_forspk_{set}{sfx}"
  xmssPkName := s!"vg_slhdsa_shake_xmsspk_{set}{sfx}"

variable (g : VFns)

open VG.Impl.SlhDsa.X86_64.Shake (fScr fCtx fCtxLen fLen fMsg fKey fHdr oKgSave kgSave kgRestore)

/-- Variable `i` of `verify`: 0 `idx_tree`, 1 `idx_leaf`, 2 the layer, 3
the next XMSS signature. -/
def vvar (i : Nat) : MemOp := at_ .rbx (oKgSave + 48 + 8 * i)

/-- `parseIdx` to `verify`'s variables 0 and 1. -/
def vParseIdx : List Instr :=
  let tb := p.h - p.h / p.d
  [.mov .rax (.mem (at_ .rbx (Layout.oDigest + p.mdLen))), .bswap .rax] ++
    (if p.treeIdxLen < 8 then [.shift .shr .rax (64 - 8 * p.treeIdxLen)] else []) ++
    (if tb < 64 then [.shift .shl .rax (64 - tb), .shift .shr .rax (64 - tb)] else []) ++
    [.store (vvar 0) .rax,
      .mov .rax (.mem (at_ .rbx (Layout.oDigest + p.mdLen + p.treeIdxLen))), .bswap .rax,
      .shift .shr .rax (64 - 8 * p.leafIdxLen), .alu .and .rax (.imm (BitVec.ofNat 32 (2 ^ p.hp - 1))),
      .store (vvar 1) .rax]

/-- The slots of `sig` and `sig_len` in verification's frame. -/
def fVSig : Nat := 16
def fVSigLen : Nat := 24

/-- One layer `j` (variable 2): the lanes' addresses, `xmssPk` of the next
XMSS signature (variable 3) and `oMsg` to `oMsg`; then the next layer's
indices, setting ZF after the last. -/
def layerBody : Prog isa :=
  .seq (.block ([.mov .r10 (.mem (vvar 2)), .mov .r9 (.mem (vvar 0))] ++ treeLanes p .r10 .r9 ++
      [.mov .rdi (.reg .rbx), .mov .rsi (.mem (vvar 1)), .mov .rdx (.mem (vvar 3))]))
    (.seq (.call g.xmssPkName (xmssPk p f))
      (.block [.mov .rax (.mem (vvar 3)), .alu .add .rax (.imm (BitVec.ofNat 32 p.xmssSigLen)), .store (vvar 3) .rax,
        .mov .rax (.mem (vvar 0)), .mov .rcx (.reg .rax), .alu .and .rcx (.imm (BitVec.ofNat 32 (2 ^ p.hp - 1))),
        .store (vvar 1) .rcx, .shift .shr .rax p.hp, .store (vvar 0) .rax,
        .mov .rax (.mem (vvar 2)), .alu .add .rax (.imm 1), .store (vvar 2) .rax,
        .alu .cmp .rax (.imm (BitVec.ofNat 32 p.d))]))

/-- The body of the frame. -/
def verifyBody : Prog isa :=
  .seq (.block ([.store8 (stk (fHdr + 1)) .r8, .mov .rdi (.mem (stk fScr)), .mov .rsi (.mem (stk fKey))] ++
      kgSave .rdi ++ [.mov .rbx (.reg .rdi)] ++ rcTable ++
      (List.range 2).flatMap (fun c => copyWords .rbx (Layout.oPkSeed + 32 * c) .rsi (p.n * c) (p.n / 8)) ++
      seedLanes p))
    (.seq (hashM' p [.slot fVSig, .scr Layout.oPkSeed, .scr Layout.oPkRoot] (.scr Layout.oDigest) p.m)
      (.seq (.block (vParseIdx p ++ [.mov32 .r10 (.imm 0), .mov .r9 (.mem (vvar 0))] ++ treeLanes p .r10 .r9 ++
          [.mov .rdi (.reg .rbx), .mov .rsi (.mem (stk fVSig)), .alu .add .rsi (.imm (BitVec.ofNat 32 p.n)),
            .mov .rdx (.mem (vvar 1))]))
        (.seq (.call g.forsPkName (forsPk p f))
          (.seq (.block [.mov32 .rax (.imm 0), .store (vvar 2) .rax, .mov .rax (.mem (stk fVSig)),
              .alu .add .rax (.imm (BitVec.ofNat 32 (p.n + p.forsSigLen))), .store (vvar 3) .rax])
            (.seq (.loop (layerBody p f g) .ne)
              (.seq (.block (.mov32 .rax (.imm 0) :: (List.range (p.n / 8)).flatMap (fun w =>
                    [.mov .rcx (.mem (at_ .rbx (Layout.oMsg + 8 * w))), .alu .xor .rcx (.mem (at_ .rbx (Layout.oPkRoot + 8 * w))),
                      .alu .or .rax (.reg .rcx)]) ++ [.alu .test .rax (.reg .rax)]))
                (.seq (.ite .e (.block [.mov32 .rax (.imm 1)]) (.block [.mov32 .rax (.imm 0)]))
                  (.block (.mov .r10 (.reg .rax) :: kgRestore ++ [.mov .rax (.reg .r10)])))))))))

/-- The registers verification pushes: as signing's, `sig` in `r9` and
`sig_len` in `r10`. -/
def verifyRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r10, .r9, .r11, .rax]

/-- `verify` for `p`. -/
def verify : Prog isa :=
  .seq (.block [.mov .r10 (.mem (stk 8)), .mov .r11 (.mem (stk 16)), .mov32 .rax (.imm 0),
      .alu .cmp .r8 (.imm 256)])
    (.ite .b
      (.seq (.block [.alu .cmp .r10 (.imm (BitVec.ofNat 32 p.sigLen))])
        (.ite .e (.frame (.push verifyRegs) (verifyBody p f g) (.pop .r11 9)) (.block [])))
      (.block []))

end VG.Impl.SlhDsa.X86_64.Verify
