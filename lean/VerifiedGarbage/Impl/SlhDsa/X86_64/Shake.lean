module

public import VerifiedGarbage.Impl.SlhDsa.X86_64.Xmss
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Fors
public import VerifiedGarbage.Impl.Sha3.X86_64.Stream
public import VerifiedGarbage.Spec.SlhDsa

/-!
# SLH-DSA (SHAKE) on x86-64: key generation and signing

* `keygen(seeds = rdi, sk = rsi, pk = rdx, scratch = rcx)`
  (`slh_keygen_internal`, Algorithm 18): the root of the top layer's XMSS
  tree (`xmssTree`, with no key pair to sign with, its signature to
  `oSigTmp`), then the keys.
* `sign(sk = rdi, msg = rsi, msg_len = rdx, ctx = rcx, ctx_len = r8,
  addrnd = r9, sig = [rsp + 8], scratch = [rsp + 16]) -> eax`
  (`slh_sign`, Algorithm 22, and `slh_sign_internal`, Algorithm 19): if
  `ctx_len ≥ 256` it returns 2 at once. Otherwise it pushes a frame of nine
  words holding the arguments and, at `rsp`, the two bytes `0 ‖ ctx_len` of
  the formatted message `M′`, and computes `R = PRF_msg(SK.prf, addrnd, M′)`
  to the signature's first `n` bytes and the digest
  `H_msg(R, PK.seed, PK.root, M′)` to `oDigest`, each by absorbing the pieces
  of its message into a Keccak state at `oStream` with the sponge functions
  (`vg_keccak_absorb_scratch`, `_pad_scratch`, `_squeeze_scratch`); then the
  FORS signature of the digest and its public key (`forsSign`), and the `d`
  XMSS signatures of the hypertree (`xmssTree` for each layer, each signing
  the root of the one below, the first the FORS public key, at `oMsg`).

Both keep their working space in `scratch` (`rbx`), save their caller's
callee-saved registers (at `oKgSave`),
and write the table of the round constants of the four-way permutation once
(with scalar stores, which every `thash4` can use). The indices `idx_tree` and `idx_leaf` (variables 0 and 1,
after the saved registers, then the layer `j`, 2, and the next XMSS signature, 3) and the
digits of every layer are secret: they reach only the data of the addresses
and the masks of `xmssTree`, `forsSign` and `levels`.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.X86_64.Shake

open VG.X86_64
open VG.Impl.Sha3.X86_64 (at_)
open VG.Spec.SlhDsa (Params)

/-- The internal functions a parameter set's code calls: the `thash4` of its
variant and the functions above it, with their names. -/
structure Fns where
  t4name : String
  t4 : Prog isa
  wotsName : String
  levelsName : String
  xmssName : String
  forsName : String

variable (p : Params) (f : Fns)

/-- The functions of the parameter set `p`, named `set` (`"128s"`, …),
over the `thash4` `t4` whose names end with `sfx` (`""` for the baseline,
`"_avx2"`, …): `vg_slhdsa_shake_thash4_n16{sfx}`, `…_wots4_n16{sfx}` and
`…_levels_n16{sfx}` for `n = 16`, which every parameter set of that `n`
shares, and `vg_slhdsa_shake_xmss_{set}{sfx}` and
`vg_slhdsa_shake_fors_{set}{sfx}`. -/
def Fns.ofVariant (sfx : String) (t4 : Prog isa) (set : String) : Fns where
  t4name := s!"vg_slhdsa_shake_thash4_n{p.n}{sfx}"
  t4 := t4
  wotsName := s!"vg_slhdsa_shake_wots4_n{p.n}{sfx}"
  levelsName := s!"vg_slhdsa_shake_levels_n{p.n}{sfx}"
  xmssName := s!"vg_slhdsa_shake_xmss_{set}{sfx}"
  forsName := s!"vg_slhdsa_shake_fors_{set}{sfx}"

/-- The layout for `p`. -/
def layout : Layout := ⟨p.n, p.len⟩

/-- The code of `wotsLeaves4`, `levels`, `xmssTree` and `forsSign` for `p`. -/
def levelsCode : Prog isa := Tree.levels (layout p) f.t4name f.t4
def xmssCode : Prog isa := Xmss.xmssTree (layout p) p.hp f.t4name f.wotsName f.levelsName f.t4
def forsCode : Prog isa := Fors.forsSign (layout p) p.a p.k f.t4name f.levelsName f.t4

/-- Where key generation and signing save the callee-saved registers: past the
signature at `oSigTmp` (at most `(67 + 9)·32 = 2432` bytes), which
`xmssTree` and `forsSign` keep, unlike the frames. -/
def oKgSave : Nat := Layout.oSigTmp + 2432

/-- Variable `i` of signing, after the saved registers. -/
def var (i : Nat) : MemOp := at_ .rbx (oKgSave + 48 + 8 * i)

/-- The table of the round constants of `thash4`, with scalar stores. -/
def rcTable : List Instr :=
  (List.range 24).flatMap fun r =>
    .movImm64 .rax (Spec.Sha3.RC r) :: (List.range 4).map fun k => .store (at_ .rbx (1600 + 32 * r + 8 * k)) .rax

/-- `PK.seed` (at `oPkSeed`) to every lane of `A` and `B`. -/
def seedLanes : List Instr :=
  (List.range 4).flatMap fun k =>
    copyWords .rbx (Layout.laneA k) .rbx Layout.oPkSeed (p.n / 8) ++
      copyWords .rbx (Layout.laneB k) .rbx Layout.oPkSeed (p.n / 8)

/-- Every lane's layer address `layer` (a register) and tree address
`tree` (a register, a 64-bit integer: bytes 4–7 are 0 and 8–15 its
big-endian bytes), through `rax`. -/
def treeLanes (layer tree : Reg) : List Instr :=
  [.mov .rax (.reg tree), .bswap .rax, .mov .r11 (.reg .rax)] ++
  (List.range 4).flatMap fun k => (List.range 2).flatMap fun b =>
    let o := (if b = 0 then Layout.laneA k else Layout.laneB k) + (layout p).adrsOff
    setFieldR .rbx o layer ++ setField .rbx (o + 4) 0 ++ [.store (at_ .rbx (o + 8)) .r11]

/-- The Keccak state of the sponge, zeroed. -/
def zeroState : List Instr :=
  .mov32 .rax (.imm 0) :: (List.range 25).map fun i => .store (at_ .rbx (Layout.oStream + 8 * i)) .rax

/-! ## Key generation -/

/-- The keys: `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root` to `sk` (`r12`) and
`PK.seed ‖ PK.root` to `pk` (`r13`). -/
def writeKeys : List Instr :=
  (List.range 4).flatMap (fun c => copyWords .r12 (p.n * c) .rbx (Layout.oKeys + 32 * c) (p.n / 8)) ++
    (List.range 2).flatMap (fun c => copyWords .r13 (p.n * c) .rbx (Layout.oKeys + 64 + 32 * c) (p.n / 8))


/-- Save the callee-saved registers at `oKgSave`, with the working space in `b`. -/
def kgSave (b : Reg) : List Instr :=
  (List.range 6).map fun i => .store (at_ b (oKgSave + 8 * i)) (savedRegs.getD i .rbx)

/-- Restore them (`rbx`, the base, last). -/
def kgRestore : List Instr :=
  (List.range 6).reverse.map fun i => .mov (savedRegs.getD i .rbx) (.mem (at_ .rbx (oKgSave + 8 * i)))

/-- `keygen` for `p`. -/
def keyGen : Prog isa :=
  .seq (.block (kgSave .rcx ++ [.mov .rbx (.reg .rcx), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx)] ++
      rcTable ++ (List.range 3).flatMap (fun c => copyWords .rbx (Layout.oKeys + 32 * c) .rdi (p.n * c) (p.n / 8)) ++
      seedLanes p ++ [.mov32 .r10 (.imm (BitVec.ofNat 32 (p.d - 1))), .mov32 .r9 (.imm 0)] ++ treeLanes p .r10 .r9 ++
      [.mov .rdi (.reg .rbx), .mov32 .rsi (.imm 0xffffffff), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 Layout.oSigTmp))]))
    (.seq (.call f.xmssName (xmssCode p f))
      (.block (copyWords .rbx Layout.oPkRoot .rbx Layout.oMsg (p.n / 8) ++ writeKeys p ++ kgRestore)))

/-! ## Signing -/

/-- `[rsp + d]`. -/
def stk (d : Nat) : MemOp := { base := .rsp, disp := d }

/-- The slots of the frame, from `rsp`: the two bytes of `M′`, `scratch`,
`addrnd`, `sig`, `ctx_len`, `ctx`, `msg_len`, `msg` and `sk`. -/
def fHdr : Nat := 0
def fScr : Nat := 8
def fRnd : Nat := 16
def fSig : Nat := 24
def fCtxLen : Nat := 32
def fCtx : Nat := 40
def fLen : Nat := 48
def fMsg : Nat := 56
def fKey : Nat := 64

/-- The registers signing pushes (the first at `rsp + 64`), with `sig` in
`r10`, `scratch` in `r11` and 0 in `rax`. -/
def signRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r10, .r9, .r11, .rax]

/-- An argument of a call. -/
inductive Arg
  /-- The slot at `rsp + f`. -/
  | slot (f : Nat)
  /-- The slot at `rsp + f`, plus `o`. -/
  | slotOff (f o : Nat)
  /-- `scratch + o`. -/
  | scr (o : Nat)
  /-- An immediate. -/
  | imm (v : Nat)
  /-- `rsp`. -/
  | sp
  /-- `rax`. -/
  | ret

/-- Move the argument `a` into `d`. -/
def Arg.mov (d : Reg) : Arg → List Instr
  | .slot f => [.mov d (.mem (stk f))]
  | .slotOff f o => [.mov d (.mem (stk f)), .alu .add d (.imm (BitVec.ofNat 32 o))]
  | .scr o => [.mov d (.reg .rbx), .alu .add d (.imm (BitVec.ofNat 32 o))]
  | .imm v => [.mov32 d (.imm (BitVec.ofNat 32 v))]
  | .sp => [.mov d (.reg .rsp)]
  | .ret => [.mov d (.reg .rax)]

/-- A call of `c`, named `n`, with the arguments `as`. -/
def callA (n : String) (c : Prog isa) (as : List Arg) : Prog isa :=
  .seq (.block (([Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip as).flatMap fun (d, a) => a.mov d)) (.call n c)

/-- Absorb `len` bytes at `src` at the position `pos` (SHAKE256's rate). -/
def kabs (src len pos : Arg) : Prog isa :=
  callA "vg_keccak_absorb_scratch" Impl.Sha3.X86_64.Stream.absorb
    [.scr Layout.oStream, .imm 136, pos, src, len, .scr (Layout.oStream + 200)]

/-- Pad at the position `pos`, with SHAKE's suffix. -/
def kpad (pos : Arg) : Prog isa :=
  callA "vg_keccak_pad_scratch" Impl.Sha3.X86_64.Stream.pad [.scr Layout.oStream, .imm 136, pos, .imm 0x1f,
    .scr (Layout.oStream + 200)]

/-- Squeeze `len` bytes from position 0 to `dst`. -/
def ksqz (dst : Arg) (len : Nat) : Prog isa :=
  callA "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze [.scr Layout.oStream, .imm 136, .imm 0, dst, .imm len,
    .scr (Layout.oStream + 200)]

/-- `SHAKE256(x₁ ‖ … ‖ xᵢ ‖ M′, len)` to `dst`, for the strings `x` of `n`
bytes each at the arguments `xs`. -/
def hashM' (xs : List Arg) (dst : Arg) (len : Nat) : Prog isa :=
  let pre := xs.zipIdx.foldr (fun (x, i) c => .seq (kabs x (.imm p.n) (.imm (p.n * i))) c)
    (.seq (kabs .sp (.imm 2) (.imm (p.n * xs.length)))
      (.seq (kabs (.slot fCtx) (.slot fCtxLen) .ret)
        (.seq (kabs (.slot fMsg) (.slot fLen) .ret) (.seq (kpad .ret) (ksqz dst len)))))
  .seq (.block zeroState) pre

/-- `idx_tree` (the `⌈(h - h/d)/8⌉` bytes after `md`, mod `2^(h - h/d)`) and
`idx_leaf` (the `⌈h/8d⌉` bytes after them, mod `2^(h/d)`) to variables 0 and
1, from 8 bytes read big-endian. -/
def parseIdx : List Instr :=
  let tb := p.h - p.h / p.d
  [.mov .rax (.mem (at_ .rbx (Layout.oDigest + p.mdLen))), .bswap .rax] ++
    (if p.treeIdxLen < 8 then [.shift .shr .rax (64 - 8 * p.treeIdxLen)] else []) ++
    (if tb < 64 then [.shift .shl .rax (64 - tb), .shift .shr .rax (64 - tb)] else []) ++
    [.store (var 0) .rax,
      .mov .rax (.mem (at_ .rbx (Layout.oDigest + p.mdLen + p.treeIdxLen))), .bswap .rax,
      .shift .shr .rax (64 - 8 * p.leafIdxLen), .alu .and .rax (.imm (BitVec.ofNat 32 (2 ^ p.hp - 1))),
      .store (var 1) .rax]

/-- One layer `j` (variable 2) of the hypertree: the lanes' layer and tree
addresses, `xmssTree` signing `oMsg` by `idx_leaf` to the next XMSS
signature (variable 3), its root to `oMsg`; then the next layer's indices,
setting ZF after the last. -/
def layerBody : Prog isa :=
  .seq (.block ([.mov .r10 (.mem (var 2)), .mov .r9 (.mem (var 0))] ++ treeLanes p .r10 .r9 ++
      [.mov .rdi (.reg .rbx), .mov .rsi (.mem (var 1)), .mov .rdx (.mem (var 3))]))
    (.seq (.call f.xmssName (xmssCode p f))
      (.block [.mov .rax (.mem (var 3)), .alu .add .rax (.imm (BitVec.ofNat 32 p.xmssSigLen)), .store (var 3) .rax,
        .mov .rax (.mem (var 0)), .mov .rcx (.reg .rax), .alu .and .rcx (.imm (BitVec.ofNat 32 (2 ^ p.hp - 1))),
        .store (var 1) .rcx, .shift .shr .rax p.hp, .store (var 0) .rax,
        .mov .rax (.mem (var 2)), .alu .add .rax (.imm 1), .store (var 2) .rax,
        .alu .cmp .rax (.imm (BitVec.ofNat 32 p.d))]))

/-- The body of the frame: the keys and the lanes, `R`, the digest, FORS
and the hypertree. -/
def signBody : Prog isa :=
  .seq (.block ([.store8 (stk (fHdr + 1)) .r8, .mov .rdi (.mem (stk fScr))] ++ kgSave .rdi ++
      [.mov .rbx (.reg .rdi), .mov .rsi (.mem (stk fKey))] ++ rcTable ++
      (List.range 4).flatMap (fun c => copyWords .rbx (Layout.oKeys + 32 * c) .rsi (p.n * c) (p.n / 8)) ++
      seedLanes p))
    (.seq (hashM' p [.scr Layout.oSkPrf, .slot fRnd] (.slot fSig) p.n)
      (.seq (hashM' p [.slot fSig, .scr Layout.oPkSeed, .scr Layout.oPkRoot] (.scr Layout.oDigest) p.m)
        (.seq (.block (parseIdx p ++ [.mov32 .r10 (.imm 0), .mov .r9 (.mem (var 0))] ++ treeLanes p .r10 .r9 ++
            [.mov .rdi (.reg .rbx), .mov .rsi (.mem (stk fSig)), .alu .add .rsi (.imm (BitVec.ofNat 32 p.n)),
              .mov .rdx (.mem (var 1))]))
          (.seq (.call f.forsName (forsCode p f))
            (.seq (.block [.mov32 .rax (.imm 0), .store (var 2) .rax, .mov .rax (.mem (stk fSig)),
                .alu .add .rax (.imm (BitVec.ofNat 32 (p.n + p.forsSigLen))), .store (var 3) .rax])
              (.seq (.loop (layerBody p f) .ne) (.block (kgRestore ++ [.mov32 .rax (.imm 1)]))))))))

/-- `sign` for `p`. -/
def sign : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 256)])
    (.ite .b (.seq (.block [.mov .r10 (.mem (stk 8)), .mov .r11 (.mem (stk 16)), .mov32 .rax (.imm 0)])
        (.frame (.push signRegs) (signBody p f) (.pop .r11 9)))
      (.block [.mov32 .rax (.imm 2)]))

end VG.Impl.SlhDsa.X86_64.Shake
