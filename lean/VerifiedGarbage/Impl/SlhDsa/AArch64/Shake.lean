module

public import VerifiedGarbage.Impl.SlhDsa.AArch64.Xmss
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Fors
public import VerifiedGarbage.Impl.Sha3.AArch64.Stream
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
public import VerifiedGarbage.Spec.SlhDsa

/-!
# SLH-DSA (SHAKE) on AArch64: key generation and signing

As on x86-64 (`Impl/SlhDsa/X86_64/Shake.lean`), in AAPCS64's registers:

* `keygen(seeds = x0, sk = x1, pk = x2, scratch = x3)`
  (`slh_keygen_internal`, Algorithm 18): the root of the top layer's XMSS
  tree (`xmssTree`, with no key pair to sign with, its signature to
  `oSigTmp`), then the keys.
* `sign(sk = x0, msg = x1, msg_len = x2, ctx = x3, ctx_len = x4,
  addrnd = x5, sig = x6, scratch = x7) -> w0` (`slh_sign`, Algorithm 22,
  and `slh_sign_internal`, Algorithm 19): if `ctx_len ≥ 256` it returns 2 at
  once. Otherwise it writes the two bytes `0 ‖ ctx_len` of the formatted
  message `M′` to `oHdr`, and computes `R = PRF_msg(SK.prf, addrnd, M′)` to
  the signature's first `n` bytes and the digest
  `H_msg(R, PK.seed, PK.root, M′)` to `oDigest`, each by absorbing the
  pieces of its message into a Keccak state at `oStream` with the sponge
  functions (`vg_keccak_absorb_scratch`, `_pad_scratch`,
  `_squeeze_scratch`, over the single-state permutation of the variant,
  `Fns.keccak`); then the FORS signature of the digest and its public key
  (`forsSign`), and the `d` XMSS signatures of the hypertree (`xmssTree` for
  each layer, each signing the root of the one below, the first the FORS
  public key, at `oMsg`).

All eight arguments are in registers, so there is no stack frame: the
functions save their caller's callee-saved registers and return address in
`oTop`, which no function they call changes, and keep their own values in
callee-saved registers. In signing, `x19` = `scratch`, and while it hashes
`x20`–`x25` = `msg`, `msg_len`, `ctx`, `ctx_len`, `addrnd`, `sig`; then
`x20` = the next XMSS signature, `x21` = the layer `j`, `x22` = `idx_tree`
and `x23` = `idx_leaf`. The indices and the digits of every layer are secret
(they are read from the digest): they reach only the data of the addresses
and the masks of `xmssTree`, `forsSign` and `levels`. The only stack the
functions use is the sponge functions' frame of 16 bytes.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.AArch64.Shake

open VG.AArch64
open VG.Impl.SlhDsa.AArch64.Thash4 (mov)
open VG.Spec.SlhDsa (Params)

/-- The internal functions a parameter set's code calls: the `thash4` of its
variant and the functions above it, with their names, and the single-state
Keccak of the sponge functions. -/
structure Fns where
  t4name : String
  t4 : Prog isa
  wotsName : String
  levelsName : String
  xmssName : String
  forsName : String
  keccak : Impl.Sha3.AArch64.Callee

variable (p : Params) (f : Fns)

/-- The single-state Keccak of the variant: FEAT_SHA3's with `sha3`, as the
two-way permutation's, and otherwise the one in general registers. Its
suffix is the two-way permutation's (`X2Permutation.suffix`). -/
def keccakOf (sha3 : Bool) : Impl.Sha3.AArch64.Callee :=
  if sha3 then Impl.Sha3.AArch64.Sha3.Vector.callee else Impl.Sha3.AArch64.Scalar.callee

/-- The functions of the parameter set `p`, named `set` (`"128s"`, …), over
the two-way permutation with FEAT_SHA3 (`sha3`) or without, whose names end
with `sfx` (`""` or `"_sha3"`, its `X2Permutation.suffix`):
`vg_slhdsa_shake_thash4_n16{sfx}`, `…_wots4_n16{sfx}` and
`…_levels_n16{sfx}` for `n = 16`, which every parameter set of that `n`
shares, and `vg_slhdsa_shake_xmss_{set}{sfx}` and
`vg_slhdsa_shake_fors_{set}{sfx}`. -/
def Fns.ofVariant (sha3 : Bool) (sfx : String) (set : String) : Fns where
  t4name := s!"vg_slhdsa_shake_thash4_n{p.n}{sfx}"
  t4 := Thash4.thash4 p.n sha3
  wotsName := s!"vg_slhdsa_shake_wots4_n{p.n}{sfx}"
  levelsName := s!"vg_slhdsa_shake_levels_n{p.n}{sfx}"
  xmssName := s!"vg_slhdsa_shake_xmss_{set}{sfx}"
  forsName := s!"vg_slhdsa_shake_fors_{set}{sfx}"
  keccak := keccakOf sha3

/-- The layout for `p`. -/
def layout : Layout := ⟨p.n, p.len⟩

/-- The code of `levels`, `xmssTree` and `forsSign` for `p`. -/
def levelsCode : Prog isa := Tree.levels (layout p) f.t4name f.t4
def xmssCode : Prog isa := Xmss.xmssTree (layout p) p.hp f.t4name f.wotsName f.levelsName f.t4
def forsCode : Prog isa := Fors.forsSign (layout p) p.a p.k f.t4name f.levelsName f.t4

/-- `PK.seed` (at `oPkSeed`) to every lane of `A` and `B`. -/
def seedLanes : List Instr :=
  (List.range 4).flatMap fun k =>
    copyWords .x19 (Layout.laneA k) .x19 Layout.oPkSeed (p.n / 8) ++
      copyWords .x19 (Layout.laneB k) .x19 Layout.oPkSeed (p.n / 8)

/-- Every lane's layer address `layer` (a register) and tree address
`tree` (a register, a 64-bit integer: bytes 4–7 are 0 and 8–15 its
big-endian bytes), through `x12`–`x14`. -/
def treeLanes (layer tree : Reg) : List Instr :=
  [.rev .x12 tree, .rev32 .x13 layer, .movz .x .x14 0 0] ++
  (List.range 4).flatMap fun k => (List.range 2).flatMap fun b =>
    let o := (if b = 0 then Layout.laneA k else Layout.laneB k) + (layout p).adrsOff
    [.str .w .x13 .x19 o, .str .w .x14 .x19 (o + 4), .str .x .x12 .x19 (o + 8)]

/-- The Keccak state of the sponge, zeroed, through `x9`. -/
def zeroState : List Instr :=
  [.addImm .x .x9 .x19 Layout.oStream] ++ zeroWords .x9 0 25

/-- The registers the functions the Rust code calls save at `oTop`. -/
def topSaved : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x30]

/-! ## Key generation -/

/-- The keys: `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root` to `sk` (`x20`) and
`PK.seed ‖ PK.root` to `pk` (`x21`). -/
def writeKeys : List Instr :=
  (List.range 4).flatMap (fun c => copyWords .x20 (p.n * c) .x19 (Layout.oKeys + 32 * c) (p.n / 8)) ++
    (List.range 2).flatMap (fun c => copyWords .x21 (p.n * c) .x19 (Layout.oKeys + 64 + 32 * c) (p.n / 8))

/-- `keygen` for `p`. -/
def keyGen : Prog isa :=
  .seq (.block (saveRegsAt Layout.oTop .x3 topSaved ++ [mov .x19 .x3, mov .x20 .x1, mov .x21 .x2] ++
      (List.range 3).flatMap (fun c => copyWords .x19 (Layout.oKeys + 32 * c) .x0 (p.n * c) (p.n / 8)) ++
      seedLanes p ++ [.movz .x .x10 (BitVec.ofNat 16 (p.d - 1)) 0, .movz .x .x11 0 0] ++ treeLanes p .x10 .x11 ++
      [mov .x0 .x19] ++ movV .x1 0xffffffff ++ lea .x2 .x19 Layout.oSigTmp))
    (.seq (.call f.xmssName (xmssCode p f))
      (.block (copyWords .x19 Layout.oPkRoot .x19 Layout.oMsg (p.n / 8) ++ writeKeys p ++
        restoreRegsAt Layout.oTop topSaved)))

/-! ## Signing -/

/-- An argument of a call. -/
inductive Arg
  /-- A register. -/
  | reg (r : Reg)
  /-- `scratch + o`. -/
  | scr (o : Nat)
  /-- An immediate. -/
  | imm (v : Nat)
  /-- `x0`, the previous call's result. -/
  | ret

/-- Move the argument `a` into `d`. -/
def Arg.mov (d : Reg) : Arg → List Instr
  | .reg r => [Thash4.mov d r]
  | .scr o => lea d .x19 o
  | .imm v => movV d v
  | .ret => [Thash4.mov d .x0]

/-- A call of `c`, named `n`, with the arguments `as` in `x0`, `x1`, …,
after `x2 ← pos` (first, as it may be `x0`, the previous call's result). -/
def callA (n : String) (c : Prog isa) (pos : Arg) (as : List (Reg × Arg)) : Prog isa :=
  .seq (.block (pos.mov .x2 ++ as.flatMap fun (d, a) => a.mov d)) (.call n c)

/-- Absorb `len` bytes at `src` at the position `pos` (SHAKE256's rate). -/
def kabs (src len pos : Arg) : Prog isa :=
  callA ("vg_keccak_absorb_scratch" ++ f.keccak.suffix) (Impl.Sha3.AArch64.Stream.absorbWith f.keccak) pos
    [(.x0, .scr Layout.oStream), (.x1, .imm 136), (.x3, src), (.x4, len), (.x5, .scr (Layout.oStream + 200))]

/-- Pad at the position `pos`, with SHAKE's suffix. -/
def kpad (pos : Arg) : Prog isa :=
  callA ("vg_keccak_pad_scratch" ++ f.keccak.suffix) (Impl.Sha3.AArch64.Stream.padWith f.keccak) pos
    [(.x0, .scr Layout.oStream), (.x1, .imm 136), (.x3, .imm 0x1f), (.x4, .scr (Layout.oStream + 200))]

/-- Squeeze `len` bytes from position 0 to `dst`. -/
def ksqz (dst : Arg) (len : Nat) : Prog isa :=
  callA ("vg_keccak_squeeze_scratch" ++ f.keccak.suffix) (Impl.Sha3.AArch64.Stream.squeezeWith f.keccak) (.imm 0)
    [(.x0, .scr Layout.oStream), (.x1, .imm 136), (.x3, dst), (.x4, .imm len), (.x5, .scr (Layout.oStream + 200))]

/-- `SHAKE256(x₁ ‖ … ‖ xᵢ ‖ M′, len)` to `dst`, for the strings `x` of `n`
bytes each at the arguments `xs`, and `M′ = 0 ‖ ctx_len ‖ ctx ‖ M` (its
header at `oHdr`, `ctx` and its length in `x22` and `x23`, `M` and its length
in `x20` and `x21`). -/
def hashM' (xs : List Arg) (dst : Arg) (len : Nat) : Prog isa :=
  let pre := xs.zipIdx.foldr (fun (x, i) c => .seq (kabs f x (.imm p.n) (.imm (p.n * i))) c)
    (.seq (kabs f (.scr Layout.oHdr) (.imm 2) (.imm (p.n * xs.length)))
      (.seq (kabs f (.reg .x22) (.reg .x23) .ret)
        (.seq (kabs f (.reg .x20) (.reg .x21) .ret) (.seq (kpad f .ret) (ksqz f dst len)))))
  .seq (.block (zeroState)) pre

/-- `idx_tree` (the `⌈(h - h/d)/8⌉` bytes after `md`, mod `2^(h - h/d)`) to
`x22` and `idx_leaf` (the `⌈h/8d⌉` bytes after them, mod `2^(h/d)`) to `x23`,
from 8 bytes read big-endian. -/
def parseIdx : List Instr :=
  let tb := p.h - p.h / p.d
  lea .x9 .x19 (Layout.oDigest + p.mdLen) ++ [.ldr .x .x10 .x9 0, .rev .x10 .x10] ++
    (if p.treeIdxLen < 8 then [.lsr .x .x10 .x10 (64 - 8 * p.treeIdxLen)] else []) ++
    (if tb < 64 then [.lsl .x .x10 .x10 (64 - tb), .lsr .x .x10 .x10 (64 - tb)] else []) ++
    [mov .x22 .x10] ++
    lea .x9 .x19 (Layout.oDigest + p.mdLen + p.treeIdxLen) ++ [.ldr .x .x10 .x9 0, .rev .x10 .x10,
      .lsr .x .x10 .x10 (64 - 8 * p.leafIdxLen)] ++ movV .x11 (2 ^ p.hp - 1) ++ [.logic .and .x .x23 .x10 .x11]

/-- One layer `j` (`x21`) of the hypertree: the lanes' layer and tree
addresses, `xmssTree` signing `oMsg` by `idx_leaf` to the next XMSS
signature (`x20`), its root to `oMsg`; then the next layer's indices, with
`x9 = 0` after the last. -/
def layerBody : Prog isa :=
  .seq (.block (treeLanes p .x21 .x22 ++ [mov .x0 .x19, mov .x1 .x23, mov .x2 .x20]))
    (.seq (.call f.xmssName (xmssCode p f))
      (.block ([.addImm .x .x20 .x20 p.xmssSigLen] ++ movV .x11 (2 ^ p.hp - 1) ++
        [.logic .and .x .x23 .x22 .x11, .lsr .x .x22 .x22 p.hp, .addImm .x .x21 .x21 1,
          .subImm .x .x9 .x21 p.d])))

/-- The body: the arguments kept and the keys, `R`, the digest, then
`PK.seed` in the lanes (after the hashes, whose sponge functions may write
all of their working space, which ends past `oA`), FORS and the hypertree. -/
def signBody : Prog isa :=
  .seq (.block (saveRegsAt Layout.oTop .x7 topSaved ++
      [mov .x19 .x7, mov .x20 .x1, mov .x21 .x2, mov .x22 .x3, mov .x23 .x4, mov .x24 .x5, mov .x25 .x6,
        .movz .x .x9 0 0, .strb .x9 .x19 Layout.oHdr, .strb .x23 .x19 (Layout.oHdr + 1)] ++
      (List.range 4).flatMap (fun c => copyWords .x19 (Layout.oKeys + 32 * c) .x0 (p.n * c) (p.n / 8))))
    (.seq (hashM' p f [.scr Layout.oSkPrf, .reg .x24] (.reg .x25) p.n)
      (.seq (hashM' p f [.reg .x25, .scr Layout.oPkSeed, .scr Layout.oPkRoot] (.scr Layout.oDigest) p.m)
        (.seq (.block (seedLanes p ++ parseIdx p ++ [.movz .x .x10 0 0] ++ treeLanes p .x10 .x22 ++
            [mov .x0 .x19, .addImm .x .x1 .x25 p.n, mov .x2 .x23]))
          (.seq (.call f.forsName (forsCode p f))
            (.seq (.block ([.movz .x .x21 0 0] ++ lea .x20 .x25 (p.n + p.forsSigLen)))
              (.seq (.loop (layerBody p f) (.nonzero .x .x9))
                (.block (restoreRegsAt Layout.oTop topSaved ++ [.movz .x .x0 1 0]))))))))

/-- `sign` for `p`: 2 if `ctx_len ≥ 256`, else the body. -/
def sign : Prog isa :=
  .seq (.block [.lsr .x .x9 .x4 8])
    (.ite (.nonzero .x .x9) (.block [.movz .x .x0 2 0]) (signBody p f))

end VG.Impl.SlhDsa.AArch64.Shake
