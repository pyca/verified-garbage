module

public import VerifiedGarbage.Impl.Sha3.X86_64
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Thash4

/-!
# SLH-DSA (SHAKE) on x86-64: the working space, and code to build code

Every function of the SHAKE parameter sets works in the caller's `scratch`
(64 KiB, `Spec.SlhDsa.scratchWords`), whose base it keeps in `rbx`, laid out
at the offsets below for the security parameter `n` (16, 24 or 32 bytes):

* `work`, from 0: `thash4`'s working space (`Impl/SlhDsa/X86_64/Thash4.lean`),
  with its table of round constants;
* the saved callee-saved registers and the functions' variables, from `oVars`;
* `SK.seed`, `PK.seed` and `PK.root`, from `oKeys`;
* the lanes `A`, from `oA`: four of `strideA` bytes, each
  `PK.seed ‖ ADRS ‖ M` for an `F`, `H` or `PRF` (`M` of at most `2n` bytes,
  from `n + 32`);
* the lanes `B`, from `oB`: four of `strideB` bytes, each
  `PK.seed ‖ ADRS ‖ M` for a `T_ℓ` (`M` of `len·n` or `k·n` bytes);
* the nodes of a tree, from `oN`, `nodeSlots` of `n` bytes;
* the roots of FORS's subtrees, the digest, the digits, the message of a
  layer, and the stream state of `H_msg` and `PRF_msg`.

The address in a lane is at `n` (`adrsOff`): its layer address in bytes 0–3,
tree address 4–15, type 16–19, key pair address 20–23, chain address or tree
height 24–27, hash address or tree index 28–31, each big-endian.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.X86_64

open VG.X86_64
open VG.Impl.Sha3.X86_64 (at_)

/-- The layout of the working space for the security parameter `n`. -/
structure Layout where
  n : Nat
  /-- `len` of WOTS⁺ (35, 51 or 67 for `lg_w = 4`). -/
  len : Nat

namespace Layout

variable (L : Layout)

def oVars : Nat := 2400
def oKeys : Nat := 3168
/-- `SK.seed`, `SK.prf`, `PK.seed`, `PK.root`, `n` bytes each (as the private key). -/
def oSkSeed : Nat := oKeys
def oSkPrf : Nat := oKeys + 32
def oPkSeed : Nat := oKeys + 64
def oPkRoot : Nat := oKeys + 96
def oA : Nat := 3296
def strideA : Nat := 128
def oB : Nat := 3808
def strideB : Nat := 2208
def oN : Nat := 12640
/-- Room for the 512 nodes of the largest tree, and 8 more that a last
group of four lanes may write past the nodes of a level. -/
def nodeSlots : Nat := 520
def oRoots : Nat := oN + 32 * nodeSlots
def oDigest : Nat := oRoots + 32 * 32
def oDigits : Nat := oDigest + 64
def oMsg : Nat := oDigits + 128
def oStream : Nat := oMsg + 64
/-- The FORS indices, 8 bytes each. -/
def oFidx : Nat := oStream + 768
/-- A signature key generation computes and discards, `(len + h′)·n` bytes. -/
def oSigTmp : Nat := oFidx + 320

/-- Where the address of a lane starts. -/
def adrsOff : Nat := L.n
/-- Where the message of a lane starts. -/
def msgOff : Nat := L.n + 32

/-- Lane `k` of the lanes `A`, and of `B`. -/
def laneA (k : Nat) : Nat := oA + strideA * k
def laneB (k : Nat) : Nat := oB + strideB * k

/-- Each function has a frame of 128 bytes from `oVars` (`0`: `wotsLeaves4`,
`1`: `xmssTree`, `2`: FORS, `3`: the functions the Rust code calls, `4`:
`levels`, `5`: spare): the six
saved registers, then the function's own variables, 8 bytes each. -/
def oFrame (f : Nat) : Nat := oVars + 128 * f
def oSave (f i : Nat) : Nat := oFrame f + 8 * i
def oVar (f i : Nat) : Nat := oFrame f + 48 + 8 * i

end Layout

/-! ## Code to build code -/

/-- The callee-saved registers, saved in the variables `0` to `5`. -/
def savedRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- Save them in frame `f`, with the working space in `b`. -/
def saveRegs (f : Nat) (b : Reg) : List Instr :=
  (List.range 6).map fun i => .store (at_ b (Layout.oSave f i)) (savedRegs.getD i .rbx)

/-- Restore them from frame `f` (`rbx`, the base, last). -/
def restoreRegs (f : Nat) : List Instr :=
  ((List.range 6).reverse.map fun i => .mov (savedRegs.getD i .rbx) (.mem (at_ .rbx (Layout.oSave f i))))

/-- `mov dword [b + d], bswap(v)`: the 32-bit field at `b + d` set to `v`
(an immediate below `2³¹`), big-endian, through `eax`. -/
def setField (b : Reg) (d v : Nat) : List Instr :=
  [.mov32 .rax (.imm (BitVec.ofNat 32 v)), .bswap32 .rax, .store32 (at_ b d) .rax]

/-- The 32-bit field at `b + d` set to the register `r` (below `2³²`), big-endian, through `eax`. -/
def setFieldR (b : Reg) (d : Nat) (r : Reg) : List Instr :=
  [.mov32 .rax (.reg r), .bswap32 .rax, .store32 (at_ b d) .rax]

/-- Copy `w` 8-byte words from `[s + d₁]` to `[t + d₂]`, through `rax`. -/
def copyWords (t : Reg) (d₂ : Nat) (s : Reg) (d₁ w : Nat) : List Instr :=
  (List.range w).flatMap fun i => [.mov .rax (.mem (at_ s (d₁ + 8 * i))), .store (at_ t (d₂ + 8 * i)) .rax]

/-- The arguments of `thash4` on the lanes at `rbx + o`, of `stride` bytes,
for messages of `len` bytes, each output written over the message from
`msgOff` on, with `work` at `rbx`. -/
def thashArgs (L : Layout) (o stride len : Nat) : List Instr :=
  [.mov .rdi (.reg .rbx), .alu .add .rdi (.imm (BitVec.ofNat 32 o)), .mov32 .rsi (.imm (BitVec.ofNat 32 stride)),
    .mov32 .rdx (.imm (BitVec.ofNat 32 len)), .mov .rcx (.reg .rdi), .alu .add .rcx (.imm (BitVec.ofNat 32 L.msgOff)),
    .mov .r8 (.reg .rbx)]

/-- A call of the variant's `thash4`, named `name`, on those lanes. -/
def thashCall (L : Layout) (name : String) (t4 : Prog isa) (o stride len : Nat) : Prog isa :=
  .seq (.block (thashArgs L o stride len)) (.call name t4)

end VG.Impl.SlhDsa.X86_64
