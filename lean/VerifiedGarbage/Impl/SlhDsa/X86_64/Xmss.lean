module

public import VerifiedGarbage.Impl.SlhDsa.X86_64.Wots
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Tree

/-!
# SLH-DSA (SHAKE) on x86-64: an XMSS tree

`xmssTree(scratch = rdi, idx = rsi, sig = rdx)` computes the XMSS tree of
height `h′` whose layer and tree addresses, and `PK.seed`, the caller has put
in the lanes `A` and `B`: its root (`xmss_node(SK.seed, 0, h′, PK.seed, ADRS)`,
Algorithm 9) to the `n` bytes at `oMsg`, and the XMSS signature (`xmss_sign`,
Algorithm 10) by the key pair `idx` of the `n` bytes that were there, its WOTS⁺ signature and its authentication
path, to the `(len + h′)·n` bytes at `sig`. For `idx ≥ 2^h′` (key generation)
the signature's bytes are unspecified.

It computes the `len` base-16 digits of `msg` and of its checksum
(`wotsDigits`, lines 1–7 of Algorithm 7) at `oDigits`; the `2^h′` leaves,
four at a time (`wotsLeaves4`), to the nodes at `oN`, which also writes the
WOTS⁺ signature; then the heights of the tree and its authentication path
(`levels`, with the type `TREE` and the key pair address 0), the root the
first node.

Registers: `rbx` = `scratch`, `r12` = `idx`, `r13` = `sig`, `r15` = the
message; variable 0 of frame 1: the key pair of the next group
of leaves.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.X86_64.Xmss

open VG.X86_64
open VG.Impl.Sha3.X86_64 (at_)

variable (L : Layout) (hp : Nat) (t4name wotsName levelsName : String) (t4 : Prog isa)

/-- Variable `i` of frame 1. -/
def var (i : Nat) : MemOp := at_ .rbx (Layout.oVar 1 i)

def pro : List Instr :=
  saveRegs 1 .rdi ++ [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx), .mov .r15 (.reg .rdi),
    .alu .add .r15 (.imm (BitVec.ofNat 32 Layout.oMsg))]

/-- The digits of byte `b` of `msg`, its high and its low half, to digits
`2b` and `2b + 1`; their sum added to `r10`. -/
def digitByte (b : Nat) : List Instr :=
  [.movzx8 .rax (at_ .r15 b), .mov .rcx (.reg .rax), .shift .shr .rax 4, .store8 (at_ .rbx (Layout.oDigits + 2 * b)) .rax,
    .alu .and .rcx (.imm 15), .store8 (at_ .rbx (Layout.oDigits + 2 * b + 1)) .rcx,
    .alu .add .r10 (.reg .rax), .alu .add .r10 (.reg .rcx)]

/-- The digits: those of `msg`, then the three of the checksum
`csum = Σ (15 - digit)`: `toByte(csum ≪ 4, 2)` in base 16, its first three
digits, `csum ≫ 8`, `(csum ≫ 4) ∧ 15` and `csum ∧ 15`. -/
def digits : List Instr :=
  .mov32 .r10 (.imm 0) :: (List.range L.n).flatMap digitByte ++
  [.mov32 .r11 (.imm (BitVec.ofNat 32 (15 * 2 * L.n))), .alu .sub .r11 (.reg .r10),
    .mov .rax (.reg .r11), .shift .shr .rax 8, .alu .and .rax (.imm 15),
      .store8 (at_ .rbx (Layout.oDigits + 2 * L.n)) .rax,
    .mov .rax (.reg .r11), .shift .shr .rax 4, .alu .and .rax (.imm 15),
      .store8 (at_ .rbx (Layout.oDigits + 2 * L.n + 1)) .rax,
    .mov .rax (.reg .r11), .alu .and .rax (.imm 15), .store8 (at_ .rbx (Layout.oDigits + 2 * L.n + 2)) .rax,
    .mov32 .rax (.imm 0), .store (var 0) .rax, .store (var 1) .rax]

/-- A group of four leaves: `wotsLeaves4` on the key pairs from variable 0;
then the next, setting ZF after the last. -/
def leafBody : Prog isa :=
  .seq (.block [.mov .rdi (.reg .rbx), .mov .rsi (.mem (var 0)), .mov .rdx (.reg .r12), .mov .rcx (.reg .r13)])
    (.seq (.call wotsName (Wots.wotsLeaves4 L t4name t4))
      (.block [.mov .rax (.mem (var 0)), .alu .add .rax (.imm 4), .store (var 0) .rax,
        .alu .cmp .rax (.imm (BitVec.ofNat 32 (2 ^ hp)))]))

/-- The heights: `levels` from the `2^h′` leaves, the authentication path at
`sig + len·n`, zeroed first. -/
def heights : Prog isa :=
  .seq (.block ([.mov .r10 (.reg .r13), .alu .add .r10 (.imm (BitVec.ofNat 32 (L.len * L.n))), .mov32 .rax (.imm 0)] ++
      (List.range (hp * L.n / 8)).map (fun w => .store (at_ .r10 (8 * w)) .rax) ++
      Tree.setParams (.imm 0) (.imm 0) (.imm 2) (.imm 0) ++
      [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 Layout.oN)),
        .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ hp))), .mov32 .rcx (.imm 0), .mov .r8 (.reg .r10),
        .mov .r9 (.reg .r12)]))
    (.call levelsName (Tree.levels L t4name t4))

/-- `xmssTree` for trees of height `h′`. -/
def xmssTree : Prog isa :=
  .seq (.block (pro ++ digits L))
    (.seq (.loop (leafBody L hp t4name wotsName t4) .ne)
      (.seq (heights L hp t4name levelsName t4)
        (.block (copyWords .r15 0 .rbx Layout.oN (L.n / 8) ++ restoreRegs 1))))

end VG.Impl.SlhDsa.X86_64.Xmss
