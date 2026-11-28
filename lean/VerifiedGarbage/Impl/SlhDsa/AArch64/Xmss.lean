module

public import VerifiedGarbage.Impl.SlhDsa.AArch64.Wots
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Tree

/-!
# SLH-DSA (SHAKE) on AArch64: an XMSS tree

`xmssTree(scratch = x0, idx = x1, sig = x2)`, as on x86-64
(`Impl/SlhDsa/X86_64/Xmss.lean`): it computes the XMSS tree of height `h′`
whose layer and tree addresses, and `PK.seed`, the caller has put in the
lanes `A` and `B`: its root (`xmss_node(SK.seed, 0, h′, PK.seed, ADRS)`,
Algorithm 9) to the `n` bytes at `oMsg`, and the XMSS signature
(`xmss_sign`, Algorithm 10) by the key pair `idx` of the `n` bytes that were
there, its WOTS⁺ signature and its authentication path, to the
`(len + h′)·n` bytes at `sig`. For `idx ≥ 2^h′` (key generation) the
signature's bytes are unspecified.

It computes the `len` base-16 digits of `msg` and of its checksum
(`wotsDigits`, lines 1–7 of Algorithm 7) at `oDigits`; the `2^h′` leaves,
four at a time (`wotsLeaves4`), to the nodes at `oN`, which also writes the
WOTS⁺ signature; then the heights of the tree and its authentication path
(`levels`, with the type `TREE` and the key pair address 0), the root the
first node.

Registers: `x19` = `scratch`, `x20` = `idx`, `x21` = `sig`, `x22` = the key
pair of the next group of leaves (public, so in a register, where x86-64
keeps it in frame 1); saved in frame 1 with `x30`.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.AArch64.Xmss

open VG.AArch64
open VG.Impl.SlhDsa.AArch64.Thash4 (mov)

variable (L : Layout) (hp : Nat) (t4name wotsName levelsName : String) (t4 : Prog isa)

/-- The registers saved in frame 1. -/
def saved : List Reg := [.x19, .x20, .x21, .x22, .x30]

def pro : List Instr := saveRegs 1 .x0 saved ++ [mov .x19 .x0, mov .x20 .x1, mov .x21 .x2]

/-- The digits of byte `b` of `msg`, its high and its low half, to digits
`2b` and `2b + 1`; their sum added to `x12` (`x11` = 15). -/
def digitByte (b : Nat) : List Instr :=
  [.ldrb .x9 .x19 (Layout.oMsg + b), .lsr .x .x10 .x9 4, .logic .and .x .x9 .x9 .x11,
    .strb .x10 .x19 (Layout.oDigits + 2 * b), .strb .x9 .x19 (Layout.oDigits + 2 * b + 1),
    .add .x .x12 .x12 .x10, .add .x .x12 .x12 .x9]

/-- The digits: those of `msg`, then the three of the checksum
`csum = Σ (15 - digit)`: `toByte(csum ≪ 4, 2)` in base 16, its first three
digits, `csum ≫ 8`, `(csum ≫ 4) ∧ 15` and `csum ∧ 15`. -/
def digits : List Instr :=
  [.movz .x .x12 0 0, .movz .x .x11 15 0] ++ (List.range L.n).flatMap digitByte ++
  [.movz .x .x13 (BitVec.ofNat 16 (15 * 2 * L.n)) 0, .sub .x .x13 .x13 .x12,
    .lsr .x .x10 .x13 8, .logic .and .x .x10 .x10 .x11, .strb .x10 .x19 (Layout.oDigits + 2 * L.n),
    .lsr .x .x10 .x13 4, .logic .and .x .x10 .x10 .x11, .strb .x10 .x19 (Layout.oDigits + 2 * L.n + 1),
    .logic .and .x .x10 .x13 .x11, .strb .x10 .x19 (Layout.oDigits + 2 * L.n + 2)]

/-- A group of four leaves: `wotsLeaves4` on the key pairs from `x22`; then
the next, with `x9 = 0` after the last. -/
def leafBody : Prog isa :=
  .seq (.block [mov .x0 .x19, mov .x1 .x22, mov .x2 .x20, mov .x3 .x21])
    (.seq (.call wotsName (Wots.wotsLeaves4 L t4name t4))
      (.block [.addImm .x .x22 .x22 4, .subImm .x .x9 .x22 (2 ^ hp)]))

/-- The heights: `levels` from the `2^h′` leaves, the authentication path at
`sig + len·n`, zeroed first. -/
def heights : Prog isa :=
  .seq (.block ([.addImm .x .x10 .x21 (L.len * L.n)] ++ zeroWords .x10 0 (hp * L.n / 8) ++
      Tree.setParams (.imm 0) (.imm 0) (.imm 2) (.imm 0) ++
      [mov .x0 .x19] ++ lea .x1 .x19 Layout.oN ++ movV .x2 (2 ^ hp) ++
      [.movz .x .x3 0 0, mov .x4 .x10, mov .x5 .x20]))
    (.call levelsName (Tree.levels L t4name t4))

/-- `xmssTree` for trees of height `h′`. -/
def xmssTree : Prog isa :=
  .seq (.block (pro ++ digits L ++ [.movz .x .x22 0 0]))
    (.seq (.loop (leafBody L hp t4name wotsName t4) (.nonzero .x .x9))
      (.seq (heights L hp t4name levelsName t4)
        (.block (copyWords .x19 Layout.oMsg .x19 Layout.oN (L.n / 8) ++ restoreRegs 1 saved))))

end VG.Impl.SlhDsa.AArch64.Xmss
