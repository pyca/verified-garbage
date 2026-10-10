import VerifiedGarbage.Impl.Seed.Layers

/-!
# `G` on 32-bit words: the constants of its last layer

Untrusted. The 32-bit targets compute `G` of eight words at once, bitsliced
in eight 32-bit planes (`Impl/Seed/<Target>/G8.lean`): each word's four
S-box outputs are then mixed as RFC 4269 §2.2 mixes them,
`Z = ⊕ᵣ rotr₃₂(s, 8r) & Mᵣ`, and the constant that `0xE7` and `0x2B`
contribute is XORed in. These are the masks `Mᵣ` and the constant, and the
masks that pick the bytes `X0` and `X2` (`S0`) or `X1` and `X3` (`S1`) of
each word.
-/

namespace VG.Impl.Seed.W32

/-- RFC 4269 §2.2's masks, by index. -/
def gMask : Nat → BitVec 8
  | 0 => 0xFC | 1 => 0xF3 | 2 => 0xCF | _ => 0x3F

/-- `Mᵣ`: byte `j` of the rotation by `8r` is byte `j + r` of the S-box
outputs, which `G` masks with `m_{(2j + r) mod 4}`. -/
def mixMask (r : Nat) : BitVec 32 :=
  gMask ((6 + r) % 4) ++ gMask ((4 + r) % 4) ++ gMask ((2 + r) % 4) ++ gMask (r % 4)

/-- The constant part of `G`: its mixing of the S-boxes' constants
`0xE7, 0x2B, 0xE7, 0x2B`. -/
def gConst32 : BitVec 32 := 0xE72BE72B

/-- The bit positions of the bytes `X0` and `X2` of each word, once
transposed (`S0`). The others are those of `X1` and `X3` (`S1`). -/
def laneMask0 : BitVec 32 := 0x00FF00FF

end VG.Impl.Seed.W32
