import VerifiedGarbage.TCB.X86_64.Print

/-!
# Semantics tests for the x86-64 `EVEX.512` forms on `zmm0`–`zmm31`

Each expected value was computed on an x86-64 CPU with AVX-512F (an Intel
Xeon, Ice Lake), by the same instruction in C inline assembly, with its
operands both in `zmm16`–`zmm31` and in `zmm0`–`zmm15` (`EZOp`, `ezLoad`,
`ezStore`): the unmasked `EVEX.512` VPADDQ, VPXORQ, VPANDQ and VPORQ,
VPTERNLOGQ (the destination also a source), VPRORQ by an immediate (counts
of 64 and more reduced modulo 64), and VMOVDQU64 loads and stores at
unaligned addresses. Each is compared with the model's result on the same
inputs, read from the state's fields directly (`xmm`, `ymmHi`, `zmmHi` for
`zmm0`–`zmm15`, `ymmH` and `zmmHiH` for `zmm16`–`zmm31`), not through
`State.vz`, so that the test does not rely on the model's own accessors.
-/

namespace VG.Test.Evex512

open X86_64


def A : BitVec 512 := 0x0badf00dfeedfacedeadbeef00c0ffee8899aabbccddeeff44556677001122330f1e2d3c4b5a6978c3d2e1f08796a5b489abcdef01234567fedcba9876543210#512
def B : BitVec 512 := 0x0f0f0f0ff0f0f0f05555aaaa3333ccccf0e1d2c3b4a5968713579bdf2468ace00123456789abcdefdeadbeefcafebabe800000007fffffffffffffff12345678#512
/-- `A + B` by quadwords (`vpaddq`). -/
def C : BitVec 512 := 0x1abcff1defdeebbe3403699933f4ccba797b7d7f8183858657ad02562479cf13104172a3d5063767a280a0e05295607209abcdef81234566fedcba9788888888#512

/-- A state with `A` in `zmm3` and `zmm17`, `B` in `zmm1` and `zmm22`, `C` in
`zmm6` and `zmm28`, and the 64 bytes of `A` at address `0x101`, readable,
and 64 bytes at `0x203` writable. -/
def s : State where
  gpr r := if r = .rdi then 0x100 else 0
  cf := none
  zf := none
  sf := none
  of := none
  xmm r := if r = .xmm3 then A.extractLsb' 0 128 else if r = .xmm1 then B.extractLsb' 0 128
    else if r = .xmm6 then C.extractLsb' 0 128 else 0
  ymmHi r := if r = .xmm3 then A.extractLsb' 128 128 else if r = .xmm1 then B.extractLsb' 128 128
    else if r = .xmm6 then C.extractLsb' 128 128 else 0
  zmmHi r := if r = .xmm3 then A.extractLsb' 256 256 else if r = .xmm1 then B.extractLsb' 256 256
    else if r = .xmm6 then C.extractLsb' 256 256 else 0
  ymmH r := if r = .xmm17 then A.extractLsb' 0 256 else if r = .xmm22 then B.extractLsb' 0 256
    else if r = .xmm28 then C.extractLsb' 0 256 else 0
  zmmHiH r := if r = .xmm17 then A.extractLsb' 256 256 else if r = .xmm22 then B.extractLsb' 256 256
    else if r = .xmm28 then C.extractLsb' 256 256 else 0
  mem addr := if 0x101 ≤ addr.toNat ∧ addr.toNat < 0x141 then
    A.extractLsb' (8 * (addr.toNat - 0x101)) 8 else 0
  rd := [⟨0x101, 64⟩]
  wr := [⟨0x203, 64⟩]

/-- `zmm0`–`zmm15` register `r` of `t`, from its fields. -/
def lo (t : State) (r : XReg) : BitVec 512 := t.zmmHi r ++ t.ymmHi r ++ t.xmm r

/-- `zmm16`–`zmm31` register `r` of `t`, from its fields. -/
def hi (t : State) (r : HReg) : BitVec 512 := t.zmmHiH r ++ t.ymmH r

#guard lo s .xmm3 == A && hi s .xmm17 == A && lo s .xmm1 == B && hi s .xmm22 == B
#guard lo s .xmm6 == C && hi s .xmm28 == C

/-! `op zmm25, zmm17, zmm1` and `op zmm4, zmm3, zmm22`. -/

/-- `zmm25` after `op zmm25, zmm17, zmm1`, and `zmm4` after `op zmm4, zmm3, zmm22`. -/
def bin (op : EBinOp) : BitVec 512 × BitVec 512 :=
  (hi ((EZOp.bin op (.hi .xmm25) (.hi .xmm17) (.lo .xmm1)).exec s) .xmm25,
    lo ((EZOp.bin op (.lo .xmm4) (.lo .xmm3) (.hi .xmm22)).exec s) .xmm4)

#guard bin .vpaddq == (0x1abcff1defdeebbe3403699933f4ccba797b7d7f8183858657ad02562479cf13104172a3d5063767a280a0e05295607209abcdef81234566fedcba9788888888#512,
  0x1abcff1defdeebbe3403699933f4ccba797b7d7f8183858657ad02562479cf13104172a3d5063767a280a0e05295607209abcdef81234566fedcba9788888888#512)
#guard bin .vpxorq == (0x04a2ff020e1d0a3e8bf8144533f3332278787878787878785702fda824798ed30e3d685bc2f1a4971d7f5f1f4d681f0a09abcdef7edcba980123456764606468#512,
  0x04a2ff020e1d0a3e8bf8144533f3332278787878787878785702fda824798ed30e3d685bc2f1a4971d7f5f1f4d681f0a09abcdef7edcba980123456764606468#512)
#guard bin .vpandq == (0x0b0d000df0e0f0c05405aaaa0000cccc8081828384858687005502570000202001020524090a4968c280a0e08296a0b48000000001234567fedcba9812141210#512,
  0x0b0d000df0e0f0c05405aaaa0000cccc8081828384858687005502570000202001020524090a4968c280a0e08296a0b48000000001234567fedcba9812141210#512)
#guard bin .vporq == (0x0fafff0ffefdfafedffdbeef33f3ffeef8f9fafbfcfdfeff5757ffff2479aef30f3f6d7fcbfbedffdfffffffcffebfbe89abcdef7fffffffffffffff76747678#512,
  0x0fafff0ffefdfafedffdbeef33f3ffeef8f9fafbfcfdfeff5757ffff2479aef30f3f6d7fcbfbedffdfffffffcffebfbe89abcdef7fffffffffffffff76747678#512)

/-! `vpternlogq zmm28, zmm17, zmm22, imm8` and `vpternlogq zmm6, zmm22, zmm3,
imm8`, the destination holding `C`: a selection (`0xca`), a parity (`0x96`),
a majority (`0xe8`), single minterms (`0x01`, `0x80`) and `0xd2`. -/

/-- `zmm28` after `vpternlogq zmm28, zmm17, zmm22, imm`, and `zmm6` after
`vpternlogq zmm6, zmm22, zmm3, imm`. -/
def tern (imm : BitVec 8) : BitVec 512 × BitVec 512 :=
  (hi ((EZOp.vpternlogq (.hi .xmm28) (.hi .xmm17) (.hi .xmm22) imm).exec s) .xmm28,
    lo ((EZOp.vpternlogq (.lo .xmm6) (.hi .xmm22) (.lo .xmm3) imm).exec s) .xmm6)

#guard tern 0xca == (0x0faff00ffeecface5555aaab00c3ccee8899aabbb4a5968744579bdf001122f30122256449abe9e8deadbeef8afebabc89abcdef7ffffffffffffff812345670#512,
  0x0b0d0f0df0f1f0f0deadbeee3330ffccf0e1d2c3ccddeeff135566772468ac200f1f4d3f8b5a4d7fc3d2e1f0c796a5b68000000001234567fedcba9f76543218#512)
#guard tern 0x96 == (0x1e1e001fe1c3e180bffb7ddc0007ff9801030507f9fbfdfe00affffe000041c01e7c1af817f793f0bfffffff1ffd7f7800000000fffffffefffffff0ece8ece0#512,
  0x1e1e001fe1c3e180bffb7ddc0007ff9801030507f9fbfdfe00affffe000041c01e7c1af817f793f0bfffffff1ffd7f7800000000fffffffefffffff0ece8ece0#512)
#guard tern 0xe8 == (0x0badff0dfefcfafe5405aaab33f0cceef8f9fafb84858687575502572479ae3301036527c90a6d6fc280a0e0c296a0b689abcdef01234567fedcba9f12141218#512,
  0x0badff0dfefcfafe5405aaab33f0cceef8f9fafb84858687575502572479ae3301036527c90a6d6fc280a0e0c296a0b689abcdef01234567fedcba9f12141218#512)
#guard tern 0x01 == (0xe04000e00000040100000000cc0800010604000002000000a8000000db86100ce080800020000000000000002000000176543210000000000000000001030107#512,
  0xe04000e00000040100000000cc0800010604000002000000a8000000db86100ce080800020000000000000002000000176543210000000000000000001030107#512)
#guard tern 0x80 == (0x0a0c000de0c0e080140128880000cc880001000380818486000502560000000000000020010201608280a0e0029420300000000001234566fedcba9000000000#512,
  0x0a0c000de0c0e080140128880000cc880001000380818486000502560000000000000020010201608280a0e0029420300000000001234566fedcba9000000000#512)
#guard tern 0xd2 == (0x1ebef01fefceeb8e3553699900c7ccba091b2d3fb1a3958644af9bde001143d3106032e055a7b3e0beadbeef1afd7a7809abcdeffffffffefffffff088a8cce0#512,
  0x1a1c0f1de1d3e1b0beab7ddc3334ff9871635547c9dbedfe13ad66762468cd001e5d5abb97561777a3d2e1f0579565720000000081234566fedcba97ecc8a888#512)

/-! `vprorq zmm30, zmm17, n` and `vprorq zmm29, zmm3, n`. -/

/-- `zmm30` after `vprorq zmm30, zmm17, n`, and `zmm29` after `vprorq zmm29, zmm3, n`. -/
def ror (n : BitVec 8) : BitVec 512 × BitVec 512 :=
  (hi ((EZOp.vprorq (.hi .xmm30) (.hi .xmm17) n).exec s) .xmm30,
    hi ((EZOp.vprorq (.hi .xmm29) (.lo .xmm3) n).exec s) .xmm29)

#guard ror 0 == (0x0badf00dfeedfacedeadbeef00c0ffee8899aabbccddeeff44556677001122330f1e2d3c4b5a6978c3d2e1f08796a5b489abcdef01234567fedcba9876543210#512,
  0x0badf00dfeedfacedeadbeef00c0ffee8899aabbccddeeff44556677001122330f1e2d3c4b5a6978c3d2e1f08796a5b489abcdef01234567fedcba9876543210#512)
#guard ror 1 == (0x05d6f806ff76fd676f56df7780607ff7c44cd55de66ef77fa22ab33b80089119078f169e25ad34bc61e970f843cb52dac4d5e6f78091a2b37f6e5d4c3b2a1908#512,
  0x05d6f806ff76fd676f56df7780607ff7c44cd55de66ef77fa22ab33b80089119078f169e25ad34bc61e970f843cb52dac4d5e6f78091a2b37f6e5d4c3b2a1908#512)
#guard ror 7 == (0x9c175be01bfddbf5ddbd5b7dde0181ffff1133557799bbdd6688aaccee002244f01e3c5a7896b4d26987a5c3e10f2d4bcf13579bde02468a21fdb97530eca864#512,
  0x9c175be01bfddbf5ddbd5b7dde0181ffff1133557799bbdd6688aaccee002244f01e3c5a7896b4d26987a5c3e10f2d4bcf13579bde02468a21fdb97530eca864#512)
#guard ror 38 == (0x37fbb7eb382eb7c0bc0303ffbb7ab6fbef3377bbfe2266aadc004488cd115599f12d69a5e03c78b4c21e5a96d30f4b87bc048d159e26af3761d950c843fb72ea#512,
  0x37fbb7eb382eb7c0bc0303ffbb7ab6fbef3377bbfe2266aadc004488cd115599f12d69a5e03c78b4c21e5a96d30f4b87bc048d159e26af3761d950c843fb72ea#512)
#guard ror 63 == (0x175be01bfddbf59cbd5b7dde0181ffdd1133557799bbddff88aaccee002244661e3c5a7896b4d2f087a5c3e10f2d4b6913579bde02468acffdb97530eca86421#512,
  0x175be01bfddbf59cbd5b7dde0181ffdd1133557799bbddff88aaccee002244661e3c5a7896b4d2f087a5c3e10f2d4b6913579bde02468acffdb97530eca86421#512)
#guard ror 64 == (0x0badf00dfeedfacedeadbeef00c0ffee8899aabbccddeeff44556677001122330f1e2d3c4b5a6978c3d2e1f08796a5b489abcdef01234567fedcba9876543210#512,
  0x0badf00dfeedfacedeadbeef00c0ffee8899aabbccddeeff44556677001122330f1e2d3c4b5a6978c3d2e1f08796a5b489abcdef01234567fedcba9876543210#512)
#guard ror 65 == (0x05d6f806ff76fd676f56df7780607ff7c44cd55de66ef77fa22ab33b80089119078f169e25ad34bc61e970f843cb52dac4d5e6f78091a2b37f6e5d4c3b2a1908#512,
  0x05d6f806ff76fd676f56df7780607ff7c44cd55de66ef77fa22ab33b80089119078f169e25ad34bc61e970f843cb52dac4d5e6f78091a2b37f6e5d4c3b2a1908#512)
#guard ror 200 == (0xce0badf00dfeedfaeedeadbeef00c0ffff8899aabbccddee3344556677001122780f1e2d3c4b5a69b4c3d2e1f08796a56789abcdef01234510fedcba98765432#512,
  0xce0badf00dfeedfaeedeadbeef00c0ffff8899aabbccddee3344556677001122780f1e2d3c4b5a69b4c3d2e1f08796a56789abcdef01234510fedcba98765432#512)

/-! `vmovdqu64 zmm29, ZMMWORD PTR [rdi+1]` and `vmovdqu64 zmm4, ZMMWORD PTR
[rdi+1]`, of the 64 bytes of `A` at `0x101`, and `vmovdqu64 ZMMWORD PTR
[rdi+0x103], zmm22`, of `B` to `0x203`: on the CPU, the 64 bytes stored are
those read back from the store's address, the bytes around it unchanged. -/

#guard (exec (.ezLoad (.hi .xmm29) { base := .rdi, disp := 1 }) s).map (hi · .xmm29) == some A
#guard (exec (.ezLoad (.lo .xmm4) { base := .rdi, disp := 1 }) s).map (lo · .xmm4) == some A
#guard (exec (.ezLoad (.hi .xmm29) { base := .rdi, disp := 2 }) s).isNone
#guard (exec (.ezStore { base := .rdi, disp := 0x103 } (.hi .xmm22)) s).map
    (·.mem.readW 0x203 512) == some 0x0f0f0f0ff0f0f0f05555aaaa3333ccccf0e1d2c3b4a5968713579bdf2468ace00123456789abcdefdeadbeefcafebabe800000007fffffffffffffff12345678#512
#guard (exec (.ezStore { base := .rdi, disp := 0x103 } (.lo .xmm1)) s).map
    (·.mem.readW 0x203 512) == some B
#guard (exec (.ezStore { base := .rdi, disp := 0x104 } (.hi .xmm22)) s).isNone
#guard addrs (.ezLoad (.hi .xmm29) { base := .rdi, disp := 1 }) s == [0x101]
#guard addrs (.ezop (.vprorq (.hi .xmm30) (.lo .xmm3) 1)) s == []

/-! What the printer emits, as the assembler takes it. -/

#guard printer.instr (.ezop (.bin .vpxorq (.hi .xmm25) (.hi .xmm17) (.lo .xmm1))) ==
  ["vpxorq zmm25, zmm17, zmm1"]
#guard printer.instr (.ezop (.vpternlogq (.lo .xmm6) (.hi .xmm22) (.lo .xmm3) 150)) ==
  ["vpternlogq zmm6, zmm22, zmm3, 150"]
#guard printer.instr (.ezop (.vprorq (.hi .xmm30) (.hi .xmm17) 63)) == ["vprorq zmm30, zmm17, 63"]
#guard printer.instr (.ezLoad (.hi .xmm29) { base := .rdi, disp := 64 }) ==
  ["vmovdqu64 zmm29, ZMMWORD PTR [rdi+64]"]
#guard printer.instr (.ezStore { base := .rcx } (.lo .xmm4)) == ["vmovdqu64 ZMMWORD PTR [rcx], zmm4"]
#guard (Instr.ezop (.vprorq (.hi .xmm30) (.hi .xmm17) 63)).requires == ["avx512f"]
#guard (Instr.ezLoad (.hi .xmm29) { base := .rdi }).requires == ["avx512f"]

end VG.Test.Evex512
