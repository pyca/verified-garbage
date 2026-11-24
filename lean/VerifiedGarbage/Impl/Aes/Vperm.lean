module

/-!
# AES by vector permutations: the tables

Sixteen-byte tables that a four-bit index selects from with a byte shuffle
(AArch64's `tbl` of one register, x86's `pshufb`), and the shuffles of the
bytes of a state, for the cipher and, in `Dec`, the inverse cipher
(`AArch64/Vperm.lean`, which says how they are used, and `X86/Vperm.lean`).
Byte `i` of a table is the table's value at `i`; a value of `0x80` is an
index for which both shuffles give 0.
-/

@[expose] public section

namespace VG.Impl.Aes.Vperm

/-- `0x0f` in every byte: the mask of a byte's low four bits. -/
def mask : BitVec 128 := 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
/-- `1 / ·` in the subfield, `0x80` for 0. -/
def inv : BitVec 128 := 0x040703090a0b0c020e05060f0d080180
/-- `a / ·` in the subfield, `0x80` for 0. -/
def inva : BitVec 128 := 0x0f09060305070e040a0d0b080c010280
/-- `L (sbox x ⊕ 0x63)`, as the XOR of `sb1u` at `io` and `sb1t` at `jo`. -/
def sb1u : BitVec 128 := 0x62cdaf73dc8e43fdbe309fec11215200
def sb1t : BitVec 128 := 0xf12cdd518c4569147d38e5b4a098c900
/-- `L (2 • (sbox x ⊕ 0x63))`, as the XOR of `sb2u` at `io` and `sb2t` at `jo`. -/
def sb2u : BitVec 128 := 0x05dbde24fac219e6ff3de3c7211c3800
def sb2t : BitVec 128 := 0xce03cd66abc3c0a565a66b0da80e6800
/-- ShiftRows, as the indices of a `tbl`: byte `t` of the result is byte
`t mod 4 + 4 ((t / 4 + t mod 4) mod 4)` of the state. -/
def sr : BitVec 128 := 0x0b06010c07020d08030e09040f0a0500
/-- ShiftRows, then each column rotated by one byte. -/
def rsr : BitVec 128 := 0x0c0b06010807020d04030e09000f0a05
/-- ShiftRows, then each column rotated by three bytes. -/
def r3sr : BitVec 128 := 0x06010c0b020d08070e0904030a05000f
/-- Each column rotated by one byte. -/
def rot : BitVec 128 := 0x0c0f0e0d080b0a090407060500030201
/-- `L` of a byte's low four bits. -/
def keyLo : BitVec 128 := 0x34350302e4e5d3d2e6e7d1d036370100
/-- `L` of a byte's high four bits, XORed with `L 0x63`. -/
def keyHi : BitVec 128 := 0x45fe3e85fa41813a8d36f64d328949f2
/-- `sbox x ⊕ 0x63`, as the XOR of `sbou` at `io` and `sbot` at `jo`. -/
def sbou : BitVec 128 := 0xa5d17490e41ecf8e415f2bbb356afa00
def sbot : BitVec 128 := 0x6e8be5f7129318647cef0afd99768100
/-- `0x63` in every byte. -/
def c63 : BitVec 128 := 0x63636363636363636363636363636363

namespace Dec

/-- `D` of the product by `0e`, `0b`, `0d` and `09` of the inverse S-box of
`x`, less `D 0`: the XOR of `x‹n›u` at `io` and `x‹n›t` at `jo`. -/
def x0u : BitVec 128 := 0xb7f64126678c7aaad05c1d3b91cdeb00
def x0t : BitVec 128 := 0xf92ad316c53218243c0eddcbefe1f700
def x1u : BitVec 128 := 0x4191d07aaa5ccd26ebb7671d3b8cf600
def x1t : BitVec 128 := 0xd3ef3c18240ee116f7f9c5ddcb322a00
def x2u : BitVec 128 := 0x8ebe30dcecc07e1c62a2924e52f02c00
def x2t : BitVec 128 := 0x45a8ed0fe2ea42e5a74da0af4a070800
def x3u : BitVec 128 := 0x1a978d70fd9e09eee779f4846a136300
def x3t : BitVec 128 := 0xc8c20a060c935195c4575d5bce999f00
/-- InvShiftRows, then each column rotated by `n` bytes, as the indices of
a `tbl`. -/
def p0 : BitVec 128 := 0x0306090c0f0205080b0e0104070a0d00
def p1 : BitVec 128 := 0x0c030609080f0205040b0e0100070a0d
def p2 : BitVec 128 := 0x090c030605080f0201040b0e0d00070a
def p3 : BitVec 128 := 0x06090c030205080f0e01040b0a0d0007
/-- `D` of the product by `0e`, `0b`, `0d` and `09` of a byte, less `D 0`
but for the first: the XOR of `y‹n›l` at its low four bits and `y‹n›h` at
its high four. -/
def y0l : BitVec 128 := 0xb78f4f778bb3734bfcc4043cc0f83800
def y0h : BitVec 128 := 0x0d8f4ac80a884dcf139154d6149653d1
def y1l : BitVec 128 := 0x418b29e3b67cde14559f3df7a268ca00
def y1h : BitVec 128 := 0x7edbff5a943115b0ce6b4fea2481a500
def y2l : BitVec 128 := 0x8e4f7dbc29e8da1b955466a732f3c100
def y2h : BitVec 128 := 0x169b79f4ff72901d0b8664e9e26f8d00
def y3l : BitVec 128 := 0x1a73dab3deb71e776d04adc4a9c06900
def y3h : BitVec 128 := 0x559c905915dcd0194c8589400cc5c900
/-- Each column rotated by two and by three bytes. -/
def rot2 : BitVec 128 := 0x0d0c0f0e09080b0a0504070601000302
def rot3 : BitVec 128 := 0x0e0d0c0f0a09080b0605040702010003
/-- `D` of a byte: the XOR of `dl` at its low four bits and `dh` at its
high four. -/
def dl : BitVec 128 := 0x6238c19bca906933510bf2a8f9a35a00
def dh : BitVec 128 := 0x30535c3f7417187b9af9f695debdb2d1
/-- The inverse S-box of `x`: the XOR of `dbou` at `io` and `dbot` at `jo`. -/
def dbou : BitVec 128 := 0x0f595681d74b12cad893c5448e1d9c00
def dbot : BitVec 128 := 0x34a99dad305ff6f2045bc66b99c26f00

end Dec

end VG.Impl.Aes.Vperm
