import VerifiedGarbage.TCB.X86_64.Print

/-!
# High-register EVEX.512 AES semantics

Expected results were computed on an AMD EPYC 9V74 with AVX512F and VAES,
using GCC's `_mm512_aesenc_epi128`, `_mm512_aesenclast_epi128`,
`_mm512_xor_si512` and `_mm512_broadcast_i32x4` intrinsics. Input byte `i`
is `i` in A and `255-i` in B. Distinct lanes catch lane duplication and
ordering mistakes. These are ISA-model tests, not algorithm test vectors.
-/

namespace VG.Test.HighAes
open X86_64

def A : BitVec 512 := 0x3f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100#512
def B : BitVec 512 := 0xc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff#512
def enc : BitVec 512 := 0xfbda51bbe6167019dde2f8bc3cdb1393b0a0b12b404b2b935a42c854eebb361bdf9b07b59e6ea868a1a4486cc97aabe9acd06ed495a82f47a9ca97d7b9a19495#512
def last : BitVec 512 := 0x22c405285ee6e1c00b7bd8d3b94d58cb21262fa218460ee3fee87fedc938e1684fa6607f142c424a959b3e112c4fb725db9e8e0d318221c78352fb098a9a959c#512
def broadcast : BitVec 512 := 0xf0f1f2f3f4f5f6f7f8f9fafbfcfdfefff0f1f2f3f4f5f6f7f8f9fafbfcfdfefff0f1f2f3f4f5f6f7f8f9fafbfcfdfefff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff#512

def hs : List HReg := [.xmm16, .xmm17, .xmm18, .xmm19, .xmm20, .xmm21,
  .xmm22, .xmm23, .xmm24, .xmm25, .xmm26, .xmm27, .xmm28, .xmm29, .xmm30, .xmm31]

def s : State where
  gpr r := if r = .rdi then 0x101 else 0xabcdef
  cf := some true
  zf := some false
  sf := some true
  of := some false
  xmm _ := A.extractLsb' 0 128
  ymmHi _ := A.extractLsb' 128 128
  zmmHi _ := A.extractLsb' 256 256
  ymmH _ := B.extractLsb' 0 256
  zmmHiH _ := B.extractLsb' 256 256
  mem addr := B.extractLsb' (8 * (addr.toNat - 0x101)) 8
  rd := [⟨0x101, 16⟩]
  wr := []

def high (t : State) (r : HReg) : BitVec 512 := t.zmmHiH r ++ t.ymmH r

-- Only the selected high source contains B; reading another register must fail.
def selected (h : HReg) : State :=
  {s with
    ymmH := fun r => if r = h then s.ymmH r else 0
    zmmHiH := fun r => if r = h then s.zmmHiH r else 0}

#guard hs.all fun h => high s h == B &&
  (List.range 4).all fun i => s.zlaneH h i == B.extractLsb' (128*i) 128

-- Every high source, separate destination and destination/source aliasing.
#guard hs.all fun h => [XReg.xmm0, .xmm15].all fun d =>
  ((ZOp.zbinH .vaesenc d .xmm0 h).exec (selected h)).zmm d == enc &&
  ((ZOp.zbinH .vaesenclast d .xmm0 h).exec (selected h)).zmm d == last &&
  ((ZOp.zbinH .vpxord d .xmm0 h).exec (selected h)).zmm d == -1

-- Sources, unrelated registers, flags and memory are preserved.
#guard hs.all fun h =>
  let t := (ZOp.zbinH .vaesenc .xmm0 .xmm0 h).exec s
  hs.all (fun r => high t r == B) && t.zmm .xmm1 == A &&
    t.gpr .rsp == s.gpr .rsp && t.cf == s.cf && t.zf == s.zf &&
    t.sf == s.sf && t.of == s.of && t.mxcsr == s.mxcsr &&
    t.mem 0x101 == s.mem 0x101 && t.rd == s.rd && t.wr == s.wr

-- The broadcast reads exactly sixteen bytes, even at an unaligned address.
#guard hs.all fun h =>
  match exec (.vbroadcasti32x4H h {base := .rdi}) s with
  | none => false
  | some t => high t h == broadcast && t.zmm .xmm0 == A &&
      hs.all (fun r => r == h || high t r == B) &&
      t.gpr .rdi == s.gpr .rdi && t.cf == s.cf && t.mxcsr == s.mxcsr
#guard (exec (.vbroadcasti32x4H .xmm31 {base := .rdi}) {s with rd := []}).isNone
#guard (exec (.vbroadcasti32x4H .xmm31 {base := .rdi}) {s with rd := [⟨0x101, 15⟩]}).isNone
#guard addrs (.vbroadcasti32x4H .xmm31 {base := .rdi}) s == [0x101]
#guard addrs (.zop (.zbinH .vaesenc .xmm0 .xmm0 .xmm31)) s == []
#guard hs.all fun h => !isa.writesSp (.vbroadcasti32x4H h {base := .rsp}) &&
  !isa.writesSp (.zop (.zbinH .vaesenc .xmm0 .xmm0 h))

-- EVEX.256 and EVEX.128 writes clear the newly modelled upper half.
#guard hs.all fun h =>
  let t := s.setVy (.hi h) 7
  t.ymmH h == 7 && t.zmmHiH h == 0 && t.zmm .xmm0 == A &&
    hs.all (fun r => r == h || high t r == B)
#guard hs.all fun h => high ((EOp.vmovq (.hi h) .rax).exec s) h == 0xabcdef
-- VZEROUPPER and low-register writes leave all sixteen high registers intact.
#guard hs.all fun h => high (VOp.vzeroupper.exec s) h == B &&
  high (s.setV .l128 .xmm0 0 0) h == B && high (s.setVy (.lo .xmm0) 0) h == B

#guard hs.all fun h =>
  (Instr.vbroadcasti32x4H h {base := .rdi}).requires == ["avx512f"] &&
  (Instr.zop (.zbinH .vpxord .xmm0 .xmm0 h)).requires == ["avx512f"] &&
  (Instr.zop (.zbinH .vaesenc .xmm0 .xmm0 h)).requires == ["vaes", "avx512f"] &&
  (Instr.zop (.zbinH .vaesenclast .xmm0 .xmm0 h)).requires == ["vaes", "avx512f"]
#guard (Instr.vbroadcasti32x4H .xmm31 {base := .rdi}).asm ==
  ["vbroadcasti32x4 zmm31, XMMWORD PTR [rdi]"]
#guard (Instr.zop (.zbinH .vaesenc .xmm15 .xmm0 .xmm16)).asm ==
  ["vaesenc zmm15, zmm0, zmm16"]
#guard (Instr.zop (.zbinH .vaesenclast .xmm0 .xmm0 .xmm31)).asm ==
  ["vaesenclast zmm0, zmm0, zmm31"]
#guard (Instr.zop (.zbinH .vpxord .xmm0 .xmm0 .xmm16)).asm ==
  ["vpxord zmm0, zmm0, zmm16"]

end VG.Test.HighAes
