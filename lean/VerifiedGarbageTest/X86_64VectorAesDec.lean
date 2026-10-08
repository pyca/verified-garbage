import VerifiedGarbageTest.X86_64VectorGcm

/-!
# Vector AES decryption instruction tests

The expected values were computed on an Intel Xeon with VAES and AVX-512F
by the instructions themselves: `_mm512_aesdec_epi128` and
`_mm512_aesdeclast_epi128` (EVEX.512 `vaesdec`, `vaesdeclast`) on `Avx512.A`
and `Avx512.B`, whose low halves `_mm256_aesdec_epi128` and
`_mm256_aesdeclast_epi128` (VEX.256) and, lane by lane, the legacy
`_mm_aesdec_si128` and `_mm_aesdeclast_si128` reproduce. (The same program
reproduces `VectorGcm.aesRound` with `_mm_aesenc_si128`.)
-/

namespace VG.Test.VectorAesDec

open X86_64
open VG.Test.VectorGcm (checkV checkZ)

def aesDecRound : BitVec 512 := 0xb5b0b21a2383891e14d28a44c09f3628e8aed19587ad9b22555dff9c74ef21413ad948b7bc322647c518769236531d01fafbac38e6a5c5c37f30df5470d1274c#512
def aesDecLast : BitVec 512 := 0x5d171bfc6eefaa1c594dd7cbaf60db5576024b3d234802fa34ae48b976a1cee2eb5ca10a729e2d2e124497f8f9b84078f06c979e72fdc00a76f15e1d1e06d604#512

#guard [VLen.l128, .l256].all fun l =>
  checkV (fun d => .vbin .vaesdec l d .xmm0 .xmm1) aesDecRound l &&
  checkV (fun d => .vbin .vaesdeclast l d .xmm0 .xmm1) aesDecLast l
#guard checkZ (fun d => .zbin .vaesdec d .xmm0 .xmm1) aesDecRound
#guard checkZ (fun d => .zbin .vaesdeclast d .xmm0 .xmm1) aesDecLast

-- The legacy `aesdec` and `aesdeclast` on lane 0 agree.
#guard ((XOp.bin .aesdec .xmm0 .xmm1).exec Avx512.s).xmm .xmm0 == aesDecRound.extractLsb' 0 128
#guard ((XOp.bin .aesdeclast .xmm0 .xmm1).exec Avx512.s).xmm .xmm0 == aesDecLast.extractLsb' 0 128

#guard printer.instr (.vop (.vbin .vaesdec .l128 .xmm5 .xmm0 .xmm1)) == ["vaesdec xmm5, xmm0, xmm1"]
#guard isa.requires (.vop (.vbin .vaesdec .l128 .xmm5 .xmm0 .xmm1)) == ["aes", "avx"]
#guard !isa.writesSp (.vop (.vbin .vaesdec .l128 .xmm5 .xmm0 .xmm1))
#guard printer.instr (.vop (.vbin .vaesdec .l256 .xmm5 .xmm0 .xmm1)) == ["vaesdec ymm5, ymm0, ymm1"]
#guard isa.requires (.vop (.vbin .vaesdec .l256 .xmm5 .xmm0 .xmm1)) == ["vaes", "avx"]
#guard !isa.writesSp (.vop (.vbin .vaesdec .l256 .xmm5 .xmm0 .xmm1))
#guard printer.instr (.zop (.zbin .vaesdec .xmm5 .xmm0 .xmm1)) == ["vaesdec zmm5, zmm0, zmm1"]
#guard isa.requires (.zop (.zbin .vaesdec .xmm5 .xmm0 .xmm1)) == ["vaes", "avx512f"]
#guard !isa.writesSp (.zop (.zbin .vaesdec .xmm5 .xmm0 .xmm1))
#guard printer.instr (.vop (.vbin .vaesdeclast .l128 .xmm5 .xmm0 .xmm1)) == ["vaesdeclast xmm5, xmm0, xmm1"]
#guard isa.requires (.vop (.vbin .vaesdeclast .l128 .xmm5 .xmm0 .xmm1)) == ["aes", "avx"]
#guard !isa.writesSp (.vop (.vbin .vaesdeclast .l128 .xmm5 .xmm0 .xmm1))
#guard printer.instr (.vop (.vbin .vaesdeclast .l256 .xmm5 .xmm0 .xmm1)) == ["vaesdeclast ymm5, ymm0, ymm1"]
#guard isa.requires (.vop (.vbin .vaesdeclast .l256 .xmm5 .xmm0 .xmm1)) == ["vaes", "avx"]
#guard !isa.writesSp (.vop (.vbin .vaesdeclast .l256 .xmm5 .xmm0 .xmm1))
#guard printer.instr (.zop (.zbin .vaesdeclast .xmm5 .xmm0 .xmm1)) == ["vaesdeclast zmm5, zmm0, zmm1"]
#guard isa.requires (.zop (.zbin .vaesdeclast .xmm5 .xmm0 .xmm1)) == ["vaes", "avx512f"]
#guard !isa.writesSp (.zop (.zbin .vaesdeclast .xmm5 .xmm0 .xmm1))
#guard isa.requires (.vbinLoad .vaesdec .l128 .xmm0 .xmm1 { base := .rdi }) == ["aes", "avx"]
#guard isa.requires (.vbinLoad .vaesdeclast .l256 .xmm0 .xmm1 { base := .rdi }) == ["vaes", "avx"]

end VG.Test.VectorAesDec
