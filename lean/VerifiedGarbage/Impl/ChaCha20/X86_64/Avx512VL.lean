module

public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512

/-!
# ChaCha20 keystream XOR: x86-64 implementation with AVX-512, short data in `ymm` registers

`xorBy`, with the contract of `vg_chacha20_xor`, for CPUs with AVX2,
AVX-512F and AVX-512VL: fewer than `shortLim` bytes by the AVX2 kernel with
AVX-512VL's `vprold` (`Avx2.xorVL`, on `ymm` registers), the rest by the
AVX-512 kernel (`Avx512.xor`). On the CPUs that lower their clock for a
while after a 512-bit instruction (Skylake-SP and Cascade Lake), the code
after a short run then keeps its speed.

The branch is on the length only.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.X86_64.Avx512VL

open VG.X86_64

/-- The length from which `xorBy` runs the AVX-512 kernel. -/
def shortLim : Nat := 513

def xorBy : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 shortLim))]) (.ite .b Avx2.xorVL Avx512.xor5)

end VG.Impl.ChaCha20.X86_64.Avx512VL
