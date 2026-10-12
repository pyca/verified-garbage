module

public import VerifiedGarbage.Impl.ChaCha20.X86.Xor

/-!
# The implementations of `vg_chacha20_xor` on x86 (32-bit)

A function that calls `vg_chacha20_xor` (`vg_chacha20_apply`,
ChaCha20-Poly1305's `seal` and `open`) takes the implementation it calls, a
`Callee`, and is emitted once for each (`Generic/ChaCha20Xor/X86/`).
-/

@[expose] public section

namespace VG.Impl.ChaCha20.X86

open VG.X86

/-- An implementation of `vg_chacha20_xor` to call: its symbol and its code. -/
structure Callee where
  name : String
  code : Prog isa

def Callee.sse2 : Callee := ⟨"vg_chacha20_xor", Xor.xor⟩
def Callee.ssse3 : Callee := ⟨"vg_chacha20_xor_ssse3", Xor.xorSsse3⟩

end VG.Impl.ChaCha20.X86
