import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512

/-!
# The implementations of `vg_chacha20_xor` on x86-64

A function that calls `vg_chacha20_xor` (ChaCha20-Poly1305's `seal` and
`open`) takes the implementation it calls, a `Callee`, and is emitted once
for each (`Generic/ChaCha20Xor/X86_64/`).
-/

namespace VG.Impl.ChaCha20.X86_64

open VG.X86_64

/-- An implementation of `vg_chacha20_xor` to call: its symbol and its code,
and `fold`: the most bytes of data for which ChaCha20-Poly1305 computes the
block with counter 0 (the one-time key) and the data's keystream in one call
of it, the length (`64 + fold`) up to which it computes all the blocks in
one pass. -/
structure Callee where
  name : String
  code : Prog isa
  fold : Nat

/-- The baseline computes one block at a time: nothing to gain. -/
def Callee.scalar : Callee := ⟨"vg_chacha20_xor", Xor.xor, 0⟩
/-- Up to 256 bytes in one computation of four blocks (`Avx2Tail.last`). -/
def Callee.avx2 : Callee := ⟨"vg_chacha20_xor_avx2", Avx2.xor, 192⟩
/-- Up to 1024 bytes in one computation of sixteen blocks (the loop, or `Avx512.last16`). -/
def Callee.avx512 : Callee := ⟨"vg_chacha20_xor_avx512", Avx512.xor, 960⟩

end VG.Impl.ChaCha20.X86_64
