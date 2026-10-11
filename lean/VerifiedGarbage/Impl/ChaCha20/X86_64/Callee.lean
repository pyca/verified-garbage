module

public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512

/-!
# The implementations of `vg_chacha20_xor` on x86-64

A function that calls `vg_chacha20_xor` (ChaCha20-Poly1305's `seal` and
`open`) takes the implementation it calls, a `Callee`, and is emitted once
for each (`Generic/ChaCha20Xor/X86_64/`).
-/

@[expose] public section

namespace VG.Impl.ChaCha20.X86_64

open VG.X86_64

/-- An implementation of `vg_chacha20_xor` to call: its symbol and its code,
and `fold`: the most bytes of data for which ChaCha20-Poly1305 computes the
block with counter 0 (the one-time key) and the data's keystream in one call
of it, the length (`64 + fold`) up to which it computes all the blocks in
one pass. For longer data, `pass` (if not 0, a power of two) is the length
its bulk passes take at once: the call with the one-time key then also
computes the keystream of the bytes past the last multiple of `pass`,
rounded up to a block, if they are at most `fold`, so that the rest of the
data is whole passes (rather than whole passes and a last pass for a few
bytes, as in TLS records of `n · 1024 + 1` bytes). -/
structure Callee where
  name : String
  code : Prog isa
  fold : Nat
  pass : Nat

/-- The baseline computes one block at a time: nothing to gain. -/
def Callee.scalar : Callee := ⟨"vg_chacha20_xor", Xor.xor, 0, 0⟩
/-- Up to 512 bytes in one call: up to 384 in one computation of at most six
blocks (`Avx2Tail.last3`), 512 in one of eight (the loop). -/
def Callee.avx2 : Callee := ⟨"vg_chacha20_xor_avx2", Avx2.xor, 448, 0⟩
/-- Up to 1024 bytes in one computation of sixteen blocks (the loop, or
`Avx512.last16`), as are the rest of the data's after the first call. -/
def Callee.avx512 : Callee := ⟨"vg_chacha20_xor_avx512", Avx512.xor, 960, 1024⟩

end VG.Impl.ChaCha20.X86_64
