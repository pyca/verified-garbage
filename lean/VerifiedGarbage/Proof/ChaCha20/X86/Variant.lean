import VerifiedGarbage.Proof.ChaCha20.X86.Xor
import VerifiedGarbage.Impl.ChaCha20.X86.Callee
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-!
# Implementations of `vg_chacha20_xor` on x86 (32-bit)

An `XorImpl` is what a function that calls `vg_chacha20_xor` needs of it, so
that its proof holds for every implementation: each is a variant of the
interface `ChaCha20Xor` on x86 (`Variants/ChaCha20Xor/X86/`), and each caller
(in `Generic/ChaCha20Xor/X86/`) is emitted once for each of them (see
`TCB/Emit.lean`). Every implementation has the contract `xorX86`, with the
12 bytes of stack below its return address.
-/

namespace VG.Proof.ChaCha20.X86

open VG.X86

/-- An implementation of `vg_chacha20_xor` on x86. -/
structure XorImpl where
  /-- Its symbol and code. -/
  callee : Impl.ChaCha20.X86.Callee
  /-- It is correct. -/
  ok : ∀ s, Proof.ChaCha20.xorX86.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.xorX86.post s s'
  /-- It is constant time. -/
  ct : ConstantTime isa Proof.ChaCha20.xorX86.pre Proof.ChaCha20.xorX86.pub callee.code
  /-- It never writes the stack pointer, and its calls and frames use 12 bytes of stack. -/
  nosp : NoSp callee.code
  stack : stackUse callee.code = 12
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- What the names of its callers' instances end with (e.g. `_ssse3`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

namespace XorImpl

/-- `vg_chacha20_xor`, with SSE2 (the baseline ISA). -/
def sse2 : XorImpl where
  callee := .sse2
  ok := Xor.xor_correct
  ct := Xor.xor_ct
  nosp := NoSp.of_all (by lit_decide)
  stack := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := ""
  features := []

/-- `vg_chacha20_xor_ssse3`, with SSSE3. -/
def ssse3 : XorImpl where
  callee := .ssse3
  ok := Xor.xorSsse3_correct
  ct := Xor.xorSsse3_ct
  nosp := NoSp.of_all (by lit_decide)
  stack := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_ssse3"
  features := ["ssse3"]

end XorImpl

end VG.Proof.ChaCha20.X86
