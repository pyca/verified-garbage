import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Verified
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor
import VerifiedGarbage.Impl.ChaCha20.X86_64.Callee
import VerifiedGarbage.Impl.Poly1305.X86_64.Callee
import VerifiedGarbage.Proof.Framework.X86_64.Depth

/-!
# Implementations of `vg_chacha20_xor` on x86-64

An `XorImpl` is what a function that calls `vg_chacha20_xor` needs of it, so
that its proof holds for every implementation: each is a variant of the
interface `ChaCha20Xor` on x86-64 (`Variants/ChaCha20Xor/X86_64/`), and each
caller (in `Generic/ChaCha20Xor/X86_64/`) is emitted once for each of them
(see `TCB/Emit.lean`). Callers leave room for 16 bytes of stack below its
return address (`stack_le`), and for two levels of calls (`depth_le`), which
take at most those 16 bytes (`xdepth`).

An implementation also names the implementation of `vg_poly1305_blocks` for
the same CPUs (`poly`), which ChaCha20-Poly1305's instance for it calls: so
each instance needs the CPU features of both.
-/

namespace VG.Proof.ChaCha20.X86_64

open VG.X86_64

/-- An implementation of `vg_chacha20_xor` on x86-64. -/
structure XorImpl where
  /-- Its symbol and code. -/
  callee : Impl.ChaCha20.X86_64.Callee
  /-- ChaCha20-Poly1305 keeps the keystream for `64 + fold` bytes in its
  working space. -/
  fold_le : callee.fold ≤ 960
  /-- The stack its calls use below its return address. -/
  stack : Nat
  stack_le : stack ≤ 16
  depth_le : callee.code.depth ≤ 2
  /-- Its calls take at most 16 bytes of stack below its return address. -/
  xdepth : callee.code.x86_64Depth ≤ 16
  /-- It is correct, and returns with `rsi` pointing at `buf`. -/
  ok : ∀ s, (xorStack stack).pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ (xorStack stack).post s s'
  /-- It is constant time. -/
  ct : ConstantTime isa (xorStack stack).pre (xorStack stack).pub callee.code
  /-- It never writes the stack pointer. -/
  nosp : NoSp callee.code
  /-- It never loads MXCSR. -/
  mxcsr : callee.code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- What the names of its callers' instances end with (e.g. `_avx2`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- The implementation of `vg_poly1305_blocks` that callers of this one
  which also call `vg_poly1305_blocks` (ChaCha20-Poly1305) call: the one
  for the same CPUs. -/
  poly : Impl.Poly1305.X86_64.Blocks
  /-- Its `fold`, `pass` and `wide` with the implementation of
  `vg_poly1305_blocks` it comes with: one of the combinations whose
  ChaCha20-Poly1305 the constant-time analysis checks (it runs on code with
  the comparisons against `fold`, the mask `pass - 1` and the loops of
  `2 ^ wide` bytes in it). -/
  fold_poly : (callee.fold = 0 ∧ callee.pass = 0 ∧ callee.wide = 4 ∧ poly = .scalar) ∨
    (callee.fold = 448 ∧ callee.pass = 0 ∧ callee.wide = 5 ∧ poly = .avx2) ∨
    (callee.fold = 960 ∧ callee.pass = 1024 ∧ callee.wide = 6 ∧ poly = .avx512)

namespace XorImpl

theorem scalar_ok : ∀ s, (xorStack 8).pre s → ∃ t s', Exec isa Impl.ChaCha20.X86_64.Callee.scalar.code s t s' ∧
    abiPreserved s s' ∧ (xorStack 8).post s s' :=
  fun s hs => Xor.xor_rsi s hs

theorem scalar_ct : ConstantTime isa (xorStack 8).pre (xorStack 8).pub Impl.ChaCha20.X86_64.Callee.scalar.code :=
  Xor.xor_ct

/-- The scalar implementation, `vg_chacha20_xor`, in the baseline ISA. -/
def scalar : XorImpl where
  callee := .scalar
  fold_le := by decide
  stack := 8
  stack_le := by decide
  depth_le := by lit_decide
  xdepth := by lit_decide
  ok := scalar_ok
  ct := scalar_ct
  nosp := Avx2.xor_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := ""
  features := []
  poly := .scalar
  fold_poly := Or.inl ⟨rfl, rfl, rfl, rfl⟩

theorem avx2_ok : ∀ s, (xorStack 16).pre s → ∃ t s', Exec isa Impl.ChaCha20.X86_64.Callee.avx2.code s t s' ∧
    abiPreserved s s' ∧ (xorStack 16).post s s' :=
  fun s hs => Avx2.xor_rsi s hs

theorem avx2_ct : ConstantTime isa (xorStack 16).pre (xorStack 16).pub Impl.ChaCha20.X86_64.Callee.avx2.code :=
  Avx2.xor_ct

theorem avx2_nosp : NoSp Impl.ChaCha20.X86_64.Callee.avx2.code := by
  have : ((instrs Impl.ChaCha20.X86_64.Callee.avx2.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

/-- The AVX2 implementation, `vg_chacha20_xor_avx2`. -/
def avx2 : XorImpl where
  callee := .avx2
  fold_le := by decide
  stack := 16
  stack_le := by decide
  depth_le := by lit_decide
  xdepth := by lit_decide
  ok := avx2_ok
  ct := avx2_ct
  nosp := avx2_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_avx2"
  features := ["avx", "avx2"]
  poly := .avx2
  fold_poly := Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)

theorem avx512_ok : ∀ s, (xorStack 16).pre s → ∃ t s', Exec isa Impl.ChaCha20.X86_64.Callee.avx512.code s t s' ∧
    abiPreserved s s' ∧ (xorStack 16).post s s' :=
  fun s hs => Avx512.xor_rsi s hs

theorem avx512_ct : ConstantTime isa (xorStack 16).pre (xorStack 16).pub Impl.ChaCha20.X86_64.Callee.avx512.code :=
  Avx512.xor_ct

theorem avx512_nosp : NoSp Impl.ChaCha20.X86_64.Callee.avx512.code := by
  have : ((instrs Impl.ChaCha20.X86_64.Callee.avx512.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

/-- The AVX-512 implementation, `vg_chacha20_xor_avx512`. -/
def avx512 : XorImpl where
  callee := .avx512
  fold_le := by decide
  stack := 16
  stack_le := by decide
  depth_le := by lit_decide
  xdepth := by lit_decide
  ok := avx512_ok
  ct := avx512_ct
  nosp := avx512_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_avx512"
  features := ["avx", "avx512f"]
  poly := .avx512
  fold_poly := Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)

end XorImpl

end VG.Proof.ChaCha20.X86_64
