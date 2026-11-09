module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.KeyGen.Frag

/-!
# ML-DSA on RISC-V: polynomials copied from a key's cache

Signing and verification (`Sign/Sign.lean`, `Verify/Verify.lean`) keep a
pointer to the polynomials of a prepared key, if they were given them, in
`s3`. `cacheCopy off dst len` copies the `len` bytes at `s3 + off` to `dst`
(a pointer of the layout), a byte at a time with ML-KEM's `copyBody`, since the
cache, part of a key given as bytes, need not be aligned. Its addresses depend
only on `s3`, the pointer of `dst`, and the constants.
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.CacheCopy

open VG.RISCV64
open VG.Impl.MlDsa.RISCV64.KeyGen (Ptr Arg glue)

/-- `len` bytes from `s3 + off` to `dst`. -/
def cacheCopy (off : Nat) (dst : Ptr) (len : Nat) : Prog isa :=
  .seq (.block (Arg.instrs .a0 (.ptr (.s3, off)) ++ glue [(.a1, .ptr dst), (.a2, .imm len)]))
    (.loop (.block Impl.MlKem.RISCV64.copyBody) (.nonzero .a2))

/-- `len` bytes from `src` to `dst` (pointers of the layout), a byte at a time. -/
def copyN (src dst : Ptr) (len : Nat) : Prog isa :=
  .seq (.block (glue [(.a0, .ptr src), (.a1, .ptr dst), (.a2, .imm len)]))
    (.loop (.block Impl.MlKem.RISCV64.copyBody) (.nonzero .a2))

end VG.Impl.MlDsa.RISCV64.CacheCopy
