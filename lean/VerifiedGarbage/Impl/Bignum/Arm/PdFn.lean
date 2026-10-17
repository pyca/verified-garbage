module

public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Impl.Bignum.Arm.PdImport
public import VerifiedGarbage.Impl.Bignum.Arm.PdChecks

/-! # Checked ARMv7 RSA with a reusable public precomputation

The packed modulus and R² are public. Their arithmetic preconditions are
checked before exponentiation; secret input acceptance only masks the result.
The argument order and 56-byte frame match the public checked operation,
with `(out_len, pre, pre_len)` replacing `(out_len, n, n_len)`.
-/

@[expose] public section
namespace VG.Impl.Bignum.Arm.PdFn
open VG VG.Arm

def entry : List Instr := PublicFn.entry ++ [.str .r1 .r12 12]
def prepare : Prog isa := .seq (.block PcFn.inputs) PublicFn.prepare
def apply : Prog isa := .seq precomputeInverse PublicFn.applyInput
def checked : Prog isa := .seq pdChecks (.ite .eq PublicFn.fail apply)
def imported : Prog isa := .seq prepare (.seq pdImport checked)
def body : Prog isa := .seq (.block PublicFn.exponentArgs) (.seq exponentCheck
  (.seq (.block [.subs .r7 .r7 (.imm 0)]) (.ite .eq PublicFn.fail imported)))
def code : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq (.block entry) (.seq body (.block PcFn.restore))) (.pop .r12 56)
end VG.Impl.Bignum.Arm.PdFn
