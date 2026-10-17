module

public import VerifiedGarbage.Impl.Bignum.Arm.PcFn

/-!
# The frames of the ARMv7 PKCS #1 v1.5 functions

Every PKCS #1 v1.5 function on ARMv7 (`vg_rsa_pkcs1_sign`,
`vg_rsa_pkcs1_verify_precomputed`, `vg_rsa_pkcs1_recover_precomputed`,
`vg_rsa_pkcs1_encrypt_precomputed`, `vg_rsa_pkcs1_decrypt`) runs its body
in two frames, as `vg_rsa_private_checked` does (`Impl/Rsa/Arm/PrivChecked.lean`):
a push of every register, `r0`–`r12` and `lr` (56 bytes, which keeps the
stack pointer 8-byte aligned), and in it a frame of `F` bytes; then it
restores the callee-saved registers from the push (`PcFn.restore`) and pops
it into `r12`. So the body may use every register, and the four register
arguments stay in the push, beside the stack arguments: argument `j` (from
0) is at `sp + argOff F j` in the inner frame.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.Arm

open VG VG.Arm

/-- The registers pushed on entry. -/
def pushRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

/-- `body` in a frame of `F` bytes, inside the push of every register. -/
def wrap (F : Nat) (body : Prog isa) : Prog isa :=
  .frame (.push pushRegs) (.seq (.frame (.alloc F) body (.free F)) (.block Bignum.Arm.PcFn.restore))
    (.pop .r12 56)

/-- The offset from the stack pointer in the inner frame of argument `j`
(from 0): the registers' in the push, then the stack arguments above it. -/
def argOff (F j : Nat) : Nat := if j < 4 then F + 4 * j else F + 56 + 4 * (j - 4)

end VG.Impl.RsaPkcs1Sig.Arm
