module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Precomputed
public import VerifiedGarbage.Impl.Bignum.Arm.MaskBytes

/-!
# RSASSA-PKCS1-v1_5 recovery with a precomputed public key on ARMv7

`vg_rsa_pkcs1_recover_precomputed(out = r0, out_len = r1, n = r2,
n_len = r3, e, e_len, hash, sig, sig_len, scratch, scratch_len, pre,
pre_len)`, the last nine on the stack. As on AArch64
(`Impl/RsaPkcs1Sig/AArch64/RecoverPrecomputed.lean`), in the frame of
`vg_rsa_pkcs1_verify_precomputed` (`Impl/RsaPkcs1Sig/Arm/Precomputed.lean`):

1. if `sig_len` is not `n_len`, it writes zeros to `out` and returns 0 (a
   branch on public lengths);
2. `vg_rsa_public_precomputed_checked` (`pd`, by its name `pdName`), given
   `pre` in place of the modulus, writes `EM₁ = s^e mod n` or zeros to the
   frame, and its status is kept in the frame's word at `oSt`;
3. `encode` writes the encoding of the last `out_len` bytes of `EM₁` to
   `EM₂`, and whether it succeeded is kept at `oOk`;
4. `Bignum.Arm.compareBytes` compares `EM₁` and `EM₂`, and the result `r`
   is the status, masked with the success of the encoding and with whether
   the two are equal;
5. the last `out_len` bytes of `EM₁` are copied to `out`
   (`Bignum.Arm.copyBytes`), and `out` is masked with `0 - r`
   (`Bignum.Arm.maskBytes`): zeros unless `r` is 1.

The status, and so `EM₁`, is unspecified when `pre` is not the modulus'
values, so nothing after the call branches on them.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.Arm.RecoverPrecomputed

open VG VG.Arm
open VG.Impl.RsaPkcs1Sig.Arm (wrap encode)
open VG.Impl.RsaPkcs1Sig.Arm.Precomputed (frameBytes oSt oOk oEM1 oEM2 arg ret0)

/-- `r0 := sig_len - n_len`. -/
def lenCheck : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 8), .ldrSp .r1 (arg 3), .dp .sub .r0 .r0 (.reg .r1)]

/-- `out`, `out_len` and the zero mask for `maskBytes`. -/
def zeroArgs : List Instr := [.addSp .r12 0, .ldrSp .r0 (arg 0), .ldrSp .lr (arg 1), .mov .r2 (.imm 0)]

/-- The call's stack arguments (`e`, `e_len`, `sig`, `n_len`, `scratch`,
`scratch_len`), then its registers: `EM₁`, `n_len`, `pre`, `pre_len`. -/
def callArgs : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 4), .str .r0 .r12 0, .ldrSp .r0 (arg 5), .str .r0 .r12 4,
    .ldrSp .r0 (arg 7), .str .r0 .r12 8, .ldrSp .r0 (arg 3), .str .r0 .r12 12,
    .ldrSp .r0 (arg 9), .str .r0 .r12 16, .ldrSp .r0 (arg 10), .str .r0 .r12 20,
    .dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oEM1)), .ldrSp .r1 (arg 3), .ldrSp .r2 (arg 11),
    .ldrSp .r3 (arg 12)]

/-- The status to its word, and `encode`'s registers: `EM₂`, the last
`out_len` bytes of `EM₁`, `hash`, `n_len` and `out_len`. -/
def encArgs : List Instr :=
  [.addSp .r12 0, .str .r0 .r12 oSt, .dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oEM2)), .ldrSp .r3 (arg 3),
    .ldrSp .lr (arg 1), .dp .add .r1 .r12 (.imm (BitVec.ofNat 32 oEM1)), .dp .add .r1 .r1 (.reg .r3),
    .dp .sub .r1 .r1 (.reg .lr), .ldrSp .r2 (arg 6)]

/-- The encoding's success to its word, and `compareBytes`' registers:
`EM₁`, `EM₂`, `n_len` and the accumulator. -/
def cmpArgs : List Instr :=
  [.addSp .r12 0, .str .r3 .r12 oOk, .dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oEM1)),
    .dp .add .r1 .r12 (.imm (BitVec.ofNat 32 oEM2)), .ldrSp .lr (arg 3), .mov .r2 (.imm 0)]

/-- The result `r3`: the status, masked with the encoding's success and with
whether the comparison found no difference (`r2 = 0`), as in
`vg_rsa_pkcs1_verify_precomputed`. -/
def result : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 oSt, .ldrSp .r3 oOk, .mov .r1 (.imm 0), .dp .sub .r1 .r1 (.reg .r2),
    .dp .orr .r1 .r1 (.reg .r2), .mov .r1 (.shifted .r1 .lsr 31), .mov .r2 (.imm 1), .dp .sub .r1 .r2 (.reg .r1),
    .dp .and .r0 .r0 (.reg .r3), .dp .and .r3 .r0 (.reg .r1)]

/-- `copyBytes`' registers: `out`, the last `out_len` bytes of `EM₁` and
`out_len`. -/
def copyArgs : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 0), .dp .add .r1 .r12 (.imm (BitVec.ofNat 32 oEM1)), .ldrSp .r2 (arg 3),
    .dp .add .r1 .r1 (.reg .r2), .ldrSp .lr (arg 1), .dp .sub .r1 .r1 (.reg .lr)]

/-- `maskBytes`' registers: the mask `0 - r3`, `out` and `out_len`. -/
def maskArgs : List Instr :=
  [.addSp .r12 0, .mov .r2 (.imm 0), .dp .sub .r2 .r2 (.reg .r3), .ldrSp .r0 (arg 0), .ldrSp .lr (arg 1)]

/-- Once the lengths are equal. -/
def rest (pdName : String) (pd : Prog isa) : Prog isa :=
  .seq (.block callArgs) (.seq (.call pdName pd) (.seq (.block encArgs) (.seq encode
    (.seq (.block cmpArgs) (.seq Bignum.Arm.compareBytes (.seq (.block result) (.seq (.block copyArgs)
      (.seq Bignum.Arm.copyBytes (.seq (.block maskArgs) (.seq Bignum.Arm.maskBytes
        (.block [.mov .r0 (.reg .r3)])))))))))))

/-- The inner frame's body. -/
def body (pdName : String) (pd : Prog isa) : Prog isa :=
  .seq (.block lenCheck) (.seq (.block [.cmp .r0 (.imm 0)])
    (.ite .ne (.seq (.block zeroArgs) (.seq Bignum.Arm.maskBytes (.block ret0))) (rest pdName pd)))

/-- `vg_rsa_pkcs1_recover_precomputed`, calling a precomputed public
operation (`pd`) by its name. -/
def code (pdName : String) (pd : Prog isa) : Prog isa := wrap frameBytes (body pdName pd)

end VG.Impl.RsaPkcs1Sig.Arm.RecoverPrecomputed
