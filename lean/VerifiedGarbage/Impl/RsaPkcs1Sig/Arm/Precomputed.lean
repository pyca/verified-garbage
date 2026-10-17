module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Wrap
public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Encode
public import VerifiedGarbage.Impl.Bignum.Arm.CompareBytes

/-!
# RSASSA-PKCS1-v1_5 verification with a precomputed public key on ARMv7

`vg_rsa_pkcs1_verify_precomputed(n = r0, n_len = r1, e = r2, e_len = r3,
hash, digest, digest_len, sig, sig_len, scratch, scratch_len, pre,
pre_len)`, the last nine on the stack. RFC 8017 §8.2.2, as on AArch64
(`Impl/RsaPkcs1Sig/AArch64/Precomputed.lean`):

1. if `sig_len` is not `n_len`, it returns 0 (a branch on public lengths);
2. `vg_rsa_public_precomputed_checked` (`pd`, by its name `pdName`), given
   `pre` in place of the modulus, writes `EM₁ = s^e mod n` or zeros to the
   frame, and its status is kept in the frame's word at `oSt`;
3. `encode` writes the encoding of `digest` to `EM₂`, and whether it
   succeeded is kept at `oOk`;
4. `Bignum.Arm.compareBytes` compares `EM₁` and `EM₂` (`n_len` bytes),
   and the result is the status, masked with the success of the encoding
   and with whether the two are equal.

The status, and so `EM₁`, is unspecified when `pre` is not the modulus'
values, so nothing after the call branches on them: the encoding, the
comparison and the masks always run.

The frame (`Impl/RsaPkcs1Sig/Arm/Wrap.lean`) holds the call's stack
arguments from its base, the status and the encoding's success at `oSt`
and `oOk`, and `EM₁` and `EM₂` (up to 1024 bytes each) at `oEM1` and
`oEM2`. Every block either addresses only the stack (through `sp` or
`r12 = sp`) or only registers holding pointers and lengths.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.Arm.Precomputed

open VG VG.Arm
open VG.Impl.RsaPkcs1Sig.Arm (wrap argOff encode)

/-- The size of the inner frame. -/
def frameBytes : Nat := 2080

/-- The status, the encoding's success, `EM₁` and `EM₂`. -/
def oSt : Nat := 24
def oOk : Nat := 28
def oEM1 : Nat := 32
def oEM2 : Nat := 1056

/-- Argument `j` (from 0). -/
def arg (j : Nat) : Nat := argOff frameBytes j

/-- `r0 := sig_len - n_len`. -/
def lenCheck : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 8), .ldrSp .r1 (arg 1), .dp .sub .r0 .r0 (.reg .r1)]

/-- 0 returned. -/
def ret0 : List Instr := [.mov .r0 (.imm 0)]

/-- The call's stack arguments (`e`, `e_len`, `sig`, `n_len`, `scratch`,
`scratch_len`), then its registers: `EM₁`, `n_len`, `pre`, `pre_len`. -/
def callArgs : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 2), .str .r0 .r12 0, .ldrSp .r0 (arg 3), .str .r0 .r12 4,
    .ldrSp .r0 (arg 7), .str .r0 .r12 8, .ldrSp .r0 (arg 1), .str .r0 .r12 12,
    .ldrSp .r0 (arg 9), .str .r0 .r12 16, .ldrSp .r0 (arg 10), .str .r0 .r12 20,
    .dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oEM1)), .ldrSp .r1 (arg 1), .ldrSp .r2 (arg 11),
    .ldrSp .r3 (arg 12)]

/-- The status to its word, and `encode`'s registers: `EM₂`, `digest`,
`hash`, `n_len` and `digest_len`. -/
def encArgs : List Instr :=
  [.addSp .r12 0, .str .r0 .r12 oSt, .dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oEM2)), .ldrSp .r1 (arg 5),
    .ldrSp .r2 (arg 4), .ldrSp .r3 (arg 1), .ldrSp .lr (arg 6)]

/-- The encoding's success to its word, and `compareBytes`' registers:
`EM₁`, `EM₂`, `n_len` and the accumulator. -/
def cmpArgs : List Instr :=
  [.addSp .r12 0, .str .r3 .r12 oOk, .dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oEM1)),
    .dp .add .r1 .r12 (.imm (BitVec.ofNat 32 oEM2)), .ldrSp .lr (arg 1), .mov .r2 (.imm 0)]

/-- The status, masked with the encoding's success and with whether the
comparison found no difference (`r2 = 0`): `1 - ((0 - r2) | r2) >> 31`, as
`vg_rsa_private_checked` finds it (`Impl/Rsa/Arm/PrivChecked.lean`). -/
def result : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 oSt, .ldrSp .r3 oOk, .mov .r1 (.imm 0), .dp .sub .r1 .r1 (.reg .r2),
    .dp .orr .r1 .r1 (.reg .r2), .mov .r1 (.shifted .r1 .lsr 31), .mov .r2 (.imm 1), .dp .sub .r1 .r2 (.reg .r1),
    .dp .and .r0 .r0 (.reg .r3), .dp .and .r0 .r0 (.reg .r1)]

/-- Once the lengths are equal. -/
def rest (pdName : String) (pd : Prog isa) : Prog isa :=
  .seq (.block callArgs) (.seq (.call pdName pd) (.seq (.block encArgs) (.seq encode
    (.seq (.block cmpArgs) (.seq Bignum.Arm.compareBytes (.block result))))))

/-- The inner frame's body. -/
def body (pdName : String) (pd : Prog isa) : Prog isa :=
  .seq (.block lenCheck) (.seq (.block [.cmp .r0 (.imm 0)]) (.ite .ne (.block ret0) (rest pdName pd)))

/-- `vg_rsa_pkcs1_verify_precomputed`, calling a precomputed public
operation (`pd`) by its name. -/
def code (pdName : String) (pd : Prog isa) : Prog isa := wrap frameBytes (body pdName pd)

end VG.Impl.RsaPkcs1Sig.Arm.Precomputed
