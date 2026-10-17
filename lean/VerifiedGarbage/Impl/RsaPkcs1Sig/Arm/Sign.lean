module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Wrap
public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Encode
public import VerifiedGarbage.Impl.Bignum.Arm.MaskBytes

/-!
# RSASSA-PKCS1-v1_5 signing on ARMv7

`vg_rsa_pkcs1_sign(out = r0, out_len = r1, n = r2, n_len = r3, e, e_len,
hash, digest, digest_len, p, p_len, q, q_len, dp, dp_len, dq, dq_len, qinv,
qinv_len, scratch, scratch_len)`, the last seventeen on the stack. RFC 8017
§8.2.1, as on AArch64 (`Impl/RsaPkcs1Sig/AArch64/Sign.lean`):

1. `encode` writes the encoding of `digest` to a buffer `EM` in the frame;
   if that fails (which depends only on `hash`, `digest_len` and `n_len`),
   it writes zeros to `out` and returns 0;
2. `vg_rsa_private_checked` (or a variant: `priv`, by its name `privName`)
   computes the signature of `EM` into `out`, checked against `e`, and
   its result is returned;
3. `EM` is overwritten with zeros.

Only the public key, the lengths and `hash` decide a branch or an address:
the hash value is only copied into `EM`, which only the private operation
reads.

The frame (`Impl/RsaPkcs1Sig/Arm/Wrap.lean`) holds the call's sixteen stack
arguments from its base and `EM` (up to 1024 bytes) at `oEM`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.Arm.Sign

open VG VG.Arm
open VG.Impl.RsaPkcs1Sig.Arm (wrap argOff encode)

/-- The size of the inner frame. -/
def frameBytes : Nat := 1088

/-- `EM`. -/
def oEM : Nat := 64

/-- Argument `j` (from 0). -/
def arg (j : Nat) : Nat := argOff frameBytes j

/-- `encode`'s registers: `EM`, `digest`, `hash`, `n_len` and `digest_len`. -/
def encArgs : List Instr :=
  [.addSp .r12 0, .dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oEM)), .ldrSp .r1 (arg 7), .ldrSp .r2 (arg 6),
    .ldrSp .r3 (arg 3), .ldrSp .lr (arg 8)]

/-- `out`, `n_len` and the zero mask for `maskBytes`. -/
def zeroArgs : List Instr := [.addSp .r12 0, .ldrSp .r0 (arg 0), .ldrSp .lr (arg 3), .mov .r2 (.imm 0)]

/-- 0 returned. -/
def ret0 : List Instr := [.mov .r0 (.imm 0)]

/-- Argument `j` to the call's stack argument `i`. -/
def copyArg (j i : Nat) : List Instr := [.ldrSp .r0 (arg j), .str .r0 .r12 (4 * i)]

/-- The call's stack arguments (`e`, `e_len`, `EM`, `n_len`, then `p` …
`scratch_len`), then its registers: `out`, `n_len`, `n`, `n_len`. -/
def callArgs : List Instr :=
  [.addSp .r12 0] ++ copyArg 4 0 ++ copyArg 5 1 ++
    ([.dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oEM)), .str .r0 .r12 8] : List Instr) ++ copyArg 3 3 ++
    copyArg 9 4 ++ copyArg 10 5 ++ copyArg 11 6 ++ copyArg 12 7 ++ copyArg 13 8 ++ copyArg 14 9 ++
    copyArg 15 10 ++ copyArg 16 11 ++ copyArg 17 12 ++ copyArg 18 13 ++ copyArg 19 14 ++ copyArg 20 15 ++
    ([.ldrSp .r0 (arg 0), .ldrSp .r1 (arg 3), .ldrSp .r2 (arg 2), .ldrSp .r3 (arg 3)] : List Instr)

/-- The result kept in `r3`, and `EM`, `n_len` and the zero mask for
`maskBytes`. -/
def wipeArgs : List Instr :=
  [.addSp .r12 0, .mov .r3 (.reg .r0), .dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oEM)), .ldrSp .lr (arg 3),
    .mov .r2 (.imm 0)]

/-- Once the encoding succeeded. -/
def rest (privName : String) (priv : Prog isa) : Prog isa :=
  .seq (.block callArgs) (.seq (.call privName priv) (.seq (.block wipeArgs) (.seq Bignum.Arm.maskBytes
    (.block [.mov .r0 (.reg .r3)]))))

/-- The inner frame's body. -/
def body (privName : String) (priv : Prog isa) : Prog isa :=
  .seq (.block encArgs) (.seq encode (.seq (.block [.cmp .r3 (.imm 0)])
    (.ite .eq (.seq (.block zeroArgs) (.seq Bignum.Arm.maskBytes (.block ret0))) (rest privName priv))))

/-- `vg_rsa_pkcs1_sign`, calling a checked private operation (`priv`) by its
name. -/
def code (privName : String) (priv : Prog isa) : Prog isa := wrap frameBytes (body privName priv)

end VG.Impl.RsaPkcs1Sig.Arm.Sign
