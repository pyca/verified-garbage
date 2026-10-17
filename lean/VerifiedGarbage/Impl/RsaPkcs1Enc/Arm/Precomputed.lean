module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Wrap
public import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes
public import VerifiedGarbage.Impl.Bignum.Arm.MaskBytes

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on ARMv7

`vg_rsa_pkcs1_encrypt_precomputed(out = r0, out_len = r1, n = r2,
n_len = r3, e, e_len, msg, msg_len, ps, ps_len, scratch, scratch_len, pre,
pre_len)`, the last ten on the stack. As on AArch64
(`Impl/RsaPkcs1Enc/AArch64/Precomputed.lean`), it builds the encoded message
`EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` in its frame and calls
`vg_rsa_public_precomputed_checked` (`pd`, by its name `pdName`) on it, with
`pre` in place of the modulus; that call writes `EM^e mod n` or zeros to
`out`:

1. `0x00 ‖ 0x02`, then `PS` copied byte by byte (`psLoop`), with `r3`
   collecting, without branches, whether a byte is zero: the top bit of
   `byte - 1`, 1 exactly when the byte is 0. `PS` is at least 8 bytes long
   (a precondition).
2. The separator, and `M` after it (`Bignum.Arm.copyBytes`), unless `M` is
   empty: a branch on a public length.
3. The call, its stack arguments (`e`, `e_len`, `EM`, `n_len`, `scratch`,
   `scratch_len`) at the frame's base.
4. The mask `z - 1` (all ones unless `PS` had a zero byte) and the result
   masked with it; `out` masked with it (`Bignum.Arm.maskBytes`), and `EM`
   overwritten with zeros. Nothing branches on the call's result.

The frame (`Impl/RsaPkcs1Sig/Arm/Wrap.lean`) holds the call's stack
arguments from its base, the zero test at `oZ` and `EM` (up to 1024 bytes)
at `oEM`. Every block either addresses only the stack (through `sp` or
`r12 = sp`) or only registers holding pointers and lengths.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.Arm.Precomputed

open VG VG.Arm
open VG.Impl.RsaPkcs1Sig.Arm (wrap argOff)

/-- The size of the inner frame. -/
def frameBytes : Nat := 1056

/-- The zero test of `PS`, and `EM`. -/
def oZ : Nat := 24
def oEM : Nat := 32

/-- Argument `j` (from 0). -/
def arg (j : Nat) : Nat := argOff frameBytes j

/-- `EM`'s place in `r0`, `PS` in `r1` and its length in `lr`. -/
def start : List Instr :=
  [.addSp .r12 0, .dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oEM)), .ldrSp .r1 (arg 8), .ldrSp .lr (arg 9)]

/-- `0x00 ‖ 0x02`, `r0` after them, and the zero test `r3` cleared. -/
def head : List Instr :=
  [.mov .r2 (.imm 0), .strb .r2 .r0 0, .mov .r2 (.imm 2), .strb .r2 .r0 1, .dp .add .r0 .r0 (.imm 2),
    .mov .r3 (.imm 0)]

/-- One byte of `PS`: copied, and `r3 |= (byte - 1) >> 31`. -/
def psBody : List Instr :=
  [.ldrb .r2 .r1 0, .strb .r2 .r0 0, .dp .sub .r2 .r2 (.imm 1), .dp .orr .r3 .r3 (.shifted .r2 .lsr 31),
    .dp .add .r0 .r0 (.imm 1), .dp .add .r1 .r1 (.imm 1), .subs .lr .lr (.imm 1)]

def psLoop : Prog isa := .loop (.block psBody) .ne

/-- The separator. -/
def sep : List Instr := [.mov .r2 (.imm 0), .strb .r2 .r0 0, .dp .add .r0 .r0 (.imm 1)]

/-- The zero test to its slot, `M` in `r1` and its length in `lr`. -/
def msgArgs : List Instr := [.addSp .r12 0, .str .r3 .r12 oZ, .ldrSp .r1 (arg 6), .ldrSp .lr (arg 7)]

/-- `M`, unless it is empty. -/
def msgCopy : Prog isa := .seq (.block [.cmp .lr (.imm 0)]) (.ite .eq (.block []) Bignum.Arm.copyBytes)

/-- The call's stack arguments, then its registers: `out`, `n_len`, `pre`,
`pre_len`. -/
def callArgs : List Instr :=
  [.addSp .r12 0, .ldrSp .r0 (arg 4), .str .r0 .r12 0, .ldrSp .r0 (arg 5), .str .r0 .r12 4,
    .dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oEM)), .str .r0 .r12 8, .ldrSp .r0 (arg 3), .str .r0 .r12 12,
    .ldrSp .r0 (arg 10), .str .r0 .r12 16, .ldrSp .r0 (arg 11), .str .r0 .r12 20,
    .ldrSp .r0 (arg 0), .ldrSp .r1 (arg 3), .ldrSp .r2 (arg 12), .ldrSp .r3 (arg 13)]

/-- The mask `r2 = z - 1`, the result `r3` masked with it, and `out` and
`n_len` for `maskBytes`. -/
def maskArgs : List Instr :=
  [.addSp .r12 0, .ldrSp .r3 oZ, .dp .sub .r2 .r3 (.imm 1), .dp .and .r3 .r0 (.reg .r2), .ldrSp .r0 (arg 0),
    .ldrSp .lr (arg 3)]

/-- `EM` and `n_len` for `maskBytes` with a zero mask. -/
def wipeArgs : List Instr :=
  [.addSp .r12 0, .dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oEM)), .ldrSp .lr (arg 3), .mov .r2 (.imm 0)]

/-- The inner frame's body. -/
def body (pdName : String) (pd : Prog isa) : Prog isa :=
  .seq (.block start) (.seq (.block head) (.seq psLoop (.seq (.block sep) (.seq (.block msgArgs)
    (.seq msgCopy (.seq (.block callArgs) (.seq (.call pdName pd) (.seq (.block maskArgs)
    (.seq Bignum.Arm.maskBytes (.seq (.block wipeArgs) (.seq Bignum.Arm.maskBytes
      (.block [.mov .r0 (.reg .r3)]))))))))))))

/-- `vg_rsa_pkcs1_encrypt_precomputed`, calling a precomputed public
operation (`pd`) by its name. -/
def code (pdName : String) (pd : Prog isa) : Prog isa := wrap frameBytes (body pdName pd)

end VG.Impl.RsaPkcs1Enc.Arm.Precomputed
