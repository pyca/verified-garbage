module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Frame
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.RecoverPrecomputed

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on RISC-V

`vg_rsa_pkcs1_encrypt_precomputed(out = a0, out_len = a1, n = a2,
n_len = a3, e = a4, e_len = a5, msg = a6, msg_len = a7, ps, ps_len,
scratch, scratch_len, pre, pre_len)`, the last six on the stack. RFC 8017
§7.2.1, as on PPC64LE (`Impl/RsaPkcs1Enc/PPC64LE/Precomputed.lean`), in the
frame of `vg_rsa_pkcs1_verify_precomputed`
(`Impl/RsaPkcs1Sig/RISCV64/Frame.lean`):

1. `EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` is written to the frame, and whether
   a byte of `PS` is zero is collected without a branch, then kept in the
   word at `oZ`;
2. `vg_rsa_public_precomputed_checked`, given `pre` in place of the
   modulus, writes `EM^e mod n` or zeros to `out`;
3. the result and `out` are masked to zero if `PS` has a zero byte
   (`vg_rsa_pkcs1_recover_precomputed`'s `maskLoop`), and `EM` is zeroed
   (`encode`'s `fillLoop`).

The lengths are the precondition's, so nothing branches but on `msg_len`
being zero. `out`, `k`, `e` and `e_len` are kept in `s1`–`s4`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.RISCV64.Precomputed

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64

/-- Whether `PS` has a zero byte, and `EM`. -/
def oZ : Nat := oSt
def oEM : Nat := oEM1

/-- Our caller's registers saved, `out`, `k`, `e` and `e_len` kept, the
first two bytes of `EM`, and `PS`'s copy's registers: `PS` in `t2`, its
length in `t3`, the place of its copy in `t4`, the collected zero test
`t5` zero. -/
def setup : List Instr :=
  save ++ [mov .s1 .a0, mov .s2 .a3, mov .s3 .a4, mov .s4 .a5, .li .t1 0, .store .b .t1 .t0 oEM, .li .t1 2,
    .store .b .t1 .t0 (oEM + 1)] ++ argBase ++
  [.load .d .t2 .t6 0, .load .d .t3 .t6 8, .addi .t4 .t0 (oEM + 2), .li .t5 0]

/-- One byte of `PS`: copied to `EM`, and `t5`'s low bit set if it is zero
(the borrow of `byte - 1`). -/
def psBody : List Instr :=
  [.load .b .t1 .t2 0, .store .b .t1 .t4 0, .addi .t1 .t1 (-1), .shift .srl .d .t1 .t1 63,
    .logic .or .t5 .t5 .t1, .addi .t2 .t2 1, .addi .t4 .t4 1]

def psLoop : Prog isa := Impl.Bignum.RISCV64.countLoop .t3 psBody

/-- The separator after `PS`; `t4` is then where `M` goes. -/
def sep : List Instr := [.li .t1 0, .store .b .t1 .t4 0, .addi .t4 .t4 1]

/-- `M` (at `a6`, `a7` bytes) to `t4` (`encode`'s `copyLoop`), unless it
is empty. -/
def msgCopy : Prog isa :=
  .ite (.nonzero .a7) (.seq (.block [mov .a4 .a6, mov .a1 .t4, mov .a5 .a7]) copyLoop) (.block [])

/-- The zero test to its word, and the arguments of the call: `out`, `k`,
`pre`, `pre_len`, `e`, `e_len`, `EM` and `k`, then `scratch` and
`scratch_len`. -/
def callArgs : List Instr :=
  [.addSp .t0 0, .store .d .t5 .t0 oZ, mov .a0 .s1, mov .a1 .s2, mov .a4 .s3, mov .a5 .s4, .addi .a6 .t0 oEM,
    mov .a7 .s2] ++ argBase ++
  [.load .d .t1 .t6 16, .store .d .t1 .t0 0, .load .d .t1 .t6 24, .store .d .t1 .t0 8,
    .load .d .a2 .t6 32, .load .d .a3 .t6 40]

/-- The mask, all ones unless `PS` has a zero byte (`z - 1`), into `a3`, and
the result under it; `out` into `a1` and `k` into `a5`. -/
def maskArgs : List Instr :=
  [.addSp .t0 0, .load .d .a3 .t0 oZ, .addi .a3 .a3 (-1), .logic .and .a0 .a0 .a3, mov .a1 .s1, mov .a5 .s2]

/-- `fillLoop`'s registers to zero `EM`: its place, `k` and the zero byte. -/
def wipeArgs : List Instr := [.addSp .t0 0, .addi .a1 .t0 oEM, mov .t5 .s2, .li .t0 0]

/-- `EM` and the call's arguments. -/
def preCall : Prog isa := .seq psLoop (.seq (.block sep) (.seq msgCopy (.block callArgs)))

/-- After the call: the masks, `EM` zeroed and the restores. -/
def tail : Prog isa :=
  .seq (.block maskArgs)
    (.seq RecoverPrecomputed.maskLoop (.seq (.block wipeArgs) (.seq fillLoop (.block restore))))

/-- The body of the frame. -/
def body : Prog isa := .seq (.block setup) (.seq preCall (.seq pubCall tail))

/-- `vg_rsa_pkcs1_encrypt_precomputed`. -/
def code : Prog isa := .frame (.alloc frameBytes) body (.free frameBytes)

end VG.Impl.RsaPkcs1Enc.RISCV64.Precomputed
