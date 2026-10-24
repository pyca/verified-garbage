module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Frame
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on PPC64LE

`vg_rsa_pkcs1_encrypt_precomputed(out = r3, out_len = r4, n = r5,
n_len = r6, e = r7, e_len = r8, msg = r9, msg_len = r10, ps, ps_len,
scratch, scratch_len, pre, pre_len)`, the last six on the stack (ELFv2 ABI
§2.2.3.3, the Parameter Save Area at `sp + 96`). RFC 8017 §7.2.1, as on
AArch64 (`Impl/RsaPkcs1Enc/AArch64/Precomputed.lean`), in the frame of
`vg_rsa_pkcs1_verify_precomputed` (`Impl/RsaPkcs1Sig/PPC64LE/Frame.lean`):

1. `EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` is written to the frame, and whether
   a byte of `PS` is zero is collected without a branch, then kept in the
   word at `oZ`;
2. `vg_rsa_public_precomputed_checked`, given `pre` in place of the
   modulus, writes `EM^e mod n` or zeros to `out`;
3. the result and `out` are masked to zero if `PS` has a zero byte
   (`vg_rsa_pkcs1_recover_precomputed`'s `maskLoop`), and `EM` is zeroed
   (`encode`'s `fillLoop`).

The lengths are the precondition's, so nothing branches but on `msg_len`
being zero. `out`, `k`, `e` and `e_len` are kept in `r28`–`r31`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.PPC64LE.Precomputed

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)

/-- Whether `PS` has a zero byte, and `EM`. -/
def oZ : Nat := oSt
def oEM : Nat := oEM1

/-- Our caller's registers saved, `out`, `k`, `e` and `e_len` kept, the
first two bytes of `EM`, and `PS`'s copy's registers: `PS` in `r4`, its
length in `r12`, the place of its copy in `r11`, the collected zero test
`r5` zero. -/
def setup : List Instr :=
  save ++ [mov .r28 .r3, mov .r29 .r6, mov .r30 .r7, mov .r31 .r8, .li .r0 0, .stb .r0 .r12 oEM, .li .r0 2,
    .stb .r0 .r12 (oEM + 1), .load .d .r4 .r12 (arg 0), .addi .r11 .r12 (oEM + 2), .li .r5 0,
    .load .d .r12 .r12 (arg 1)]

/-- One byte of `PS`: copied to `EM`, and `r5`'s low bit set if it is zero
(the borrow of `byte - 1`). -/
def psBody : List Instr :=
  [.lbz .r3 .r4 0, .stb .r3 .r11 0, .subi .r0 .r3 1, .lsr .d .r0 .r0 63, .logic .or .r5 .r5 .r0,
    .addi .r4 .r4 1, .addi .r11 .r11 1, .subi .r12 .r12 1]

def psLoop : Prog isa := .loop (.block psBody) (.nonzero .d .r12)

/-- The separator after `PS`; `r11` is then where `M` goes, and `r12` the
frame's base again. -/
def sep : List Instr := [.li .r0 0, .stb .r0 .r11 0, .addi .r11 .r11 1, .addSp .r12 0]

/-- `M` (at `r9`, `r10` bytes) to `r11` (`encode`'s `copyLoop`), unless it
is empty. -/
def msgCopy : Prog isa :=
  .ite (.nonzero .d .r10) (.seq (.block [mov .r7 .r9, mov .r4 .r11, mov .r8 .r10]) copyLoop) (.block [])

/-- The zero test to its word, and the arguments of the call: `out`, `k`,
`pre`, `pre_len`, `e`, `e_len`, `EM` and `k`, then `scratch` and
`scratch_len`. -/
def callArgs : List Instr :=
  [.store .d .r5 .r12 oZ, mov .r3 .r28, mov .r4 .r29, mov .r7 .r30, mov .r8 .r31, .addi .r9 .r12 oEM,
    mov .r10 .r29,
    .load .d .r0 .r12 (arg 2), .store .d .r0 .r12 96, .load .d .r0 .r12 (arg 3), .store .d .r0 .r12 104,
    .load .d .r5 .r12 (arg 4), .load .d .r6 .r12 (arg 5)]

/-- The mask, all ones unless `PS` has a zero byte (`z - 1`), into `r9`, and
the result under it; `out` into `r11` and `k` into `r8`. -/
def maskArgs : List Instr :=
  [.addSp .r12 0, .load .d .r9 .r12 oZ, .subi .r9 .r9 1, .logic .and .r3 .r3 .r9, mov .r11 .r28, mov .r8 .r29]

/-- `fillLoop`'s registers to zero `EM`: its place, `k` and the zero byte. -/
def wipeArgs : List Instr := [.addSp .r12 0, .addi .r4 .r12 oEM, mov .r11 .r29, .li .r0 0]

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

end VG.Impl.RsaPkcs1Enc.PPC64LE.Precomputed
