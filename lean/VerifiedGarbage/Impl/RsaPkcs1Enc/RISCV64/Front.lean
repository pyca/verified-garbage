module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.RISCV64.Decrypt
public import VerifiedGarbage.Impl.RsaOaep.RISCV64.Decrypt
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# RSAES-PKCS1-v1_5 decryption with the message first, on RISC-V

`vg_rsa_pkcs1_decrypt_precomputed` takes the arguments of
`vg_rsa_pkcs1_decrypt_precomputed_body` and calls it (`body`, by its name) with
them: the eight argument registers as they came, and its 17 stack arguments
copied to the bottom of a frame of `frameBytes` (176) bytes (`copyArg`, as
`withStackScratchArgs` copies them), which keeps `sp` a multiple of 16 at
the call. The call overwrites the return address, which waits in the frame's
slot `sRa`; `out`, `out_len` (`k`) and `msg_len` wait in `sOut`, `sK` and
`sMl` (`setup`).

That function writes the message `M` at the end of `out`, after `k - L`
zeros (`L` its length, at `*msg_len`), or zeros and a length of 0. After the
call its result stays in `a0`, which nothing after writes, and `out`, `k`,
`scratch` (our stack argument 13) and `s = k - *msg_len` are loaded into
`a7`, `t6`, `a6` and `t3` (`load`, `diff`). The first 2048 bytes of
`scratch`, whose contents on return are unspecified, hold a buffer: cleared
(`clearBuf`, RSASSA-PKCS1-v1_5's `fillLoop`), `out`'s `k` bytes copied to it
(`copyIn`, its `copyLoop`), shifted left by `s` bytes in eleven passes
(`shift`), pass `j` replacing each of its first `k` bytes by the one `2^j`
bytes after it under the mask of bit `j` of `s` (RSAES-OAEP decryption's
`passBody`; `s ≤ k ≤ 1024 < 2^11`, and `k + 1024 ≤ 2048`), and its first `k`
bytes copied back to `out` (`copyOut`): `M`, then zeros. `*msg_len` is left
as the call wrote it, and the result is the call's. No address or branch
depends on `s`, which is secret: only masks do.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.RISCV64.Front

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (mov)
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Impl.RsaPkcs1Sig.RISCV64 (copyLoop fillLoop)
open VG.Impl.StackScratch.RISCV64 (copyArg)

/-! ## The frame -/

/-- The size of the frame: the 17 copies of the stack arguments (136
bytes), then the slots. -/
def frameBytes : Nat := 176

/-- Where the return address, `out`, `k` and `msg_len` wait for the call. -/
def sRa : Nat := 136
def sOut : Nat := 144
def sK : Nat := 152
def sMl : Nat := 160

/-- Where our stack argument 13, `scratch`, is from `sp`. -/
def aScr : Nat := frameBytes + 8 * 13

/-- `t0 := sp`, the stack arguments to the frame's bottom, then the return
address, `out`, `k` and `msg_len` to their slots. -/
def setup : List Instr :=
  [.addSp .t0 0] ++ (List.range 17).flatMap (copyArg frameBytes) ++
    [.store .d .ra .t0 sRa, .store .d .a0 .t0 sOut, .store .d .a1 .t0 sK, .store .d .a2 .t0 sMl]

/-! ## After the call -/

/-- `out`, `k`, `scratch` and `msg_len` into `a7`, `t6`, `a6` and `t3`. -/
def load : List Instr :=
  [.addSp .t0 0, .load .d .a7 .t0 sOut, .load .d .t6 .t0 sK, .load .d .a6 .t0 aScr, .load .d .t3 .t0 sMl]

/-- `s = k - *msg_len` into `t3`. -/
def diff : List Instr := [.load .d .t3 .t3 0, .sub .t3 .t6 .t3]

/-- The buffer's 2048 bytes cleared (`2048 = 1 << 11`, past the reach of an
immediate). -/
def clearBuf : Prog isa :=
  .seq (.block [mov .a1 .a6, .li .t5 1, .shift .sll .d .t5 .t5 11, .li .t0 0]) fillLoop

/-- `out`'s `k` bytes to the buffer. -/
def copyIn : Prog isa := .seq (.block [mov .a4 .a7, mov .a1 .a6, mov .a5 .t6]) copyLoop

/-- A pass: each of the buffer's first `k` bytes replaced by the one `d`
(`t4`) bytes after it if bit 0 of `x` (`t3`) is set. -/
def shiftPass : Prog isa :=
  .seq (.block [mov .a1 .a6, .add .a2 .a1 .t4, .li .a3 1, .logic .and .a3 .t3 .a3, .li .a4 0,
      .sub .a3 .a4 .a3, mov .a5 .t6])
    (countLoop .a5 Impl.RsaOaep.RISCV64.Dec.passBody)

/-- The next pass: `x` halved, `d` doubled, the count of passes (`t5`) less
one. -/
def nextPass : List Instr := [.shift .srl .d .t3 .t3 1, .add .t4 .t4 .t4, .addi .t5 .t5 (-1)]

/-- The buffer shifted left by `s` (`t3`) bytes, in eleven passes, the
`j`-th by `d = 2^j`. -/
def shift : Prog isa := .seq (.block [.li .t4 1, .li .t5 11]) (.loop (.seq shiftPass (.block nextPass)) (.nonzero .t5))

/-- The buffer's first `k` bytes to `out`. -/
def copyOut : Prog isa := .seq (.block [mov .a4 .a6, mov .a1 .a7, mov .a5 .t6]) copyLoop

/-- The return address back. -/
def ret : List Instr := [.addSp .t0 0, .load .d .ra .t0 sRa]

/-- After the loads: the message moved to the start of `out`. -/
def tail : Prog isa :=
  .seq (.block diff) (.seq clearBuf (.seq copyIn (.seq shift (.seq copyOut (.block ret)))))

/-- The function's body, calling `vg_rsa_pkcs1_decrypt_precomputed_body`
(`callee`) by `name`. -/
def body (name : String) (callee : Prog isa) : Prog isa :=
  .seq (.block setup) (.seq (.call name callee) (.seq (.block load) tail))

/-- `vg_rsa_pkcs1_decrypt_precomputed`, calling `callee` by `name`. -/
def code (name : String) (callee : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body name callee) (.free frameBytes)

end VG.Impl.RsaPkcs1Enc.RISCV64.Front

namespace VG.Impl.RsaPkcs1Enc.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll)

/-- The internal name of `vg_rsa_pkcs1_decrypt_precomputed_body`'s code before
its cleanup, which `vg_rsa_pkcs1_decrypt_precomputed` calls. -/
def bodyName : String := "vg_rsa_pkcs1_decrypt_precomputed_body"

/-- `vg_rsa_pkcs1_decrypt_precomputed`: `Front.code` calling
`vg_rsa_pkcs1_decrypt_precomputed_body`'s code before its cleanup, then the
cleanup of the 3632 bytes of stack its frame (176) and the callee (3456)
use. -/
def decryptPrecomputed : Prog isa := scrubAll 32 3632 (Front.code bodyName Decrypt.codeP)

end VG.Impl.RsaPkcs1Enc.RISCV64.Fn
