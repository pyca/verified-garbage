module

public import VerifiedGarbage.Impl.RsaOaep.X86_64
public import VerifiedGarbage.Impl.ForwardCall.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-!
# RSAES-PKCS1-v1_5 decryption with the message first, on x86-64

`vg_rsa_pkcs1_decrypt_precomputed` takes the arguments of
`vg_rsa_pkcs1_decrypt_precomputed_body` and calls it (`body`, by its name) with
them: the six argument registers as they came, and its 19 stack arguments
copied to the bottom of a frame of `frameBytes` (296) bytes, RSAES-OAEP's
(`Impl/RsaOaep/X86_64.lean`), which keeps `rsp` a multiple of 16 at the
call. `out`, `out_len` (`k`) and `msg_len` wait for the call in the frame's
slots `sOut`, `sK` and `sMl` (`setup`).

That function writes the message `M` at the end of `out`, after `k - L`
zeros (`L` its length, at `*msg_len`), or zeros and a length of 0. After
the call its result waits in `sR`, `scratch` (the stack argument 15) in
`sScr` (`after`), and the first `oBuf + 2048` bytes of `scratch`, whose
contents on return are unspecified, hold a buffer of 2048 bytes at `oBuf`:
its first `8 ⌈k / 4⌉` bytes, at least the `2 k` that the shift reads,
cleared (`clearBuf`), `out`'s `k` bytes copied to it (`copyIn`), shifted
left by `s = k - *msg_len` bytes in a pass for each bit of `k` (`shift`),
pass `j` moving each of its first `k` bytes `2^j` bytes under the mask of
bit `j` of `s` (`shiftPass`), after which the next pass runs while
`2^(j+1) ≤ k` (`nextPass`; `s ≤ k < 2^(j+1)` after the last), and its first
`k` bytes copied back to `out` (`copyOut`): `M`, then zeros. Pass `j` reads
at most `k + 2^j ≤ 2 k` bytes of the buffer. `*msg_len` is left as the call
wrote it, and the result is the call's. No address or branch depends on
`s`, which is secret, but on `k`, which is public: only masks do.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.X86_64.Front

open VG.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sOut sK sMl sR sA sScr oBuf scr arg)
open VG.Impl.Mgf1.X86_64 (sp ix at_ byteLoop seqs)
open VG.Impl.ForwardCall.X86_64 (copies)

/-- The stack arguments to the frame's bottom, then `out`, `k` and
`msg_len` to their slots. -/
def setup : List Instr :=
  copies frameBytes 19 ++ [.store (sp sOut) .rdi, .store (sp sK) .rsi, .store (sp sMl) .rdx]

/-- The call's result to `sR`, and `scratch` (the stack argument 15) to
`sScr`, by `r11`. -/
def after : List Instr := [.store (sp sR) .rax, .mov .r11 (.mem (arg 15)), .store (sp sScr) .r11]

/-- The buffer's first `8 ⌈k / 4⌉` bytes (in `r10`) cleared, with its
address in `rcx` for the pieces after it. -/
def clearBuf : Prog isa :=
  .seq (.block (scr .rcx oBuf ++ [.mov32 .rax (.imm 0), .mov32 .r8 (.imm 0), .mov .r10 (.mem (sp sK)),
      .alu .add .r10 (.imm 3), .shift .shr .r10 2, .shift .shl .r10 3]))
    (.loop (.block [.store (ix .rcx .r8) .rax, .alu .add .r8 (.imm 8), .alu .cmp .r8 (.reg .r10)]) .ne)

/-- `out`'s `k` bytes (at `rsi`, `r10` of them) to the buffer (at `rcx`). -/
def copyIn : Prog isa :=
  .seq (.block [.mov .rsi (.mem (sp sOut)), .mov .r10 (.mem (sp sK)), .mov32 .r8 (.imm 0)])
    (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8) .rax] (.reg .r10))

/-- One pass, with the buffer at `rcx`: each of its first `k` (`r10`) bytes
replaced by the one `d` (`rdx`) after it if bit 0 of `a` (`sA`) is set. -/
def shiftPass : Prog isa :=
  .seq (.block [.mov .rsi (.reg .rdx), .alu .add .rsi (.reg .rcx),
      .mov .r11 (.mem (sp sA)), .alu .and .r11 (.imm 1), .mov32 .r9 (.imm 0), .alu .sub .r9 (.reg .r11),
      .mov32 .r8 (.imm 0)])
    (byteLoop [.movzx8 .rax (ix .rcx .r8), .movzx8 .rdi (ix .rsi .r8), .alu .xor .rdi (.reg .rax),
      .alu .and .rdi (.reg .r9), .alu .xor .rax (.reg .rdi), .store8 (ix .rcx .r8) .rax] (.reg .r10))

/-- The next pass: `a >>= 1`, `d += d`, and CF clear while `d ≤ k`. -/
def nextPass : List Instr :=
  [.mov .rax (.mem (sp sA)), .shift .shr .rax 1, .store (sp sA) .rax, .alu .add .rdx (.reg .rdx),
    .alu .cmp .r10 (.reg .rdx)]

/-- The buffer (at `rcx`) shifted left by `k - *msg_len` bytes, in a pass
for each bit of `k`. -/
def shift : Prog isa :=
  .seq (.block [.mov .rax (.mem (sp sK)), .mov .r10 (.reg .rax), .mov .rdi (.mem (sp sMl)),
      .alu .sub .rax (.mem (at_ .rdi)), .store (sp sA) .rax, .mov32 .rdx (.imm 1)])
    (.loop (.seq shiftPass (.block nextPass)) .ae)

/-- The buffer's first `k` bytes to `out`. -/
def copyOut : Prog isa :=
  .seq (.block [.mov .rdi (.mem (sp sOut)), .mov .r10 (.mem (sp sK)), .mov32 .r8 (.imm 0)])
    (byteLoop [.movzx8 .rax (ix .rcx .r8), .store8 (ix .rdi .r8) .rax] (.reg .r10))

/-- The call's result back to `rax`. -/
def ret : List Instr := [.mov .rax (.mem (sp sR))]

/-- `out`'s bytes, shifted, in the buffer. -/
def toBuf : Prog isa := seqs [clearBuf, copyIn, shift]

/-- After the call: the message moved to the start of `out`. -/
def tail : Prog isa := seqs [toBuf, copyOut, .block ret]

/-- The function's body, calling `vg_rsa_pkcs1_decrypt_precomputed_body`
(`callee`) by `name`. -/
def body (name : String) (callee : Prog isa) : Prog isa :=
  seqs [.block setup, .call name callee, .block after, tail]

/-- `vg_rsa_pkcs1_decrypt_precomputed`, calling `callee` by `name`. -/
def code (name : String) (callee : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body name callee) (.free frameBytes)

end VG.Impl.RsaPkcs1Enc.X86_64.Front

namespace VG.Impl.RsaPkcs1Enc.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

/-- `Spec.RsaPkcs1Enc.decryptPrecomputedApi`'s function as emitted,
calling `vg_rsa_pkcs1_decrypt_precomputed_body`'s code `callee` by `name`, then
its cleanup at the level `v`: the 3784 bytes of stack its frame (296), its
call (8) and the callee (3480) use zeroed. -/
def decryptPrecomputed (v : VecLevel) (name : String) (callee : Prog isa) : Prog isa :=
  scrubAll v 32 3784 (Front.code name callee)

end VG.Impl.RsaPkcs1Enc.X86_64.Fn
