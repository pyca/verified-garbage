module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Recover
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Encrypt

/-!
# RSASSA-PKCS1-v1_5 recovery with a precomputed public key on x86-64

`vg_rsa_pkcs1_recover_precomputed(out, out_len, n, n_len, e, e_len, hash,
sig, sig_len, scratch, scratch_len, pre, pre_len)`: `Recover.code`, with the
precomputed modulus `pre` (the stack arguments 5 and 6) in place of `n` for
the public operation, `vg_rsa_public_precomputed_checked` or one of its
variants. Its result is unspecified when `pre` does not hold the values for
`n`, so nothing after the call branches on it or on `EM₁`: the call's status
is kept in a slot, the encoding of the last `out_len` bytes of `EM₁` is
always written and compared with `EM₁`, and the value is copied to `out` and
masked to zeros, and the result to 0, unless the status is not 0 and the two
are equal (`release`). The branch on whether `encode` succeeds depends only
on `hash` and `n_len`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed

open VG VG.X86_64
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes sp arg test0 cmpArgs)
open VG.Impl.RsaPkcs1Sig.X86_64.Recover (lenCheck zeroOut zeroSlots copyOut encArgs oOut oOl)

/-- The original arguments of the public operation, then `pre` and
`pre_len` in place of `n` and `n_len`. -/
def pubArgs : List Instr := Recover.pubArgs ++
  ([.mov .rdx (.mem (arg 5)), .mov .rcx (.mem (arg 6))] : List Instr)

/-- The mask into slot 8: all ones if `rdx` (the comparison's difference)
is 0 and the low 32 bits of the status in slot 0 are not, zero if not. -/
def maskM : List Instr :=
  [.alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx), .mov .rax (.mem (sp 0)), .alu32 .cmp .rax (.imm 1),
    .alu .sbb .rax (.reg .rax), .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))), .alu .and .rdx (.reg .rax),
    .store (sp 8) .rdx]

/-- The registers of `Encrypt.maskLoop`: `out`, `out_len`, the mask and the
index. -/
def maskArgs : List Instr :=
  [.mov .rdi (.mem (sp oOut)), .mov .rcx (.mem (sp oOl)), .mov .rdx (.mem (sp 8)), .mov32 .r10 (.imm 0)]

/-- The result: 1 under the mask. -/
def fin : List Instr := [.mov .rax (.reg .rdx), .alu .and .rax (.imm 1)]

/-- After the comparison, its difference in `rdx`: the value to `out`, then
`out` and the result masked. -/
def release : Prog isa :=
  .seq (.block maskM) (.seq copyOut (.seq (.block maskArgs) (.seq Impl.RsaPkcs1Enc.X86_64.Encrypt.maskLoop
    (.block fin))))

/-- After the encoding. -/
def tail : Prog isa :=
  .seq (.block test0) (.ite .e zeroSlots (.seq (.block cmpArgs) (.seq compare release)))

/-- After the call: its status to slot 0, and the encoding. -/
def afterPub : Prog isa :=
  .seq (.block ([.store (sp 0) .rax] ++ encArgs)) (.seq encode tail)

/-- The body of the frame. -/
def body (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block pubArgs) (.seq (.call pubName pub) afterPub)

/-- `vg_rsa_pkcs1_recover_precomputed`, calling an implementation of
`vg_rsa_public_precomputed_checked` (`pub`) by its name. -/
def code (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block lenCheck)
    (.ite .ne zeroOut (.frame (.alloc frameBytes) (body pubName pub) (.free frameBytes)))

end VG.Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed
