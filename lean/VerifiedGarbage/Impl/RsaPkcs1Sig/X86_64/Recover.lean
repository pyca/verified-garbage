module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Verify

/-!
# RSASSA-PKCS1-v1_5 recovery on x86-64

`vg_rsa_pkcs1_recover(out, out_len, n, n_len, e, e_len, hash, sig, sig_len,
scratch, scratch_len)`: the first six arguments in registers, the others on
the stack. It recovers as OpenSSL's `ossl_rsa_verify` with `rm` does, which
`Proof/RsaPkcs1Sig/Recover.lean` proves BoringSSL's recovery:

1. if `sig_len` is not `n_len`, it writes zeros to `out` and returns 0;
2. `vg_rsa_public_checked` writes `EM = s^e mod n` (`k` bytes) to a buffer
   `EM₁` in its frame, and it writes zeros and returns 0 if that fails;
3. `encode` writes the encoding of the last `out_len` bytes of `EM₁` (the
   hash value, if `EM` is an encoding: `out_len` is the length of the hash
   function's values) to a buffer `EM₂`, and it writes zeros and returns 0 if
   that fails;
4. if `EM₁` and `EM₂` are equal (`compare`), it copies those `out_len` bytes
   to `out` and returns 1; otherwise it writes zeros and returns 0.

Everything is public, so it branches freely. The frame is
`vg_rsa_pkcs1_verify`'s, with other slots.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.X86_64.Recover

open VG VG.X86_64
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea test0)

/-- The slots: `out`, `out_len`, `n`, `n_len`, `e`, `e_len`. -/
def oOut : Nat := 32
def oOl : Nat := 40
def oN : Nat := 48
def oK : Nat := 56
def oE : Nat := 64
def oEl : Nat := 72

/-- `sig_len` against `n_len`. -/
def lenCheck : List Instr := [.mov .rax (.mem (arg0 2)), .alu .cmp .rax (.reg .rcx)]

/-- Zeros to the `rsi` (at least 1) bytes at `rdi` (`encode`'s loop for `PS`,
with `r8` the buffer), and 0 returned. -/
def zeroOut : Prog isa :=
  .seq (.block [.mov .r8 (.reg .rdi), .mov .r10 (.reg .rsi), .mov32 .rax (.imm 0)]) psLoop

/-- `zeroOut`, with `out` and `out_len` from their slots. -/
def zeroSlots : Prog isa :=
  .seq (.block [.mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oOl))]) zeroOut

/-- The arguments kept into the slots, and those of `vg_rsa_public_checked`:
`EM₁`, `n`, `e`, `sig` and the working space, `n_len` as every length of the
modulus. -/
def pubArgs : List Instr :=
  [.store (sp oOut) .rdi, .store (sp oOl) .rsi, .store (sp oN) .rdx, .store (sp oK) .rcx,
    .store (sp oE) .r8, .store (sp oEl) .r9,
    .mov .rax (.mem (arg 1)), .mov .r10 (.mem (arg 3)), .mov .r11 (.mem (arg 4)),
    .store (sp 0) .rax, .store (sp 8) .rcx, .store (sp 16) .r10, .store (sp 24) .r11,
    .mov .rsi (.reg .rcx)] ++
  lea .rdi oEM1

/-- `rsi := EM₁ + k - out_len`, the hash value's place in `EM₁`, with `k` in
`rcx` and `out_len` in `r9`. -/
def valPtr : List Instr := lea .rsi oEM1 ++ [.alu .add .rsi (.reg .rcx), .alu .sub .rsi (.reg .r9)]

/-- The arguments of `encode`: `EM₂`, `k`, `hash` (zero-extended from its 32
bits), the last `out_len` bytes of `EM₁` and `out_len`. -/
def encArgs : List Instr :=
  lea .r8 oEM2 ++ [.mov .rcx (.mem (sp oK)), .mov .rdx (.mem (arg 0)), .mov32 .rdx (.reg .rdx),
    .mov .r9 (.mem (sp oOl))] ++ valPtr

/-- The value to `out`, and 1 returned: `out_len` bytes from the hash value's
place in `EM₁` (`encode`'s loop for the hash value, with `r8` the buffer),
counted down in `r9`. -/
def copyOut : Prog isa :=
  .seq (.block ([.mov .r8 (.mem (sp oOut)), .mov .rdi (.reg .r8), .mov .r9 (.mem (sp oOl))] ++ valPtr))
    (.seq copyLoop (.block [.mov32 .rax (.imm 1)]))

/-- After the comparison, its result in `rdx`. -/
def release : Prog isa := .seq (.block [.alu .test .rdx (.reg .rdx)]) (.ite .ne zeroSlots copyOut)

/-- After the encoding. -/
def tail : Prog isa :=
  .seq (.block test0) (.ite .e zeroSlots (.seq (.block Verify.cmpArgs) (.seq compare release)))

/-- After the call. -/
def afterPub : Prog isa :=
  .seq (.block test0) (.ite .e zeroSlots (.seq (.block encArgs) (.seq encode tail)))

/-- The body of the frame. -/
def body (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block pubArgs) (.seq (.call pubName pub) afterPub)

/-- `vg_rsa_pkcs1_recover`, calling `vg_rsa_public_checked` (`pub`) by its
name. -/
def code (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block lenCheck)
    (.ite .ne zeroOut (.frame (.alloc frameBytes) (body pubName pub) (.free frameBytes)))

end VG.Impl.RsaPkcs1Sig.X86_64.Recover
