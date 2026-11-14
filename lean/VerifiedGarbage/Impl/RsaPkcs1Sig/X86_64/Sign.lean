module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Recover

/-!
# RSASSA-PKCS1-v1_5 signing on x86-64

`vg_rsa_pkcs1_sign(out, out_len, n, n_len, e, e_len, hash, digest,
digest_len, p, p_len, q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len,
scratch, scratch_len)`: the first six arguments in registers, the others on
the stack. It is RFC 8017 §8.2.1, from verified functions:

1. `encode` writes the encoding of `digest` to a buffer `EM` in its frame;
   if that fails, it writes zeros to `out` and returns 0;
2. `vg_rsa_private_checked` (or a variant) computes the signature of `EM`
   into `out`, checked against `e`, and returns its result;
3. it overwrites `EM` with zeros.

`vg_rsa_pkcs1_sign_precomputed` (`codeP`) is the same, but for its call of
`vg_rsa_private_checked_precomputed`, which it also gives `pre`.

Only the public key, the lengths and `hash` decide a branch or an address:
the hash value is only copied into `EM`, which only the private operation
reads.

The frame of `frameBytes` bytes holds, at `rsp`, the 14 stack arguments of
the call; at `oOut` … `oEl`, the arguments kept across `encode`; at `oEM`,
`EM`, up to 1024 bytes. Only caller-saved registers are used. With the
frame, `rsp` is a multiple of 16 at the call.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.X86_64.Sign

open VG VG.X86_64
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea test0)
open VG.Impl.RsaPkcs1Sig.X86_64.Recover (zeroOut)

/-- The size of the frame. -/
def frameBytes : Nat := 1192

/-- The slots: `out`, `out_len`, `n`, `n_len`, `e`, `e_len`. -/
def oOut : Nat := 112
def oOl : Nat := 120
def oN : Nat := 128
def oK : Nat := 136
def oE : Nat := 144
def oEl : Nat := 152
/-- `EM`. -/
def oEM : Nat := 160

/-- The stack argument `j` (from 0) of the function, from the frame. -/
def arg (j : Nat) : MemOp := sp (frameBytes + 8 + 8 * j)

/-- The arguments kept into the slots. -/
def slotStores : List Instr :=
  [.store (sp oOut) .rdi, .store (sp oOl) .rsi, .store (sp oN) .rdx, .store (sp oK) .rcx,
    .store (sp oE) .r8, .store (sp oEl) .r9]

/-- The arguments of `encode`: `EM`, `k` (still in `rcx`), `hash`
(zero-extended from its 32 bits), `digest` and `digest_len`. -/
def encArgs : List Instr :=
  lea .r8 oEM ++ [.mov .rdx (.mem (arg 0)), .mov32 .rdx (.reg .rdx), .mov .rsi (.mem (arg 1)),
    .mov .r9 (.mem (arg 2))]

/-- Zeros to `out`, with its address and length from the slots. -/
def zeroSlots : Prog isa :=
  .seq (.block [.mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oOl))]) zeroOut

/-- Stack argument `j + 3` of the function to the call's stack argument
`j + 2`: `p` … `scratch_len`. -/
def copyArg (j : Nat) : List Instr := [.mov .rax (.mem (arg (j + 3))), .store (sp (8 * (j + 2))) .rax]

/-- The arguments of `vg_rsa_private_checked`: those of the function, with
`EM` as the input. -/
def callArgs : List Instr :=
  [.mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oOl)), .mov .rdx (.mem (sp oN)), .mov .rcx (.mem (sp oK)),
    .mov .r8 (.mem (sp oE)), .mov .r9 (.mem (sp oEl))] ++ lea .rax oEM ++
  [.store (sp 0) .rax, .store (sp 8) .rcx] ++ (List.range 12).flatMap copyArg

/-- `EM` overwritten with zeros, keeping the result in `rax`. -/
def wipe : Prog isa :=
  .seq (.block ([.mov .r11 (.mem (sp oK)), .mov32 .rdx (.imm 0)] ++ lea .r10 oEM))
    (.loop (.block [.store8 { base := .r10 } .rdx, .alu .add .r10 (.imm 1), .alu .sub .r11 (.imm 1)]) .ne)

/-- The arguments of `vg_rsa_private_checked_precomputed`: `callArgs`, then
`pre` and `pre_len` (the function's stack arguments 15 and 16) as its stack
arguments 14 and 15, over the slots of `out` and `out_len`, which nothing
reads after the call. -/
def callArgsP : List Instr := callArgs ++ copyArg 12 ++ copyArg 13

/-- After the encoding, with the arguments `args` of the call. -/
def afterEncWith (args : List Instr) (privName : String) (priv : Prog isa) : Prog isa :=
  .seq (.block test0) (.ite .e zeroSlots (.seq (.block args) (.seq (.call privName priv) wipe)))

/-- The body of `codeP`'s frame. -/
def bodyP (privName : String) (priv : Prog isa) : Prog isa :=
  .seq (.block (slotStores ++ encArgs)) (.seq encode (afterEncWith callArgsP privName priv))

/-- `vg_rsa_pkcs1_sign_precomputed`: `code`, calling
`vg_rsa_private_checked_precomputed` (`priv`) by its name with the key's
precomputed values `pre`. -/
def codeP (privName : String) (priv : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (bodyP privName priv) (.free frameBytes)

end VG.Impl.RsaPkcs1Sig.X86_64.Sign
