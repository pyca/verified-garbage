module

public import VerifiedGarbage.Impl.Rsa.X86_64.PrivChecked

/-!
# RSA's private-key operation checked against `e`, with precomputed values, on x86-64

`vg_rsa_private_checked_precomputed(out, out_len, n, n_len, e, e_len, input,
input_len, p, p_len, q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len,
scratch, scratch_len, pre, pre_len)`: the first six arguments in registers,
the others on the stack. It is `vg_rsa_private_checked`
(`PrivChecked.lean`) with the values `vg_rsa_private_precompute` wrote to
`pre`:

1. `vg_rsa_private_crt_precomputed` (or one of its variants) computes `m`
   from the input `c` and `pre` into a buffer `M` on the stack, returning
   `r₁`;
2. `vg_rsa_public_precomputed_checked` writes `M^e mod n` to `out` from
   `n`'s values, the first `2 ⌈n_len / 8⌉` words of `pre`, returning `r₂`;
3. `out` is compared with `c` and `M` released as `vg_rsa_private_checked`
   does, with `r₁ = r₂ = 1`.

The frame is `vg_rsa_private_checked`'s without `n`'s values and `r₃`, with
the slots past the 14 stack arguments of the CRT's call.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.PrivCheckedPc

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Rsa.X86_64.PrivChecked (sp lea oM cmpLoop masks releaseLoop at10)

/-- The size of the frame. -/
def frameBytes : Nat := 1192

/-- The slots: `out`, `n`, `n_len`, `e`, `e_len`, `r₁`. -/
def oOut : Nat := 112
def oN : Nat := 120
def oK : Nat := 128
def oE : Nat := 136
def oEl : Nat := 144
def oR1 : Nat := 152

/-- The stack argument `j` (from 0) of the function, from the frame. -/
def arg (j : Nat) : MemOp := sp (frameBytes + 8 + 8 * j)

/-- `r := 2 ⌈n_len / 8⌉`, the words of `n`'s values. -/
def preWords (r : Reg) : List Instr :=
  [.mov r (.mem (sp oK)), .alu .add r (.imm 7), .shift .shr r 3, .alu .add r (.reg r)]

/-- The arguments kept into the slots, and those of
`vg_rsa_private_crt_precomputed`: `M`, `n`, the input, the private key, the
working space and `pre`, `n_len` as every length of the modulus. -/
def crtArgs : List Instr :=
  ([.store (sp oOut) .rdi, .store (sp oN) .rdx, .store (sp oK) .rcx, .store (sp oE) .r8, .store (sp oEl) .r9] : List Instr) ++
  (List.range 14).flatMap (fun j => [.mov .rax (.mem (arg (j + 2))), .store (sp (8 * j)) .rax]) ++
  lea .rdi oM ++ ([.mov .rsi (.reg .rcx), .mov .r8 (.mem (arg 0)), .mov .r9 (.reg .rcx)] : List Instr)

/-- `r₁` kept, and the arguments of `vg_rsa_public_precomputed_checked`:
`out`, `n`'s values from `pre`, `e`, `M` as the input, the working space. -/
def pdArgs : List Instr :=
  ([.store (sp oR1) .rax, .mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oK)), .mov .rdx (.mem (arg 14))] :
    List Instr) ++ preWords .rcx ++
  ([.mov .r8 (.mem (sp oE)), .mov .r9 (.mem (sp oEl))] : List Instr) ++ lea .rax oM ++
  ([.store (sp 0) .rax, .mov .rax (.mem (sp oK)), .store (sp 8) .rax, .mov .rax (.mem (arg 12)),
    .store (sp 16) .rax, .mov .rax (.mem (arg 13)), .store (sp 24) .rax] : List Instr)

/-- `r₂ & r₁ & 1` into `r11`, and the comparison's registers: `out` in
`rdi`, the input in `rsi`, `n_len` in `rcx`, the index `r10` and the
difference `rdx` zero. -/
def cmpArgs : List Instr :=
  [.alu .and .rax (.mem (sp oR1)), .alu .and .rax (.imm 1), .mov .r11 (.reg .rax),
    .mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (arg 0)), .mov .rcx (.mem (sp oK)), .mov32 .r10 (.imm 0),
    .mov32 .rdx (.imm 0)]

/-- The check and the release, after the calls: `r₂` in `rax`. -/
def tail : List (Prog isa) :=
  [.block cmpArgs, cmpLoop, .block masks, releaseLoop, .block [.mov .rax (.reg .r11)]]

/-- The body of the frame. -/
def body (crtName : String) (crt : Prog isa) (pdName : String) (pd : Prog isa) : Prog isa :=
  seqs ([.block crtArgs, .call crtName crt, .block pdArgs, .call pdName pd] ++ tail)

/-- `vg_rsa_private_checked_precomputed`, calling the CRT `crt` and the
public operation's `pd`, by their names. -/
def code (crtName : String) (crt : Prog isa) (pdName : String) (pd : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body crtName crt pdName pd) (.free frameBytes)

end VG.Impl.Rsa.X86_64.PrivCheckedPc
