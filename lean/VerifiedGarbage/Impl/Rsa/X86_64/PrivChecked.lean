module

public import VerifiedGarbage.Impl.Rsa.X86_64.Checked

/-!
# RSA's private-key operation checked against `e`, on x86-64

`vg_rsa_private_checked(out, out_len, n, n_len, e, e_len, input, input_len,
p, p_len, q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len, scratch,
scratch_len)`: the first six arguments in registers, the others on the
stack. It is BoringSSL's `rsa_default_private_transform`, from verified
functions:

1. `vg_rsa_private_crt` (or one of its variants) computes `m` from the
   input `c` into a buffer `M` on the stack, returning `r₁`;
2. `vg_rsa_public_precompute` writes `n`'s values to a buffer on the stack,
   returning `r₃`, and `vg_rsa_public_precomputed_checked` writes
   `M^e mod n` to `out`, returning `r₂`;
3. `out` is compared with `c`, without branches, and `M` is released to
   `out` only if they are equal and `r₁ = r₂ = r₃ = 1`; `out` is zeros
   otherwise. The function returns 1 if it released `M`, 2 if `r₁ = r₂ = r₃
   = 1` but `out` is not `c` (the internal error), and 0 otherwise. `M` is
   zeroed before returning.

The release depends only on what step 2 computes from `M`: whatever `M`
holds (a faulted exponentiation), what is released is a number `m < n` with
`m^e mod n = c`.

The functions are called from a frame of `frameBytes` bytes on the stack:
at `rsp`, the stack arguments of the calls; at `oSlot`, the arguments kept
across the calls and the return values; at `oM`, `M`; at `oPre`, `n`'s
values. Only caller-saved registers are used, so the frame's slots hold
everything kept across a call. With the frame `rsp` is a multiple of 16 at
each call, as the System V ABI asks.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.PrivChecked

open VG VG.X86_64 VG.Impl.Bignum.X86_64

/-- The size of the frame. -/
def frameBytes : Nat := 3240

/-- The slots: `out`, `n`, `n_len`, `e`, `e_len`, `r₁`, `r₃`. -/
def oOut : Nat := 96
def oN : Nat := 104
def oK : Nat := 112
def oE : Nat := 120
def oEl : Nat := 128
def oR1 : Nat := 136
def oR3 : Nat := 144
/-- `M`, up to 1024 bytes. -/
def oM : Nat := 160
/-- `n`'s values, up to 256 words. -/
def oPre : Nat := 1184

/-- `[rsp + d]`. -/
def sp (d : Nat) : MemOp := { base := .rsp, disp := (d : Int) }

/-- The stack argument `j` (from 0) of the function, from the frame. -/
def arg (j : Nat) : MemOp := sp (frameBytes + 8 + 8 * j)

/-- `r := rsp + d`. -/
def lea (r : Reg) (d : Nat) : List Instr := [.mov r (.reg .rsp), .alu .add r (.imm (BitVec.ofNat 32 d))]

/-- `r := 2 ⌈n_len / 8⌉`, the words of `n`'s values. -/
def preWords (r : Reg) : List Instr :=
  [.mov r (.mem (sp oK)), .alu .add r (.imm 7), .shift .shr r 3, .alu .add r (.reg r)]

/-- The arguments kept into the slots, and those of `vg_rsa_private_crt`:
`M`, `n`, the input, the private key and the working space, `n_len` as
every length of the modulus. -/
def crtArgs : List Instr :=
  ([.store (sp oOut) .rdi, .store (sp oN) .rdx, .store (sp oK) .rcx, .store (sp oE) .r8, .store (sp oEl) .r9] : List Instr) ++
  (List.range 12).flatMap (fun j => [.mov .rax (.mem (arg (j + 2))), .store (sp (8 * j)) .rax]) ++
  lea .rdi oM ++ ([.mov .rsi (.reg .rcx), .mov .r8 (.mem (arg 0)), .mov .r9 (.reg .rcx)] : List Instr)

/-- `r₁` kept, and the arguments of `vg_rsa_public_precompute`: its values
to `oPre`, `n` and the working space. -/
def pcArgs : List Instr :=
  ([.store (sp oR1) .rax] : List Instr) ++ lea .rdi oPre ++ preWords .rsi ++
  ([.mov .rdx (.mem (sp oN)), .mov .rcx (.mem (sp oK)), .mov .r8 (.mem (arg 12)), .mov .r9 (.mem (arg 13))] : List Instr)

/-- `r₃` kept, and the arguments of `vg_rsa_public_precomputed_checked`:
`out`, `n`'s values, `e`, `M` as the input, the working space. -/
def pdArgs : List Instr :=
  ([.store (sp oR3) .rax, .mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oK))] : List Instr) ++ lea .rdx oPre ++ preWords .rcx ++
  ([.mov .r8 (.mem (sp oE)), .mov .r9 (.mem (sp oEl))] : List Instr) ++ lea .rax oM ++
  ([.store (sp 0) .rax, .mov .rax (.mem (sp oK)), .store (sp 8) .rax, .mov .rax (.mem (arg 12)),
    .store (sp 16) .rax, .mov .rax (.mem (arg 13)), .store (sp 24) .rax] : List Instr)

/-- `r₂ & r₁ & r₃ & 1` into `r11`, and the comparison's registers: `out`
in `rdi`, the input in `rsi`, `n_len` in `rcx`, the index `r10` and the
difference `rdx` zero. -/
def cmpArgs : List Instr :=
  [.alu .and .rax (.mem (sp oR1)), .alu .and .rax (.mem (sp oR3)), .alu .and .rax (.imm 1), .mov .r11 (.reg .rax),
    .mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (arg 0)), .mov .rcx (.mem (sp oK)), .mov32 .r10 (.imm 0),
    .mov32 .rdx (.imm 0)]

/-- `[r + r10]`, and `M`'s byte `r10`. -/
def at10 (r : Reg) : MemOp := { base := r, index := some .r10 }
def mByte : MemOp := { base := .rsp, index := some .r10, disp := (oM : Int) }

/-- `rdx |= out[r10] ^ input[r10]` for each byte. -/
def cmpLoop : Prog isa :=
  .loop (.block [.movzx8 .rax (at10 .rdi), .movzx8 .r9 (at10 .rsi), .alu .xor .rax (.reg .r9),
    .alu .or .rdx (.reg .rax), .alu .add .r10 (.imm 1), .alu .cmp .r10 (.reg .rcx)]) .ne

/-- With `g = r₁ & r₂ & r₃ & 1` in `r11` and the comparison in `rdx`: the
mask of the release, `-(g ∧ out = c)`, into `r9`; the result,
`g (2 - [out = c])`, into `r11`; `r10 := 0`. -/
def masks : List Instr :=
  [.alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx), .mov32 .r9 (.imm 0), .alu .sub .r9 (.reg .r11),
    .mov .rax (.reg .rdx), .alu .and .rax (.imm 1), .mov32 .r8 (.imm 2), .alu .sub .r8 (.reg .rax),
    .alu .and .r8 (.reg .r9), .alu .and .r9 (.reg .rdx), .mov .r11 (.reg .r8), .mov32 .r10 (.imm 0)]

/-- `out[r10] := M[r10] & r9` and `M[r10] := 0` for each byte. -/
def releaseLoop : Prog isa :=
  .loop (.block [.movzx8 .rax mByte, .alu .and .rax (.reg .r9), .store8 (at10 .rdi) .rax, .mov32 .rax (.imm 0),
    .store8 mByte .rax, .alu .add .r10 (.imm 1), .alu .cmp .r10 (.reg .rcx)]) .ne

/-- The check and the release, after the calls: `r₂` in `rax`. -/
def tail : List (Prog isa) :=
  [.block cmpArgs, cmpLoop, .block masks, releaseLoop, .block [.mov .rax (.reg .r11)]]

/-- The calls of `vg_rsa_public_precompute` (`pc`) and
`vg_rsa_public_precomputed_checked` (`pd`), then the check and the
release: what follows the CRT, whatever it wrote to `M`. -/
def check (pcName : String) (pc : Prog isa) (pdName : String) (pd : Prog isa) : List (Prog isa) :=
  [.block pcArgs, .call pcName pc, .block pdArgs, .call pdName pd] ++ tail

/-- The body of the frame. -/
def body (crtName : String) (crt : Prog isa) (pcName : String) (pc : Prog isa) (pdName : String)
    (pd : Prog isa) : Prog isa :=
  seqs ([.block crtArgs, .call crtName crt] ++ check pcName pc pdName pd)

/-- `vg_rsa_private_checked`, calling the CRT `crt` and the public
operation's `pc` and `pd`, by their names. -/
def code (crtName : String) (crt : Prog isa) (pcName : String) (pc : Prog isa) (pdName : String)
    (pd : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body crtName crt pcName pc pdName pd) (.free frameBytes)

end VG.Impl.Rsa.X86_64.PrivChecked
