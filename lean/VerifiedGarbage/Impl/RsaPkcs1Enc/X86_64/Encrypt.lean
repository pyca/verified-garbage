module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# RSAES-PKCS1-v1_5 encryption on x86-64

`vg_rsa_pkcs1_encrypt(out, out_len, n, n_len, e, e_len, msg, msg_len, ps,
ps_len, scratch, scratch_len)`: the first six arguments in registers, the
others on the stack. It builds the encoded message
`EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` in its frame and calls
`vg_rsa_public_checked` (`pub`, by its name `pubName`) on it, which checks
`n` and `e` and writes `EM^e mod n` or zeros to `out`:

1. The arguments that the call takes again are kept in slots of the frame,
   and the call's stack arguments (`EM`, `n_len`, `scratch`, `scratch_len`)
   are written at `rsp`. `EM` starts with `0x00 ‖ 0x02`.
2. `PS` is copied after them, byte by byte, and `rdx` collects, without
   branches, whether any byte is zero: all ones if one is, zero if not
   (`psLoop`). The length of `PS` is at least 8 (a precondition).
3. The separator `0x00` follows, and `M` after it (`msgCopy`, skipped if
   `msg_len` is 0: a branch on a public length).
4. The call.
5. If `PS` had a zero byte, `out` is masked to zeros and the result to 0
   (`maskLoop`), without branches; the loop also overwrites `EM` with
   zeros.

The frame is `frameBytes` bytes, an odd number of words, so that `rsp` is a
multiple of 16 at the call, as the System V ABI asks: at `rsp`, the call's
stack arguments; from `oOut`, the slots; from `oEM`, `EM`, up to 1024
bytes.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.X86_64.Encrypt

open VG VG.X86_64

/-- The size of the frame. -/
def frameBytes : Nat := 1112

/-- The slots: `out`, `n`, `n_len`, `e`, `e_len`, and whether `PS` has a
zero byte. -/
def oOut : Nat := 32
def oN : Nat := 40
def oK : Nat := 48
def oE : Nat := 56
def oEl : Nat := 64
def oZ : Nat := 72
/-- `EM`, up to 1024 bytes. -/
def oEM : Nat := 80

/-- `[rsp + d]`. -/
def sp (d : Nat) : MemOp := { base := .rsp, disp := (d : Int) }

/-- The stack argument `j` (from 0) of the function, from the frame. -/
def arg (j : Nat) : MemOp := sp (frameBytes + 8 + 8 * j)

/-- `[b + i + d]`: byte `i` of the buffer at `b + d`. -/
def bx (b i : Reg) (d : Nat := 0) : MemOp := { base := b, index := some i, disp := (d : Int) }

/-- The slots, the call's stack arguments, the first two bytes of `EM`, and
`PS`'s copy's registers: `PS` in `rsi`, its length in `rcx`, the index
`r10` and the collected zero test `rdx` zero. -/
def setup : List Instr :=
  [.mov .r10 (.mem (arg 4)), .mov .r11 (.mem (arg 5)), .mov .rsi (.mem (arg 2)), .mov .rax (.mem (arg 3)),
    .store (sp oOut) .rdi, .store (sp oN) .rdx, .store (sp oK) .rcx, .store (sp oE) .r8, .store (sp oEl) .r9,
    .mov .rdi (.reg .rsp), .alu .add .rdi (.imm (BitVec.ofNat 32 oEM)), .store (sp 0) .rdi, .store (sp 8) .rcx,
    .store (sp 16) .r10, .store (sp 24) .r11, .mov .rcx (.reg .rax),
    .mov32 .rax (.imm 0), .store8 (sp oEM) .rax, .mov32 .rax (.imm 2), .store8 (sp (oEM + 1)) .rax,
    .mov32 .r10 (.imm 0), .mov32 .rdx (.imm 0)]

/-- One byte of `PS`: copied to `EM`, and `rdx` all ones if it is zero. -/
def psLoop : Prog isa :=
  .loop (.block [.movzx8 .rax (bx .rsi .r10), .store8 (bx .rsp .r10 (oEM + 2)) .rax,
    .alu .cmp .rax (.imm 1), .alu .sbb .r11 (.reg .r11), .alu .or .rdx (.reg .r11),
    .alu .add .r10 (.imm 1), .alu .cmp .r10 (.reg .rcx)]) .ne

/-- The separator after `PS` (of `rcx` bytes), the zero test to its slot,
and `M`'s copy's registers: its place in `EM` in `rdi`, `M` in `rsi`, its
length in `rcx` (ZF set if it is 0), the index `r10` zero. -/
def sep : List Instr :=
  [.mov .rsi (.mem (arg 0)), .mov .r11 (.mem (arg 1)), .mov32 .rax (.imm 0),
    .store8 (bx .rsp .rcx (oEM + 2)) .rax, .store (sp oZ) .rdx,
    .mov .rdi (.reg .rsp), .alu .add .rdi (.reg .rcx), .alu .add .rdi (.imm (BitVec.ofNat 32 (oEM + 3))),
    .mov .rcx (.reg .r11), .mov32 .r10 (.imm 0), .alu .test .rcx (.reg .rcx)]

/-- `M`'s `rcx` bytes, from `rsi` to `rdi`. -/
def msgLoop : Prog isa :=
  .loop (.block [.movzx8 .rax (bx .rsi .r10), .store8 (bx .rdi .r10) .rax, .alu .add .r10 (.imm 1),
    .alu .cmp .r10 (.reg .rcx)]) .ne

/-- `M`, unless it is empty. -/
def msgCopy : Prog isa := .ite .ne msgLoop (.block [])

/-- The arguments of `vg_rsa_public_checked`: `out`, `n_len`, `n`, `n_len`,
`e`, `e_len`, from the slots. -/
def callArgs : List Instr :=
  [.mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oK)), .mov .rdx (.mem (sp oN)), .mov .rcx (.mem (sp oK)),
    .mov .r8 (.mem (sp oE)), .mov .r9 (.mem (sp oEl))]

/-- The mask, all ones unless `PS` had a zero byte, into `rdx`; the result
masked into `r11`; `out` into `rdi`, `n_len` into `rcx`, the index `r10`
zero. -/
def maskArgs : List Instr :=
  [.mov .rdx (.mem (sp oZ)), .alu .xor .rdx (.imm (BitVec.ofInt 32 (-1))), .alu .and .rax (.reg .rdx),
    .mov .r11 (.reg .rax), .mov .rdi (.mem (sp oOut)), .mov .rcx (.mem (sp oK)), .mov32 .r10 (.imm 0)]

/-- `out[r10] &= rdx` and `EM[r10] := 0` for each byte. -/
def maskLoop : Prog isa :=
  .loop (.block [.movzx8 .rax (bx .rdi .r10), .alu .and .rax (.reg .rdx), .store8 (bx .rdi .r10) .rax,
    .mov32 .rax (.imm 0), .store8 (bx .rsp .r10 oEM) .rax, .alu .add .r10 (.imm 1),
    .alu .cmp .r10 (.reg .rcx)]) .ne

/-- The body of the frame. -/
def body (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block setup) (.seq psLoop (.seq (.block sep) (.seq msgCopy (.seq (.block callArgs)
    (.seq (.call pubName pub) (.seq (.block maskArgs) (.seq maskLoop (.block [.mov .rax (.reg .r11)]))))))))

/-- `vg_rsa_pkcs1_encrypt`, calling `vg_rsa_public_checked`'s code `pub` by
its name. -/
def code (pubName : String) (pub : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body pubName pub) (.free frameBytes)

end VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
