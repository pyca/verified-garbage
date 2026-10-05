import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Encode

/-!
# RSASSA-PKCS1-v1_5 verification on x86-64

`vg_rsa_pkcs1_verify(n, n_len, e, e_len, hash, digest, digest_len, sig,
sig_len, scratch, scratch_len)`: the first six arguments in registers, the
others on the stack. It is RFC 8017 §8.2.2 as written (which
`Proof/RsaPkcs1Sig/Verify.lean` proves BoringSSL's check), from verified
functions:

1. if `sig_len` is not `n_len`, it returns 0;
2. `vg_rsa_public_checked` writes `EM = s^e mod n` (`k` bytes) to a buffer
   `EM₁` in its frame, checking `n`, `e` and `s < n`, and it returns 0 if
   that fails;
3. `encode` writes the encoding of `digest` to a buffer `EM₂`, and it
   returns 0 if that fails;
4. it returns 1 if `EM₁` and `EM₂` are equal (`compare`), 0 if not.

Everything is public, so it branches freely.

The frame of `frameBytes` bytes holds, at `rsp`, the stack arguments of the
call; at `oN` … `oD`, the arguments kept across it; at `oEM1` and `oEM2`,
the two buffers of up to 1024 bytes. Only caller-saved registers are used.
With the frame, `rsp` is a multiple of 16 at the call.
-/

namespace VG.Impl.RsaPkcs1Sig.X86_64.Verify

open VG VG.X86_64

/-- The size of the frame. -/
def frameBytes : Nat := 2136

/-- The slots: `n`, `n_len`, `e`, `e_len`, `hash`, `digest`. -/
def oN : Nat := 32
def oK : Nat := 40
def oE : Nat := 48
def oEl : Nat := 56
def oH : Nat := 64
def oD : Nat := 72
/-- The buffers. -/
def oEM1 : Nat := 80
def oEM2 : Nat := 1104

/-- `[rsp + d]`. -/
def sp (d : Nat) : MemOp := { base := .rsp, disp := (d : Int) }

/-- The stack argument `j` (from 0) of the function, from the frame. -/
def arg (j : Nat) : MemOp := sp (frameBytes + 8 + 8 * j)

/-- The stack argument `j` before the frame. -/
def arg0 (j : Nat) : MemOp := sp (8 + 8 * j)

/-- `r := rsp + d`. -/
def lea (r : Reg) (d : Nat) : List Instr := [.mov r (.reg .rsp), .alu .add r (.imm (BitVec.ofNat 32 d))]

/-- `sig_len` against `n_len`. -/
def lenCheck : List Instr := [.mov .rax (.mem (arg0 2)), .alu .cmp .rax (.reg .rsi)]

/-- 0 returned. -/
def ret0 : Prog isa := .block [.mov32 .rax (.imm 0)]

/-- The arguments kept into the slots, and those of `vg_rsa_public_checked`:
`EM₁`, `n`, `e`, `sig` and the working space, `n_len` as every length of
the modulus. -/
def pubArgs : List Instr :=
  [.store (sp oN) .rdi, .store (sp oK) .rsi, .store (sp oE) .rdx, .store (sp oEl) .rcx,
    .store (sp oH) .r8, .store (sp oD) .r9,
    .mov .rax (.mem (arg 1)), .mov .r10 (.mem (arg 3)), .mov .r11 (.mem (arg 4)),
    .store (sp 0) .rax, .store (sp 8) .rsi, .store (sp 16) .r10, .store (sp 24) .r11,
    .mov .r8 (.reg .rdx), .mov .r9 (.reg .rcx), .mov .rdx (.reg .rdi), .mov .rcx (.reg .rsi)] ++
  lea .rdi oEM1

/-- ZF set if the low 32 bits of `rax` are 0. -/
def test0 : List Instr := [.alu32 .cmp .rax (.imm 0)]

/-- The arguments of `encode`: `EM₂`, `k`, `hash` (zero-extended from its 32
bits), `digest` and `digest_len`. -/
def encArgs : List Instr :=
  lea .r8 oEM2 ++ [.mov .rcx (.mem (sp oK)), .mov .rdx (.mem (sp oH)), .mov32 .rdx (.reg .rdx),
    .mov .rsi (.mem (sp oD)), .mov .r9 (.mem (arg 0))]

/-- The arguments of `compare`: `EM₁` and `EM₂` (`k` is still in `rcx`). -/
def cmpArgs : List Instr := lea .rdi oEM1 ++ lea .rsi oEM2

/-- 1 if `rdx` is 0, 0 if not. -/
def result : List Instr :=
  [.alu .cmp .rdx (.imm 1), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 1)]

/-- After the encoding. -/
def tail : Prog isa :=
  .seq (.block test0) (.ite .e ret0 (.seq (.block cmpArgs) (.seq compare (.block result))))

/-- After the call. -/
def afterPub : Prog isa :=
  .seq (.block test0) (.ite .e ret0 (.seq (.block encArgs) (.seq encode tail)))

/-- The body of the frame. -/
def body (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block pubArgs) (.seq (.call pubName pub) afterPub)

/-- `vg_rsa_pkcs1_verify`, calling `vg_rsa_public_checked` (`pub`) by its
name. -/
def code (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block lenCheck)
    (.ite .ne ret0 (.frame (.alloc frameBytes) (body pubName pub) (.free frameBytes)))

end VG.Impl.RsaPkcs1Sig.X86_64.Verify
