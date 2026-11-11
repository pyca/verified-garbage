module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Encode
public import VerifiedGarbage.Impl.Rsa.RISCV64.Priv

/-!
# RSASSA-PKCS1-v1_5 signing on RISC-V

`vg_rsa_pkcs1_sign(out = a0, out_len = a1, n = a2, n_len = a3, e = a4,
e_len = a5, hash = a6, digest = a7, digest_len, p, p_len, q, q_len, dp,
dp_len, dq, dq_len, qinv, qinv_len, scratch, scratch_len)`, the last
thirteen on the stack. As on PPC64LE (`Impl/RsaPkcs1Sig/PPC64LE/Sign.lean`),
RFC 8017 §8.2.1 from verified functions:

1. `encode` writes the encoding of `digest` to a buffer `EM` in the frame;
   if that fails, zeros are written to `out` and 0 is returned;
2. `vg_rsa_private_checked` (or, for `vg_rsa_pkcs1_sign_precomputed`,
   `vg_rsa_private_checked_precomputed`, given the key's precomputed values
   `pre`, our stack arguments 13 and 14) computes the signature of `EM` into
   `out`, checked against `e`, and returns its result;
3. `EM` is overwritten with zeros.

Only the public key, the lengths and `hash` decide a branch or an address:
the hash value is only copied into `EM`, which only the private operation
reads.

The frame (`alloc frameBytes`) holds the call's twelve, or fourteen, stack
arguments (at `sp`); our caller's `s1`–`s5` and our return address, which the call
overwrites in `ra` (`oSave`, `oRa`); and `EM`, of up to 1024 bytes (`oEM`).
Our own stack arguments are then at `sp + frameBytes + 8 i`, from `t6`
(`argBase`). Across `encode` and the call, `out`, `n`, `k`, `e` and `e_len`
are kept in `s1`–`s5`. The frame is addressed through `t0`, which holds
`sp`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.RISCV64.Sign

open VG VG.RISCV64
open VG.Impl.RsaPkcs1Sig.RISCV64 (mov encode fillLoop)

/-- The size of the frame. -/
def frameBytes : Nat := 1184

/-- Our caller's `s1`–`s5` and our return address. -/
def oSave : Nat := 112
def oRa : Nat := 152

/-- `EM`. -/
def oEM : Nat := 160

/-- `t6 :=` the address of our first stack argument, `sp + frameBytes`. -/
def argBase : List Instr := [.addSp .t6 frameBytes]

/-- `vg_rsa_private_checked`, or with `pc` `vg_rsa_private_checked_precomputed`. -/
def privCall : Bool → Prog isa
  | false => .call "vg_rsa_private_checked" Impl.Rsa.RISCV64.Priv.code
  | true => .call "vg_rsa_private_checked_precomputed" Impl.Rsa.RISCV64.Priv.codeP

/-- The call's stack arguments: twelve, or with `pc` fourteen (`pre` and
`pre_len` too). -/
def nCallArgs (pc : Bool) : Nat := if pc then 14 else 12

/-- `t0 := sp`; our caller's `s1`–`s5` and our return address into the
frame; `out`, `n`, `k`, `e` and `e_len` into `s1`–`s5`. -/
def save : List Instr :=
  [.addSp .t0 0, .store .d .s1 .t0 oSave, .store .d .s2 .t0 (oSave + 8), .store .d .s3 .t0 (oSave + 16),
    .store .d .s4 .t0 (oSave + 24), .store .d .s5 .t0 (oSave + 32), .store .d .ra .t0 oRa,
    mov .s1 .a0, mov .s2 .a2, mov .s3 .a3, mov .s4 .a4, mov .s5 .a5]

/-- `encode`'s arguments: `EM`, `k`, `hash` (zero-extended, since only its
low word is an argument), `digest` and `digest_len` (our stack argument 0). -/
def encArgs : List Instr :=
  argBase ++ [.addi .a1 .t0 oEM, mov .a2 .s3, .shift .sll .d .a3 .a6 32, .shift .srl .d .a3 .a3 32,
    mov .a4 .a7, .load .d .a5 .t6 0]

/-- Zeros to `out` (`k` bytes), keeping 0 in `a0`. -/
def zeroOut : Prog isa := .seq (.block [mov .a1 .s1, mov .t5 .s3, .li .t0 0]) fillLoop

/-- Our stack argument `1 + j` (`p` … `scratch_len`, then `pre` and
`pre_len`) to the call's stack argument `j`. -/
def copyArg (j : Nat) : List Instr := [.load .d .t1 .t6 (8 * (1 + j)), .store .d .t1 .t0 (8 * j)]

/-- The call's arguments: `out`, `k`, `n`, `k`, `e`, `e_len`, `EM`, `k`,
and its stack arguments, ours from `p` on. -/
def callArgs (pc : Bool) : List Instr :=
  [.addSp .t0 0] ++ argBase ++ (List.range (nCallArgs pc)).flatMap copyArg ++
  [mov .a0 .s1, mov .a1 .s3, mov .a2 .s2, mov .a3 .s3, mov .a4 .s4, mov .a5 .s5, .addi .a6 .t0 oEM,
    mov .a7 .s3]

/-- `EM` overwritten with zeros, keeping the result in `a0`. -/
def wipe : Prog isa := .seq (.block [.addSp .t0 0, .addi .a1 .t0 oEM, mov .t5 .s3, .li .t0 0]) fillLoop

/-- After the encoding: zeros and 0 if it failed, else the signature. -/
def afterEnc (pc : Bool) : Prog isa :=
  .ite (.zero .a0) zeroOut (.seq (.block (callArgs pc)) (.seq (privCall pc) wipe))

/-- Our caller's `s1`–`s5` and our return address back from the frame. -/
def restore : List Instr :=
  [.addSp .t0 0, .load .d .s1 .t0 oSave, .load .d .s2 .t0 (oSave + 8), .load .d .s3 .t0 (oSave + 16),
    .load .d .s4 .t0 (oSave + 24), .load .d .s5 .t0 (oSave + 32), .load .d .ra .t0 oRa]

/-- The body of the frame. -/
def body (pc : Bool) : Prog isa :=
  .seq (.block (save ++ encArgs)) (.seq encode (.seq (afterEnc pc) (.block restore)))

/-- `vg_rsa_pkcs1_sign`, or with `pc` `vg_rsa_pkcs1_sign_precomputed`. -/
def codeG (pc : Bool) : Prog isa := .frame (.alloc frameBytes) (body pc) (.free frameBytes)

/-- `vg_rsa_pkcs1_sign`. -/
abbrev code : Prog isa := codeG false

/-- `vg_rsa_pkcs1_sign_precomputed`. -/
abbrev codeP : Prog isa := codeG true

end VG.Impl.RsaPkcs1Sig.RISCV64.Sign
