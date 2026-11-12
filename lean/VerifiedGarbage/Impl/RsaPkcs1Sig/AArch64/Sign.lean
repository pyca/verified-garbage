module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Recover

/-!
# RSASSA-PKCS1-v1_5 signing on AArch64

`vg_rsa_pkcs1_sign(out = x0, out_len = x1, n = x2, n_len = x3, e = x4,
e_len = x5, hash = w6, digest = x7, digest_len = [sp], p = [sp + 8], …,
scratch_len = [sp + 96])`. As on x86-64
(`Impl/RsaPkcs1Sig/X86_64/Sign.lean`), RFC 8017 §8.2.1 from verified
functions:

1. `encode` writes the encoding of `digest` to a buffer `EM` in its frame;
   if that fails, it writes zeros to `out` and returns 0;
2. `vg_rsa_private_checked` (or a variant) computes the signature of `EM`
   into `out`, checked against `e`, and returns its result;
3. it overwrites `EM` with zeros.

Only the public key, the lengths and `hash` decide a branch or an address:
the hash value is only copied into `EM`, which only the private operation
reads.

`vg_rsa_pkcs1_sign_precomputed` takes the key's precomputed values `pre`
and `pre_len` after `scratch_len`, and passes them on to
`vg_rsa_private_checked_precomputed`: the same code, copying 14 stack
arguments rather than 12 (`codeN`).

The frame of `frameBytes` bytes holds, at `sp`, the 12 or 14 stack arguments
of the call; at `112`, our caller's `x19` and our return address (`saved`);
at `oEM`, `EM`, up to 1024 bytes. `out` is kept in `x17` across `encode`,
and `k` in `x19` across the call.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.AArch64.Sign

open VG VG.AArch64
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (mov movw)
open VG.Impl.RsaPkcs1Sig.AArch64.Recover (zeroOut)

/-- The size of the frame. -/
def frameBytes : Nat := 1152

/-- `EM`. -/
def oEM : Nat := 128

def saved : List (Reg × Nat) := [(.x19, 112), (.x30, 120)]

def save : List Instr := .addSp .x16 0 :: saved.map fun (r, d) => .str .x r .x16 d

def restore : List Instr := .addSp .x16 0 :: saved.map fun (r, d) => .ldr .x r .x16 d

/-- The registers saved, `k` kept in `x19` and `out` in `x17`, and the
arguments of `encode`: `EM`, `k`, `hash`, `digest` and `digest_len`. -/
def encArgs : List Instr :=
  save ++ [mov .x19 .x3, mov .x17 .x0, .addSp .x8 oEM, mov .x9 .x3, movw .x10 .x6, mov .x11 .x7,
    .ldrSp .x12 frameBytes]

/-- Stack argument `j + 1` of the function (`p` … `scratch_len`) to the
call's stack argument `j`. -/
def copyArg (j : Nat) : List Instr := [.ldrSp .x15 (frameBytes + 8 * (j + 1)), .str .x .x15 .x16 (8 * j)]

/-- The arguments of the private operation, of which `n` on the stack:
those of the function, with `EM` (still in `x8`) as the input. -/
def callArgsN (n : Nat) : List Instr :=
  (List.range n).flatMap copyArg ++ [mov .x0 .x17, mov .x6 .x8, mov .x7 .x19]

/-- The arguments of `vg_rsa_private_checked`. -/
abbrev callArgs : List Instr := callArgsN 12

/-- Zeros to `out`, kept in `x17` and `x19`. -/
def zeroSlots : Prog isa := .seq (.block [mov .x14 .x17, mov .x13 .x19]) zeroOut

/-- `EM` overwritten with zeros, keeping the result in `x0`. -/
def wipe : Prog isa := .seq (.block [.addSp .x14 oEM, mov .x13 .x19, .movz .x .x15 0 0]) psLoop

/-- After the encoding, passing on `n` stack arguments. -/
def afterEncN (n : Nat) (privName : String) (priv : Prog isa) : Prog isa :=
  .ite (.zero .x .x0) zeroSlots (.seq (.block (callArgsN n)) (.seq (.call privName priv) wipe))

def bodyN (n : Nat) (privName : String) (priv : Prog isa) : Prog isa :=
  .seq (.block encArgs) (.seq encode (.seq (afterEncN n privName priv) (.block restore)))

/-- The function, calling the private operation `priv` by its name with `n`
stack arguments. -/
def codeN (n : Nat) (privName : String) (priv : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (bodyN n privName priv) (.free frameBytes)

/-- `vg_rsa_pkcs1_sign`, calling `vg_rsa_private_checked` (`priv`) by its
name. -/
abbrev code (privName : String) (priv : Prog isa) : Prog isa := codeN 12 privName priv

/-- `vg_rsa_pkcs1_sign_precomputed`, calling
`vg_rsa_private_checked_precomputed` (`priv`) by its name. -/
abbrev codeP (privName : String) (priv : Prog isa) : Prog isa := codeN 14 privName priv

end VG.Impl.RsaPkcs1Sig.AArch64.Sign
