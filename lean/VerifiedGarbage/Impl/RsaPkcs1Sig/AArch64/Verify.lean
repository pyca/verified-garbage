import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Encode

/-!
# RSASSA-PKCS1-v1_5 verification on AArch64

`vg_rsa_pkcs1_verify(n = x0, n_len = x1, e = x2, e_len = x3, hash = w4,
digest = x5, digest_len = x6, sig = x7, sig_len = [sp],
scratch = [sp + 8], scratch_len = [sp + 16])`. It is RFC 8017 §8.2.2 as
written, as on x86-64 (`Impl/RsaPkcs1Sig/X86_64/Verify.lean`), from
verified functions:

1. if `sig_len` is not `n_len`, it returns 0;
2. `vg_rsa_public_checked` writes `EM = s^e mod n` (`k` bytes) to a buffer
   `EM₁` in its frame, checking `n`, `e` and `s < n`, and it returns 0 if
   that fails;
3. `encode` writes the encoding of `digest` to a buffer `EM₂`, and it
   returns 0 if that fails;
4. it returns 1 if `EM₁` and `EM₂` are equal (`compare`), 0 if not.

Everything is public, so it branches freely.

The frame of `frameBytes` bytes holds, at `sp`, the two stack arguments of
the call; at `16`, our caller's `x19`–`x22` and our return address
(`saved`); at `oEM1` and `oEM2`, the two buffers of up to 1024 bytes. Across
the call, `k`, `hash`, `digest` and `digest_len` are kept in `x19`–`x22`,
which the callee preserves; the slots are written through `x16`, which holds
`sp`.
-/

namespace VG.Impl.RsaPkcs1Sig.AArch64.Verify

open VG VG.AArch64

/-- The size of the frame. -/
def frameBytes : Nat := 2128

/-- The buffers. -/
def oEM1 : Nat := 80
def oEM2 : Nat := 1104

/-- `d ← n`. -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- Our caller's registers that we use, and our return address, and where
they are kept. -/
def saved : List (Reg × Nat) := [(.x19, 16), (.x20, 24), (.x21, 32), (.x22, 40), (.x30, 48)]

/-- `x16 := sp`, and the registers of `saved` stored. -/
def save : List Instr := .addSp .x16 0 :: saved.map fun (r, d) => .str .x r .x16 d

/-- The registers of `saved` restored. -/
def restore : List Instr := .addSp .x16 0 :: saved.map fun (r, d) => .ldr .x r .x16 d

/-- `sig_len` against `n_len`. -/
def lenCheck : List Instr := [.ldrSp .x8 0, .sub .x .x8 .x8 .x1]

/-- 0 returned. -/
def ret0 : Prog isa := .block [.movz .x .x0 0 0]

/-- The stack argument `j` (from 0) of the function into `x8`, then to the
call's stack argument `i`. -/
def copyArg (j i : Nat) : List Instr := [.ldrSp .x8 (frameBytes + 8 * j), .str .x .x8 .x16 (8 * i)]

/-- The registers saved; `k`, `hash`, `digest` and `digest_len` kept in
`x19`–`x22`; and the arguments of `vg_rsa_public_checked`: `EM₁`, `n`, `e`,
`sig` and the working space, `n_len` as every length of the modulus. -/
def pubArgs : List Instr :=
  save ++ [mov .x19 .x1, mov .x20 .x4, mov .x21 .x5, mov .x22 .x6] ++ copyArg 1 0 ++ copyArg 2 1 ++
    [mov .x4 .x2, mov .x5 .x3, mov .x2 .x0, mov .x3 .x1, mov .x6 .x7, mov .x7 .x1, .addSp .x0 oEM1]

/-- The arguments of `encode`: `EM₂`, `k`, `hash`, `digest` and `digest_len`. -/
def encArgs : List Instr := [.addSp .x8 oEM2, mov .x9 .x19, mov .x10 .x20, mov .x11 .x21, mov .x12 .x22]

/-- The arguments of `compare`: `EM₁`, `EM₂` and `k`. -/
def cmpArgs : List Instr := [.addSp .x14 oEM1, .addSp .x15 oEM2, mov .x13 .x19]

/-- 1 if `x12` (at most 255) is 0, 0 if not: the borrow of `x12 - 1`. -/
def result : List Instr := [.subImm .x .x0 .x12 1, .lsr .x .x0 .x0 63]

/-- After the encoding. -/
def tail : Prog isa :=
  .ite (.zero .x .x0) ret0 (.seq (.block cmpArgs) (.seq compare (.block result)))

/-- After the call. -/
def afterPub : Prog isa :=
  .ite (.zero .w .x0) ret0 (.seq (.block encArgs) (.seq encode tail))

/-- The body of the frame. -/
def body (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block pubArgs) (.seq (.call pubName pub) (.seq afterPub (.block restore)))

/-- `vg_rsa_pkcs1_verify`, calling `vg_rsa_public_checked` (`pub`) by its
name. -/
def code (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block lenCheck)
    (.ite (.nonzero .x .x8) ret0 (.frame (.alloc frameBytes) (body pubName pub) (.free frameBytes)))

end VG.Impl.RsaPkcs1Sig.AArch64.Verify
