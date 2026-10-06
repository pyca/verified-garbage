import VerifiedGarbage.TCB.AArch64.Isa

/-!
# RSA's private-key operation checked against `e`, on AArch64

`vg_rsa_private_checked(out, out_len, n, n_len, e, e_len, input, input_len,
p, p_len, q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len, scratch,
scratch_len)`: the first eight arguments in `x0`–`x7`, the other twelve on
the stack. As on x86-64 (`Impl/Rsa/X86_64/PrivChecked.lean`), it is
BoringSSL's `rsa_default_private_transform`, from verified functions:

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

The function runs in two frames: one saving our return address `x30`, and
in it one of `frameBytes` bytes, from `sp`: the stack arguments of the calls
(those of `vg_rsa_private_crt` are our last ten), at `oSlot` the arguments
kept across the calls and the values they return, at `oM` the buffer `M`,
at `oPre` `n`'s values. Our own stack arguments are above both frames, from
`sp + frameBytes + 16`. Only registers the callees may change are used, so
the frame holds everything kept across a call.
-/

namespace VG.Impl.Rsa.AArch64.PrivChecked

open VG VG.AArch64

/-- `c₁; c₂; …`. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- The size of the inner frame. -/
def frameBytes : Nat := 3232

/-- The slots: `out`, `n`, `n_len`, `e`, `e_len`, the input, `r₁`, `r₃`. -/
def oOut : Nat := 80
def oN : Nat := 88
def oK : Nat := 96
def oE : Nat := 104
def oEl : Nat := 112
def oIn : Nat := 120
def oR1 : Nat := 128
def oR3 : Nat := 136
/-- `M`, up to 1024 bytes. -/
def oM : Nat := 160
/-- `n`'s values, up to 256 words. -/
def oPre : Nat := 1184

/-- The offset from `sp` of our stack argument `j` (from 0). -/
def arg (j : Nat) : Nat := frameBytes + 16 + 8 * j

/-- `r := 2 ⌈n_len / 8⌉`, the words of `n`'s values. -/
def preWords (r : Reg) : List Instr :=
  [.ldrSp r oK, .addImm .x r r 7, .lsr .x r r 3, .add .x r r r]

/-- The arguments kept in the slots, with `x15 = sp`. -/
def saveSlots : List Instr :=
  [.addSp .x15 0, .str .x .x0 .x15 oOut, .str .x .x2 .x15 oN, .str .x .x3 .x15 oK, .str .x .x4 .x15 oE,
    .str .x .x5 .x15 oEl, .str .x .x6 .x15 oIn]

/-- Our stack argument `j + 2` as the stack argument `j` of
`vg_rsa_private_crt`. -/
def copyArg (j : Nat) : List Instr := [.ldrSp .x8 (arg (j + 2)), .str .x .x8 .x15 (8 * j)]

/-- Our last ten stack arguments as those of `vg_rsa_private_crt`. -/
def copyArgs : List Instr := (List.range 10).flatMap copyArg

/-- The arguments of `vg_rsa_private_crt` in registers: `M`, `n_len`, `n`,
`n_len`, the input, `n_len`, `p` and `p_len`. -/
def crtRegs : List Instr :=
  [.addSp .x0 oM, .addImm .x .x1 .x3 0, .addImm .x .x4 .x6 0, .addImm .x .x5 .x3 0, .ldrSp .x6 (arg 0),
    .ldrSp .x7 (arg 1)]

/-- The arguments of `vg_rsa_private_crt`, keeping ours in the slots. -/
def crtArgs : List Instr := saveSlots ++ copyArgs ++ crtRegs

/-- `r₁` kept, and the arguments of `vg_rsa_public_precompute`: its values
to `oPre`, `n` and the working space. -/
def pcArgs : List Instr :=
  [.addSp .x15 0, .str .x .x0 .x15 oR1, .addSp .x0 oPre] ++ preWords .x1 ++
  [.ldrSp .x2 oN, .ldrSp .x3 oK, .ldrSp .x4 (arg 10), .ldrSp .x5 (arg 11)]

/-- `r₃` kept, and the arguments of `vg_rsa_public_precomputed_checked`:
`out`, `n`'s values, `e`, `M` as the input, the working space (on the
stack). -/
def pdArgs : List Instr :=
  [.addSp .x15 0, .str .x .x0 .x15 oR3, .ldrSp .x0 oOut, .ldrSp .x1 oK, .addSp .x2 oPre] ++ preWords .x3 ++
  [.ldrSp .x4 oE, .ldrSp .x5 oEl, .addSp .x6 oM, .addImm .x .x7 .x1 0, .ldrSp .x8 (arg 10),
    .str .x .x8 .x15 0, .ldrSp .x8 (arg 11), .str .x .x8 .x15 8]

/-- `r₂ & r₁ & r₃ & 1` into `x9`, and the comparison's registers: `out` in
`x11`, the input in `x12`, the bytes left `n_len` in `x13` and the
difference `x14` zero. -/
def cmpArgs : List Instr :=
  [.ldrSp .x10 oR1, .logic .and .x .x9 .x0 .x10, .ldrSp .x10 oR3, .logic .and .x .x9 .x9 .x10,
    .movz .x .x10 1 0, .logic .and .x .x9 .x9 .x10, .ldrSp .x11 oOut, .ldrSp .x12 oIn, .ldrSp .x13 oK,
    .movz .x .x14 0 0]

/-- `x14 |= out[i] ^ input[i]` for each byte. -/
def cmpLoop : Prog isa :=
  .loop (.block [.ldrb .x8 .x11 0, .ldrb .x10 .x12 0, .logic .eor .x .x8 .x8 .x10,
    .logic .orr .x .x14 .x14 .x8, .addImm .x .x11 .x11 1, .addImm .x .x12 .x12 1,
    .subImm .x .x13 .x13 1]) (.nonzero .x .x13)

/-- With `g = r₁ & r₂ & r₃ & 1` in `x9` and the comparison in `x14`: the
equality `eq = [x14 = 0]` (from the Z flag of `x14 + 0`, without a
branch); the result, `-g & (2 - eq)`, into `x13`; the mask of the release,
`-(g & eq)`, into `x12`; `out` into `x11`, `M` into `x14` and `n_len` into
`x15` for the release, and `x10 := 0`. -/
def masks : List Instr :=
  [.movz .x .x10 0 0, .movz .x .x13 1 0, .adds .x .x8 .x14 .x10, .cselc .x .x8 .x13 .x10 .eq,
    .movz .x .x13 2 0, .sub .x .x13 .x13 .x8, .sub .x .x12 .x10 .x9, .logic .and .x .x13 .x13 .x12,
    .logic .and .x .x8 .x8 .x9, .sub .x .x12 .x10 .x8, .ldrSp .x11 oOut, .addSp .x14 oM, .ldrSp .x15 oK]

/-- `out[i] := M[i] & x12` and `M[i] := 0` for each byte. -/
def releaseLoop : Prog isa :=
  .loop (.block [.ldrb .x8 .x14 0, .logic .and .x .x8 .x8 .x12, .strb .x8 .x11 0, .strb .x10 .x14 0,
    .addImm .x .x11 .x11 1, .addImm .x .x14 .x14 1, .subImm .x .x15 .x15 1]) (.nonzero .x .x15)

/-- The check and the release, after the calls: `r₂` in `x0`. -/
def tail : List (Prog isa) :=
  [.block cmpArgs, cmpLoop, .block masks, releaseLoop, .block [.addImm .x .x0 .x13 0]]

/-- The calls of `vg_rsa_public_precompute` (`pc`) and
`vg_rsa_public_precomputed_checked` (`pd`), then the check and the
release: what follows the CRT, whatever it wrote to `M`. -/
def check (pcName : String) (pc : Prog isa) (pdName : String) (pd : Prog isa) : List (Prog isa) :=
  [.block pcArgs, .call pcName pc, .block pdArgs, .call pdName pd] ++ tail

/-- The body of the inner frame. -/
def body (crtName : String) (crt : Prog isa) (pcName : String) (pc : Prog isa) (pdName : String)
    (pd : Prog isa) : Prog isa :=
  seqs ([.block crtArgs, .call crtName crt] ++ check pcName pc pdName pd)

/-- `vg_rsa_private_checked`, calling the CRT `crt` and the public
operation's `pc` and `pd`, by their names. -/
def code (crtName : String) (crt : Prog isa) (pcName : String) (pc : Prog isa) (pdName : String)
    (pd : Prog isa) : Prog isa :=
  .frame (.push .x30) (.frame (.alloc frameBytes) (body crtName crt pcName pc pdName pd) (.free frameBytes))
    (.pop .x30)

end VG.Impl.Rsa.AArch64.PrivChecked
