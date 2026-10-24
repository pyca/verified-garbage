module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked
public import VerifiedGarbage.Impl.AesGcm.PPC64LE

/-!
# The checked RSA private-key operation on PPC64LE

`vg_rsa_private_checked(out = r3, out_len = r4, n = r5, n_len = r6, e = r7,
e_len = r8, input = r9, input_len = r10, p, p_len, q, q_len, dp, dp_len, dq,
dq_len, qinv, qinv_len, scratch, scratch_len)`, the last twelve on the stack
(the Parameter Save Area at `sp + 96`). As BoringSSL's
`rsa_default_private_transform`:

1. `vg_rsa_private_crt` writes the result `m` (or zeros) to the frame, and
   its status (1 if the key and the input are valid) is kept in the frame;
2. `vg_rsa_public_precompute` writes `n`'s values to the frame;
3. `vg_rsa_public_precomputed_checked` writes `m^e mod n` to `out`, and its
   status (1 if `e` is valid) is kept in the frame;
4. `out` is compared with the input in constant time, the result is 1 if
   both statuses are 1 and they are equal, 2 if both statuses are 1 and they
   are not, and 0 if not, computed without a branch, and `out` is
   overwritten with `m` under a mask of the first case, or with zeros;
5. the frame's `m` is overwritten with zeros.

Nothing branches on the statuses or on the comparison. Across the calls,
`out`, `n`, `k = n_len`, `e`, `e_len` and the input are kept in
`r24`–`r29`, which the callees preserve.

The frame (`stdu r1, -frameBytes(r1)`) holds the Parameter Save Area of the
calls (the ten stack arguments of `vg_rsa_private_crt`, at `r1 + 96`); our
caller's `r24`–`r29` and our return address, which each call (`bl`)
overwrites in the link register (`oSave`, `oLr`); the two statuses (`oSt`,
`oEs`); `m`, of up to 1024 bytes (`oM`); and `n`'s values, of up to 256
words (`oPre`). Our own stack arguments are then at
`r1 + frameBytes + 96 + 8 i` (`arg i`).
-/

@[expose] public section

namespace VG.Impl.Rsa.PPC64LE.Priv

open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)

/-- The size of the frame. -/
def frameBytes : Nat := 3328

/-- Our caller's `r24`–`r29`, our return address and the statuses. -/
def oSave : Nat := 176
def oLr : Nat := 224
def oSt : Nat := 232
def oEs : Nat := 240

/-- `m` and `n`'s values. -/
def oM : Nat := 248
def oPre : Nat := 1272

/-- Our stack argument `i` (from 0), in the frame. -/
def arg (i : Nat) : Nat := frameBytes + 96 + 8 * i

/-- `vg_rsa_private_crt`. -/
def crtCall : Prog isa := .call "vg_rsa_private_crt" Impl.Bignum.PPC64LE.Crt.crt

/-- `vg_rsa_public_precompute`. -/
def preCall : Prog isa := .call "vg_rsa_public_precompute" Impl.Bignum.PPC64LE.Precompute.precompute

/-- `vg_rsa_public_precomputed_checked`. -/
def pubCall : Prog isa :=
  .call "vg_rsa_public_precomputed_checked" Impl.Bignum.PPC64LE.PublicChecked.publicChecked

/-- `r12 := r1`; our caller's `r24`–`r29` and our return address into the
frame; `out`, `n`, `k`, `e`, `e_len` and the input into `r24`–`r29`. -/
def save : List Instr :=
  [.addSp .r12 0, .store .d .r24 .r12 oSave, .store .d .r25 .r12 (oSave + 8), .store .d .r26 .r12 (oSave + 16),
    .store .d .r27 .r12 (oSave + 24), .store .d .r28 .r12 (oSave + 32), .store .d .r29 .r12 (oSave + 40),
    .mflr .r0, .store .d .r0 .r12 oLr, mov .r24 .r3, mov .r25 .r5, mov .r26 .r6, mov .r27 .r7, mov .r28 .r8,
    mov .r29 .r9]

/-- Our stack argument `2 + i` to the call's stack argument `i`. -/
def argCopy (i : Nat) : List Instr := [.load .d .r0 .r12 (arg (2 + i)), .store .d .r0 .r12 (96 + 8 * i)]

/-- `vg_rsa_private_crt`'s arguments: `m`, `k`, `n`, `k`, the input, `k`,
`p` and `p_len` (our stack arguments 0 and 1), and its ten stack arguments,
our stack arguments 2 to 11. -/
def crtArgs : List Instr :=
  [.addi .r3 .r12 oM, mov .r4 .r26, mov .r7 .r29, mov .r8 .r26, .load .d .r9 .r12 (arg 0),
    .load .d .r10 .r12 (arg 1)] ++
  (List.range 10).flatMap argCopy

/-- `r4 := 2 ⌈k / 8⌉`, the words of `n`'s values. -/
def preLen : List Instr := [.addi .r4 .r26 7, .lsr .d .r4 .r4 3, .lsl .r4 .r4 1]

/-- The status kept, and `vg_rsa_public_precompute`'s arguments: `n`'s
values, their length, `n`, `k`, `scratch` and `scratch_len`. -/
def preArgs : List Instr :=
  [.addSp .r12 0, .store .d .r3 .r12 oSt, .addi .r3 .r12 oPre] ++ preLen ++
  [mov .r5 .r25, mov .r6 .r26, .load .d .r7 .r12 (arg 10), .load .d .r8 .r12 (arg 11)]

/-- `vg_rsa_public_precomputed_checked`'s arguments: `out`, `k`, `n`'s
values, their length, `e`, `e_len`, `m`, `k`, and its stack arguments
`scratch` and `scratch_len`. -/
def pubArgs : List Instr :=
  [.addSp .r12 0, mov .r3 .r24, mov .r4 .r26, .addi .r5 .r12 oPre] ++ preLen ++
  [.addi .r6 .r4 0, mov .r4 .r26, mov .r7 .r27, mov .r8 .r28, .addi .r9 .r12 oM, mov .r10 .r26,
    .load .d .r0 .r12 (arg 10), .store .d .r0 .r12 96, .load .d .r0 .r12 (arg 11), .store .d .r0 .r12 104]

/-- The status kept; `r5 := 0`, the comparison's accumulator, over `k`
bytes (`r6`) of `out` (`r3`) and the input (`r4`). -/
def cmpArgs : List Instr :=
  [.addSp .r12 0, .store .d .r3 .r12 oEs, mov .r3 .r24, mov .r4 .r29, .li .r5 0, mov .r6 .r26]

/-- `r5 |= out[i] ^ input[i]`, both advanced. -/
def compare : Prog isa :=
  Impl.Bignum.PPC64LE.Precompute.countLoop .r6
    [.lbz .r7 .r3 0, .lbz .r8 .r4 0, .logic .xor .r7 .r7 .r8, .logic .or .r5 .r5 .r7, .addi .r3 .r3 1,
      .addi .r4 .r4 1]

/-- From the statuses (their bit 0) and the accumulator (at most 255): the
result `v (2 - q)` into `r3` for `v` both statuses and `q` the equality, and
the mask of `v q` into `r9`; `r6 := k`, `r7 := out`, `r8 := m`. -/
def result : List Instr :=
  [.addSp .r12 0, .load .d .r3 .r12 oSt, .load .d .r4 .r12 oEs, .logic .and .r3 .r3 .r4, .li .r4 1,
    .logic .and .r3 .r3 .r4, .subi .r5 .r5 1, .lsr .d .r5 .r5 63, .li .r4 2, .sub .r4 .r4 .r5,
    .logic .and .r5 .r5 .r3, .li .r9 0, .sub .r9 .r9 .r5, .li .r7 0, .sub .r3 .r7 .r3, .logic .and .r3 .r3 .r4,
    mov .r6 .r26, mov .r7 .r24, .addi .r8 .r12 oM]

/-- `out[i] := m[i] & r9`, then `m[i] := 0`, both advanced. -/
def release : Prog isa :=
  Impl.Bignum.PPC64LE.Precompute.countLoop .r6
    [.lbz .r0 .r8 0, .logic .and .r0 .r0 .r9, .stb .r0 .r7 0, .li .r0 0, .stb .r0 .r8 0, .addi .r7 .r7 1,
      .addi .r8 .r8 1]

/-- Our caller's `r24`–`r29` and our return address back from the frame. -/
def restore : List Instr :=
  [.addSp .r12 0, .load .d .r0 .r12 oLr, .mtlr .r0, .load .d .r24 .r12 oSave, .load .d .r25 .r12 (oSave + 8),
    .load .d .r26 .r12 (oSave + 16), .load .d .r27 .r12 (oSave + 24), .load .d .r28 .r12 (oSave + 32),
    .load .d .r29 .r12 (oSave + 40)]

/-- The body of the frame. -/
def body : Prog isa :=
  .seq (.block (save ++ crtArgs)) (.seq crtCall (.seq (.block preArgs) (.seq preCall (.seq (.block pubArgs)
    (.seq pubCall (.seq (.block cmpArgs) (.seq compare (.seq (.block result) (.seq release
      (.block restore))))))))))

/-- `vg_rsa_private_checked`. -/
def code : Prog isa := .frame (.alloc frameBytes) body (.free frameBytes)

end VG.Impl.Rsa.PPC64LE.Priv
