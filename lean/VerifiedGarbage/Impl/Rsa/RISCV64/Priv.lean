module

public import VerifiedGarbage.Impl.Bignum.RISCV64.Crt

/-!
# The checked RSA private-key operation on RISC-V

`vg_rsa_private_checked(out = a0, out_len = a1, n = a2, n_len = a3, e = a4,
e_len = a5, input = a6, input_len = a7, p, p_len, q, q_len, dp, dp_len, dq,
dq_len, qinv, qinv_len, scratch, scratch_len)`, the last twelve on the stack.
As on PPC64LE (`Impl/Rsa/PPC64LE/Priv.lean`), BoringSSL's
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
`out`, `n`, `k = n_len`, `e`, `e_len` and the input are kept in `s1`–`s6`,
which the callees preserve.

The frame (`alloc frameBytes`) holds the stack arguments of the calls (the
ten of `vg_rsa_private_crt`, at `sp`); our caller's `s1`–`s6` and our return
address, which each call overwrites in `ra` (`oSave`, `oRa`); the two
statuses (`oSt`, `oEs`); `m`, of up to 1024 bytes (`oM`); and `n`'s values,
of up to 256 words (`oPre`). Our own stack arguments are then at `sp +
frameBytes + 8 i` (`arg i`), from `t6`, which `argBase` points at the first.
-/

@[expose] public section

namespace VG.Impl.Rsa.RISCV64.Priv

open VG VG.RISCV64

/-- `mv d, n` (`addi d, n, 0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- The size of the frame. -/
def frameBytes : Nat := 3248

/-- Our caller's `s1`–`s6`, our return address and the statuses. -/
def oSave : Nat := 96
def oRa : Nat := 144
def oSt : Nat := 152
def oEs : Nat := 160

/-- `m` and `n`'s values. -/
def oM : Nat := 176
def oPre : Nat := 1200

/-- `t6 :=` the address of our first stack argument, `sp + frameBytes`. -/
def argBase : List Instr := [.addSp .t6 2032, .addi .t6 .t6 ((frameBytes - 2032 : Nat) : Int)]

/-- `vg_rsa_private_crt`. -/
def crtCall : Prog isa := .call "vg_rsa_private_crt" Impl.Bignum.RISCV64.Crt.crt

/-- `vg_rsa_public_precompute`. -/
def preCall : Prog isa := .call "vg_rsa_public_precompute" Impl.Bignum.RISCV64.Precompute.precompute

/-- `vg_rsa_public_precomputed_checked`. -/
def pubCall : Prog isa :=
  .call "vg_rsa_public_precomputed_checked" Impl.Bignum.RISCV64.PublicChecked.publicChecked

/-- `t0 := sp`; our caller's `s1`–`s6` and our return address into the frame;
`out`, `n`, `k`, `e`, `e_len` and the input into `s1`–`s6`. -/
def save : List Instr :=
  [.addSp .t0 0, .store .d .s1 .t0 oSave, .store .d .s2 .t0 (oSave + 8), .store .d .s3 .t0 (oSave + 16),
    .store .d .s4 .t0 (oSave + 24), .store .d .s5 .t0 (oSave + 32), .store .d .s6 .t0 (oSave + 40),
    .store .d .ra .t0 oRa, mov .s1 .a0, mov .s2 .a2, mov .s3 .a3, mov .s4 .a4, mov .s5 .a5, mov .s6 .a6]

/-- Our stack argument `2 + i` to the call's stack argument `i`. -/
def argCopy (i : Nat) : List Instr := [.load .d .t1 .t6 (8 * (2 + i)), .store .d .t1 .t0 (8 * i)]

/-- `vg_rsa_private_crt`'s arguments: `m`, `k`, `n`, `k`, the input, `k`,
`p` and `p_len` (our stack arguments 0 and 1), and its ten stack arguments,
our stack arguments 2 to 11. -/
def crtArgs : List Instr :=
  argBase ++ [.addi .a0 .t0 oM, mov .a1 .s3, mov .a4 .s6, mov .a5 .s3, .load .d .a6 .t6 0,
    .load .d .a7 .t6 8] ++
  (List.range 10).flatMap argCopy

/-- `a1 := 2 ⌈k / 8⌉`, the words of `n`'s values. -/
def preLen (rd : Reg) : List Instr := [.addi rd .s3 7, .shift .srl .d rd rd 3, .shift .sll .d rd rd 1]

/-- The status kept, and `vg_rsa_public_precompute`'s arguments: `n`'s
values, their length, `n`, `k`, `scratch` and `scratch_len`. -/
def preArgs : List Instr :=
  [.addSp .t0 0, .store .d .a0 .t0 oSt, .addi .a0 .t0 oPre] ++ preLen .a1 ++
  [mov .a2 .s2, mov .a3 .s3] ++ argBase ++ [.load .d .a4 .t6 80, .load .d .a5 .t6 88]

/-- `vg_rsa_public_precomputed_checked`'s arguments: `out`, `k`, `n`'s
values, their length, `e`, `e_len`, `m`, `k`, and its stack arguments
`scratch` and `scratch_len`. -/
def pubArgs : List Instr :=
  [.addSp .t0 0, mov .a0 .s1, mov .a1 .s3, .addi .a2 .t0 oPre] ++ preLen .a3 ++
  [mov .a4 .s4, mov .a5 .s5, .addi .a6 .t0 oM, mov .a7 .s3] ++ argBase ++
  [.load .d .t1 .t6 80, .store .d .t1 .t0 0, .load .d .t1 .t6 88, .store .d .t1 .t0 8]

/-- The status kept; `t4 := 0`, the comparison's accumulator, over `k` bytes
(`t5`) of `out` (`t2`) and the input (`t3`). -/
def cmpArgs : List Instr :=
  [.addSp .t0 0, .store .d .a0 .t0 oEs, mov .t2 .s1, mov .t3 .s6, .li .t4 0, mov .t5 .s3]

/-- `t4 |= out[i] ^ input[i]`, both advanced. -/
def compare : Prog isa :=
  Impl.Bignum.RISCV64.countLoop .t5
    [.load .b .a1 .t2 0, .load .b .a2 .t3 0, .logic .xor .a1 .a1 .a2, .logic .or .t4 .t4 .a1,
      .addi .t2 .t2 1, .addi .t3 .t3 1]

/-- From the statuses (their bit 0) and the accumulator (at most 255): the
result `v (2 - q)` into `a0` for `v` both statuses and `q` the equality, and
the mask of `v q` into `a3`; `t5 := k`, `t2 := out`, `t3 := m`. -/
def result : List Instr :=
  [.addSp .t0 0, .load .d .a0 .t0 oSt, .load .d .a1 .t0 oEs, .logic .and .a0 .a0 .a1,
    .logicImm .and .a0 .a0 1, .addi .t4 .t4 (-1), .shift .srl .d .t4 .t4 63, .li .a1 2,
    .sub .a1 .a1 .t4, .logic .and .t4 .t4 .a0, .li .a2 0, .sub .a3 .a2 .t4, .sub .a0 .a2 .a0,
    .logic .and .a0 .a0 .a1, mov .t5 .s3, mov .t2 .s1, .addi .t3 .t0 oM]

/-- `out[i] := m[i] & a3`, then `m[i] := 0`, both advanced. -/
def release : Prog isa :=
  Impl.Bignum.RISCV64.countLoop .t5
    [.load .b .a1 .t3 0, .logic .and .a1 .a1 .a3, .store .b .a1 .t2 0, .li .a2 0, .store .b .a2 .t3 0,
      .addi .t2 .t2 1, .addi .t3 .t3 1]

/-- Our caller's `s1`–`s6` and our return address back from the frame. -/
def restore : List Instr :=
  [.addSp .t0 0, .load .d .ra .t0 oRa, .load .d .s1 .t0 oSave, .load .d .s2 .t0 (oSave + 8),
    .load .d .s3 .t0 (oSave + 16), .load .d .s4 .t0 (oSave + 24), .load .d .s5 .t0 (oSave + 32),
    .load .d .s6 .t0 (oSave + 40)]

/-- The body of the frame. -/
def body : Prog isa :=
  .seq (.block (save ++ crtArgs)) (.seq crtCall (.seq (.block preArgs) (.seq preCall (.seq (.block pubArgs)
    (.seq pubCall (.seq (.block cmpArgs) (.seq compare (.seq (.block result) (.seq release
      (.block restore))))))))))

/-- `vg_rsa_private_checked`. -/
def code : Prog isa := .frame (.alloc frameBytes) body (.free frameBytes)

end VG.Impl.Rsa.RISCV64.Priv
