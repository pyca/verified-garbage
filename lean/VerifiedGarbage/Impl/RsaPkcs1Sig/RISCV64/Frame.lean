module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Encode
public import VerifiedGarbage.Impl.Bignum.RISCV64.PublicChecked

/-!
# RSASSA-PKCS1-v1_5 on RISC-V: the frame

`vg_rsa_pkcs1_verify_precomputed` and `vg_rsa_pkcs1_recover_precomputed`
allocate a frame of `frameBytes` bytes. It holds the stack arguments of the
call of `vg_rsa_public_precomputed_checked`, `scratch` and `scratch_len` (at
`sp`, `sp + 8`); our caller's `s1`–`s4` and our return address, which the
call overwrites in `ra` (`oSave`, `oRa`); the call's status (`oSt`);
`recover`'s mask (`oMk`); and the two buffers `EM₁` and `EM₂` of up to 1024
bytes (`oEM1`, `oEM2`). Our own stack arguments are then at
`sp + frameBytes + 8 i`, from `t6`, which `argBase` points at the first. The
frame is addressed through `t0`, which holds `sp`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.RISCV64

open VG VG.RISCV64

/-- The size of the frame. -/
def frameBytes : Nat := 2128

/-- Our caller's `s1`–`s4`, our return address, the status and the mask. -/
def oSave : Nat := 16
def oRa : Nat := 48
def oSt : Nat := 56
def oMk : Nat := 64

/-- The buffers. -/
def oEM1 : Nat := 72
def oEM2 : Nat := 1096

/-- `t6 :=` the address of our first stack argument, `sp + frameBytes`. -/
def argBase : List Instr := [.addSp .t6 2032, .addi .t6 .t6 ((frameBytes - 2032 : Nat) : Int)]

/-- `vg_rsa_public_precomputed_checked`. -/
def pubCall : Prog isa :=
  .call "vg_rsa_public_precomputed_checked" Impl.Bignum.RISCV64.PublicChecked.publicChecked

/-- `t0 := sp`; our caller's `s1`–`s4` and our return address into the
frame. -/
def save : List Instr :=
  [.addSp .t0 0, .store .d .s1 .t0 oSave, .store .d .s2 .t0 (oSave + 8), .store .d .s3 .t0 (oSave + 16),
    .store .d .s4 .t0 (oSave + 24), .store .d .ra .t0 oRa]

/-- Our caller's `s1`–`s4` and our return address back from the frame. -/
def restore : List Instr :=
  [.addSp .t0 0, .load .d .s1 .t0 oSave, .load .d .s2 .t0 (oSave + 8), .load .d .s3 .t0 (oSave + 16),
    .load .d .s4 .t0 (oSave + 24), .load .d .ra .t0 oRa]

/-- `d :=` the low 32 bits of `n`, zero-extended. -/
def zext (d n : Reg) : List Instr := [.shift .sll .d d n 32, .shift .srl .d d d 32]

/-- The call's stack arguments `scratch` and `scratch_len` (our stack
arguments 1 and 2); `pre` and `pre_len` (our stack arguments 3 and 4) into
`a2` and `a3`; `a0 := EM₁`, `a1 := k` (in `s`). -/
def callTail (s : Reg) : List Instr :=
  argBase ++ [.load .d .t1 .t6 8, .store .d .t1 .t0 0, .load .d .t1 .t6 16, .store .d .t1 .t0 8,
    .load .d .a2 .t6 24, .load .d .a3 .t6 32, .addi .a0 .t0 oEM1, mov .a1 s]

/-- 0 returned. -/
def ret0 : List Instr := [.li .a0 0]

/-- `compare`'s registers: `EM₁`, `EM₂` and `k` (in `r`). -/
def cmpArgs (r : Reg) : List Instr := [.addSp .t0 0, .addi .a1 .t0 oEM1, .addi .a2 .t0 oEM2, mov .a3 r]

/-- `sig_len - n_len` (`n_len` in `r`) into `t0`: `sig_len` is our first
stack argument, at `sp`. -/
def lenCheck (r : Reg) : List Instr := [.addSp .t0 0, .load .d .t0 .t0 0, .sub .t0 .t0 r]

end VG.Impl.RsaPkcs1Sig.RISCV64
