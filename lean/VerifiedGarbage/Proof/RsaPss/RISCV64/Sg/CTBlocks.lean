module

-- separate module: its taint checks evaluate the code, so it imports what it uses for `meta` too, which
-- the other proofs need not.

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
public import VerifiedGarbage.Impl.RsaPss.RISCV64.Sign
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
meta import VerifiedGarbage.Impl.RsaPss.RISCV64.Sign

/-!
# RSASSA-PSS signing on RISC-V: the taint checks

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Sg/CTBlocks.lean`): the code between the calls,
checked by the taint analysis from the stack pointer and the registers that
hold public values (`two_taint`): `a2` (`n`, on entry), `s0` (`scratch`),
`s1` (`k`), `s3` (`lo`) and `s4` (`salt_len`); the blocks that use a hash
function's length on their copy for one hash function (`Hd`), with the same
code without its immediates (`zImm`). Every address and branch depends only
on the pointers, the lengths and `n₀`: the digest, the salt, `H`, `EM`, the
saved arguments and the mask `c` are only loaded, stored and masked.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64.Sign VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Impl.RsaOaep.RISCV64 (save argBase clearEm oEm oDig)
open VG.Impl.RsaPss.RISCV64 (yBase clearY)
open VG.Impl.RsaPkcs1Sig.RISCV64 (copyLoop)
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.RsaOaep.RISCV64 (Hd zImm isSome_check_of_zImm)

section
variable {α : Type} {Φ : α → State → Prop} (H : Hash)

theorem entry_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (save ++ prologue)) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem spill_taint (h : Pins Φ [.s0, .a2]) : RelCT isa (Two Φ) (.block spill) fun _ _ => True :=
  two_taint [.s0, .a2] h (by taint_decide)

theorem chkEm_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (chkEm H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [])
    (c := .block (chkEm H)) (c' := .block (chkEm Hd)) (by rfl) (by taint_decide))

theorem chkSalt_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (chkSalt H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [])
    (c := .block (chkSalt H)) (c' := .block (chkSalt Hd)) (by rfl) (by taint_decide))

theorem zeros8_taint (h : Pins Φ [.s0]) : RelCT isa (Two Φ) (clearY [.li .t5 8]) fun _ _ => True :=
  two_taint [.s0] h (by taint_decide)

theorem digArgs_taint (h : Pins Φ [.s0]) : RelCT isa (Two Φ)
    (.block (([argBase, .load .d .a4 .t6 64] : List Instr) ++ yBase .a1 ++
      ([.addi .a1 .a1 8, .li .a5 H.D] : List Instr))) fun _ _ => True :=
  two_taint [.s0] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0])
    (c := .block (([argBase, .load .d .a4 .t6 64] : List Instr) ++ yBase .a1 ++
      ([.addi .a1 .a1 8, .li .a5 H.D] : List Instr)))
    (c' := .block (([argBase, .load .d .a4 .t6 64] : List Instr) ++ yBase .a1 ++
      ([.addi .a1 .a1 8, .li .a5 Hd.D] : List Instr))) (by rfl)
    (by taint_decide))

theorem copy_taint (h : Pins Φ [.a4, .a1, .a5]) : RelCT isa (Two Φ) copyLoop fun _ _ => True :=
  two_taint [.a4, .a1, .a5] h (by taint_decide)

theorem saltDst_taint (h : Pins Φ [.s0]) : RelCT isa (Two Φ)
    (.block (yBase .a1 ++ ([.addi .a1 .a1 ((8 + H.D : Nat) : Int)] : List Instr))) fun _ _ => True :=
  two_taint [.s0] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0])
    (c := .block (yBase .a1 ++ ([.addi .a1 .a1 ((8 + H.D : Nat) : Int)] : List Instr)))
    (c' := .block (yBase .a1 ++ ([.addi .a1 .a1 ((8 + Hd.D : Nat) : Int)] : List Instr))) (by rfl) (by taint_decide))

theorem saltArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [argBase, .load .d .a4 .t6 72, mov .a5 .s4]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem skip_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block []) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem hashArg_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [mov .s6 .s4]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem clearEm_taint (h : Pins Φ [.s0]) : RelCT isa (Two Φ) clearEm fun _ _ => True :=
  two_taint [.s0] h (by taint_decide)

theorem saltHead_taint (h : Pins Φ [.s0, .s1, .s4]) : RelCT isa (Two Φ)
    (.block [.add .a1 .s0 .s1, .sub .a1 .a1 .s4, .addi .a1 .a1 (-(H.D + 2 : Nat)), .li .t1 1,
      .store .b .t1 .a1 0, .addi .a1 .a1 1]) fun _ _ => True :=
  two_taint [.s0, .s1, .s4] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0, .s1, .s4])
    (c := .block [.add .a1 .s0 .s1, .sub .a1 .a1 .s4, .addi .a1 .a1 (-(H.D + 2 : Nat)), .li .t1 1,
      .store .b .t1 .a1 0, .addi .a1 .a1 1])
    (c' := .block [.add .a1 .s0 .s1, .sub .a1 .a1 .s4, .addi .a1 .a1 (-(Hd.D + 2 : Nat)), .li .t1 1,
      .store .b .t1 .a1 0, .addi .a1 .a1 1]) (by rfl) (by taint_decide))

theorem putH_taint (h : Pins Φ [.s0, .s1]) : RelCT isa (Two Φ) (putH H) fun _ _ => True :=
  two_taint [.s0, .s1] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0, .s1])
    (c := putH H) (c' := putH Hd) (by rfl) (by taint_decide))

theorem dbArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (dbArgs H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [])
    (c := .block (dbArgs H)) (c' := .block (dbArgs Hd)) (by rfl) (by taint_decide))

theorem clearTop_taint (h : Pins Φ [.s0, .s3]) : RelCT isa (Two Φ) (.block clearTop) fun _ _ => True :=
  two_taint [.s0, .s3] h (by taint_decide)

theorem privArgs_taint (h : Pins Φ [.s0]) : RelCT isa (Two Φ) (.block privArgs) fun _ _ => True :=
  two_taint [.s0] h (by taint_decide)

end

end VG.Proof.RsaPss.RISCV64.Sg
