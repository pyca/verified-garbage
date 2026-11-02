module

-- separate module: its taint checks evaluate the code, so it imports what it uses for `meta` too, which
-- the other proofs need not.
import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
public import VerifiedGarbage.Impl.RsaOaep.RISCV64.Decrypt
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
meta import VerifiedGarbage.Impl.RsaOaep.RISCV64.Decrypt
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two

/-!
# RSAES-OAEP decryption on RISC-V: the taint checks

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/CTBlocks.lean`): the code between the calls,
checked by the taint analysis from the stack pointer and the registers that
hold public values (`two_taint`): `s0` (`scratch`), `s1` (`k`), `s2`
(`out`), `s3` (`msg_len`). The blocks that use a hash length are checked on
their copy for one hash function (`Hd`), as for encryption. Every address
and branch depends only on those; `EM`, the private operation's result, the
digests, the scan's masks and the shift's count are only loaded, combined
and stored.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.RsaOaep.RISCV64 (Hd isSome_check_of_zImm)

section
variable {α : Type} {Φ : α → State → Prop} (H : Hash)

theorem dentry_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (save ++ Dec.prologue)) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem privArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block privArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem zext_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.shift .sll .d .s4 .a0 32, .shift .srl .d .s4 .s4 32]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem decFail_taint (h : Pins Φ [.s1, .s2, .s3]) : RelCT isa (Two Φ) decFail fun _ _ => True :=
  two_taint [.s1, .s2, .s3] h (by taint_decide)

theorem lab2_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [argBase, .addi .a0 .s0 oSt, .li .a1 0, .load .d .a2 .t6 72, .load .d .a3 .t6 80]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem lab3_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [argBase, .addi .a0 .s0 oSt, .load .d .a1 .t6 80, .addi .a2 .s0 oDig]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem accLh_taint (h : Pins Φ [.s0]) : RelCT isa (Two Φ) (accLh H) fun _ _ => True :=
  two_taint [.s0] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0])
    (c := accLh H) (c' := accLh Hd) (by rfl) (by taint_decide))

theorem scan_taint (h : Pins Φ [.s0, .s1]) : RelCT isa (Two Φ) (scan H) fun _ _ => True :=
  two_taint [.s0, .s1] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0, .s1])
    (c := scan H) (c' := scan Hd) (by rfl) (by taint_decide))

theorem clearBuf_taint (h : Pins Φ [.s0]) : RelCT isa (Two Φ) clearBuf fun _ _ => True :=
  two_taint [.s0] h (by taint_decide)

theorem copyT_taint (h : Pins Φ [.s0, .s1]) : RelCT isa (Two Φ) (copyT H) fun _ _ => True :=
  two_taint [.s0, .s1] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0, .s1])
    (c := copyT H) (c' := copyT Hd) (by rfl) (by taint_decide))

theorem shift_taint (h : Pins Φ [.s0, .s1]) : RelCT isa (Two Φ) shift fun _ _ => True :=
  two_taint [.s0, .s1] h (by taint_decide)

theorem okMask_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block okMask) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem outLoop_taint (h : Pins Φ [.s0, .s1, .s2]) : RelCT isa (Two Φ) outLoop fun _ _ => True :=
  two_taint [.s0, .s1, .s2] h (by taint_decide)

theorem decRet_taint (h : Pins Φ [.s3]) : RelCT isa (Two Φ) (.block (decRet H)) fun _ _ => True :=
  two_taint [.s3] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s3])
    (c := .block (decRet H)) (c' := .block (decRet Hd)) (by rfl) (by taint_decide))

end

end VG.Proof.RsaOaep.RISCV64.Dec
