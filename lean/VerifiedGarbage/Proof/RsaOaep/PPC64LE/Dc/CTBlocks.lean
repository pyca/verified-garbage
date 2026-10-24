module

import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE.Decrypt
meta import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
meta import VerifiedGarbage.Impl.RsaOaep.PPC64LE.Decrypt
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two

/-!
# RSAES-OAEP decryption on PPC64LE: the taint checks

Untrusted: everything here is checked by Lean. The code between the calls,
checked by the taint analysis from the stack pointer and the registers that
hold public values (`two_taint`): `r14` (`scratch`), `r15` (`k`), `r16`
(`out`), `r17` (`msg_len`). The blocks that use a hash length are checked on
their copy for one hash function (`Hd`), as for encryption. Every address
and branch depends only on those; `EM`, the private operation's result, the
digests, the scan's masks and the shift's count are only loaded, combined
and stored.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.RsaOaep.PPC64LE (Hd zImm isSome_check_of_zImm)

section
variable {α : Type} {Φ : α → State → Prop} (H : Hash)

theorem entry_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (save ++ Dec.prologue)) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem privArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block privArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem lsr_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.lsr .w .r20 .r3 0]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem chkK_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (Dec.chkK H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block (Dec.chkK H)) (c' := .block (Dec.chkK Hd)) (by rfl) (by taint_decide))

theorem decFail_taint (h : Pins Φ [.r15, .r16, .r17]) : RelCT isa (Two Φ) decFail fun _ _ => True :=
  two_taint [.r15, .r16, .r17] h (by taint_decide)

theorem lab2_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.addi .r3 .r14 oSt, .li .r4 0, Impl.AesGcm.PPC64LE.mov .r5 .r18, Impl.AesGcm.PPC64LE.mov .r6 .r19,
      .addi .r7 .r14 oW]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem lab3_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.addi .r3 .r14 oSt, Impl.AesGcm.PPC64LE.mov .r4 .r19, .addi .r5 .r14 oDig, .addi .r6 .r14 oW])
    fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem accLh_taint (h : Pins Φ [.r14]) : RelCT isa (Two Φ) (accLh H) fun _ _ => True :=
  two_taint [.r14] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r14])
    (c := accLh H) (c' := accLh Hd) (by rfl) (by taint_decide))

theorem scan_taint (h : Pins Φ [.r14, .r15]) : RelCT isa (Two Φ) (scan H) fun _ _ => True :=
  two_taint [.r14, .r15] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r14, .r15])
    (c := scan H) (c' := scan Hd) (by rfl) (by taint_decide))

theorem clearBuf_taint (h : Pins Φ [.r14]) : RelCT isa (Two Φ) clearBuf fun _ _ => True :=
  two_taint [.r14] h (by taint_decide)

theorem copyT_taint (h : Pins Φ [.r14, .r15]) : RelCT isa (Two Φ) (copyT H) fun _ _ => True :=
  two_taint [.r14, .r15] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r14, .r15])
    (c := copyT H) (c' := copyT Hd) (by rfl) (by taint_decide))

theorem shift_taint (h : Pins Φ [.r14, .r15]) : RelCT isa (Two Φ) shift fun _ _ => True :=
  two_taint [.r14, .r15] h (by taint_decide)

theorem okMask_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block okMask) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem outLoop_taint (h : Pins Φ [.r14, .r15, .r16]) : RelCT isa (Two Φ) outLoop fun _ _ => True :=
  two_taint [.r14, .r15, .r16] h (by taint_decide)

theorem decRet_taint (h : Pins Φ [.r17]) : RelCT isa (Two Φ) (.block (decRet H)) fun _ _ => True :=
  two_taint [.r17] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r17])
    (c := .block (decRet H)) (c' := .block (decRet Hd)) (by rfl) (by taint_decide))

end

end VG.Proof.RsaOaep.PPC64LE.Dec
