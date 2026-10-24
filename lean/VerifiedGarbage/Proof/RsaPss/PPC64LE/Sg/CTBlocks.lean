module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Impl.RsaPss.PPC64LE.Sign
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.TaintImm
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
meta import VerifiedGarbage.Proof.RsaOaep.PPC64LE.TaintImm
meta import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
meta import VerifiedGarbage.Impl.RsaPss.PPC64LE.Sign

/-!
# RSASSA-PSS signing on PPC64LE: the taint checks

Untrusted: everything here is checked by Lean. The code between the calls,
checked by the taint analysis from the stack pointer and the registers that
hold public values (`two_taint`): `r5` (`n`, on entry), `r14` (`scratch`),
`r15` (`k`), `r19` (`salt_len`), `r20` (`n`) and `r23` (`lo`); the blocks that
use a hash function's length on their copy for one hash function (`Hd`),
with the same code without its immediates (`zImm`). Every address and branch
depends only on the pointers, the lengths and `n₀`: the digest, the salt,
`H` and `EM` are only loaded, stored and masked.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (save)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.RsaOaep.PPC64LE (Hd zImm isSome_check_of_zImm)

section
variable {α : Type} {Φ : α → State → Prop} (H : Hash)

theorem entry_taint (h : Pins Φ [.r5]) : RelCT isa (Two Φ) (.block (save ++ prologue)) fun _ _ => True :=
  two_taint [.r5] h (by taint_decide)

theorem chkEm_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (chkEm H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block (chkEm H)) (c' := .block (chkEm Hd)) (by rfl) (by taint_decide))

theorem chkSalt_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (chkSalt H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block (chkSalt H)) (c' := .block (chkSalt Hd)) (by rfl) (by taint_decide))

theorem zeros8_taint (h : Pins Φ [.r14]) : RelCT isa (Two Φ)
    (.seq (.block [.addi .r4 .r14 Impl.RsaPss.PPC64LE.oY, .li .r5 8, .li .r6 0]) Impl.RsaOaep.PPC64LE.zeroLoop)
    fun _ _ => True :=
  two_taint [.r14] h (by taint_decide)

theorem digArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block (ldArg .r4 8 ++ ([.addi .r5 .r14 (Impl.RsaPss.PPC64LE.oY + 8), .li .r6 H.D] : List Instr))) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block (ldArg .r4 8 ++ [.addi .r5 .r14 (Impl.RsaPss.PPC64LE.oY + 8), .li .r6 H.D]))
    (c' := .block (ldArg .r4 8 ++ [.addi .r5 .r14 0, .li .r6 0])) (by rfl) (by taint_decide))

theorem copy_taint (h : Pins Φ [.r4, .r5, .r6]) : RelCT isa (Two Φ) Impl.RsaOaep.PPC64LE.copyLoop fun _ _ => True :=
  two_taint [.r4, .r5, .r6] h (by taint_decide)

theorem saltDst_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.addi .r5 .r14 (Impl.RsaPss.PPC64LE.oY + 8 + H.D)]) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block [.addi .r5 .r14 (Impl.RsaPss.PPC64LE.oY + 8 + H.D)]) (c' := .block [.addi .r5 .r14 0])
    (by rfl) (by taint_decide))

theorem saltArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block (ldArg .r4 9 ++ [Impl.AesGcm.PPC64LE.mov .r6 .r19])) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem skip_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block []) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem clearEm_taint (h : Pins Φ [.r14, .r15]) : RelCT isa (Two Φ) clearEm fun _ _ => True :=
  two_taint [.r14, .r15] h (by taint_decide)

theorem putSaltHead_taint (h : Pins Φ [.r14, .r15, .r19]) : RelCT isa (Two Φ)
    (.block [.addi .r4 .r14 Impl.RsaOaep.PPC64LE.oEm, .add .r4 .r4 .r15, .sub .r4 .r4 .r19, .subi .r4 .r4 (H.D + 2),
      .li .r5 1, .stb .r5 .r4 0, .addi .r5 .r4 1]) fun _ _ => True :=
  two_taint [.r14, .r15, .r19] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r14, .r15, .r19])
    (c := .block [.addi .r4 .r14 Impl.RsaOaep.PPC64LE.oEm, .add .r4 .r4 .r15, .sub .r4 .r4 .r19,
      .subi .r4 .r4 (H.D + 2), .li .r5 1, .stb .r5 .r4 0, .addi .r5 .r4 1])
    (c' := .block [.addi .r4 .r14 0, .add .r4 .r4 .r15, .sub .r4 .r4 .r19, .subi .r4 .r4 0, .li .r5 0,
      .stb .r5 .r4 0, .addi .r5 .r4 0]) (by rfl) (by taint_decide))

theorem putH_taint (h : Pins Φ [.r14, .r15]) : RelCT isa (Two Φ) (putH H) fun _ _ => True :=
  two_taint [.r14, .r15] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r14, .r15])
    (c := putH H) (c' := putH Hd) (by rfl) (by taint_decide))

theorem dbArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (dbArgs H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block (dbArgs H)) (c' := .block (dbArgs Hd)) (by rfl) (by taint_decide))

theorem clearTop_taint (h : Pins Φ [.r14, .r20, .r23]) : RelCT isa (Two Φ) (.block clearTop) fun _ _ => True :=
  two_taint [.r14, .r20, .r23] h (by taint_decide)

theorem privArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block privArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

end

end VG.Proof.RsaPss.PPC64LE.Sg
