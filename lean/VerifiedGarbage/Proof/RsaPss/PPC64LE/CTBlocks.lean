module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.TaintImm
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
meta import VerifiedGarbage.Proof.RsaOaep.PPC64LE.TaintImm
meta import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
meta import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# RSASSA-PSS verification on PPC64LE: the taint checks

Untrusted: everything here is checked by Lean. The code between the calls,
checked by the taint analysis from the stack pointer and the registers that
hold public values (`two_taint`); the blocks that use a hash function's
lengths on their copy for one hash function (`Hd`), with the same code
without its immediates (`zImm`). Every address and branch depends only on
the pointers, the lengths and the salt-length mode: `EM`, `DB`, `M'` and the
digests are only loaded, stored, masked and compared, the position of `DB`'s
first nonzero byte and the salt's length only masked.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (save restore oSt oDig oW copyLoop zeroLoop)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.RsaOaep.PPC64LE (Hd zImm isSome_check_of_zImm)

section
variable {α : Type} {Φ : α → State → Prop} (H : Hash)

theorem entry_taint (h : Pins Φ [.r3]) : RelCT isa (Two Φ) (.block (save ++ prologue H)) fun _ _ => True :=
  two_taint [.r3] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r3])
    (c := .block (save ++ prologue H)) (c' := .block (save ++ prologue Hd)) (by rfl) (by taint_decide))

theorem fail_taint (h : Pins Φ []) : RelCT isa (Two Φ) fail fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem chkEm_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (chkEm H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block (chkEm H)) (c' := .block (chkEm Hd)) (by rfl) (by taint_decide))

theorem expLen_taint (h : Pins Φ [.r20]) : RelCT isa (Two Φ) expLen fun _ _ => True :=
  two_taint [.r20] h (by taint_decide)

theorem chkSalt_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (chkSalt H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block (chkSalt H)) (c' := .block (chkSalt Hd)) (by rfl) (by taint_decide))

theorem pubArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem acc0_taint (h : Pins Φ [.r14, .r15, .r17]) : RelCT isa (Two Φ) (.block acc0) fun _ _ => True :=
  two_taint [.r14, .r15, .r17] h (by taint_decide)

theorem dbArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (dbArgs H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block (dbArgs H)) (c' := .block (dbArgs Hd)) (by rfl) (by taint_decide))

theorem clearTop_taint (h : Pins Φ [.r14, .r17]) : RelCT isa (Two Φ) (.block clearTop) fun _ _ => True :=
  two_taint [.r14, .r17] h (by taint_decide)

theorem scan_taint (h : Pins Φ [.r14, .r17, .r21]) : RelCT isa (Two Φ) scan fun _ _ => True :=
  two_taint [.r14, .r17, .r21] h (by taint_decide)

theorem posCheck_taint (h : Pins Φ [.r14, .r15]) : RelCT isa (Two Φ) (.block posCheck) fun _ _ => True :=
  two_taint [.r14, .r15] h (by taint_decide)

theorem lenCheck_taint (h : Pins Φ [.r20]) : RelCT isa (Two Φ) lenCheck fun _ _ => True :=
  two_taint [.r20] h (by taint_decide)

theorem mPrefix_taint (n : Nat) (h : Pins Φ [.r14, .r16]) : RelCT isa (Two Φ) (mPrefix H n) fun _ _ => True :=
  two_taint [.r14, .r16] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r14, .r16])
    (c := mPrefix H n) (c' := mPrefix Hd 0) (by rfl) (by taint_decide))

theorem copySalt_taint (h : Pins Φ [.r14, .r17, .r19, .r21]) : RelCT isa (Two Φ) (copySalt H) fun _ _ => True :=
  two_taint [.r14, .r17, .r19, .r21] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r14, .r17, .r19, .r21])
    (c := copySalt H) (c' := copySalt Hd) (by rfl) (by taint_decide))

theorem cmpH_taint (o : Nat) (h : Pins Φ [.r14, .r17, .r21]) : RelCT isa (Two Φ) (cmpH H o) fun _ _ => True :=
  two_taint [.r14, .r17, .r21] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r14, .r17, .r21])
    (c := cmpH H o) (c' := cmpH Hd 0) (by rfl) (by taint_decide))

theorem copyDb_taint (h : Pins Φ [.r14, .r17, .r21]) : RelCT isa (Two Φ) (copyDb H) fun _ _ => True :=
  two_taint [.r14, .r17, .r21] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r14, .r17, .r21])
    (c := copyDb H) (c' := copyDb Hd) (by rfl) (by taint_decide))

theorem shift_taint (h : Pins Φ [.r14, .r21]) : RelCT isa (Two Φ) (shift H) fun _ _ => True :=
  two_taint [.r14, .r21] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r14, .r21])
    (c := shift H) (c' := shift Hd) (by rfl) (by taint_decide))

theorem copyN_taint (a b n : Nat) (h : Pins Φ [.r14]) : RelCT isa (Two Φ) (copyN a b n) fun _ _ => True :=
  two_taint [.r14] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r14])
    (c := copyN a b n) (c' := copyN 0 0 0) (by rfl) (by taint_decide))

theorem select_taint (h : Pins Φ [.r14]) : RelCT isa (Two Φ) (select H) fun _ _ => True :=
  two_taint [.r14] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r14])
    (c := select H) (c' := select Hd) (by rfl) (by taint_decide))

theorem fixUpd_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.li .r4 0, .addi .r5 .r14 oY, .addi .r6 .r19 (8 + H.D)]) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block [.li .r4 0, .addi .r5 .r14 oY, .addi .r6 .r19 (8 + H.D)])
    (c' := .block [.li .r4 0, .addi .r5 .r14 0, .addi .r6 .r19 0]) (by rfl) (by taint_decide))

theorem fixFin_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.addi .r4 .r19 (8 + H.D)]) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block [.addi .r4 .r19 (8 + H.D)]) (c' := .block [.addi .r4 .r19 0]) (by rfl) (by taint_decide))

theorem anyUpd_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.li .r4 0, .addi .r5 .r14 oY, .li .r6 (8 + H.D)]) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block [.li .r4 0, .addi .r5 .r14 oY, .li .r6 (8 + H.D)])
    (c' := .block [.li .r4 0, .addi .r5 .r14 0, .li .r6 0]) (by rfl) (by taint_decide))

theorem loopInit_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.li .r26 0, Impl.AesGcm.PPC64LE.mov .r27 .r21]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem lr1_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.addi .r4 .r26 (8 + H.D)]) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block [.addi .r4 .r26 (8 + H.D)]) (c' := .block [.addi .r4 .r26 0]) (by rfl) (by taint_decide))

theorem lr2_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.addi .r4 .r26 (8 + H.D), .addi .r5 .r14 (oY + 8 + H.D), .add .r5 .r5 .r26, .li .r6 1]) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block [.addi .r4 .r26 (8 + H.D), .addi .r5 .r14 (oY + 8 + H.D), .add .r5 .r5 .r26, .li .r6 1])
    (c' := .block [.addi .r4 .r26 0, .addi .r5 .r14 0, .add .r5 .r5 .r26, .li .r6 0]) (by rfl) (by taint_decide))

theorem lr3_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.addi .r26 .r26 1, .subi .r27 .r27 1])
    fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem updRegs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.addi .r3 .r14 oSt, .addi .r7 .r14 oW])
    fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem finRegs_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.addi .r3 .r14 oSt, .addi .r5 .r14 oDig, .addi .r6 .r14 oW]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

end

end VG.Proof.RsaPss.PPC64LE
