module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.TaintImm
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
meta import VerifiedGarbage.Proof.RsaOaep.PPC64LE.TaintImm
meta import VerifiedGarbage.Impl.RsaOaep.PPC64LE

/-!
# RSAES-OAEP encryption on PPC64LE: the taint checks

Untrusted: everything here is checked by Lean. The code between the calls,
checked by the taint analysis from the stack pointer and the registers that
hold public values (`two_taint`). The blocks that use a hash length are
checked on their copy for one hash function (`Hd`), which has the same code
without its immediates (`zImm`). Every address and branch depends only on
the pointers and lengths; the seed, the message, the label and the digests
are only copied and XORed.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)

/-- A hash function whose code is checked in place of any other's. -/
def Hd : Hash := ⟨64, 32, 32, 32, 160, "", .block [], "", .block [], "", .block [], ""⟩

section
variable {α : Type} {Φ : α → State → Prop} (H G : Hash)

theorem entry_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (save ++ prologue)) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem chkK_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (chkK H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block (chkK H)) (c' := .block (chkK Hd))
    (by rfl) (by taint_decide))

theorem chkMsg_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (chkMsg H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block (chkMsg H)) (c' := .block (chkMsg Hd))
    (by rfl) (by taint_decide))

theorem fail_taint (h : Pins Φ [.r15, .r16]) : RelCT isa (Two Φ) encFail fun _ _ => True :=
  two_taint [.r15, .r16] h (by taint_decide)

theorem encEm_taint (h : Pins Φ [.r9, .r10, .r11, .r14, .r15]) : RelCT isa (Two Φ) (encEm H) fun _ _ => True :=
  two_taint [.r9, .r10, .r11, .r14, .r15] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r9, .r10, .r11, .r14, .r15])
    (c := encEm H) (c' := encEm Hd)
    (by rfl) (by taint_decide))

theorem copyLh_taint (h : Pins Φ [.r14]) : RelCT isa (Two Φ) (copyLh H) fun _ _ => True :=
  two_taint [.r14] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r14])
    (c := copyLh H) (c' := copyLh Hd)
    (by rfl) (by taint_decide))

theorem dbArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (dbArgs H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block (dbArgs H)) (c' := .block (dbArgs Hd))
    (by rfl) (by taint_decide))

theorem seedArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (seedArgs H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block (seedArgs H)) (c' := .block (seedArgs Hd))
    (by rfl) (by taint_decide))

theorem st_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.addi .r3 .r14 oSt]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem lab2_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.addi .r3 .r14 oSt, .li .r4 0, Impl.AesGcm.PPC64LE.mov .r5 .r19, Impl.AesGcm.PPC64LE.mov .r6 .r20,
      .addi .r7 .r14 oW]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem lab3_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.addi .r3 .r14 oSt, Impl.AesGcm.PPC64LE.mov .r4 .r20, .addi .r5 .r14 oDig, .addi .r6 .r14 oW])
    fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem mgfHead_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.li .r28 0, .li .r29 0]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem r2_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.addi .r3 .r14 oSt, .li .r4 0, Impl.AesGcm.PPC64LE.mov .r5 .r24, Impl.AesGcm.PPC64LE.mov .r6 .r25,
      .addi .r7 .r14 oW]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem ctr_taint (h : Pins Φ [.r14]) : RelCT isa (Two Φ) (.block updCtrArgs) fun _ _ => True :=
  two_taint [.r14] h (by taint_decide)

theorem r4_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.addi .r3 .r14 oSt, .addi .r4 .r25 4, .addi .r5 .r14 oDig, .addi .r6 .r14 oW]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem xorOut_taint (h : Pins Φ [.r14, .r26, .r27, .r29]) : RelCT isa (Two Φ) (xorOut G) fun _ _ => True :=
  two_taint [.r14, .r26, .r27, .r29] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r14, .r26, .r27, .r29])
    (c := xorOut G) (c' := xorOut Hd)
    (by rfl) (by taint_decide))

theorem nextCtr_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (nextCtr G)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block (nextCtr G)) (c' := .block (nextCtr Hd))
    (by rfl) (by taint_decide))

/-- The first two loads of a table's word, through our stack argument `j`. -/
theorem twA_taint {d : Reg} (j : Nat) (hd : d = .r9 ∨ d = .r12) (h : Pins Φ []) :
    RelCT isa (Two Φ) (.block [.addSp d 0, .load .d d d (arg j)]) fun _ _ => True := by
  rcases hd with rfl | rfl
  · exact two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
      (c := .block [.addSp .r9 0, .load .d .r9 .r9 (arg j)]) (c' := .block [.addSp .r9 0, .load .d .r9 .r9 0])
      (by rfl) (by taint_decide))
  · exact two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
      (c := .block [.addSp .r12 0, .load .d .r12 .r12 (arg j)]) (c' := .block [.addSp .r12 0, .load .d .r12 .r12 0])
      (by rfl) (by taint_decide))

/-- The load of the table's word, through its address in `d`. -/
theorem twB_taint {d : Reg} (o : Nat) (hd : d = .r9 ∨ d = .r12) (h : Pins Φ [d]) :
    RelCT isa (Two Φ) (.block [.load .d d d o]) fun _ _ => True := by
  rcases hd with rfl | rfl
  · exact two_taint [.r9] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r9])
      (c := .block [.load .d .r9 .r9 o]) (c' := .block [.load .d .r9 .r9 0]) (by rfl) (by taint_decide))
  · exact two_taint [.r12] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r12])
      (c := .block [.load .d .r12 .r12 o]) (c' := .block [.load .d .r12 .r12 0]) (by rfl) (by taint_decide))

/-- `xorOut` after the load of `hLen` into `r9`. -/
abbrev xorRest : List Instr :=
  [.addi .r11 .r14 oDig, .add .r12 .r26 .r29, .sub .r8 .r27 .r29, .sub .r10 .r8 .r9,
    .lsr .d .r6 .r10 63, .li .r7 0, .sub .r6 .r7 .r6, .logic .and .r10 .r10 .r6, .add .r9 .r9 .r10]

theorem xorRest_taint (h : Pins Φ [.r9, .r14, .r26, .r27, .r29]) :
    RelCT isa (Two Φ) (.seq (.block xorRest) (.loop (.block xorBody) (.nonzero .d .r9))) fun _ _ => True :=
  two_taint [.r9, .r14, .r26, .r27, .r29] h (by taint_decide)

/-- `nextCtr` after the load of `hLen` into `r12`. -/
abbrev nextRest : List Instr := [.addi .r28 .r28 1, .add .r29 .r29 .r12, .sub .r12 .r29 .r27, .lsr .d .r12 .r12 63]

theorem nextRest_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block nextRest) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem pubArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem restore_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block restore) fun _ _ => True :=
  two_taint [] h (by taint_decide)

end

end VG.Proof.RsaOaep.PPC64LE
