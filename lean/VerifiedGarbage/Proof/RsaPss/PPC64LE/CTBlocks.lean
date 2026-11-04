module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.TaintImm
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
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
open VG.Impl.RsaOaep.PPC64LE (save restore oSt oDig oW copyLoop zeroLoop arg)
open VG.Impl.MdStream.PPC64LE (Params)
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

/-- The taint checks of the blocks of `ctHash` that depend on the hash
function's Merkle–Damgård code (its block size's shifts and its length
field's code), which each instance decides. -/
structure CtTaint (P : Params) : Prop where
  lens : ∃ hc, (VG.Taint.check taint (VG.PPC64LE.Taint.ofRegs []) (.block (ctLens Hd P)) hc).isSome = true
  pad : ∃ hc, (VG.Taint.check taint (VG.PPC64LE.Taint.ofRegs [.r14, .r28]) (pad80 P) hc).isSome = true
  lenF : ∃ hc, (VG.Taint.check taint (VG.PPC64LE.Taint.ofRegs [.r14]) (.block (lenField P)) hc).isSome = true
  lenL : ∃ hc, (VG.Taint.check taint (VG.PPC64LE.Taint.ofRegs [.r14, .r28]) (lenLoop P) hc).isSome = true
  comp : ∃ hc, (VG.Taint.check taint (VG.PPC64LE.Taint.ofRegs []) (.block (compArgs P)) hc).isSome = true
  sel : ∃ hc, (VG.Taint.check taint (VG.PPC64LE.Taint.ofRegs [.r14]) (selHash P) hc).isSome = true

section
variable {P : Params} (ct : CtTaint P)
include ct

theorem ctLens_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (ctLens H P)) fun _ _ => True :=
  let ⟨_, hc⟩ := ct.lens
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block (ctLens H P)) (c' := .block (ctLens Hd P)) (by rfl) hc)

theorem pad80_taint (h : Pins Φ [.r14, .r28]) : RelCT isa (Two Φ) (pad80 P) fun _ _ => True :=
  let ⟨_, hc⟩ := ct.pad; two_taint [.r14, .r28] h hc

theorem lenField_taint (h : Pins Φ [.r14]) : RelCT isa (Two Φ) (.block (lenField P)) fun _ _ => True :=
  let ⟨_, hc⟩ := ct.lenF; two_taint [.r14] h hc

theorem lenLoop_taint (h : Pins Φ [.r14, .r28]) : RelCT isa (Two Φ) (lenLoop P) fun _ _ => True :=
  let ⟨_, hc⟩ := ct.lenL; two_taint [.r14, .r28] h hc

theorem compArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (compArgs P)) fun _ _ => True :=
  let ⟨_, hc⟩ := ct.comp; two_taint [] h hc

theorem selHash_taint (h : Pins Φ [.r14]) : RelCT isa (Two Φ) (selHash P) fun _ _ => True :=
  let ⟨_, hc⟩ := ct.sel; two_taint [.r14] h hc

end

theorem compStep_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.addi .r26 .r26 1, .subi .r28 .r28 1])
    fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem compInit_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.li .r26 0]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem digArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.addi .r3 .r14 oSel, .addi .r4 .r14 oDig])
    fun _ _ => True :=
  two_taint [] h (by taint_decide)

/-- The load of a stack argument into `r11`, from the state after the
frame's push. -/
theorem twA11_taint (j : Nat) (h : Pins Φ []) :
    RelCT isa (Two Φ) (.block [.addSp .r11 0, .load .d .r11 .r11 (arg j)]) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
    (c := .block [.addSp .r11 0, .load .d .r11 .r11 (arg j)]) (c' := .block [.addSp .r11 0, .load .d .r11 .r11 0])
    (by rfl) (by taint_decide))

/-- The load of a table's word through `r11`. -/
theorem twB11_taint (o : Nat) (h : Pins Φ [.r11]) : RelCT isa (Two Φ) (.block [.load .d .r11 .r11 o]) fun _ _ => True :=
  two_taint [.r11] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r11])
    (c := .block [.load .d .r11 .r11 o]) (c' := .block [.load .d .r11 .r11 0]) (by rfl) (by taint_decide))

theorem updRegs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.addi .r3 .r14 oSt, .addi .r7 .r14 oW])
    fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem finRegs_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.addi .r3 .r14 oSt, .addi .r5 .r14 oDig, .addi .r6 .r14 oW]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

end

end VG.Proof.RsaPss.PPC64LE
