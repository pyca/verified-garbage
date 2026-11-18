module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
meta import VerifiedGarbage.Impl.RsaOaep.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-! ### `RsaOaep.PPC64LE.TaintImm`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP encryption on PPC64LE: code without its immediates

Untrusted: everything here is checked by Lean. As `Code.eraseImm`
(`Proof/Framework/PPC64LE/TaintErase.lean`), which zeroes the immediates of
`li`, `lis`, `ori` and `oris`, `zImm` also zeroes those of `addi` and `subi`,
which the analysis does not read either (`check_zImm`). The blocks that use
a hash length (as an immediate) are then checked once, for any hash function,
on their copy for one of them (`isSome_check_of_zImm`), as on AArch64
(`Proof/RsaOaep/AArch64/TaintImm.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE

/-- The instruction with the immediate of an `li`, `addi` or `subi`, or the
offset of a load, zeroed. -/
def Instr.zImm : Instr → Instr
  | .li d _ => .li d 0
  | .addi d n _ => .addi d n 0
  | .subi d n _ => .subi d n 0
  | .load sz t n _ => .load sz t n 0
  | i => i

/-- The code with those immediates zeroed. -/
def zImm : Prog isa → Prog isa
  | .block is => .block (is.map Instr.zImm)
  | .seq a b => .seq (zImm a) (zImm b)
  | .ite c t e => .ite c (zImm t) (zImm e)
  | .loop b c => .loop (zImm b) c
  | .call n b => .call n (zImm b)
  | .frame p b q => .frame p (zImm b) q
  | .icall i n b nx => .icall i n b nx

theorem step_zImm (τ : VG.PPC64LE.Taint.T) (i : Instr) :
    VG.PPC64LE.Taint.step τ (Instr.zImm i) = VG.PPC64LE.Taint.step τ i := by
  cases i <;> rfl

theorem checkBlock_zImm (τ : taint.T) (is : List isa.Instr) :
    taint.checkBlock τ (is.map Instr.zImm) = taint.checkBlock τ is := by
  induction is generalizing τ with
  | nil => rfl
  | cons i is ih =>
    show (taint.step τ (Instr.zImm i)).bind (taint.checkBlock · _) = (taint.step τ i).bind (taint.checkBlock · _)
    rw [taint_step τ (Instr.zImm i), taint_step τ i, step_zImm τ i]
    exact congrArg (Option.bind _) (funext ih)

theorem checkChunks_zImm {chunkSize : Nat} (τ : taint.T) (is : List isa.Instr) (ms : List taint.T) :
    taint.checkChunks chunkSize τ (is.map Instr.zImm) ms = taint.checkChunks chunkSize τ is ms := by
  induction ms generalizing τ is with
  | nil => exact checkBlock_zImm τ is
  | cons m ms ih =>
    simp only [VG.Taint.checkChunks, KList.take_eq, KList.drop_eq, ← List.map_take, ← List.map_drop, ih]
    exact congrArg (Option.bind · _) (checkBlock_zImm τ _)

theorem check_zImm (τ : taint.T) (c : Prog isa) (h : VG.Taint.Hint taint.T) :
    taint.check τ (zImm c) h = taint.check τ c h := by
  induction c generalizing τ h with
  | icall => cases h <;> rfl
  | block is => cases h <;> first | rfl | exact checkChunks_zImm τ is _
  | seq a b iha ihb => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, iha, ihb]
  | ite c t e iht ihe => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, iht, ihe]
  | loop b c ih => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, ih]
  | call n b ih => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, ih]
  | frame p b q ih => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, ih]

/-- The analysis of `c` from that of `c'`, which has the same code without
those immediates. -/
theorem isSome_check_of_zImm {c c' : Prog isa} (he : zImm c = zImm c') {τ : taint.T}
    {hc : VG.Taint.Hint taint.T} (h : (taint.check τ c' hc).isSome = true) :
    (taint.check τ c hc).isSome = true := by
  rw [← check_zImm, he, check_zImm]; exact h

end VG.Proof.RsaOaep.PPC64LE

end

end

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

/-- The first two loads of a table's word, through our stack argument `j`. -/
theorem twA_taint {d : Reg} (j : Nat) (hd : d = .r9 ∨ d = .r12 ∨ d = .r3) (h : Pins Φ []) :
    RelCT isa (Two Φ) (.block [.addSp d 0, .load .d d d (arg j)]) fun _ _ => True := by
  rcases hd with rfl | rfl | rfl
  · exact two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
      (c := .block [.addSp .r9 0, .load .d .r9 .r9 (arg j)]) (c' := .block [.addSp .r9 0, .load .d .r9 .r9 0])
      (by rfl) (by taint_decide))
  · exact two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
      (c := .block [.addSp .r12 0, .load .d .r12 .r12 (arg j)]) (c' := .block [.addSp .r12 0, .load .d .r12 .r12 0])
      (by rfl) (by taint_decide))
  · exact two_taint [] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [])
      (c := .block [.addSp .r3 0, .load .d .r3 .r3 (arg j)]) (c' := .block [.addSp .r3 0, .load .d .r3 .r3 0])
      (by rfl) (by taint_decide))

/-- The load of the table's word, through its address in `d`. -/
theorem twB_taint {d : Reg} (o : Nat) (hd : d = .r9 ∨ d = .r12 ∨ d = .r3) (h : Pins Φ [d]) :
    RelCT isa (Two Φ) (.block [.load .d d d o]) fun _ _ => True := by
  rcases hd with rfl | rfl | rfl
  · exact two_taint [.r9] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r9])
      (c := .block [.load .d .r9 .r9 o]) (c' := .block [.load .d .r9 .r9 0]) (by rfl) (by taint_decide))
  · exact two_taint [.r12] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r12])
      (c := .block [.load .d .r12 .r12 o]) (c' := .block [.load .d .r12 .r12 0]) (by rfl) (by taint_decide))
  · exact two_taint [.r3] h (isSome_check_of_zImm (τ := VG.PPC64LE.Taint.ofRegs [.r3])
      (c := .block [.load .d .r3 .r3 o]) (c' := .block [.load .d .r3 .r3 0]) (by rfl) (by taint_decide))

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
