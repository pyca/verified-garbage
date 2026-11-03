module

-- separate module: its taint checks evaluate the code, so it imports what it uses for `meta` too, which
-- the other proofs need not.
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Impl.RsaOaep.RISCV64
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Impl.RsaOaep.RISCV64

/-!
# RSAES-OAEP encryption on RISC-V: the taint checks

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/CTBlocks.lean`, `TaintImm.lean`): the code between
the calls, checked by the taint analysis from the stack pointer and the
registers that hold public values (`two_taint`). The blocks that use a hash
length are checked on their copy for one hash function (`Hd`), which has the
same code but for the immediates of `li` and `addi` (`zImm`), which the
analysis does not read (`check_zImm`), and the blocks that read MGF1's table
on their copy with the offsets of their `addSp` and loads zeroed. Every address and branch depends only
on the pointers and lengths; the seed, the message, the label and the
digests are only copied and XORed.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)

/-! ## Code without its immediates -/

/-- The instruction with the immediate of an `li` or `addi`, the offset of
an `addSp` or that of a load zeroed. -/
def Instr.zImm : Instr → Instr
  | .li d _ => .li d 0
  | .addi d n _ => .addi d n 0
  | .addSp d _ => .addSp d 0
  | .load wd t n _ => .load wd t n 0
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

theorem step_zImm (τ : VG.RISCV64.Taint.T) (i : Instr) :
    VG.RISCV64.Taint.step τ (Instr.zImm i) = VG.RISCV64.Taint.step τ i := by
  cases i <;> rfl

theorem checkBlock_zImm (τ : taint.T) (is : List isa.Instr) :
    taint.checkBlock τ (is.map Instr.zImm) = taint.checkBlock τ is := by
  induction is generalizing τ with
  | nil => rfl
  | cons i is ih =>
    show (VG.RISCV64.Taint.step τ (Instr.zImm i)).bind _ = (VG.RISCV64.Taint.step τ i).bind _
    exact congr (congrArg Option.bind (step_zImm τ i)) (funext ih)

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
  | block is => cases h <;> first | rfl | exact checkChunks_zImm τ is _
  | seq a b iha ihb => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, iha, ihb]
  | ite c t e iht ihe => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, iht, ihe]
  | loop b c ih => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, ih]
  | call n b ih => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, ih]
  | frame p b q ih => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, ih]
  | icall => cases h <;> rfl

/-- The analysis of `c` from that of `c'`, which has the same code without
those immediates. -/
theorem isSome_check_of_zImm {c c' : Prog isa} (he : zImm c = zImm c') {τ : taint.T}
    {hc : VG.Taint.Hint taint.T} (h : (taint.check τ c' hc).isSome = true) :
    (taint.check τ c hc).isSome = true := by
  rw [← check_zImm, he, check_zImm]; exact h

/-! ## The blocks -/

/-- A hash function whose code is checked in place of any other's. -/
def Hd : Hash := ⟨6, 32, 32, 144, "", .block [], "", .block [], "", .block []⟩

section
variable {α : Type} {Φ : α → State → Prop} (H G : Hash)

theorem entry_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (save ++ prologue)) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem chkK_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (chkK H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [])
    (c := .block (chkK H)) (c' := .block (chkK Hd)) (by rfl) (by taint_decide))

theorem chkMsg_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (chkMsg H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [])
    (c := .block (chkMsg H)) (c' := .block (chkMsg Hd)) (by rfl) (by taint_decide))

theorem fail_taint (h : Pins Φ [.s1, .s2]) : RelCT isa (Two Φ) encFail fun _ _ => True :=
  two_taint [.s1, .s2] h (by taint_decide)

theorem encEm_taint (h : Pins Φ [.t2, .t3, .t4, .s0, .s1]) : RelCT isa (Two Φ) (encEm H) fun _ _ => True :=
  two_taint [.t2, .t3, .t4, .s0, .s1] h (isSome_check_of_zImm
    (τ := VG.RISCV64.Taint.ofRegs [.t2, .t3, .t4, .s0, .s1]) (c := encEm H) (c' := encEm Hd) (by rfl)
    (by taint_decide))

theorem copyLh_taint (h : Pins Φ [.s0]) : RelCT isa (Two Φ) (copyLh H) fun _ _ => True :=
  two_taint [.s0] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0])
    (c := copyLh H) (c' := copyLh Hd) (by rfl) (by taint_decide))

theorem dbArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (dbArgs H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [])
    (c := .block (dbArgs H)) (c' := .block (dbArgs Hd)) (by rfl) (by taint_decide))

theorem seedArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (seedArgs H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [])
    (c := .block (seedArgs H)) (c' := .block (seedArgs Hd)) (by rfl) (by taint_decide))

theorem st_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.addi .a0 .s0 oSt]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

/-- `update`'s arguments for the label, and for MGF1's `src`. -/
theorem upd1_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.addi .a0 .s0 oSt, .li .a1 0, mov .a2 .s6, mov .a3 .s7]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem lab3_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.addi .a0 .s0 oSt, mov .a1 .s7, .addi .a2 .s0 oDig]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem mgfHead_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.li .s10 0, .li .s11 0]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem ctr_taint (h : Pins Φ [.s0]) : RelCT isa (Two Φ) (.block updCtrArgs) fun _ _ => True :=
  two_taint [.s0] h (by taint_decide)

theorem r4_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.addi .a0 .s0 oSt, .addi .a1 .s7 4, .addi .a2 .s0 oDig]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem xorOut_taint (h : Pins Φ [.s0, .s8, .s9, .s11]) : RelCT isa (Two Φ) (xorOut G) fun _ _ => True :=
  two_taint [.s0, .s8, .s9, .s11] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0, .s8, .s9, .s11])
    (c := xorOut G) (c' := xorOut Hd) (by rfl) (by taint_decide))

theorem nextCtr_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (nextCtr G)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [])
    (c := .block (nextCtr G)) (c' := .block (nextCtr Hd)) (by rfl) (by taint_decide))

/-- The first two loads of a table's word, through our stack argument `j`. -/
theorem twA_taint {d : Reg} (j : Nat) (hd : d = .a6 ∨ d = .t1) (h : Pins Φ []) :
    RelCT isa (Two Φ) (.block [.addSp d (frameBytes + 8 * j), .load .d d d 0]) fun _ _ => True := by
  rcases hd with rfl | rfl
  · exact two_taint [] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [])
      (c := .block [.addSp .a6 (frameBytes + 8 * j), .load .d .a6 .a6 0])
      (c' := .block [.addSp .a6 0, .load .d .a6 .a6 0]) (by rfl) (by taint_decide))
  · exact two_taint [] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [])
      (c := .block [.addSp .t1 (frameBytes + 8 * j), .load .d .t1 .t1 0])
      (c' := .block [.addSp .t1 0, .load .d .t1 .t1 0]) (by rfl) (by taint_decide))

/-- The load of the table's word, through its address in `d`. -/
theorem twB_taint {d : Reg} (o : Nat) (hd : d = .a6 ∨ d = .t1) (h : Pins Φ [d]) :
    RelCT isa (Two Φ) (.block [.load .d d d o]) fun _ _ => True := by
  rcases hd with rfl | rfl
  · exact two_taint [.a6] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.a6])
      (c := .block [.load .d .a6 .a6 o]) (c' := .block [.load .d .a6 .a6 0]) (by rfl) (by taint_decide))
  · exact two_taint [.t1] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.t1])
      (c := .block [.load .d .t1 .t1 o]) (c' := .block [.load .d .t1 .t1 0]) (by rfl) (by taint_decide))

/-- `xorOutT` after the load of `hLen` into `a6`. -/
abbrev xorRest : List Instr :=
  [.addi .a4 .s0 oDig, .add .a5 .s8 .s11, .sub .t1 .s9 .s11, .sub .t2 .t1 .a6,
    .shift .srl .d .t3 .t2 63, .li .t4 0, .sub .t3 .t4 .t3, .logic .and .t2 .t2 .t3, .add .a6 .a6 .t2]

theorem xorRest_taint (h : Pins Φ [.a6, .s0, .s8, .s9, .s11]) :
    RelCT isa (Two Φ) (.seq (.block xorRest) (Impl.Bignum.RISCV64.countLoop .a6 xorBody)) fun _ _ => True :=
  two_taint [.a6, .s0, .s8, .s9, .s11] h (by taint_decide)

/-- `nextCtrT` after the load of `hLen` into `t1`. -/
abbrev nextRest : List Instr := [.addi .s10 .s10 1, .add .s11 .s11 .t1, .sub .t1 .s11 .s9, .shift .srl .d .t1 .t1 63]

theorem nextRest_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block nextRest) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem pubArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem restore_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block restore) fun _ _ => True :=
  two_taint [] h (by taint_decide)

end

end VG.Proof.RsaOaep.RISCV64
