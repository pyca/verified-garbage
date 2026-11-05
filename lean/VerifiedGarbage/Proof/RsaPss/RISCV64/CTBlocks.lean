module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
public import VerifiedGarbage.Impl.RsaPss.RISCV64
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
meta import VerifiedGarbage.Impl.RsaPss.RISCV64

/-!
# RSASSA-PSS verification on RISC-V: the taint checks

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/CTBlocks.lean`): the code between the calls, checked
by the taint analysis from the stack pointer and the registers that hold
public values (`two_taint`); the blocks that use a hash function's lengths
on their copy for one hash function (`Hd`), with the same code without its
immediates (`zImm`). Every address and branch depends only on the pointers,
the lengths and the salt-length mode: `EM`, `DB`, `M'` and the digests are
only loaded, stored, masked and compared, the position of `DB`'s first
nonzero byte and the salt's length only masked.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64 VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Impl.RsaOaep.RISCV64 (save restore oSt oDig)
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.RsaOaep.RISCV64 (Hd zImm isSome_check_of_zImm)

section
variable {α : Type} {Φ : α → State → Prop} (H : Hash)

theorem entry_taint (h : Pins Φ [.a0]) : RelCT isa (Two Φ) (.block (save ++ prologue H)) fun _ _ => True :=
  two_taint [.a0] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.a0])
    (c := .block (save ++ prologue H)) (c' := .block (save ++ prologue Hd)) (by rfl) (by taint_decide))

theorem fail_taint (h : Pins Φ []) : RelCT isa (Two Φ) fail fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem chkEm_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (chkEm H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [])
    (c := .block (chkEm H)) (c' := .block (chkEm Hd)) (by rfl) (by taint_decide))

theorem expLen_taint (h : Pins Φ [.s7]) : RelCT isa (Two Φ) expLen fun _ _ => True :=
  two_taint [.s7] h (by taint_decide)

theorem chkSalt_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (chkSalt H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [])
    (c := .block (chkSalt H)) (c' := .block (chkSalt Hd)) (by rfl) (by taint_decide))

theorem pubArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem acc0_taint (h : Pins Φ [.s0, .s1, .s3]) : RelCT isa (Two Φ) (.block acc0) fun _ _ => True :=
  two_taint [.s0, .s1, .s3] h (by taint_decide)

theorem spill_taint (h : Pins Φ [.s0]) : RelCT isa (Two Φ) (.block spill) fun _ _ => True :=
  two_taint [.s0] h (by taint_decide)

theorem reload_taint (h : Pins Φ [.s0]) : RelCT isa (Two Φ) (.block reload) fun _ _ => True :=
  two_taint [.s0] h (by taint_decide)

theorem dbArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (dbArgs H)) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [])
    (c := .block (dbArgs H)) (c' := .block (dbArgs Hd)) (by rfl) (by taint_decide))

theorem clearTop_taint (h : Pins Φ [.s0, .s3]) : RelCT isa (Two Φ) (.block clearTop) fun _ _ => True :=
  two_taint [.s0, .s3] h (by taint_decide)

theorem scan_taint (h : Pins Φ [.s0, .s3, .s4]) : RelCT isa (Two Φ) scan fun _ _ => True :=
  two_taint [.s0, .s3, .s4] h (by taint_decide)

theorem posCheck_taint (h : Pins Φ [.s0, .s1]) : RelCT isa (Two Φ) (.block posCheck) fun _ _ => True :=
  two_taint [.s0, .s1] h (by taint_decide)

theorem lenCheck_taint (h : Pins Φ [.s7]) : RelCT isa (Two Φ) lenCheck fun _ _ => True :=
  two_taint [.s7] h (by taint_decide)

theorem mPrefix8_taint (h : Pins Φ [.s0, .s2]) : RelCT isa (Two Φ) (mPrefix H [.li .t5 8]) fun _ _ => True :=
  two_taint [.s0, .s2] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0, .s2])
    (c := mPrefix H [.li .t5 8]) (c' := mPrefix Hd [.li .t5 0]) (by rfl) (by taint_decide))

theorem mPrefix2048_taint (h : Pins Φ [.s0, .s2]) :
    RelCT isa (Two Φ) (mPrefix H [.li .t5 1024, .shift .sll .d .t5 .t5 1]) fun _ _ => True :=
  two_taint [.s0, .s2] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0, .s2])
    (c := mPrefix H [.li .t5 1024, .shift .sll .d .t5 .t5 1])
    (c' := mPrefix Hd [.li .t5 0, .shift .sll .d .t5 .t5 1]) (by rfl) (by taint_decide))

theorem copySalt_taint (h : Pins Φ [.s0, .s3, .s4, .s6]) : RelCT isa (Two Φ) (copySalt H) fun _ _ => True :=
  two_taint [.s0, .s3, .s4, .s6] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0, .s3, .s4, .s6])
    (c := copySalt H) (c' := copySalt Hd) (by rfl) (by taint_decide))

theorem cmpH_taint (o : Nat) (h : Pins Φ [.s0, .s3, .s4]) : RelCT isa (Two Φ) (cmpH H o) fun _ _ => True :=
  two_taint [.s0, .s3, .s4] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0, .s3, .s4])
    (c := cmpH H o) (c' := cmpH Hd 0) (by rfl) (by taint_decide))

theorem copyDb_taint (h : Pins Φ [.s0, .s3, .s4]) : RelCT isa (Two Φ) (copyDb H) fun _ _ => True :=
  two_taint [.s0, .s3, .s4] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0, .s3, .s4])
    (c := copyDb H) (c' := copyDb Hd) (by rfl) (by taint_decide))

theorem shift_taint (h : Pins Φ [.s0, .s4]) : RelCT isa (Two Φ) (shift H) fun _ _ => True :=
  two_taint [.s0, .s4] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0, .s4])
    (c := shift H) (c' := shift Hd) (by rfl) (by taint_decide))

theorem copyN_taint (a b n : Nat) (h : Pins Φ [.s0]) : RelCT isa (Two Φ) (copyN a b n) fun _ _ => True :=
  two_taint [.s0] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0])
    (c := copyN a b n) (c' := copyN 0 0 0) (by rfl) (by taint_decide))

theorem select_taint (h : Pins Φ [.s0]) : RelCT isa (Two Φ) (select H) fun _ _ => True :=
  two_taint [.s0] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0])
    (c := select H) (c' := select Hd) (by rfl) (by taint_decide))

theorem anyUpd_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block (([.li .a1 0] : List Instr) ++ yBase .a2 ++ ([.li .a3 (8 + H.D)] : List Instr))) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [])
    (c := .block ([.li .a1 0] ++ yBase .a2 ++ [.li .a3 (8 + H.D)]))
    (c' := .block ([.li .a1 0] ++ yBase .a2 ++ [.li .a3 0])) (by rfl) (by taint_decide))

theorem loopInit_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.li .s8 0, mov .s9 .s4]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem lr1_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block [.addi .a1 .s8 ((8 + H.D : Nat) : Int)]) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [])
    (c := .block [.addi .a1 .s8 ((8 + H.D : Nat) : Int)]) (c' := .block [.addi .a1 .s8 0]) (by rfl)
    (by taint_decide))

theorem lr2_taint (h : Pins Φ []) : RelCT isa (Two Φ)
    (.block (([.addi .a1 .s8 ((8 + H.D : Nat) : Int)] : List Instr) ++ yBase .a2 ++
      ([.addi .a2 .a2 ((8 + H.D : Nat) : Int), .add .a2 .a2 .s8, .li .a3 1] : List Instr))) fun _ _ => True :=
  two_taint [] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [])
    (c := .block ([.addi .a1 .s8 ((8 + H.D : Nat) : Int)] ++ yBase .a2 ++
      [.addi .a2 .a2 ((8 + H.D : Nat) : Int), .add .a2 .a2 .s8, .li .a3 1]))
    (c' := .block ([.addi .a1 .s8 0] ++ yBase .a2 ++ [.addi .a2 .a2 0, .add .a2 .a2 .s8, .li .a3 0])) (by rfl)
    (by taint_decide))

theorem lr3_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.addi .s8 .s8 1, .addi .s9 .s9 (-1)])
    fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem finRegs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.addi .a0 .s0 oSt, .addi .a2 .s0 oDig])
    fun _ _ => True :=
  two_taint [] h (by taint_decide)


theorem digArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block digArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

/-- The padding of `M'`, for the hash functions' block sizes (`2^6` and
`2^7`, the shift of its lengths). -/
theorem padAll_taint (hb : H.b = 6 ∨ H.b = 7) (be : Bool) (h : Pins Φ [.s0, .s6]) :
    RelCT isa (Two Φ) (padAll H be) fun _ _ => True := by
  obtain ⟨b, N, D, F, i₁, c₁, i₂, c₂, i₃, c₃⟩ := H
  simp only at hb
  rcases hb with rfl | rfl <;> cases be
  · exact two_taint [.s0, .s6] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0, .s6])
      (c' := padAll ⟨6, 0, 0, 0, "", .block [], "", .block [], "", .block []⟩ false) (by rfl) (by taint_decide))
  · exact two_taint [.s0, .s6] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0, .s6])
      (c' := padAll ⟨6, 0, 0, 0, "", .block [], "", .block [], "", .block []⟩ true) (by rfl) (by taint_decide))
  · exact two_taint [.s0, .s6] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0, .s6])
      (c' := padAll ⟨7, 0, 0, 0, "", .block [], "", .block [], "", .block []⟩ false) (by rfl) (by taint_decide))
  · exact two_taint [.s0, .s6] h (isSome_check_of_zImm (τ := VG.RISCV64.Taint.ofRegs [.s0, .s6])
      (c' := padAll ⟨7, 0, 0, 0, "", .block [], "", .block [], "", .block []⟩ true) (by rfl) (by taint_decide))

end

end VG.Proof.RsaPss.RISCV64
