import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Impl.Poly1305.X86_64
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Poly1305.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Poly1305.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Setup`. -/
section

section

section

/-!
# Poly1305 on x86-64: the arithmetic of a block

The numbers the code computes while absorbing a block (see
`Impl/Poly1305/X86_64.lean`), as natural numbers: the accumulator `h = h0 +
2⁶⁴ h1 + 2¹²⁸ h2`, the clamped `r = r0 + 2⁶⁴ r1` with `r1 = 4 q`, and `s1 = 5
q`. The products are named (`h0 * r0`, …) so that `omega` treats them as
atoms.
-/

namespace VG.Proof.Poly1305.X86_64

open VG.Proof.Poly1305.Limbs64

open VG.Spec.Poly1305 (P)

open VG.Proof.Poly1305.Limbs64

end VG.Proof.Poly1305.X86_64

end

/-!
# Poly1305 on x86-64: the steps of a block

Each lemma runs a few instructions symbolically and states their effect on the
numbers in the registers.
-/

namespace VG.Proof.Poly1305.X86_64

open VG.Proof.Poly1305.Limbs64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64 VG.Proof.Poly1305.Limbs64

/-- Two states agree except on the registers `rs`, in memory and regions. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

set_option simprocs false in
theorem mulTo_ok {lo hi a b : Reg} (s : State) (hb : b ≠ .rax) (hlo : lo ≠ .rdx)
    (hlh : lo ≠ hi) :
    WP isa (.block (mulTo lo hi a b)) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat = (s.gpr a).toNat * (s.gpr b).toNat ∧
      VG.Proof.Poly1305.X86_64.Keeps [lo, hi, .rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [mulTo, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul, State.setReg,
    State.setFlags, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [ite_true, hlh, hlo.symm, ite_false, hb]
    exact toNat_mul_lo _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.1, ite_true, hr.1, hr.2.2.2, hr.2.2.1, ite_false]

set_option simprocs false in
theorem mulAdd_ok {lo hi a b : Reg} (s : State) (hb : b ≠ .rax) (hlo : lo ≠ .rdx) (hlo' : lo ≠ .rax)
    (hhi : hi ≠ .rdx) (hhi' : hi ≠ .rax) (hlh : lo ≠ hi) :
    WP isa (.block (mulAdd lo hi a b)) s fun s' =>
      ((s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat + (s.gpr a).toNat * (s.gpr b).toNat < 2 ^ 128 →
        (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat =
          (s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat + (s.gpr a).toNat * (s.gpr b).toNat) ∧
      VG.Proof.Poly1305.X86_64.Keeps [lo, hi, .rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mulAdd, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execMul, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false, hb, hlo, hlo', hhi,
    hhi', hlh, hlo.symm, hlh.symm]
  refine ⟨fun hlt => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := toNat_mul_lo (s.gpr a) (s.gpr b)
    rw [add_adc_toNat _ _ _ _ (by have := (s.gpr hi).isLt; omega_using [hlt, e])]
    omega_using [e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.1, BitVec.toNat_ofNat, hr.1, hr.2.2.2, hr.2.2.1, ite_false]

set_option simprocs false in
/-- `h2 * r0`, which fits one word. -/
theorem mulSmall_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .rbp), .mul .r8]) s fun s' =>
      ((s.gpr .rbp).toNat * (s.gpr .r8).toNat < 2 ^ 64 →
        (s'.gpr .rax).toNat = (s.gpr .rbp).toNat * (s.gpr .r8).toNat) ∧ VG.Proof.Poly1305.X86_64.Keeps [.rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execMul, State.setReg, State.setFlags, Option.map_some, Option.some.injEq,
    exists_eq_left', ite_true, ite_false]
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2, hr.1, ite_false]

set_option simprocs false in
theorem addPair_ok (s : State) :
    WP isa (.block [.alu .add .r14 (.reg .r13), .alu .adc .r15 (.reg .rax)]) s fun s' =>
      ((s.gpr .r14).toNat + (s.gpr .r13).toNat + 2 ^ 64 * ((s.gpr .r15).toNat + (s.gpr .rax).toNat) <
          2 ^ 128 →
        (s'.gpr .r14).toNat + 2 ^ 64 * (s'.gpr .r15).toNat =
          (s.gpr .r14).toNat + (s.gpr .r13).toNat + 2 ^ 64 * ((s.gpr .r15).toNat + (s.gpr .rax).toNat)) ∧
      VG.Proof.Poly1305.X86_64.Keeps [.r14, .r15] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, ite_false]
  refine ⟨add_adc_toNat _ _ _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.2, hr.1, ite_false]

theorem se3 : BitVec.signExtend 64 (3 : BitVec 32) = 3 := by decide
theorem se0 : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide
theorem se1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

set_option simprocs false in
/-- Splitting the top word `t` (in `r15`) into `t mod 4` (in `rbp`) and `5 ⌊t / 4⌋`
(in `rax`), and moving the low words into `r11, rbx`. -/
theorem split_ok (s : State) :
    WP isa (.block [.mov .r11 (.reg .r12), .mov .rbx (.reg .r14), .mov .rbp (.reg .r15),
      .alu .and .rbp (.imm 3), .mov .rax (.reg .r15), .alu .sub .rax (.reg .rbp),
      .shift .shr .r15 2, .alu .add .rax (.reg .r15)]) s fun s' =>
      s'.gpr .r11 = s.gpr .r12 ∧ s'.gpr .rbx = s.gpr .r14 ∧
      (s'.gpr .rbp).toNat = (s.gpr .r15).toNat % 4 ∧
      ((s.gpr .r15).toNat < 2 ^ 63 → (s'.gpr .rax).toNat = 5 * ((s.gpr .r15).toNat / 4)) ∧
      VG.Proof.Poly1305.X86_64.Keeps [.r11, .rbx, .rbp, .rax, .r15] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, execShift, arithFlags, State.setReg, State.setFlags, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false, VG.Proof.Poly1305.X86_64.se3]
  refine ⟨trivial, trivial, and3_toNat _, fun ht => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h3 := and3_toNat (s.gpr .r15)
    have hle : s.gpr .r15 &&& 3 ≤ s.gpr .r15 := by
      rw [BitVec.le_def, h3]; exact Nat.mod_le _ _
    rw [BitVec.toNat_add, BitVec.toNat_sub_of_le hle, h3, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    omega_using [ht, h3]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.2.2.1, BitVec.ofNat_eq_ofNat, hr.2.2.2.2, hr.2.2.1, hr.2.1, hr.1, ite_false]

set_option simprocs false in
/-- Adding `rax` into `r11, rbx, rbp`, with carries. -/
theorem addLow_ok (s : State) :
    WP isa (.block [.alu .add .r11 (.reg .rax), .alu .adc .rbx (.imm 0), .alu .adc .rbp (.imm 0)]) s
      fun s' =>
      ((s.gpr .r11).toNat + (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rbx).toNat +
          2 ^ 128 * (s.gpr .rbp).toNat < 2 ^ 192 →
        (s'.gpr .r11).toNat + 2 ^ 64 * (s'.gpr .rbx).toNat + 2 ^ 128 * (s'.gpr .rbp).toNat =
          (s.gpr .r11).toNat + (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rbx).toNat +
            2 ^ 128 * (s.gpr .rbp).toNat) ∧
      VG.Proof.Poly1305.X86_64.Keeps [.r11, .rbx, .rbp] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false, VG.Proof.Poly1305.X86_64.se0]
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have hz : (0 : BitVec 64).toNat = 0 := rfl
    rw [add3_toNat _ _ _ _ _ _ (by rw [hz]; omega_using [h]), hz]
    omega_using []
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.2, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero, hr.2.1, hr.1, ite_false]

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

/-- The two words of the block at `p`. -/
abbrev word (m : Mem) (p : Addr) (d : Nat) : Nat := (m.readW (p + BitVec.ofInt 64 (d : Int)) 64).toNat

set_option simprocs false in
/-- `h += m + pad · 2¹²⁸` for the block `m` at `b + d`. -/
theorem addBlockAt_ok (s : State) {b : Reg} (hb : b ≠ .r11) {d : Nat} {pad : BitVec 32}
    (hpad : pad = 0 ∨ pad = 1)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofInt 64 (d : Int)) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofInt 64 ((d + 8 : Nat) : Int)) 8) :
    WP isa (.block (addBlockAt b d pad)) s fun s' =>
      ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .rbx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat +
          (VG.Proof.Poly1305.X86_64.word s.mem (s.gpr b) d + 2 ^ 64 * VG.Proof.Poly1305.X86_64.word s.mem (s.gpr b) (d + 8) + 2 ^ 128 * pad.toNat) <
          2 ^ 192 →
        (s'.gpr .r11).toNat + 2 ^ 64 * (s'.gpr .rbx).toNat + 2 ^ 128 * (s'.gpr .rbp).toNat =
          (s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .rbx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat +
            (VG.Proof.Poly1305.X86_64.word s.mem (s.gpr b) d + 2 ^ 64 * VG.Proof.Poly1305.X86_64.word s.mem (s.gpr b) (d + 8) + 2 ^ 128 * pad.toNat)) ∧
      VG.Proof.Poly1305.X86_64.Keeps [.r11, .rbx, .rbp] s s' := by
  have hp : (pad.signExtend 64).toNat = pad.toNat := by rcases hpad with rfl | rfl <;> rfl
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addBlockAt, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, State.load64, VG.Proof.Poly1305.X86_64.ea_at, hb, h0, h8,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false]
  refine ⟨fun hlt => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [VG.Proof.Poly1305.X86_64.word] at hlt ⊢
    rw [add3_toNat _ _ _ _ _ _ (by rw [hp]; omega_using [hlt]), hp]
    omega_using []
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.2, Int.natCast_add, Int.cast_ofNat_Int, BitVec.ofInt_natCast, hr.2.1, hr.1, ite_false]

end VG.Proof.Poly1305.X86_64

end

section

/-!
# Poly1305 on x86-64: absorbing a block
-/

namespace VG.Proof.Poly1305.X86_64

open VG.Proof.Poly1305.Limbs64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P)

theorem Keeps.gpr' {rs : List Reg} {s s' : State} (h : VG.Proof.Poly1305.X86_64.Keeps rs s s') {r : Reg}
    (hr : r ∉ rs := by decide) : s'.gpr r = s.gpr r := h.1 r hr

theorem Keeps.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Poly1305.X86_64.Keeps rs s₁ s₂)
    (h₂ : VG.Proof.Poly1305.X86_64.Keeps rs' s₂ s₃) : VG.Proof.Poly1305.X86_64.Keeps (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1],
   h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.Poly1305.X86_64.Keeps rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : VG.Proof.Poly1305.X86_64.Keeps rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

/-- The registers `absorb` writes. -/
abbrev absorbRegs : List Reg := [.r11, .rbx, .rbp, .rax, .rdx, .r12, .r13, .r14, .r15]

theorem carry_eq : VG.Impl.Poly1305.X86_64.carry =
    ([.alu .add .r14 (.reg .r13), .alu .adc .r15 (.reg .rax)] : List Instr) ++
    (([.mov .r11 (.reg .r12), .mov .rbx (.reg .r14), .mov .rbp (.reg .r15),
      .alu .and .rbp (.imm 3), .mov .rax (.reg .r15), .alu .sub .rax (.reg .rbp),
      .shift .shr .r15 2, .alu .add .rax (.reg .r15)] : List Instr) ++
    ([.alu .add .r11 (.reg .rax), .alu .adc .rbx (.imm 0), .alu .adc .rbp (.imm 0)] : List Instr)) := rfl

theorem absorbAt_eq (b : Reg) (d : Nat) (pad : BitVec 32) : absorbAt b d pad =
    addBlockAt b d pad ++ (mulTo .r12 .r13 .r11 .r8 ++ (mulAdd .r12 .r13 .rbx .r10 ++
    (mulTo .r14 .r15 .r11 .r9 ++ (mulAdd .r14 .r15 .rbx .r8 ++ (mulAdd .r14 .r15 .rbp .r10 ++
    (([.mov .rax (.reg .rbp), .mul .r8] : List Instr) ++ VG.Impl.Poly1305.X86_64.carry)))))) := by
  simp only [absorbAt, products, List.append_assoc]

/-- The accumulator in `r11, rbx, rbp`. -/
abbrev hval (s : State) : Nat :=
  (s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .rbx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat

/-- Absorbing the block at `b + d`: from `h` with `h2 ≤ 4`, the clamped `r0, r1 = 4 q`
in `r8, r9` and `s1 = 5 q` in `r10`, the new `h` is congruent to
`(h + m + pad · 2¹²⁸) r` modulo `p`, and its `h2` is at most 4. -/
theorem absorbAt_ok (s : State) {b : Reg} (hb : b ≠ .r11) {d : Nat} {pad : BitVec 32}
    (hpad : pad = 0 ∨ pad = 1) {q : Nat}
    (hr0 : (s.gpr .r8).toNat < 2 ^ 60) (hr1 : (s.gpr .r9).toNat = 4 * q) (hq : q < 2 ^ 58)
    (hs1 : (s.gpr .r10).toNat = 5 * q)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofInt 64 (d : Int)) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofInt 64 ((d + 8 : Nat) : Int)) 8) :
    WP isa (.block (absorbAt b d pad)) s fun s' =>
      ((s.gpr .rbp).toNat ≤ 4 →
        VG.Proof.Poly1305.X86_64.hval s' % P = ((VG.Proof.Poly1305.X86_64.hval s + (VG.Proof.Poly1305.X86_64.word s.mem (s.gpr b) d + 2 ^ 64 * VG.Proof.Poly1305.X86_64.word s.mem (s.gpr b) (d + 8) +
          2 ^ 128 * pad.toNat)) * ((s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r9).toNat)) % P ∧
        (s'.gpr .rbp).toNat ≤ 4) ∧ VG.Proof.Poly1305.X86_64.Keeps VG.Proof.Poly1305.X86_64.absorbRegs s s' := by
  rw [VG.Proof.Poly1305.X86_64.absorbAt_eq, VG.Proof.Poly1305.X86_64.carry_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.addBlockAt_ok s hb hpad h0 h8) fun s₁ ⟨e₁, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.mulTo_ok s₁ (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.mulAdd_ok s₂ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₃ ⟨e₃, k₃⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.mulTo_ok s₃ (by decide) (by decide) (by decide))
    fun s₄ ⟨e₄, k₄⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.mulAdd_ok s₄ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₅ ⟨e₅, k₅⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.mulAdd_ok s₅ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₆ ⟨e₆, k₆⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.mulSmall_ok s₆) fun s₇ ⟨e₇, k₇⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.addPair_ok s₇) fun s₈ ⟨e₈, k₈⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.split_ok s₈) fun s₉ ⟨f₁, f₂, f₃, f₄, k₉⟩ => ?_)
  refine WP.mono (VG.Proof.Poly1305.X86_64.addLow_ok s₉) fun s₁₀ ⟨e₁₀, k₁₀⟩ => ?_
  refine ⟨fun hh2 => ?_, (k₁.trans ((((((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans
    k₈).trans k₉).trans k₁₀)).mono (by decide)⟩
  have hp1 : pad.toNat ≤ 1 := by rcases hpad with rfl | rfl <;> decide
  have hw0 := (s.mem.readW (s.gpr b + BitVec.ofInt 64 (d : Int)) 64).isLt
  have hw8 := (s.mem.readW (s.gpr b + BitVec.ofInt 64 ((d + 8 : Nat) : Int)) 64).isLt
  have g0 := (s.gpr .r11).isLt; have g1 := (s.gpr .rbx).isLt
  -- h += m
  have e₁ := e₁ (by simp only [VG.Proof.Poly1305.X86_64.word]; omega_using [hh2, hp1, hw0, hw8, g0, g1])
  have a0 := (s₁.gpr .r11).isLt; have a1 := (s₁.gpr .rbx).isLt
  have a2 : (s₁.gpr .rbp).toNat ≤ 6 := add_arith g0 g1 hh2 hw0 hw8 hp1 e₁ a0 a1
  have r8₁ : s₁.gpr .r8 = s.gpr .r8 := k₁.gpr'
  have r9₁ : s₁.gpr .r9 = s.gpr .r9 := k₁.gpr'
  have r10₁ : s₁.gpr .r10 = s.gpr .r10 := k₁.gpr'
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := absorb_bounds a0 a1 a2 hr0 hq
  -- x = h0 r0
  rw [r8₁] at e₂
  have rbx₂ : s₂.gpr .rbx = s₁.gpr .rbx := k₂.gpr'
  have r10₂ : s₂.gpr .r10 = s.gpr .r10 := k₂.gpr'.trans r10₁
  -- x += h1 s1
  rw [rbx₂, r10₂, hs1] at e₃
  have e₃ := e₃ (by omega_using [e₂, b1, b2])
  rw [e₂] at e₃
  have k₃' := k₂.trans k₃
  have r11₃ : s₃.gpr .r11 = s₁.gpr .r11 := k₃'.gpr'
  have r9₃ : s₃.gpr .r9 = s.gpr .r9 := k₃'.gpr'.trans r9₁
  -- y = h0 r1
  rw [r11₃, r9₃, hr1] at e₄
  have k₄' := k₃'.trans k₄
  have rbx₄ : s₄.gpr .rbx = s₁.gpr .rbx := k₄'.gpr'
  have r8₄ : s₄.gpr .r8 = s.gpr .r8 := k₄'.gpr'.trans r8₁
  -- y += h1 r0
  rw [rbx₄, r8₄] at e₅
  have e₅ := e₅ (by omega_using [e₄, b3, b4])
  rw [e₄] at e₅
  have k₅' := k₄'.trans k₅
  have rbp₅ : s₅.gpr .rbp = s₁.gpr .rbp := k₅'.gpr'
  have r10₅ : s₅.gpr .r10 = s.gpr .r10 := k₅'.gpr'.trans r10₁
  -- y += h2 s1
  rw [rbp₅, r10₅, hs1] at e₆
  have e₆ := e₆ (by omega_using [e₄, b3, b4, b5, e₅])
  rw [e₅] at e₆
  have k₆' := k₅'.trans k₆
  have rbp₆ : s₆.gpr .rbp = s₁.gpr .rbp := k₆'.gpr'
  have r8₆ : s₆.gpr .r8 = s.gpr .r8 := k₆'.gpr'.trans r8₁
  -- h2 r0
  rw [rbp₆, r8₆] at e₇
  have e₇ := e₇ (by omega_using [hr0, b6])
  have r14₇ : s₇.gpr .r14 = s₆.gpr .r14 := k₇.gpr'
  have r15₇ : s₇.gpr .r15 = s₆.gpr .r15 := k₇.gpr'
  have r13₇ : s₇.gpr .r13 = s₃.gpr .r13 := ((k₄.trans k₅).trans (k₆.trans k₇)).gpr'
  have r12₇ : s₇.gpr .r12 = s₃.gpr .r12 := ((k₄.trans k₅).trans (k₆.trans k₇)).gpr'
  have x0 := (s₃.gpr .r12).isLt; have x1 := (s₃.gpr .r13).isLt
  have y0 := (s₆.gpr .r14).isLt; have y1 := (s₆.gpr .r15).isLt
  -- the top word
  rw [r14₇, r13₇, r15₇, e₇] at e₈
  have e₈ := e₈ (by omega_using [hr0, e₂, e₄, b1, b2, b3, b4, b5, b6, e₃, e₅, e₆, e₇])
  have u0 := (s₈.gpr .r14).isLt
  have ht : (s₈.gpr .r15).toNat < 2 ^ 63 := by omega_using [hr0, e₂, e₄, b1, b2, b3, b4, b5, b6, e₃, e₅, e₆, e₇, e₈]
  have f₄ := f₄ ht
  have r12₈ : s₈.gpr .r12 = s₃.gpr .r12 := k₈.gpr'.trans r12₇
  rw [r12₈] at f₁
  rw [f₁, f₂, f₃, f₄] at e₁₀
  have e₁₀ := e₁₀ (by omega_using [hr0, e₂, e₄, b1, b2, b3, b4, b5, b6, e₃, e₅, e₆, e₇, e₈])
  have w0 := (s₁₀.gpr .r11).isLt; have w1 := (s₁₀.gpr .rbx).isLt
  have hu : (s₈.gpr .r14).toNat + 2 ^ 64 * (((s₆.gpr .r14).toNat + (s₃.gpr .r13).toNat) / 2 ^ 64) =
      (s₆.gpr .r14).toNat + (s₃.gpr .r13).toNat := by
    clear e₁₀ f₁ f₂ f₃ f₄ e₁ e₃ e₆ e₇
    omega_using [e₈]
  have ht' : (s₈.gpr .r15).toNat = (s₆.gpr .r15).toNat + (s₁.gpr .rbp).toNat * (s.gpr .r8).toNat +
      ((s₆.gpr .r14).toNat + (s₃.gpr .r13).toNat) / 2 ^ 64 := by
    clear e₁₀ f₁ f₂ f₃ f₄ e₁ e₃ e₆ e₇
    omega_using [e₈, hu]
  rw [ht'] at e₁₀
  obtain ⟨m, hb⟩ := absorb_arith (q := q) (x0 := (s₃.gpr .r12).toNat) (x1 := (s₃.gpr .r13).toNat)
    (y0 := (s₆.gpr .r14).toNat) (y1 := (s₆.gpr .r15).toNat) (u0 := (s₈.gpr .r14).toNat)
    (c1 := ((s₆.gpr .r14).toNat + (s₃.gpr .r13).toNat) / 2 ^ 64)
    a0 a1 a2 hr0 hq e₃ x0 e₆ hu u0 e₁₀ w0 w1
  refine ⟨?_, hb⟩
  rw [VG.Proof.Poly1305.X86_64.hval, m, e₁, hr1]

/-- Absorbing the block at `rsi`. -/
theorem absorb_ok (s : State) {pad : BitVec 32} (hpad : pad = 0 ∨ pad = 1) {q : Nat}
    (hr0 : (s.gpr .r8).toNat < 2 ^ 60) (hr1 : (s.gpr .r9).toNat = 4 * q) (hq : q < 2 ^ 58)
    (hs1 : (s.gpr .r10).toNat = 5 * q)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8) :
    WP isa (.block (absorb pad)) s fun s' =>
      ((s.gpr .rbp).toNat ≤ 4 →
        VG.Proof.Poly1305.X86_64.hval s' % P = ((VG.Proof.Poly1305.X86_64.hval s + (VG.Proof.Poly1305.X86_64.word s.mem (s.gpr .rsi) 0 + 2 ^ 64 * VG.Proof.Poly1305.X86_64.word s.mem (s.gpr .rsi) 8 +
          2 ^ 128 * pad.toNat)) * ((s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r9).toNat)) % P ∧
        (s'.gpr .rbp).toNat ≤ 4) ∧ VG.Proof.Poly1305.X86_64.Keeps VG.Proof.Poly1305.X86_64.absorbRegs s s' :=
  VG.Proof.Poly1305.X86_64.absorbAt_ok s (b := .rsi) (d := 0) (by decide) hpad hr0 hr1 hq hs1 h0 h8

end VG.Proof.Poly1305.X86_64

end

section

/-!
# Poly1305 on x86-64: the final reduction
-/

namespace VG.Proof.Poly1305.X86_64

open VG.Proof.Poly1305.Limbs64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P)

theorem se5 : BitVec.signExtend 64 (5 : BitVec 32) = 5 := by decide

theorem select_zero (x y : BitVec 64) : x ^^^ ((y ^^^ x) &&& ((0 : BitVec 64) - 0)) = x := by simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_self, BitVec.and_zero, BitVec.xor_zero]
theorem select_one (x y : BitVec 64) : x ^^^ ((y ^^^ x) &&& ((0 : BitVec 64) - 1)) = y := by
  rw [show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes, BitVec.xor_comm y,
    ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem reduce_eq : reduce =
    ([.mov .rax (.reg .r11), .alu .add .rax (.imm 5), .mov .rdx (.reg .rbx), .alu .adc .rdx (.imm 0),
      .mov .r12 (.reg .rbp), .alu .adc .r12 (.imm 0)] : List Instr) ++
    (([.mov .r13 (.reg .r12), .shift .shr .r13 2, .mov32 .r14 (.imm 0), .alu .sub .r14 (.reg .r13),
      .alu .and .r12 (.imm 3)] : List Instr) ++
    ([.alu .xor .rax (.reg .r11), .alu .and .rax (.reg .r14), .alu .xor .r11 (.reg .rax),
      .alu .xor .rdx (.reg .rbx), .alu .and .rdx (.reg .r14), .alu .xor .rbx (.reg .rdx),
      .alu .xor .r12 (.reg .rbp), .alu .and .r12 (.reg .r14), .alu .xor .rbp (.reg .r12)] : List Instr)) := rfl

set_option simprocs false in
/-- `g = h + 5` into `rax, rdx, r12`. -/
theorem plus5_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .r11), .alu .add .rax (.imm 5), .mov .rdx (.reg .rbx),
      .alu .adc .rdx (.imm 0), .mov .r12 (.reg .rbp), .alu .adc .r12 (.imm 0)]) s fun s' =>
      (VG.Proof.Poly1305.X86_64.hval s + 5 < 2 ^ 192 →
        (s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rdx).toNat + 2 ^ 128 * (s'.gpr .r12).toNat =
          VG.Proof.Poly1305.X86_64.hval s + 5) ∧ VG.Proof.Poly1305.X86_64.Keeps [.rax, .rdx, .r12] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false, VG.Proof.Poly1305.X86_64.se0, VG.Proof.Poly1305.X86_64.se5]
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have hz : (0 : BitVec 64).toNat = 0 := rfl
    have h5 : (5 : BitVec 64).toNat = 5 := rfl
    rw [add3_toNat _ _ _ _ _ _ (by rw [hz, h5]; simp only [VG.Proof.Poly1305.X86_64.hval] at h; omega_using [h]), hz, h5]
    simp only [VG.Proof.Poly1305.X86_64.hval]; omega_using []
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.2, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero, hr.2.1, hr.1, ite_false]

set_option simprocs false in
/-- The mask `-(g2 / 4)` into `r14`, and `g2 mod 4` into `r12`. -/
theorem mask_ok (s : State) :
    WP isa (.block [.mov .r13 (.reg .r12), .shift .shr .r13 2, .mov32 .r14 (.imm 0),
      .alu .sub .r14 (.reg .r13), .alu .and .r12 (.imm 3)]) s fun s' =>
      s'.gpr .r14 = (0 : BitVec 64) - (s.gpr .r12 >>> 2) ∧ s'.gpr .r12 = s.gpr .r12 &&& 3 ∧
      VG.Proof.Poly1305.X86_64.Keeps [.r12, .r13, .r14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, readSrc32, execAlu, execShift, arithFlags, State.setReg, State.setReg32, State.setFlags,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false, VG.Proof.Poly1305.X86_64.se3]
  refine ⟨by simp only [BitVec.ofNat_eq_ofNat, BitVec.setWidth_zero, BitVec.zero_sub], trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, BitVec.ofNat_eq_ofNat, hr.2.2, BitVec.setWidth_zero, BitVec.zero_sub, hr.2.1, ite_false]

set_option simprocs false in
/-- Selecting `rax, rdx, r12` over `r11, rbx, rbp` where the mask `r14` is set. -/
theorem select_ok (s : State) :
    WP isa (.block [.alu .xor .rax (.reg .r11), .alu .and .rax (.reg .r14), .alu .xor .r11 (.reg .rax),
      .alu .xor .rdx (.reg .rbx), .alu .and .rdx (.reg .r14), .alu .xor .rbx (.reg .rdx),
      .alu .xor .r12 (.reg .rbp), .alu .and .r12 (.reg .r14), .alu .xor .rbp (.reg .r12)]) s fun s' =>
      s'.gpr .r11 = s.gpr .r11 ^^^ ((s.gpr .rax ^^^ s.gpr .r11) &&& s.gpr .r14) ∧
      s'.gpr .rbx = s.gpr .rbx ^^^ ((s.gpr .rdx ^^^ s.gpr .rbx) &&& s.gpr .r14) ∧
      s'.gpr .rbp = s.gpr .rbp ^^^ ((s.gpr .r12 ^^^ s.gpr .rbp) &&& s.gpr .r14) ∧
      VG.Proof.Poly1305.X86_64.Keeps [.rax, .rdx, .r12, .r11, .rbx, .rbp] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false]
  refine ⟨trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.2.2.2.2.2, hr.2.2.1, hr.2.2.2.2.1, hr.2.1, hr.2.2.2.1, hr.1, ite_false]

theorem reduce_ok (s : State) :
    WP isa (.block reduce) s fun s' =>
      ((s.gpr .rbp).toNat ≤ 4 → VG.Proof.Poly1305.X86_64.hval s' = VG.Proof.Poly1305.X86_64.hval s % P) ∧
      VG.Proof.Poly1305.X86_64.Keeps [.rax, .rdx, .r11, .rbx, .rbp, .r12, .r13, .r14] s s' := by
  have g0 := (s.gpr .r11).isLt; have g1 := (s.gpr .rbx).isLt
  rw [VG.Proof.Poly1305.X86_64.reduce_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.plus5_ok s) fun s₁ ⟨e₁, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.mask_ok s₁) fun s₂ ⟨m₁, m₂, k₂⟩ => ?_)
  refine WP.mono (VG.Proof.Poly1305.X86_64.select_ok s₂) fun s₃ ⟨c₁, c₂, c₃, k₃⟩ => ?_
  refine ⟨fun hh2 => ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  have e₁ := e₁ (by simp only [VG.Proof.Poly1305.X86_64.hval]; omega_using [g0, g1, hh2])
  have ga := (s₁.gpr .rax).isLt; have gd := (s₁.gpr .rdx).isLt
  have hg2 : (s₁.gpr .r12).toNat ≤ 5 := by simp only [VG.Proof.Poly1305.X86_64.hval] at e₁; omega_using [g0, g1, hh2, e₁]
  have r11₂ : s₂.gpr .r11 = s.gpr .r11 := (k₁.trans k₂).gpr'
  have rbx₂ : s₂.gpr .rbx = s.gpr .rbx := (k₁.trans k₂).gpr'
  have rbp₂ : s₂.gpr .rbp = s.gpr .rbp := (k₁.trans k₂).gpr'
  have rax₂ : s₂.gpr .rax = s₁.gpr .rax := k₂.gpr'
  have rdx₂ : s₂.gpr .rdx = s₁.gpr .rdx := k₂.gpr'
  rw [r11₂, rax₂, m₁] at c₁; rw [rbx₂, rdx₂, m₁] at c₂; rw [rbp₂, m₂, m₁] at c₃
  have ht : (s₁.gpr .r12 >>> 2).toNat = (s₁.gpr .r12).toNat / 4 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [VG.Proof.Poly1305.X86_64.hval, c₁, c₂, c₃]
  unfold VG.Proof.Poly1305.X86_64.hval at e₁
  have hP : P = 2 ^ 130 - 5 := rfl
  by_cases hge : 4 ≤ (s₁.gpr .r12).toNat
  · have h1 : s₁.gpr .r12 >>> 2 = 1 := BitVec.eq_of_toNat_eq (by rw [ht]; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.one_mod]; omega_using [hg2, ht, hge])
    rw [h1, VG.Proof.Poly1305.X86_64.select_one, VG.Proof.Poly1305.X86_64.select_one, VG.Proof.Poly1305.X86_64.select_one, and3_toNat]
    have ge : P ≤ (s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .rbx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat := by
      omega_using [e₁, hg2, hP, hge]
    have lt : (s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .rbx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat - P <
        P := by omega_using [g0, g1, hh2, e₁, hP, ge]
    rw [Nat.mod_eq_sub_mod ge, Nat.mod_eq_of_lt lt]
    omega_using [g0, g1, hh2, e₁, hP, ge, lt]
  · have h0 : s₁.gpr .r12 >>> 2 = 0 := BitVec.eq_of_toNat_eq (by rw [ht]; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.div_eq_zero_iff, reduceCtorEq, false_or]; omega_using [hg2, hge])
    have lt : (s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .rbx).toNat + 2 ^ 128 * (s.gpr .rbp).toNat <
        P := by omega_using [e₁, hg2, hP, hge]
    rw [h0, VG.Proof.Poly1305.X86_64.select_zero, VG.Proof.Poly1305.X86_64.select_zero, VG.Proof.Poly1305.X86_64.select_zero, Nat.mod_eq_of_lt lt]

end VG.Proof.Poly1305.X86_64

end

section

/-!
# Poly1305 on x86-64: the state in memory, and loading the key
-/

namespace VG.Proof.Poly1305.X86_64

open VG.Proof.Poly1305.Limbs64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp only [BitVec.ofInt_natCast]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The address `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofInt 64 (d : Int)

theorem contains_off {base : Addr} {len d n : Nat} (h : d + n ≤ len) (hd : d < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (VG.Proof.Poly1305.X86_64.off base d) n := by
  simp only [VG.Proof.Poly1305.X86_64.off, VG.Proof.Poly1305.X86_64.ofInt_natCast]; exact Offset.contains_base base h hd

theorem sep_off (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 16)
    (hk : k ≤ 16) (h : d + n ≤ e ∨ e + k ≤ d) : Mem.Sep (VG.Proof.Poly1305.X86_64.off p d) n (VG.Proof.Poly1305.X86_64.off p e) k := by
  simp only [VG.Proof.Poly1305.X86_64.off, VG.Proof.Poly1305.X86_64.ofInt_natCast]; exact Offset.sep p h (by omega_using [hd, hn]) (by omega_using [he, hk])

theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (VG.Proof.Poly1305.X86_64.off p e) v).readW (VG.Proof.Poly1305.X86_64.off p d) 64 = m.readW (VG.Proof.Poly1305.X86_64.off p d) 64 :=
  Mem.readW_writeW_sep (VG.Proof.Poly1305.X86_64.sep_off p hd he (by decide) (by decide) h) (by decide)

/-! ## The regions of the state -/

section
variable (st : Addr)
/-- The accumulator. -/
abbrev hR : Region := ⟨st, 24⟩
/-- The key. -/
abbrev kR : Region := ⟨VG.Proof.Poly1305.X86_64.off st 24, 32⟩
/-- The working space: the buffer and the saved registers. -/
abbrev wR : Region := ⟨VG.Proof.Poly1305.X86_64.off st 56, 72⟩
/-- The buffer. -/
abbrev bfR : Region := ⟨VG.Proof.Poly1305.X86_64.off st 56, 16⟩
/-- Where the callee-saved registers are saved. -/
abbrev svR : Region := ⟨VG.Proof.Poly1305.X86_64.off st 72, 48⟩
/-- The whole state. -/
abbrev sR : Region := ⟨st, 128⟩
end

theorem sub_sR (st : Addr) {d n : Nat} (h : d + n ≤ 128) : Region.Sub ⟨VG.Proof.Poly1305.X86_64.off st d, n⟩ (VG.Proof.Poly1305.X86_64.sR st) := by
  simp only [VG.Proof.Poly1305.X86_64.off, VG.Proof.Poly1305.X86_64.ofInt_natCast]; exact Offset.sub_base st h

theorem kR_disjoint (st : Addr) : ∀ r ∈ [VG.Proof.Poly1305.X86_64.hR st, VG.Proof.Poly1305.X86_64.wR st], (VG.Proof.Poly1305.X86_64.kR st).Disjoint r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl) <;> simp only [VG.Proof.Poly1305.X86_64.kR, VG.Proof.Poly1305.X86_64.hR, VG.Proof.Poly1305.X86_64.wR, VG.Proof.Poly1305.X86_64.off, VG.Proof.Poly1305.X86_64.ofInt_natCast]
  · exact Offset.disjoint_base st (by decide) (by decide)
  · exact Offset.disjoint st (by decide) (by decide) (by decide)

/-- The key is unchanged by writes to the accumulator and the working space. -/
theorem key_frame {st : Addr} {m m' : Mem} (hf : Frame [VG.Proof.Poly1305.X86_64.hR st, VG.Proof.Poly1305.X86_64.wR st] m m') :
    bytesAt m' (VG.Proof.Poly1305.X86_64.off st 24) 32 = bytesAt m (VG.Proof.Poly1305.X86_64.off st 24) 32 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := VG.Proof.Poly1305.X86_64.kR st) (VG.Proof.Poly1305.X86_64.kR_disjoint st) (by simp only [Nat.reducePow, Nat.reduceLeDiff]) (List.mem_range.mp hi)

theorem hR_contains (st : Addr) {d : Nat} (h : d + 8 ≤ 24) : (VG.Proof.Poly1305.X86_64.hR st).Contains (VG.Proof.Poly1305.X86_64.off st d) 8 := by
  have := VG.Proof.Poly1305.X86_64.contains_off (base := st) (len := 24) h (by omega_using [h]); simpa using this

theorem wR_contains (st : Addr) {d n : Nat} (h₁ : 56 ≤ d) (h₂ : d + n ≤ 128) :
    (VG.Proof.Poly1305.X86_64.wR st).Contains (VG.Proof.Poly1305.X86_64.off st d) n := by
  simp only [VG.Proof.Poly1305.X86_64.off, VG.Proof.Poly1305.X86_64.ofInt_natCast]; exact Offset.contains st h₁ (by omega_using [h₂]) (by decide)

theorem svR_contains (st : Addr) {d n : Nat} (h₁ : 72 ≤ d) (h₂ : d + n ≤ 120) :
    (VG.Proof.Poly1305.X86_64.svR st).Contains (VG.Proof.Poly1305.X86_64.off st d) n := by
  simp only [VG.Proof.Poly1305.X86_64.off, VG.Proof.Poly1305.X86_64.ofInt_natCast]; exact Offset.contains st h₁ (by omega_using [h₂]) (by decide)

theorem svR_sub_wR (st : Addr) : Region.Sub (VG.Proof.Poly1305.X86_64.svR st) (VG.Proof.Poly1305.X86_64.wR st) := by
  simp only [VG.Proof.Poly1305.X86_64.svR, VG.Proof.Poly1305.X86_64.wR, VG.Proof.Poly1305.X86_64.off, VG.Proof.Poly1305.X86_64.ofInt_natCast]; exact Offset.sub st (by decide) (by decide)

/-! ## The accumulator and the key as numbers -/

theorem off_eq (p : Addr) (d : Nat) : VG.Proof.Poly1305.X86_64.off p d = p + BitVec.ofNat 64 d := by
  simp only [VG.Proof.Poly1305.X86_64.off, VG.Proof.Poly1305.X86_64.ofInt_natCast]

/-- The accumulator stored in the state. -/
theorem leNum_acc (m : Mem) (st : Addr) :
    leNum (bytesAt m st 24) = (m.readW (VG.Proof.Poly1305.X86_64.off st 0) 64).toNat + 2 ^ 64 * (m.readW (VG.Proof.Poly1305.X86_64.off st 8) 64).toNat +
      2 ^ 128 * (m.readW (VG.Proof.Poly1305.X86_64.off st 16) 64).toNat := by
  rw [leNum_bytesAt_24, VG.Proof.Poly1305.X86_64.off_eq, VG.Proof.Poly1305.X86_64.off_eq, VG.Proof.Poly1305.X86_64.off_eq, BitVec.add_zero]
  rfl

/-- The key stored in the state is the 32 bytes at `off st 24`. -/
theorem key_take (m : Mem) (st : Addr) :
    (bytesAt m (VG.Proof.Poly1305.X86_64.off st 24) 32).take 16 = bytesAt m (VG.Proof.Poly1305.X86_64.off st 24) 16 := by
  rw [show 32 = 16 + 16 from rfl, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]

theorem key_drop (m : Mem) (st : Addr) :
    ((bytesAt m (VG.Proof.Poly1305.X86_64.off st 24) 32).drop 16).take 16 = bytesAt m (VG.Proof.Poly1305.X86_64.off st 40) 16 := by
  rw [show 32 = 16 + 16 from rfl, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
    List.take_of_length_le (by rw [length_bytesAt])]
  congr 1
  simp only [VG.Proof.Poly1305.X86_64.off, VG.Proof.Poly1305.X86_64.ofInt_natCast]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem leNum_key (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = (m.readW (VG.Proof.Poly1305.X86_64.off p 0) 64).toNat + 2 ^ 64 * (m.readW (VG.Proof.Poly1305.X86_64.off p 8) 64).toNat := by
  rw [leNum_bytesAt_16, VG.Proof.Poly1305.X86_64.off_eq, VG.Proof.Poly1305.X86_64.off_eq, BitVec.add_zero]
  rfl

theorem off_24 (p : Addr) : VG.Proof.Poly1305.X86_64.off p 24 = p + 24 := by rw [VG.Proof.Poly1305.X86_64.off_eq]; rfl

theorem off_off (p : Addr) (d e : Nat) : VG.Proof.Poly1305.X86_64.off (VG.Proof.Poly1305.X86_64.off p d) e = VG.Proof.Poly1305.X86_64.off p (d + e) := by
  simp only [VG.Proof.Poly1305.X86_64.off, VG.Proof.Poly1305.X86_64.ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The clamped `r` as the code computes it. -/
abbrev M0 : BitVec 64 := 0x0ffffffc0fffffff
abbrev M1 : BitVec 64 := 0x0ffffffc0ffffffc

theorem clamp_key (m : Mem) (st : Addr) :
    clamp (leNum ((bytesAt m (VG.Proof.Poly1305.X86_64.off st 24) 32).take 16)) =
      (m.readW (VG.Proof.Poly1305.X86_64.off st 24) 64 &&& VG.Proof.Poly1305.X86_64.M0).toNat + 2 ^ 64 * (m.readW (VG.Proof.Poly1305.X86_64.off st 32) 64 &&& VG.Proof.Poly1305.X86_64.M1).toNat := by
  rw [VG.Proof.Poly1305.X86_64.key_take, VG.Proof.Poly1305.X86_64.leNum_key, VG.Proof.Poly1305.X86_64.off_off, VG.Proof.Poly1305.X86_64.off_off, clamp_words]

theorem r0_lt (k : BitVec 64) : (k &&& VG.Proof.Poly1305.X86_64.M0).toNat < 2 ^ 60 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem r1_mod (k : BitVec 64) : (k &&& VG.Proof.Poly1305.X86_64.M1).toNat % 4 = 0 := by
  rw [BitVec.toNat_and, show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_assoc, show M1.toNat &&& 2 ^ 2 - 1 = 0 by decide, Nat.and_zero]

theorem r1_lt (k : BitVec 64) : (k &&& VG.Proof.Poly1305.X86_64.M1).toNat < 2 ^ 60 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

end VG.Proof.Poly1305.X86_64

end

/-!
# Poly1305 on x86-64: saving registers, loading the key and the accumulator
-/

namespace VG.Proof.Poly1305

open Spec.Poly1305

open VG.X86_64 in
/-- `vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let key : Region := ⟨s.gpr .rsi, 32⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [state] ∧ state.Disjoint key ∧ ret.Disjoint state
  post s s' := Repr s'.mem (s.gpr .rdi) (bytesAt s.mem (s.gpr .rsi) 32) []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

open VG.X86_64 in
/-- `vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n:
usize)`. -/
def blocksX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let blocks : Region := ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [blocks] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧ ret.Disjoint state ∧
      (s.gpr .rsi).toNat + 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' := ∀ key msg, Repr s.mem (s.gpr .rdi) key msg →
    Repr s'.mem (s.gpr .rdi) key (msg ++ bytesAt s.mem (s.gpr .rsi) (16 * (s.gpr .rdx).toNat))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx

open VG.X86_64 in
/-- `vg_poly1305_finalize(state: *mut [u64; 16], count: u64, out: *mut [u8; 16],
…)`: only `count mod 16`, the number of bytes buffered, matters, and it returns
with `rcx = out`. The state and `out` must be writable, and it may be permitted
to write other regions (which it does not). -/
def finalizeX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let out : Region := ⟨s.gpr .rdx, 16⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    state ∈ s.wr ∧ out ∈ s.wr ∧ state.Disjoint out ∧ ret.Disjoint state ∧ ret.Disjoint out
  post s s' := s'.gpr .rcx = s.gpr .rdx ∧ ∀ key msg, Buffered s.mem (s.gpr .rdi) key msg →
    (s.gpr .rsi).toNat % 16 = msg.length % 16 → bytesAt s'.mem (s.gpr .rdx) 16 = mac key msg
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx

end VG.Proof.Poly1305

namespace VG.Proof.Poly1305.X86_64

open VG.Proof.Poly1305.Limbs64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

section
variable (s₀ : State)
/-- The state, and the return address, on entry. -/
abbrev st : Addr := s₀.gpr .rdi
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
end

/-- The callee-saved registers of `s` are saved in the state at `st`. -/
def Saved (st : Addr) (s : State) (m : Mem) : Prop :=
  m.readW (VG.Proof.Poly1305.X86_64.off st 72) 64 = s.gpr .rbx ∧ m.readW (VG.Proof.Poly1305.X86_64.off st 80) 64 = s.gpr .rbp ∧
  m.readW (VG.Proof.Poly1305.X86_64.off st 88) 64 = s.gpr .r12 ∧ m.readW (VG.Proof.Poly1305.X86_64.off st 96) 64 = s.gpr .r13 ∧
  m.readW (VG.Proof.Poly1305.X86_64.off st 104) 64 = s.gpr .r14 ∧ m.readW (VG.Proof.Poly1305.X86_64.off st 112) 64 = s.gpr .r15

theorem save_eq : save = [
    .store (at_ .rdi 72) .rbx, .store (at_ .rdi 80) .rbp, .store (at_ .rdi 88) .r12,
    .store (at_ .rdi 96) .r13, .store (at_ .rdi 104) .r14, .store (at_ .rdi 112) .r15] := rfl

theorem restore_eq : restore = [
    .mov .rbx (.mem (at_ .rdi 72)), .mov .rbp (.mem (at_ .rdi 80)), .mov .r12 (.mem (at_ .rdi 88)),
    .mov .r13 (.mem (at_ .rdi 96)), .mov .r14 (.mem (at_ .rdi 104)), .mov .r15 (.mem (at_ .rdi 112))] := rfl

set_option simprocs false in
theorem save_ok (s : State) (hw : VG.Proof.Poly1305.X86_64.sR (s.gpr .rdi) ∈ s.wr) :
    WP isa (.block save) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.cf = s.cf ∧ s'.zf = s.zf ∧
      Frame [VG.Proof.Poly1305.X86_64.svR (s.gpr .rdi)] s.mem s'.mem ∧ VG.Proof.Poly1305.X86_64.Saved (s.gpr .rdi) s s'.mem := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (VG.Proof.Poly1305.X86_64.off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, hw, VG.Proof.Poly1305.X86_64.contains_off hd (by omega_using [hd])⟩
  have o0 := o 72 (by decide); have o1 := o 80 (by decide); have o2 := o 88 (by decide)
  have o3 := o 96 (by decide); have o4 := o 104 (by decide); have o5 := o 112 (by decide)
  apply WP.of_runBlock
  rw [VG.Proof.Poly1305.X86_64.save_eq]
  simp only [VG.Proof.Poly1305.X86_64.off] at o0 o1 o2 o3 o4 o5
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.Poly1305.X86_64.ea_at,
    State.store64, o0, o1, o2, o3, o4, o5, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
  · have c : ∀ d, 72 ≤ d → d + 8 ≤ 120 → (VG.Proof.Poly1305.X86_64.svR (s.gpr .rdi)).Contains (VG.Proof.Poly1305.X86_64.off (s.gpr .rdi) d) (64 / 8) :=
      fun d h₁ h₂ => VG.Proof.Poly1305.X86_64.svR_contains _ h₁ h₂
    refine (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 72 ?_ ?_)).writeW
      (List.mem_singleton_self _) _ (c 80 ?_ ?_)).writeW (List.mem_singleton_self _) _ (c 88 ?_ ?_)).writeW
      (List.mem_singleton_self _) _ (c 96 ?_ ?_)).writeW (List.mem_singleton_self _) _ (c 104 ?_ ?_)
      |>.writeW (List.mem_singleton_self _) _ (c 112 ?_ ?_) <;> omega_using []
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (config := {decide := true}) only [VG.Proof.Poly1305.X86_64.off, Mem.readW_writeW_self64, VG.Proof.Poly1305.X86_64.readW_writeW_off]

theorem setup_eq : setup = [
    .movImm64 .rax VG.Proof.Poly1305.X86_64.M0, .mov .r8 (.mem (at_ .rdi 24)), .alu .and .r8 (.reg .rax),
    .movImm64 .rax VG.Proof.Poly1305.X86_64.M1, .mov .r9 (.mem (at_ .rdi 32)), .alu .and .r9 (.reg .rax),
    .mov .r10 (.reg .r9), .shift .shr .r10 2, .alu .add .r10 (.reg .r9),
    .mov .r11 (.mem (at_ .rdi 0)), .mov .rbx (.mem (at_ .rdi 8)), .mov .rbp (.mem (at_ .rdi 16))] := rfl

/-- `s1 = r1 + r1 / 4` is `5 q` for `r1 = 4 q`. -/
theorem s1_toNat (k : BitVec 64) :
    (((k &&& VG.Proof.Poly1305.X86_64.M1) >>> 2) + (k &&& VG.Proof.Poly1305.X86_64.M1)).toNat = 5 * ((k &&& VG.Proof.Poly1305.X86_64.M1).toNat / 4) := by
  have h1 := VG.Proof.Poly1305.X86_64.r1_lt k; have h2 := VG.Proof.Poly1305.X86_64.r1_mod k
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega_using [h1, h2]

set_option simprocs false in
theorem setup_ok (s : State) (hw : VG.Proof.Poly1305.X86_64.sR (s.gpr .rdi) ∈ s.rd ++ s.wr) :
    WP isa (.block setup) s fun s' =>
      s'.gpr .r8 = s.mem.readW (VG.Proof.Poly1305.X86_64.off (s.gpr .rdi) 24) 64 &&& VG.Proof.Poly1305.X86_64.M0 ∧
      s'.gpr .r9 = s.mem.readW (VG.Proof.Poly1305.X86_64.off (s.gpr .rdi) 32) 64 &&& VG.Proof.Poly1305.X86_64.M1 ∧
      (s'.gpr .r10).toNat = 5 * ((s'.gpr .r9).toNat / 4) ∧
      s'.gpr .r11 = s.mem.readW (VG.Proof.Poly1305.X86_64.off (s.gpr .rdi) 0) 64 ∧
      s'.gpr .rbx = s.mem.readW (VG.Proof.Poly1305.X86_64.off (s.gpr .rdi) 8) 64 ∧
      s'.gpr .rbp = s.mem.readW (VG.Proof.Poly1305.X86_64.off (s.gpr .rdi) 16) 64 ∧
      VG.Proof.Poly1305.X86_64.Keeps [.rax, .r8, .r9, .r10, .r11, .rbx, .rbp] s s' := by
  have i : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (VG.Proof.Poly1305.X86_64.off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, hw, VG.Proof.Poly1305.X86_64.contains_off hd (by omega_using [hd])⟩
  have i0 := i 0 (by decide); have i8 := i 8 (by decide); have i16 := i 16 (by decide)
  have i24 := i 24 (by decide); have i32 := i 32 (by decide)
  simp only [VG.Proof.Poly1305.X86_64.off] at i0 i8 i16 i24 i32
  apply WP.of_runBlock
  rw [VG.Proof.Poly1305.X86_64.setup_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.Poly1305.X86_64.ea_at,
    readSrc, execAlu, execShift, arithFlags, State.setReg, State.setFlags, State.load64, i0, i8, i16,
    i24, i32, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, VG.Proof.Poly1305.X86_64.s1_toNat _, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.2.2.2.2.2.2, Int.cast_ofNat_Int, BitVec.ofInt_ofNat, hr.2.2.2.2.2.1, hr.2.2.2.2.1, BitVec.add_zero, hr.2.2.2.1, BitVec.ofNat_eq_ofNat, hr.2.2.1, hr.1, hr.2.1, ite_false]

end VG.Proof.Poly1305.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Blocks`. -/
section

/-!
# Poly1305 on x86-64: `blocks`
-/

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem mod_step {h X M R : Nat} (hv : h % P = X % P) :
    ((h + M) * R) % P = (R * (X + M)) % P % P := by
  rw [Nat.mod_mod, Nat.mul_comm R, Nat.mul_mod, Nat.add_mod, hv, ← Nat.add_mod, ← Nat.mul_mod]

section
variable (s₀ : State)
abbrev bp : Addr := s₀.gpr .rsi
abbrev nb : Nat := (s₀.gpr .rdx).toNat
abbrev blR : Region := ⟨VG.Proof.Poly1305.X86_64.bp s₀, 16 * VG.Proof.Poly1305.X86_64.nb s₀⟩
/-- The clamped `r`. -/
abbrev R0 : BitVec 64 := s₀.mem.readW (VG.Proof.Poly1305.X86_64.off (VG.Proof.Poly1305.X86_64.st s₀) 24) 64 &&& VG.Proof.Poly1305.X86_64.M0
abbrev R1 : BitVec 64 := s₀.mem.readW (VG.Proof.Poly1305.X86_64.off (VG.Proof.Poly1305.X86_64.st s₀) 32) 64 &&& VG.Proof.Poly1305.X86_64.M1
abbrev Rn : Nat := (VG.Proof.Poly1305.X86_64.R0 s₀).toNat + 2 ^ 64 * (VG.Proof.Poly1305.X86_64.R1 s₀).toNat
/-- The accumulator on entry, and its top word. -/
abbrev A0 : Nat := leNum (bytesAt s₀.mem (VG.Proof.Poly1305.X86_64.st s₀) 24)
abbrev H2 : Nat := (s₀.mem.readW (VG.Proof.Poly1305.X86_64.off (VG.Proof.Poly1305.X86_64.st s₀) 16) 64).toNat
/-- The first `i` blocks. -/
abbrev blks (i : Nat) : List Byte := bytesAt s₀.mem (VG.Proof.Poly1305.X86_64.bp s₀) (16 * i)
/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : Addr := VG.Proof.Poly1305.X86_64.bp s₀ + BitVec.ofNat 64 (16 * i)
end

structure BPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Poly1305.X86_64.blR s₀]
  wr : s₀.wr = [VG.Proof.Poly1305.X86_64.sR (VG.Proof.Poly1305.X86_64.st s₀)]
  st_bl : (VG.Proof.Poly1305.X86_64.sR (VG.Proof.Poly1305.X86_64.st s₀)).Disjoint (VG.Proof.Poly1305.X86_64.blR s₀)
  ret_st : (VG.Proof.Poly1305.X86_64.retR s₀).Disjoint (VG.Proof.Poly1305.X86_64.sR (VG.Proof.Poly1305.X86_64.st s₀))
  nowrap : (VG.Proof.Poly1305.X86_64.bp s₀).toNat + 16 * VG.Proof.Poly1305.X86_64.nb s₀ ≤ 2 ^ 64

theorem BPre.of (s₀ : State) (h : Proof.Poly1305.blocksX86_64.pre s₀) : VG.Proof.Poly1305.X86_64.BPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- What holds between blocks, after `i` of them, with the memory `m₁` left
by the prologue. -/
structure Common (s₀ : State) (m₁ : Mem) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = VG.Proof.Poly1305.X86_64.st s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r8 : s.gpr .r8 = VG.Proof.Poly1305.X86_64.R0 s₀
  r9 : s.gpr .r9 = VG.Proof.Poly1305.X86_64.R1 s₀
  r10 : (s.gpr .r10).toNat = 5 * ((VG.Proof.Poly1305.X86_64.R1 s₀).toNat / 4)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = m₁
  acc : VG.Proof.Poly1305.X86_64.H2 s₀ ≤ 4 →
    VG.Proof.Poly1305.X86_64.hval s % P = Poly1305.absorbAll (VG.Proof.Poly1305.X86_64.Rn s₀) (VG.Proof.Poly1305.X86_64.A0 s₀) (VG.Proof.Poly1305.X86_64.blks s₀ i) % P ∧ (s.gpr .rbp).toNat ≤ 4

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (m₁ : Mem) (i : Nat) (s : State) : Prop extends VG.Proof.Poly1305.X86_64.Common s₀ m₁ i s where
  rsi : s.gpr .rsi = VG.Proof.Poly1305.X86_64.blkAddr s₀ i
  rcx : s.gpr .rcx = BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.nb s₀ - i)

/-- The memory the prologue leaves. -/
structure Mem₁ (s₀ : State) (m₁ : Mem) : Prop where
  frame : Frame [VG.Proof.Poly1305.X86_64.svR (VG.Proof.Poly1305.X86_64.st s₀)] s₀.mem m₁
  saved : VG.Proof.Poly1305.X86_64.Saved (VG.Proof.Poly1305.X86_64.st s₀) s₀ m₁

namespace BPre
variable {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.BPre s₀)
include hp

theorem nb_lt : 16 * VG.Proof.Poly1305.X86_64.nb s₀ < 2 ^ 64 := by
  have := (VG.Proof.Poly1305.X86_64.bp s₀).isLt
  by_contra h
  refine hp.st_bl (VG.Proof.Poly1305.X86_64.st s₀) (by simp [Region.Contains]) ?_
  simp only [Region.Contains]
  have := (VG.Proof.Poly1305.X86_64.st s₀ - VG.Proof.Poly1305.X86_64.bp s₀).isLt
  omega_using [h, this]

theorem blk_contains {i d : Nat} (hi : i < VG.Proof.Poly1305.X86_64.nb s₀) (hd : d + 8 ≤ 16) :
    (VG.Proof.Poly1305.X86_64.blR s₀).Contains (VG.Proof.Poly1305.X86_64.blkAddr s₀ i + BitVec.ofInt 64 (d : Int)) 8 := by
  have := hp.nb_lt
  rw [VG.Proof.Poly1305.X86_64.ofInt_natCast, VG.Proof.Poly1305.X86_64.blkAddr, Offset.add_add]
  exact Offset.contains_base _ (by omega_using [hi, hd]) (by omega_using [hi, hd, this])

/-- Block words read from memory the code has written only in the state. -/
theorem blk_word {m : Mem} (hf : Frame [VG.Proof.Poly1305.X86_64.sR (VG.Proof.Poly1305.X86_64.st s₀)] s₀.mem m) {i d : Nat} (hi : i < VG.Proof.Poly1305.X86_64.nb s₀)
    (hd : d + 8 ≤ 16) :
    m.readW (VG.Proof.Poly1305.X86_64.blkAddr s₀ i + BitVec.ofInt 64 (d : Int)) 64 =
      s₀.mem.readW (VG.Proof.Poly1305.X86_64.blkAddr s₀ i + BitVec.ofInt 64 (d : Int)) 64 :=
  hf.readW (hp.blk_contains hi hd) (by simpa using hp.st_bl.symm) (by decide)

end BPre

theorem Mem₁.frame_sR {s₀ : State} {m₁ : Mem} (h : VG.Proof.Poly1305.X86_64.Mem₁ s₀ m₁) : Frame [VG.Proof.Poly1305.X86_64.sR (VG.Proof.Poly1305.X86_64.st s₀)] s₀.mem m₁ :=
  h.frame.sub fun r hr => ⟨VG.Proof.Poly1305.X86_64.sR (VG.Proof.Poly1305.X86_64.st s₀), List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Poly1305.X86_64.sub_sR _ (by decide)⟩

theorem Mem₁.frame_wR {s₀ : State} {m₁ : Mem} (h : VG.Proof.Poly1305.X86_64.Mem₁ s₀ m₁) : Frame [VG.Proof.Poly1305.X86_64.wR (VG.Proof.Poly1305.X86_64.st s₀)] s₀.mem m₁ :=
  h.frame.sub fun r hr => ⟨VG.Proof.Poly1305.X86_64.wR (VG.Proof.Poly1305.X86_64.st s₀), List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Poly1305.X86_64.svR_sub_wR _⟩

/-- A word of the accumulator or the key, which the prologue does not change. -/
theorem Mem₁.readW_low {s₀ : State} {m₁ : Mem} (h : VG.Proof.Poly1305.X86_64.Mem₁ s₀ m₁) {d : Nat} (hd : d + 8 ≤ 56) :
    m₁.readW (VG.Proof.Poly1305.X86_64.off (VG.Proof.Poly1305.X86_64.st s₀) d) 64 = s₀.mem.readW (VG.Proof.Poly1305.X86_64.off (VG.Proof.Poly1305.X86_64.st s₀) d) 64 := by
  refine h.frame.readW (r := ⟨VG.Proof.Poly1305.X86_64.off (VG.Proof.Poly1305.X86_64.st s₀) d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq, VG.Proof.Poly1305.X86_64.svR, VG.Proof.Poly1305.X86_64.off, VG.Proof.Poly1305.X86_64.ofInt_natCast]
  exact Offset.disjoint (VG.Proof.Poly1305.X86_64.st s₀) (by omega_using [hd]) (by omega_using [hd]) (by decide)

theorem se16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide

set_option simprocs false in
theorem advance_ok (s : State) :
    WP isa (.block [.alu .add .rsi (.imm 16), .alu .sub .rcx (.imm 1)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rsi + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ VG.Proof.Poly1305.X86_64.Keeps [.rsi, .rcx] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, ite_true, ite_false, Option.bind_some,
    Option.some.injEq, exists_eq_left', VG.Proof.Poly1305.X86_64.se16, VG.Proof.Poly1305.X86_64.se1]
  refine ⟨trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2]

/-- The value of block `i`, with the `0x01` byte appended: its two words and `2¹²⁸`. -/
theorem block_value {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.BPre s₀) {m : Mem} (hf : Frame [VG.Proof.Poly1305.X86_64.sR (VG.Proof.Poly1305.X86_64.st s₀)] s₀.mem m)
    {i : Nat} (hi : i < VG.Proof.Poly1305.X86_64.nb s₀) :
    VG.Proof.Poly1305.X86_64.word m (VG.Proof.Poly1305.X86_64.blkAddr s₀ i) 0 + 2 ^ 64 * VG.Proof.Poly1305.X86_64.word m (VG.Proof.Poly1305.X86_64.blkAddr s₀ i) 8 + 2 ^ 128 * (1 : BitVec 32).toNat =
      leNum (bytesAt s₀.mem (VG.Proof.Poly1305.X86_64.blkAddr s₀ i) 16 ++ [0x01]) := by
  simp only [VG.Proof.Poly1305.X86_64.word]
  rw [hp.blk_word hf hi (by decide), hp.blk_word hf hi (by decide), Poly1305.leNum_append,
    Poly1305.length_bytesAt, VG.Proof.Poly1305.X86_64.leNum_key]
  have h1 : leNum [(0x01 : Byte)] = 1 := rfl
  have h2 : (1 : BitVec 32).toNat = 1 := rfl
  rw [h1, h2]

theorem blks_succ (s₀ : State) (i : Nat) :
    VG.Proof.Poly1305.X86_64.blks s₀ (i + 1) = VG.Proof.Poly1305.X86_64.blks s₀ i ++ bytesAt s₀.mem (VG.Proof.Poly1305.X86_64.blkAddr s₀ i) 16 := by
  simp only [VG.Proof.Poly1305.X86_64.blks, VG.Proof.Poly1305.X86_64.blkAddr]
  rw [show 16 * (i + 1) = 16 * i + 16 by omega_using [], Poly1305.bytesAt_add]

theorem body_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.BPre s₀) {m₁ : Mem} (hm : VG.Proof.Poly1305.X86_64.Mem₁ s₀ m₁) {i : Nat}
    (hi : i < VG.Proof.Poly1305.X86_64.nb s₀) {s : State} (hL : VG.Proof.Poly1305.X86_64.LInv s₀ m₁ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ VG.Proof.Poly1305.X86_64.Common s₀ m₁ (VG.Proof.Poly1305.X86_64.nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < VG.Proof.Poly1305.X86_64.nb s₀ ∧ VG.Proof.Poly1305.X86_64.LInv s₀ m₁ (i + 1) s') := by
  have hq : (VG.Proof.Poly1305.X86_64.R1 s₀).toNat % 4 = 0 := VG.Proof.Poly1305.X86_64.r1_mod _
  have hq' : (VG.Proof.Poly1305.X86_64.R1 s₀).toNat < 2 ^ 60 := VG.Proof.Poly1305.X86_64.r1_lt _
  have hin : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 (d : Int)) 8 := by
    intro d hd
    rw [hL.rd, hL.wr, hL.rsi, hp.rd]
    exact ⟨VG.Proof.Poly1305.X86_64.blR s₀, List.mem_append_left _ (List.mem_singleton_self _), hp.blk_contains hi hd⟩
  have hr0 : (s.gpr .r8).toNat < 2 ^ 60 := by rw [hL.r8]; exact VG.Proof.Poly1305.X86_64.r0_lt _
  have hr1 : (s.gpr .r9).toNat = 4 * ((VG.Proof.Poly1305.X86_64.R1 s₀).toNat / 4) := by rw [hL.r9]; omega_using [hq]
  have hq2 : (VG.Proof.Poly1305.X86_64.R1 s₀).toNat / 4 < 2 ^ 58 := by omega_using [hq, hq']
  have hs1 : (s.gpr .r10).toNat = 5 * ((VG.Proof.Poly1305.X86_64.R1 s₀).toNat / 4) := hL.r10
  have hab := VG.Proof.Poly1305.X86_64.absorb_ok s (pad := 1) (Or.inr rfl) hr0 hr1 hq2 hs1 (hin 0 (by decide)) (hin 8 (by decide))
  rw [body]
  refine WP.block_append (WP.mono hab fun s₁ ⟨ha, k₁⟩ => ?_)
  refine WP.mono (VG.Proof.Poly1305.X86_64.advance_ok s₁) fun s₂ ⟨a₁, a₂, a₃, k₂⟩ => ?_
  have k := k₁.trans k₂
  have hc : VG.Proof.Poly1305.X86_64.Common s₀ m₁ (i + 1) s₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun hH2 => ?_⟩
    · rw [k.gpr' (r := .rdi), hL.rdi]
    · rw [k.gpr' (r := .rsp), hL.rsp]
    · rw [k.gpr' (r := .r8), hL.r8]
    · rw [k.gpr' (r := .r9), hL.r9]
    · rw [k.gpr' (r := .r10), hL.r10]
    · rw [k.2.2.1, hL.rd]
    · rw [k.2.2.2, hL.wr]
    · rw [k.2.1, hL.mem]
    · obtain ⟨hv, hb⟩ := hL.acc hH2
      obtain ⟨hv', hb'⟩ := ha hb
      have hval₂ : VG.Proof.Poly1305.X86_64.hval s₂ = VG.Proof.Poly1305.X86_64.hval s₁ := by
        simp only [VG.Proof.Poly1305.X86_64.hval, k₂.gpr' (r := .r11), k₂.gpr' (r := .rbx), k₂.gpr' (r := .rbp)]
      have hrbp₂ : s₂.gpr .rbp = s₁.gpr .rbp := k₂.gpr'
      refine ⟨?_, by rw [hrbp₂]; exact hb'⟩
      have h16 : (VG.Proof.Poly1305.X86_64.blks s₀ i).length % 16 = 0 := by simp only [VG.Proof.Poly1305.X86_64.blks, Poly1305.length_bytesAt]; omega_using []
      have hb1 : 0 < (bytesAt s₀.mem (VG.Proof.Poly1305.X86_64.blkAddr s₀ i) 16).length := by rw [Poly1305.length_bytesAt]; omega_using []
      have hb2 : (bytesAt s₀.mem (VG.Proof.Poly1305.X86_64.blkAddr s₀ i) 16).length ≤ 16 := by rw [Poly1305.length_bytesAt]
      rw [hval₂, hv', hL.rsi, hL.mem, VG.Proof.Poly1305.X86_64.block_value hp (hL.mem ▸ hm.frame_sR) hi, hL.r8, hL.r9,
        VG.Proof.Poly1305.X86_64.mod_step hv, VG.Proof.Poly1305.X86_64.blks_succ, Poly1305.absorbAll_append h16, Poly1305.absorbAll_block hb1 hb2]
  have hrcx : s₂.gpr .rcx = BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.nb s₀ - (i + 1)) := by
    rw [a₂, k₁.gpr' (r := .rcx), hL.rcx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]
  have hev : eval .ne s₂ = some (!(BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, a₃, Option.map_some]; rw [← hrcx, a₂]
  by_cases hlast : i + 1 = VG.Proof.Poly1305.X86_64.nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hc⟩
  · right
    have hne : VG.Proof.Poly1305.X86_64.nb s₀ - (i + 1) ≠ 0 := by omega_using [hi, hlast]
    have := hp.nb_lt
    have h0 : BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, this, h'])] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega_using [hi, hne], { hc with rsi := ?_, rcx := hrcx }⟩
    rw [a₁, k₁.gpr' (r := .rsi), hL.rsi, VG.Proof.Poly1305.X86_64.blkAddr, VG.Proof.Poly1305.X86_64.blkAddr,
      show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add, Nat.mul_succ]

/-! ## Prologue and epilogue -/

set_option simprocs false in
theorem mov_rcx_ok (s : State) :
    WP isa (.block [.mov .rcx (.reg .rdx)]) s fun s' =>
      s'.gpr .rcx = s.gpr .rdx ∧ VG.Proof.Poly1305.X86_64.Keeps [.rcx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp [hr]

set_option simprocs false in
theorem test_ok (s : State) (r : Reg) :
    WP isa (.block [.alu .test r (.reg r)]) s fun s' =>
      s'.zf = some (s.gpr r &&& s.gpr r == 0) ∧ VG.Proof.Poly1305.X86_64.Keeps [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r _ => rfl, rfl, rfl, rfl⟩

theorem prologue_eq : save ++ ([.mov .rcx (.reg .rdx)] : List Instr) ++ setup ++ ([.alu .test .rcx (.reg .rcx)] : List Instr) =
    save ++ (([.mov .rcx (.reg .rdx)] : List Instr) ++ (setup ++ ([.alu .test .rcx (.reg .rcx)] : List Instr))) := by
  simp only [List.append_assoc]

theorem blks_zero (s₀ : State) : VG.Proof.Poly1305.X86_64.blks s₀ 0 = [] := by simp [VG.Proof.Poly1305.X86_64.blks, bytesAt]

theorem prologue_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.BPre s₀) :
    WP isa (.block (save ++ ([.mov .rcx (.reg .rdx)] : List Instr) ++ setup ++ ([.alu .test .rcx (.reg .rcx)] : List Instr))) s₀
      fun s => ∃ m₁, VG.Proof.Poly1305.X86_64.Mem₁ s₀ m₁ ∧ VG.Proof.Poly1305.X86_64.Common s₀ m₁ 0 s ∧ s.gpr .rsi = VG.Proof.Poly1305.X86_64.bp s₀ ∧
        s.gpr .rcx = s₀.gpr .rdx ∧ s.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) := by
  rw [VG.Proof.Poly1305.X86_64.prologue_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.save_ok s₀ (by rw [hp.wr]; exact List.mem_singleton_self _))
    fun s₁ ⟨g₁, rd₁, wr₁, _, _, f₁, sv₁⟩ => ?_)
  have hm : VG.Proof.Poly1305.X86_64.Mem₁ s₀ s₁.mem := ⟨f₁, sv₁⟩
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.mov_rcx_ok s₁) fun s₂ ⟨c₂, k₂⟩ => ?_)
  have rdi₂ : s₂.gpr .rdi = VG.Proof.Poly1305.X86_64.st s₀ := by rw [k₂.gpr' (r := .rdi), g₁]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.setup_ok s₂ (by
    rw [k₂.2.2.2, wr₁, hp.wr, rdi₂]; exact List.mem_append_right _ (List.mem_singleton_self _)))
    fun s₃ ⟨e8, e9, e10, e11, e12, e13, k₃⟩ => ?_)
  refine WP.mono (VG.Proof.Poly1305.X86_64.test_ok s₃ .rcx) fun s₄ ⟨z₄, k₄⟩ => ?_
  have k := (k₂.trans k₃).trans k₄
  rw [k₂.2.1, rdi₂, hm.readW_low (by decide)] at e8 e9 e11 e12 e13
  have g : ∀ r, r ∉ [Reg.rcx, .rax, .r8, .r9, .r10, .r11, .rbx, .rbp] → s₄.gpr r = s₀.gpr r :=
    fun r hr => by rw [k.1 r (by simpa using hr), g₁]
  refine ⟨s₁.mem, hm, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun hH2 => ?_⟩, ?_, ?_, ?_⟩
  · exact g .rdi (by decide)
  · exact g .rsp (by decide)
  · rw [k₄.gpr' (r := .r8), e8]
  · rw [k₄.gpr' (r := .r9), e9]
  · rw [k₄.gpr' (r := .r10), e10, e9]
  · rw [k.2.2.1, rd₁]
  · rw [k.2.2.2, wr₁]
  · rw [k.2.1]
  · rw [VG.Proof.Poly1305.X86_64.blks_zero, Poly1305.absorbAll_nil]
    simp only [VG.Proof.Poly1305.X86_64.hval, k₄.gpr' (r := .r11), k₄.gpr' (r := .rbx), k₄.gpr' (r := .rbp), e11, e12, e13]
    refine ⟨?_, hH2⟩
    rw [VG.Proof.Poly1305.X86_64.A0, VG.Proof.Poly1305.X86_64.leNum_acc]
  · exact g .rsi (by decide)
  · rw [k₄.gpr' (r := .rcx), k₃.gpr' (r := .rcx), c₂, g₁]
  · rw [z₄, k₃.gpr' (r := .rcx), c₂, g₁]

/-- The memory after storing `h0, h1, h2` in the state. -/
def storeH (m : Mem) (st : Addr) (h0 h1 h2 : BitVec 64) : Mem :=
  ((m.writeW (VG.Proof.Poly1305.X86_64.off st 0) h0).writeW (VG.Proof.Poly1305.X86_64.off st 8) h1).writeW (VG.Proof.Poly1305.X86_64.off st 16) h2

theorem storeRestore_eq : [Instr.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx,
    .store (at_ .rdi 16) .rbp] ++ restore = [.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx,
    .store (at_ .rdi 16) .rbp, .mov .rbx (.mem (at_ .rdi 72)), .mov .rbp (.mem (at_ .rdi 80)),
    .mov .r12 (.mem (at_ .rdi 88)), .mov .r13 (.mem (at_ .rdi 96)), .mov .r14 (.mem (at_ .rdi 104)),
    .mov .r15 (.mem (at_ .rdi 112))] := rfl

set_option simprocs false in
/-- Storing `h` and restoring the callee-saved registers. -/
theorem storeRestore_ok (s : State) (hw : VG.Proof.Poly1305.X86_64.sR (s.gpr .rdi) ∈ s.wr) :
    WP isa (.block (([.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx,
      .store (at_ .rdi 16) .rbp] : List Instr) ++ restore)) s fun s' =>
      let m := VG.Proof.Poly1305.X86_64.storeH s.mem (s.gpr .rdi) (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp)
      s'.mem = m ∧ s'.gpr .rbx = m.readW (VG.Proof.Poly1305.X86_64.off (s.gpr .rdi) 72) 64 ∧
      s'.gpr .rbp = m.readW (VG.Proof.Poly1305.X86_64.off (s.gpr .rdi) 80) 64 ∧ s'.gpr .r12 = m.readW (VG.Proof.Poly1305.X86_64.off (s.gpr .rdi) 88) 64 ∧
      s'.gpr .r13 = m.readW (VG.Proof.Poly1305.X86_64.off (s.gpr .rdi) 96) 64 ∧ s'.gpr .r14 = m.readW (VG.Proof.Poly1305.X86_64.off (s.gpr .rdi) 104) 64 ∧
      s'.gpr .r15 = m.readW (VG.Proof.Poly1305.X86_64.off (s.gpr .rdi) 112) 64 ∧ s'.gpr .rsp = s.gpr .rsp := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (VG.Proof.Poly1305.X86_64.off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, hw, VG.Proof.Poly1305.X86_64.contains_off hd (by omega_using [hd])⟩
  have i : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (VG.Proof.Poly1305.X86_64.off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, VG.Proof.Poly1305.X86_64.contains_off hd (by omega_using [hd])⟩
  have o0 := o 0 (by decide); have o8 := o 8 (by decide); have o16 := o 16 (by decide)
  have i0 := i 72 (by decide); have i1 := i 80 (by decide); have i2 := i 88 (by decide)
  have i3 := i 96 (by decide); have i4 := i 104 (by decide); have i5 := i 112 (by decide)
  simp only [VG.Proof.Poly1305.X86_64.off] at o0 o8 o16 i0 i1 i2 i3 i4 i5
  apply WP.of_runBlock
  rw [VG.Proof.Poly1305.X86_64.storeRestore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.Poly1305.X86_64.ea_at,
    readSrc, State.store64, State.load64, State.setReg, o0, o8, o16, i0, i1, i2, i3, i4, i5,
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

theorem storeH_frame {st : Addr} {m m' : Mem} (hf : Frame [VG.Proof.Poly1305.X86_64.hR st, VG.Proof.Poly1305.X86_64.wR st] m m') (h0 h1 h2 : BitVec 64) :
    Frame [VG.Proof.Poly1305.X86_64.hR st, VG.Proof.Poly1305.X86_64.wR st] m (VG.Proof.Poly1305.X86_64.storeH m' st h0 h1 h2) := by
  have c : ∀ d, d + 8 ≤ 24 → (VG.Proof.Poly1305.X86_64.hR st).Contains (VG.Proof.Poly1305.X86_64.off st d) (64 / 8) := fun d hd => VG.Proof.Poly1305.X86_64.hR_contains st hd
  exact ((hf.writeW List.mem_cons_self _ (c 0 (by decide))).writeW List.mem_cons_self _ (c 8 (by decide))).writeW
    List.mem_cons_self _ (c 16 (by decide))

theorem storeH_saved (m : Mem) (st : Addr) (h0 h1 h2 : BitVec 64) {d : Nat} (h₁ : 24 ≤ d)
    (h₂ : d < 2 ^ 32) : (VG.Proof.Poly1305.X86_64.storeH m st h0 h1 h2).readW (VG.Proof.Poly1305.X86_64.off st d) 64 = m.readW (VG.Proof.Poly1305.X86_64.off st d) 64 := by
  simp only [VG.Proof.Poly1305.X86_64.storeH]
  rw [VG.Proof.Poly1305.X86_64.readW_writeW_off _ _ _ (by omega_using [h₂]) (by decide) (by omega_using [h₁, h₂]),
    VG.Proof.Poly1305.X86_64.readW_writeW_off _ _ _ (by omega_using [h₂]) (by decide) (by omega_using [h₁, h₂]),
    VG.Proof.Poly1305.X86_64.readW_writeW_off _ _ _ (by omega_using [h₂]) (by decide) (by omega_using [h₁, h₂])]

theorem storeH_acc (m : Mem) (st : Addr) (h0 h1 h2 : BitVec 64) :
    leNum (bytesAt (VG.Proof.Poly1305.X86_64.storeH m st h0 h1 h2) st 24) = h0.toNat + 2 ^ 64 * h1.toNat + 2 ^ 128 * h2.toNat := by
  rw [VG.Proof.Poly1305.X86_64.leNum_acc]
  simp only [VG.Proof.Poly1305.X86_64.storeH]
  rw [VG.Proof.Poly1305.X86_64.readW_writeW_off _ _ _ (by decide) (by decide) (by decide),
    VG.Proof.Poly1305.X86_64.readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64,
    VG.Proof.Poly1305.X86_64.readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64,
    Mem.readW_writeW_self64]

/-- The accumulator on entry is less than `p` if the state represents a message. -/
theorem H2_le {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (VG.Proof.Poly1305.X86_64.st s₀) key msg) : VG.Proof.Poly1305.X86_64.H2 s₀ ≤ 4 := by
  have := Poly1305.accumulate_lt (clamp (leNum (key.take 16))) msg
  rw [← h.2.2, VG.Proof.Poly1305.X86_64.leNum_acc] at this
  simp only [VG.Proof.Poly1305.X86_64.H2, P] at this ⊢
  omega_using [this]

theorem epilogue_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.BPre s₀) {m₁ : Mem} (hm : VG.Proof.Poly1305.X86_64.Mem₁ s₀ m₁) {s : State}
    (hc : VG.Proof.Poly1305.X86_64.Common s₀ m₁ (VG.Proof.Poly1305.X86_64.nb s₀) s) :
    WP isa (.block (reduce ++ ([.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx,
      .store (at_ .rdi 16) .rbp] : List Instr) ++ restore)) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Poly1305.blocksX86_64.post s₀ s' := by
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.reduce_ok s) fun s₁ ⟨hr, k₁⟩ => ?_)
  have rdi₁ : s₁.gpr .rdi = VG.Proof.Poly1305.X86_64.st s₀ := by rw [k₁.gpr' (r := .rdi), hc.rdi]
  have hw : VG.Proof.Poly1305.X86_64.sR (s₁.gpr .rdi) ∈ s₁.wr := by
    rw [k₁.2.2.2, hc.wr, hp.wr, rdi₁]; exact List.mem_singleton_self _
  refine WP.mono (VG.Proof.Poly1305.X86_64.storeRestore_ok s₁ hw) fun s₂ ⟨m₂, g1, g2, g3, g4, g5, g6, g7⟩ => ?_
  rw [rdi₁, k₁.2.1, hc.mem] at m₂ g1 g2 g3 g4 g5 g6
  obtain ⟨sv1, sv2, sv3, sv4, sv5, sv6⟩ := hm.saved
  have hf : Frame [VG.Proof.Poly1305.X86_64.hR (VG.Proof.Poly1305.X86_64.st s₀), VG.Proof.Poly1305.X86_64.wR (VG.Proof.Poly1305.X86_64.st s₀)] s₀.mem s₂.mem := by
    rw [m₂]; exact VG.Proof.Poly1305.X86_64.storeH_frame (hm.frame_wR.mono (by simp)) _ _ _
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun key msg hrep => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g1, VG.Proof.Poly1305.X86_64.storeH_saved _ _ _ _ _ (by decide) (by decide), sv1]
    · rw [g2, VG.Proof.Poly1305.X86_64.storeH_saved _ _ _ _ _ (by decide) (by decide), sv2]
    · rw [g7, k₁.gpr' (r := .rsp), hc.rsp]
    · rw [g3, VG.Proof.Poly1305.X86_64.storeH_saved _ _ _ _ _ (by decide) (by decide), sv3]
    · rw [g4, VG.Proof.Poly1305.X86_64.storeH_saved _ _ _ _ _ (by decide) (by decide), sv4]
    · rw [g5, VG.Proof.Poly1305.X86_64.storeH_saved _ _ _ _ _ (by decide) (by decide), sv5]
    · rw [g6, VG.Proof.Poly1305.X86_64.storeH_saved _ _ _ _ _ (by decide) (by decide), sv6]
  · refine hf.readW (Region.contains_self _ _) ?_ (by decide)
    have hd := hp.ret_st
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hd.sub_right (Region.sub_prefix (by decide))
    · exact hd.sub_right (VG.Proof.Poly1305.X86_64.sub_sR _ (by decide))
  · obtain ⟨hlen, hkey, hacc⟩ := hrep
    have hH2 := VG.Proof.Poly1305.X86_64.H2_le ⟨hlen, hkey, hacc⟩
    obtain ⟨hv, hb⟩ := hc.acc hH2
    have hR := hr hb
    rw [← VG.Proof.Poly1305.X86_64.off_24] at hkey
    have hkey' : bytesAt s₀.mem (VG.Proof.Poly1305.X86_64.off (VG.Proof.Poly1305.X86_64.st s₀) 24) 32 = key := hkey
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_append, Poly1305.length_bytesAt]; omega_using [hlen]
    · rw [← VG.Proof.Poly1305.X86_64.off_24, VG.Proof.Poly1305.X86_64.key_frame hf, hkey']
    · rw [m₂, VG.Proof.Poly1305.X86_64.storeH_acc, ← hkey', VG.Proof.Poly1305.X86_64.clamp_key, Poly1305.accumulate_append hlen]
      have hA : accumulate (VG.Proof.Poly1305.X86_64.Rn s₀) msg = VG.Proof.Poly1305.X86_64.A0 s₀ := by rw [VG.Proof.Poly1305.X86_64.A0, hacc, ← hkey', VG.Proof.Poly1305.X86_64.clamp_key]
      rw [hA]
      change VG.Proof.Poly1305.X86_64.hval s₁ = _
      have hlt : VG.Proof.Poly1305.X86_64.A0 s₀ < P := by rw [← hA]; exact Poly1305.accumulate_lt _ _
      rw [hR, hv, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _)]

/-! ## The whole function -/

theorem blocks_correct {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.BPre s₀) :
    WP isa blocks s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Poly1305.blocksX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.prologue_ok hp) fun s₁ ⟨m₁, hm, hc, hrsi, hrcx, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Poly1305.X86_64.Common s₀ m₁ (VG.Proof.Poly1305.X86_64.nb s₀)) ?_ fun s₂ hc₂ => VG.Proof.Poly1305.X86_64.epilogue_ok hp hm hc₂)
  refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have h0 : VG.Proof.Poly1305.X86_64.nb s₀ = 0 := by simp at h; simp [VG.Proof.Poly1305.X86_64.nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc)
  · have hpos : 0 < VG.Proof.Poly1305.X86_64.nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = VG.Proof.Poly1305.X86_64.nb s₀ - i ∧ i < VG.Proof.Poly1305.X86_64.nb s₀ ∧ VG.Proof.Poly1305.X86_64.LInv s₀ m₁ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ VG.Proof.Poly1305.X86_64.Common s₀ m₁ (VG.Proof.Poly1305.X86_64.nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (VG.Proof.Poly1305.X86_64.body_ok hp hm hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, VG.Proof.Poly1305.X86_64.nb s₀ - (i + 1), by omega_using [hi'], i + 1, rfl, hi', hL'⟩
    have hL₀ : VG.Proof.Poly1305.X86_64.LInv s₀ m₁ 0 s₁ :=
      { hc with
        rsi := by rw [hrsi]; simp [VG.Proof.Poly1305.X86_64.blkAddr]
        rcx := by rw [hrcx]; simp [VG.Proof.Poly1305.X86_64.nb] }
    exact WP.loop (M := isa) Inv hstep (VG.Proof.Poly1305.X86_64.nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def blocksSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩]

theorem blocks_ok (s : State) (hs : Proof.Poly1305.blocksX86_64.pre s) :
    ∃ t s', Exec isa Impl.Poly1305.X86_64.blocks s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.blocksX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Poly1305.X86_64.blocks_correct (BPre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem blocks_ct : ConstantTime isa Proof.Poly1305.blocksX86_64.pre Proof.Poly1305.blocksX86_64.pub
    Impl.Poly1305.X86_64.blocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

theorem blocks_verified :
    Verified X86_64.target Impl.Poly1305.X86_64.blocks (Spec.Poly1305.blocksContract X86_64.abi) :=
  Verified.of_correct VG.Proof.Poly1305.X86_64.blocks_ok VG.Proof.Poly1305.X86_64.blocks_ct (by
    sig_implies [Spec.Poly1305.blocksContract, Spec.Poly1305.blocksSig, Proof.Poly1305.blocksX86_64,
      X86_64.abi, X86_64.argRegs] [Proof.Poly1305.X86_64.blocksSat] using
      Proof.Poly1305.X86_64.blocksSat)

end VG.Proof.Poly1305.X86_64

end
