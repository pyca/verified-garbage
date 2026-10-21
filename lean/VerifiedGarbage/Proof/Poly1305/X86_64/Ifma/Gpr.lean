module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Vec
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.VKeep
public import VerifiedGarbage.Proof.Poly1305.X86_64.Setup
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Poly1305 on x86-64 with AVX-512 IFMA: the integer instructions

The blocks of integer instructions between the vector ones: they leave the
vector registers, MXCSR and the regions as they were (`VKeep`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Ifma
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Proof.Poly1305.X86_64 (off off_eq M0 M1 Keeps ea_at se1 se3)
open VG.Proof.Poly1305.X86_64.Avx2 (vec vec_gpr vec_mem vec_rd vec_wr)
open VG.Proof.Poly1305.X86_64.Avx512 (VKeep)

theorem se32 : BitVec.signExtend 64 (BitVec.ofNat 32 32) = 32 := by decide

set_option simprocs false in
theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 minBlocks))]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ VKeep s s' ∧
      s'.cf = some (decide ((s.gpr .rdx).toNat < 32)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', minBlocks, se32]
  exact ⟨trivial, trivial, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem loadR_ok (s : State) (r₁ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 24) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 32) 8) (w₁ : InRegions s.wr (off (s.gpr .rdi) 104) 8)
    (w₂ : InRegions s.wr (off (s.gpr .rdi) 112) 8) :
    WP isa (.block loadR) s fun s' =>
      s'.gpr .r10 = s.mem.readW (off (s.gpr .rdi) 24) 64 &&& M0 ∧
      s'.gpr .r11 = s.mem.readW (off (s.gpr .rdi) 32) 64 &&& M1 ∧ s'.gpr .r8 = 0xfffffffffff ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.mem = (s.mem.writeW (off (s.gpr .rdi) 104) (0xfffffffffff : BitVec 64)).writeW
        (off (s.gpr .rdi) 112) (0x10000000000 : BitVec 64) ∧ VKeep s s' := by
  apply WP.of_runBlock
  simp only [off] at r₁ r₂ w₁ w₂
  simp only [reduceCtorEq, ↓reduceIte, loadR, mMask, mPad, runBlock_cons, runStep_some, runBlock_nil,
    exec, ea_at, readSrc, execAlu, arithFlags, State.load64, State.store64, State.setReg, State.setFlags,
    r₁, r₂, w₁, w₂, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  finish_gpr8

/-- The integer part of `splitRg`: the limbs of `r` into `rax`, `rcx`, `r9`. -/
def splitG : List Instr :=
  [.mov .rax (.reg .r10), .alu .and .rax (.reg .r8),
   .mov .rcx (.reg .r11), .shift .shl .rcx 20, .mov .r9 (.reg .r10), .shift .shr .r9 44,
   .alu .or .rcx (.reg .r9), .alu .and .rcx (.reg .r8),
   .mov .r9 (.reg .r11), .shift .shr .r9 24]

theorem splitRg_eq : splitRg = splitG ++ bc3 := rfl

set_option simprocs false in
theorem splitG_ok (s : State) :
    WP isa (.block splitG) s fun s' =>
      s'.gpr .rax = s.gpr .r10 &&& s.gpr .r8 ∧
      s'.gpr .rcx = (s.gpr .r11 <<< 20 ||| s.gpr .r10 >>> 44) &&& s.gpr .r8 ∧
      s'.gpr .r9 = s.gpr .r11 >>> 24 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [splitG, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, execShift, arithFlags, State.setReg, State.setFlags, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  finish_gpr8

/-- The integer part of `loadH`: the limbs of the accumulator into `rax`,
`rcx`, `r9`. -/
def loadHG : List Instr := [
  .mov .r9 (.mem (at_ .rdi 16)), .shift .shl .r9 40, .mov .rcx (.mem (at_ .rdi 8)), .shift .shr .rcx 24,
  .alu .or .r9 (.reg .rcx),
  .mov .rcx (.mem (at_ .rdi 8)), .shift .shl .rcx 20, .mov .rax (.mem (at_ .rdi 0)), .shift .shr .rax 44,
  .alu .or .rcx (.reg .rax), .alu .and .rcx (.reg .r8),
  .mov .rax (.mem (at_ .rdi 0)), .alu .and .rax (.reg .r8)]

theorem loadH_eq : loadH = loadHG ++
    ([.vop (.vmovq (hreg 0) .rax), .vop (.vmovq (hreg 1) .rcx), .vop (.vmovq (hreg 2) .r9)] : List Instr) := rfl

set_option simprocs false in
theorem loadHG_ok (s : State) (r₀ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 0) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 8) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 16) 8) :
    WP isa (.block loadHG) s fun s' =>
      s'.gpr .rax = s.mem.readW (off (s.gpr .rdi) 0) 64 &&& s.gpr .r8 ∧
      s'.gpr .rcx = (s.mem.readW (off (s.gpr .rdi) 8) 64 <<< 20 |||
        s.mem.readW (off (s.gpr .rdi) 0) 64 >>> 44) &&& s.gpr .r8 ∧
      s'.gpr .r9 = s.mem.readW (off (s.gpr .rdi) 16) 64 <<< 40 ||| s.mem.readW (off (s.gpr .rdi) 8) 64 >>> 24 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VKeep s s' := by
  apply WP.of_runBlock
  simp only [off] at r₀ r₁ r₂
  simp (config := {decide := true}) only [loadHG, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, execAlu, execShift, arithFlags, State.load64, State.setReg, State.setFlags,
    r₀, r₁, r₂, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  finish_gpr8

/-- The integer part of `loadY`: the limbs at `rdi + d`, `d + 8`, `d + 16`
into `rax`, `rcx`, `r9`. -/
def loadYG (m : Nat → MemOp) : List Instr :=
  [.mov .rax (.mem (m 0)), .mov .rcx (.mem (m 1)), .mov .r9 (.mem (m 2))]

theorem loadY_eq (m : Nat → MemOp) : loadY m = loadYG m ++ bc3 := rfl

theorem loadYG_ok (s : State) (d : Nat)
    (r : ∀ i < 3, InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) (d + 8 * i)) 8) :
    WP isa (.block (loadYG fun i => at_ .rdi (d + 8 * i))) s fun s' =>
      (∀ i < 3, s'.gpr (lg i) = s.mem.readW (off (s.gpr .rdi) (d + 8 * i)) 64) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VKeep s s' := by
  have r₀ := r 0 (by decide)
  have r₁ := r 1 (by decide)
  have r₂ := r 2 (by decide)
  apply WP.of_runBlock
  simp only [off] at r₀ r₁ r₂
  simp only [reduceCtorEq, ↓reduceIte, loadYG, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, State.load64, State.setReg, r₀, r₁, r₂, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi => ?_, ?_⟩
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl
  · finish_gpr8

/-- Quadword 0 of the limbs of `H`, stored at `rdi + d`, `d + 8`, `d + 16`. -/
def hMem (m : Mem) (p : Addr) (d : Nat) (x : XReg → BitVec 128) : Mem :=
  ((m.writeW (off p d) ((x (hreg 0)).extractLsb' 0 64)).writeW (off p (d + 8))
    ((x (hreg 1)).extractLsb' 0 64)).writeW (off p (d + 16)) ((x (hreg 2)).extractLsb' 0 64)

theorem storeH_ok (s : State) (d : Nat) (w : ∀ i < 3, InRegions s.wr (off (s.gpr .rdi) (d + 8 * i)) 8) :
    WP isa (.block (storeH fun i => at_ .rdi (d + 8 * i))) s fun s' =>
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = hMem s.mem (s.gpr .rdi) d s.xmm ∧ VKeep s s' := by
  have w₀ := w 0 (by decide)
  have w₁ := w 1 (by decide)
  have w₂ := w 2 (by decide)
  apply WP.of_runBlock
  simp only [off] at w₀ w₁ w₂
  simp only [reduceCtorEq, ↓reduceIte, storeH, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    State.store64, State.setReg, w₀, w₁, w₂, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => by simp [hr], ?_, ?_⟩
  · simp only [hMem, off]; rfl
  · finish_gpr8

/-! ## The accumulator to words -/

def twA : List Instr := [
  .movqR .r11 (hreg 0), .movqR .rax (hreg 1), .movqR .rcx (hreg 2),
  .mov .rbx (.reg .rax), .shift .shl .rax 44, .shift .shr .rbx 20,
  .mov .rbp (.reg .rcx), .shift .shl .rcx 24, .shift .shr .rbp 40]
def twB : List Instr := [.alu .add .r11 (.reg .rax), .alu .adc .rbx (.reg .rcx), .alu .adc .rbp (.imm 0)]
def twC : List Instr := [
  .mov .rax (.reg .rbp), .alu .and .rbp (.imm 3), .shift .shr .rax 2,
  .mov .rcx (.reg .rax), .shift .shl .rcx 2, .alu .add .rax (.reg .rcx)]

theorem toWords_eq : toWords = twA ++ (twB ++ (twC ++
    ([.alu .add .r11 (.reg .rax), .alu .adc .rbx (.imm 0), .alu .adc .rbp (.imm 0)] : List Instr))) := rfl

/-- Limb `i` in quadword 0 of `H`. -/
abbrev h0w (s : State) (i : Nat) : BitVec 64 := (s.xmm (hreg i)).extractLsb' 0 64

/-- What a block of integer instructions keeps, but some registers. -/
structure GKeep (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  xmm : s'.xmm = s.xmm
  mxcsr : s'.mxcsr = s.mxcsr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem GKeep.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : GKeep rs s₁ s₂) (h₂ : GKeep rs s₂ s₃) :
    GKeep rs s₁ s₃ :=
  ⟨fun r hr => by rw [h₂.gpr r hr, h₁.gpr r hr], h₂.mem.trans h₁.mem, h₂.xmm.trans h₁.xmm,
    h₂.mxcsr.trans h₁.mxcsr, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

abbrev twRegs : List Reg := [.r11, .rax, .rbx, .rcx, .rbp]

set_option simprocs false in
theorem twA_ok (s : State) :
    WP isa (.block twA) s fun s' =>
      s'.gpr .r11 = h0w s 0 ∧ s'.gpr .rax = h0w s 1 <<< 44 ∧ s'.gpr .rbx = h0w s 1 >>> 20 ∧
      s'.gpr .rcx = h0w s 2 <<< 24 ∧ s'.gpr .rbp = h0w s 2 >>> 40 ∧ GKeep twRegs s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [twA, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execShift, State.setReg, State.setFlags, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem twB_ok (s : State) :
    WP isa (.block twB) s fun s' =>
      ((s.gpr .r11).toNat + (s.gpr .rax).toNat + 2 ^ 64 * ((s.gpr .rbx).toNat + (s.gpr .rcx).toNat) +
          2 ^ 128 * (s.gpr .rbp).toNat < 2 ^ 192 →
        (s'.gpr .r11).toNat + 2 ^ 64 * (s'.gpr .rbx).toNat + 2 ^ 128 * (s'.gpr .rbp).toNat =
          (s.gpr .r11).toNat + (s.gpr .rax).toNat + 2 ^ 64 * ((s.gpr .rbx).toNat + (s.gpr .rcx).toNat) +
            2 ^ 128 * (s.gpr .rbp).toNat) ∧ GKeep twRegs s s' := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, twB, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', VG.Proof.Poly1305.X86_64.se0]
  refine ⟨fun h => ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩⟩
  · have hz : (0 : BitVec 64).toNat = 0 := rfl
    rw [VG.Proof.Poly1305.Limbs64.add3_toNat _ _ _ _ _ _ (by rw [hz]; omega_using [h]), hz]
    omega_using []
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.2.1, hr.2.2.2.2, ite_false]

set_option simprocs false in
theorem twC_ok (s : State) :
    WP isa (.block twC) s fun s' =>
      s'.gpr .rbp = s.gpr .rbp &&& 3 ∧ s'.gpr .rax = (s.gpr .rbp >>> 2) + (s.gpr .rbp >>> 2) <<< 2 ∧
      s'.gpr .r11 = s.gpr .r11 ∧ s'.gpr .rbx = s.gpr .rbx ∧ GKeep twRegs s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [twC, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, execShift, arithFlags, State.setReg, State.setFlags, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, ite_false, se3]
  refine ⟨trivial, trivial, trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- Adding `rax` into `r11, rbx, rbp`, with carries (`addLow_ok`, keeping
the vector registers). -/
theorem twD_ok (s : State) :
    WP isa (.block [.alu .add .r11 (.reg .rax), .alu .adc .rbx (.imm 0), .alu .adc .rbp (.imm 0)]) s
      fun s' =>
      ((s.gpr .r11).toNat + (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rbx).toNat +
          2 ^ 128 * (s.gpr .rbp).toNat < 2 ^ 192 →
        (s'.gpr .r11).toNat + 2 ^ 64 * (s'.gpr .rbx).toNat + 2 ^ 128 * (s'.gpr .rbp).toNat =
          (s.gpr .r11).toNat + (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rbx).toNat +
            2 ^ 128 * (s.gpr .rbp).toNat) ∧ GKeep twRegs s s' := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', VG.Proof.Poly1305.X86_64.se0]
  refine ⟨fun h => ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩⟩
  · have hz : (0 : BitVec 64).toNat = 0 := rfl
    rw [VG.Proof.Poly1305.Limbs64.add3_toNat _ _ _ _ _ _ (by rw [hz]; omega_using [h]), hz]
    omega_using []
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.2.1, hr.2.2.2.2, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat,
      Nat.zero_mod, Nat.add_zero, ite_false]

/-- The value of quadword 0 of `H`, from its limbs. -/
def h0val (s : State) : Nat := (h0w s 0).toNat + 2 ^ 44 * (h0w s 1).toNat + 2 ^ 88 * (h0w s 2).toNat

/-- `toWords`: the accumulator, below `2¹³⁴`, as words `r11, rbx, rbp` with
the same value modulo `p` and `rbp ≤ 4`. -/
theorem toWords_ok (s : State) :
    WP isa (.block toWords) s fun s' =>
      ((∀ i < 3, (h0w s i).toNat ≤ 2 ^ 45) →
        VG.Proof.Poly1305.X86_64.hval s' % Spec.Poly1305.P = h0val s % Spec.Poly1305.P ∧
        (s'.gpr .rbp).toNat ≤ 4) ∧ GKeep twRegs s s' := by
  rw [toWords_eq]
  refine WP.block_append (WP.mono (twA_ok s) fun s₁ ⟨a1, a2, a3, a4, a5, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (twB_ok s₁) fun s₂ ⟨b, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (twC_ok s₂) fun s₃ ⟨c1, c2, r11₃, rbx₃, k₃⟩ => ?_)
  refine WP.mono (twD_ok s₃) fun s₄ ⟨d, k₄⟩ => ⟨fun hb => ?_, (k₁.trans k₂).trans (k₃.trans k₄)⟩
  · have b0 := hb 0 (by decide)
    have b1 := hb 1 (by decide)
    have b2 := hb 2 (by decide)
    -- The words of `h0val`, before the bits from `2¹³⁰` on are folded.
    have e1 : (s₁.gpr .rax).toNat = (h0w s 1).toNat * 2 ^ 44 % 2 ^ 64 := by
      rw [a2, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have e2 : (s₁.gpr .rbx).toNat = (h0w s 1).toNat / 2 ^ 20 := by
      rw [a3, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have e3 : (s₁.gpr .rcx).toNat = (h0w s 2).toNat * 2 ^ 24 % 2 ^ 64 := by
      rw [a4, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have e4 : (s₁.gpr .rbp).toNat = (h0w s 2).toNat / 2 ^ 40 := by
      rw [a5, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have e0 : (s₁.gpr .r11).toNat = (h0w s 0).toNat := by rw [a1]
    have W := b (by rw [e0, e1, e2, e3, e4]; omega)
    rw [e0, e1, e2, e3, e4] at W
    -- The fold.
    have t3 : (s₃.gpr .rbp).toNat = (s₂.gpr .rbp).toNat % 4 := by
      rw [c1, VG.Proof.Poly1305.Limbs64.and3_toNat]
    have t2 : (s₃.gpr .rax).toNat = 5 * ((s₂.gpr .rbp).toNat / 4) := by
      have hl := (s₂.gpr .rbp).isLt
      rw [c2, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow]
      omega
    have g0 := (s₂.gpr .r11).isLt
    have g1 := (s₂.gpr .rbx).isLt
    have D := d (by rw [t2, t3, r11₃, rbx₃]; omega)
    rw [t2, t3, r11₃, rbx₃] at D
    have hP : Spec.Poly1305.P = 2 ^ 130 - 5 := rfl
    have key : VG.Proof.Poly1305.X86_64.hval s₄ + Spec.Poly1305.P * ((s₂.gpr .rbp).toNat / 4) = h0val s := by
      simp only [VG.Proof.Poly1305.X86_64.hval, h0val]
      rw [D, hP]
      omega
    refine ⟨by rw [← key, Nat.add_mul_mod_self_left], ?_⟩
    have := (s₄.gpr .r11).isLt
    have := (s₄.gpr .rbx).isLt
    omega

set_option simprocs false in
theorem movR9_ok (s : State) :
    WP isa (.block [.mov .r9 (.reg .rdx)]) s fun s' =>
      s'.gpr .r9 = s.gpr .rdx ∧ (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.setReg, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp [hr], trivial, trivial, trivial, trivial⟩

set_option simprocs false in
theorem fin3_ok (s : State) :
    WP isa (.block [.mov .rdx (.reg .r9), .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rsi + 128 ∧ s'.gpr .rdx = s.gpr .r9 &&& 7 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, ite_true,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', Avx512.se7, Avx512.se128]
  finish_gpr8

set_option simprocs false in
theorem vzu_ok (s : State) :
    WP isa (.block [.vop .vzeroupper]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ s'.mxcsr = s.mxcsr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.Poly1305.X86_64.Ifma
