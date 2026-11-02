module

public import VerifiedGarbage.Impl.Poly1305.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
public import VerifiedGarbage.Spec.Poly1305
public import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Poly1305.Limbs64

/-!
# Poly1305 on RISC-V: absorbing a block

The arithmetic in radix `2⁶⁴` of `Proof/Poly1305/Limbs64.lean` (as on AArch64,
`Proof/Poly1305/AArch64/Radix64/Absorb.lean`), with the sums of
`Proof/Framework/RISCV64/Wide.lean`: `absorb_ok` says that absorbing a block
multiplies the accumulator plus the block by the clamped `r`, modulo `p`,
keeping its top word at most 4.
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.Poly1305.RISCV64
open VG.Proof.Poly1305.Limbs64
open VG.Spec.Poly1305 (P)

/-- The accumulator in `t0`–`t2`. -/
abbrev hv (s : State) : Nat := val3 s H0 H1 H2

/-- The key in the registers: `r0`, `r1 = 4 q` and `s1 = 5 q`, the clamped `r`
being `R`. -/
def Keys (R : Nat) (s : State) : Prop :=
  ∃ q, (s.gpr R0).toNat < 2 ^ 60 ∧ (s.gpr R1).toNat = 4 * q ∧ q < 2 ^ 58 ∧
    (s.gpr S1).toNat = 5 * q ∧ (s.gpr R0).toNat + 2 ^ 64 * (s.gpr R1).toNat = R

/-- The bound on the accumulator between blocks. -/
def Bounds (s : State) : Prop := (s.gpr H2).toNat ≤ 4

/-- The registers absorbing a block writes. -/
abbrev absorbRegs : List Reg := [H0, H1, H2, X0, X1, Y0, Y1, T1, T2]

/-- The little-endian doubleword at `off(b)`, as a number. -/
abbrev word (m : Mem) (p : Addr) (d : Nat) : Nat := (m.readW (p + BitVec.ofNat 64 d) 64).toNat

theorem Keys.of_regs {R : Nat} {s s' : State} (hk : Keys R s)
    (h : ∀ r ∈ [R0, R1, S1], s'.gpr r = s.gpr r) : Keys R s' := by
  simpa only [Keys, h R0 (by simp), h R1 (by simp), h S1 (by simp)] using hk

theorem Keeps.keys {rs : List Reg} {R : Nat} {s s' : State} (hk : Keys R s) (h : Keeps rs s s')
    (hr : R0 ∉ rs ∧ R1 ∉ rs ∧ S1 ∉ rs := by decide) : Keys R s' :=
  hk.of_regs fun r hm => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    exacts [h.1 _ hr.1, h.1 _ hr.2.1, h.1 _ hr.2.2]

/-! ## Adding the block -/

/-- `h2 += pad`. -/
def padI (pad : Bool) : List Instr := if pad then [.addi H2 H2 1] else []

theorem addBlock_eq (b : Reg) (off : Nat) (pad : Bool) : addBlock b off pad false =
    Impl.Words64.RISCV64.loadLE64 X0 T1 T2 b off ++
      (Impl.Words64.RISCV64.loadLE64 X1 T1 T2 b (off + 8) ++
      (Impl.Words.RISCV64.add3 H0 H1 H2 X0 X1 ++ padI pad)) := by
  simp only [addBlock, padI, List.append_assoc, Bool.false_eq_true, ite_false]

theorem addBlock_eq_wide (b : Reg) (off : Nat) (pad : Bool) : addBlock b off pad true =
    .load .d X0 b off :: .load .d X1 b (off + 8) ::
      (Impl.Words.RISCV64.add3 H0 H1 H2 X0 X1 ++ padI pad) := by
  simp only [addBlock, padI, ite_true, List.cons_append, List.nil_append]

theorem padI_ok (s : State) (pad : Bool) :
    WP isa (.block (padI pad)) s fun s' =>
      ((s.gpr H2).toNat + pad.toNat < 2 ^ 64 → (s'.gpr H2).toNat = (s.gpr H2).toNat + pad.toNat) ∧
      Keeps [H2] s s' := by
  cases pad
  · exact WP.block_nil ⟨fun _ => rfl, Keeps.refl _ _⟩
  · apply WP.of_runBlock
    simp only [padI, ite_true, runBlock_cons, runStep_some, runBlock_nil,
      exec_addi (show imm12 1 by decide), Option.some.injEq, exists_eq_left']
    refine ⟨fun h => ?_, (Keeps.refl [H2] s).write _ (by decide)⟩
    rw [RegUpd.gpr_write_self, BitVec.toNat_add, show (BitVec.ofInt 64 1).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt h

theorem upd3_keeps {s s' : State} {d t₁ t₂ : Reg} {v : BitVec 64} (h : Words64.Upd3 s s' d t₁ t₂ v) :
    Keeps [d, t₁, t₂] s s' :=
  ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact h.other r hr.1 hr.2.1 hr.2.2, h.mem, h.rd, h.wr, h.sp⟩

/-- A register write keeps everything else. -/
theorem upd_keeps {s s' : State} {d : Reg} {v : BitVec 64} (h : VG.RISCV64.Steps.Upd s s' d v) : Keeps [d] s s' :=
  ⟨fun r hr => h.other r (by simpa using hr), h.mem, h.rd, h.wr, h.sp⟩

/-- The sum and the pad, after the block's words are in `X0` and `X1`. -/
theorem addTail_ok (s : State) (b : Reg) (off : Nat) (pad : Bool) {s₂ : State}
    (x₀ : (s₂.gpr X0).toNat = word s.mem (s.gpr b) off)
    (x₁ : (s₂.gpr X1).toNat = word s.mem (s.gpr b) (off + 8)) (k₂ : Keeps [X0, X1, T1, T2] s s₂) :
    WP isa (.block (Impl.Words.RISCV64.add3 H0 H1 H2 X0 X1 ++ padI pad)) s₂ fun s' =>
      (hv s + (word s.mem (s.gpr b) off + 2 ^ 64 * word s.mem (s.gpr b) (off + 8) +
          2 ^ 128 * pad.toNat) < 2 ^ 192 →
        hv s' = hv s + (word s.mem (s.gpr b) off + 2 ^ 64 * word s.mem (s.gpr b) (off + 8) +
          2 ^ 128 * pad.toNat)) ∧
      Keeps [H0, H1, H2, X0, X1, T1, T2] s s' := by
  refine WP.block_append (WP.mono add3_ok fun s₃ ⟨e₃, k₃⟩ => ?_)
  refine WP.mono (padI_ok s₃ pad) fun s₄ ⟨e₄, k₄⟩ => ?_
  refine ⟨fun hlt => ?_, ((k₂.trans k₃).trans k₄).mono⟩
  have hv₂ : val3 s₂ H0 H1 H2 = hv s := by
    simp only [val3, hv, k₂.gpr' (r := H0), k₂.gpr' (r := H1), k₂.gpr' (r := H2)]
  rw [hv₂, x₀, x₁] at e₃
  have hp := Bool.toNat_le pad
  have w₀ := (s₃.gpr H0).isLt; have w₁ := (s₃.gpr H1).isLt
  have m₀ := (s.mem.readW (s.gpr b + BitVec.ofNat 64 off) 64).isLt
  have m₁ := (s.mem.readW (s.gpr b + BitVec.ofNat 64 (off + 8)) 64).isLt
  have hh := (s.gpr H0).isLt; have hh1 := (s.gpr H1).isLt
  rw [Nat.mod_eq_of_lt (by omega_using [hlt, hp])] at e₃
  have e₄ := e₄ (by simp only [val3, word, hv] at e₃ hlt; omega_using [e₃, hlt, hp, w₀, w₁])
  simp only [hv, val3, k₄.gpr' (r := H0), k₄.gpr' (r := H1), e₄]
  simp only [val3] at e₃
  have hvs : hv s = (s.gpr H0).toNat + 2 ^ 64 * (s.gpr H1).toNat + 2 ^ 128 * (s.gpr H2).toNat := rfl
  omega_using [e₃, hp, hvs]

theorem addBlock_ok (s : State) (b : Reg) (off : Nat) (pad : Bool) (wide : Bool) (ho : off + 15 < 2048)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 off) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 (off + 8)) 8)
    (hal : wide = true → (s.gpr b + BitVec.ofNat 64 off).toNat % 8 = 0)
    (hb : b ∉ absorbRegs := by decide) :
    WP isa (.block (addBlock b off pad wide)) s fun s' =>
      (hv s + (word s.mem (s.gpr b) off + 2 ^ 64 * word s.mem (s.gpr b) (off + 8) +
          2 ^ 128 * pad.toNat) < 2 ^ 192 →
        hv s' = hv s + (word s.mem (s.gpr b) off + 2 ^ 64 * word s.mem (s.gpr b) (off + 8) +
          2 ^ 128 * pad.toNat)) ∧
      Keeps [H0, H1, H2, X0, X1, T1, T2] s s' := by
  simp only [absorbRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩ := hb
  cases wide
  · rw [addBlock_eq]
    refine WP.block_append (WP.mono (Words64.loadLE64_ok (Ne.symm b3) (Ne.symm b7) (by decide)
      (Ne.symm b8) (by decide) (by decide) (by omega) h0) fun s₁ u₁ => ?_)
    have hb₁ : s₁.gpr b = s.gpr b := u₁.other b b3 b7 b8
    refine WP.block_append (WP.mono (Words64.loadLE64_ok (Ne.symm b4) (Ne.symm b7) (by decide)
      (Ne.symm b8) (by decide) (by decide) (by omega)
      (by rw [hb₁, u₁.rd, u₁.wr]; exact h8)) fun s₂ u₂ => ?_)
    exact addTail_ok s b off pad (by rw [u₂.other _ (by decide) (by decide) (by decide), u₁.gpr])
      (by rw [u₂.gpr, u₁.mem, hb₁]) ((upd3_keeps u₁).trans (upd3_keeps u₂)).mono
  · have a0 := hal rfl
    have a8 : (s.gpr b + BitVec.ofNat 64 (off + 8)).toNat % 8 = 0 := by
      rw [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (s.gpr b + BitVec.ofNat 64 off).isLt
      omega
    rw [addBlock_eq_wide]
    refine VG.RISCV64.Steps.wp_ld (a := s.gpr b + BitVec.ofNat 64 off) (by omega) rfl a0 h0 fun s₁ u₁ => ?_
    have hb₁ : s₁.gpr b = s.gpr b := u₁.other b b3
    refine VG.RISCV64.Steps.wp_ld (a := s.gpr b + BitVec.ofNat 64 (off + 8)) (by omega) (by rw [hb₁]) a8
      (by rw [u₁.rd, u₁.wr]; exact h8) fun s₂ u₂ => ?_
    exact addTail_ok s b off pad (by rw [u₂.other _ (by decide), u₁.gpr])
      (by rw [u₂.gpr, u₁.mem]) ((upd_keeps (d := X0) u₁).trans (upd_keeps (d := X1) u₂)).mono

/-! ## The products, folded -/

theorem notFour_bits : ∀ i : Fin 64, (BitVec.ofInt 64 (-4)).getLsbD i.val = decide (2 ≤ i.val) := by
  decide

/-- `andi` with `-4` clears the two low bits. -/
theorem andm4_toNat (x : BitVec 64) :
    (x &&& BitVec.ofInt 64 (-4)).toNat = x.toNat - x.toNat % 4 := by
  have e : x &&& BitVec.ofInt 64 (-4) = (x >>> 2) <<< 2 := by
    ext i hi
    have hb := notFour_bits ⟨i, hi⟩
    rw [BitVec.getLsbD_eq_getElem hi] at hb
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight, hb]
    by_cases h : i < 2
    · simp [h]
    · simp [h]
      rw [show 2 + (i - 2) = i by omega, BitVec.getLsbD_eq_getElem hi]
      simp; omega
  rw [e, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem and3_toNat' (x : BitVec 64) : (x &&& BitVec.ofInt 64 3).toNat = x.toNat % 4 := by
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 3).toNat = 2 ^ 2 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- The first four instructions of `fold`: `t mod 4` and `5 ⌊t / 4⌋`. -/
def foldA : List Instr :=
  [.logicImm .and H2 Y1 3, .logicImm .and T1 Y1 (-4), .shift .srl .d T2 Y1 2, .add T1 T1 T2]

theorem foldA_ok (s : State) :
    WP isa (.block foldA) s fun s' =>
      (s'.gpr H2).toNat = (s.gpr Y1).toNat % 4 ∧
      ((s.gpr Y1).toNat < 2 ^ 63 → (s'.gpr T1).toNat = 5 * ((s.gpr Y1).toNat / 4)) ∧
      Keeps [H2, T1, T2] s s' := by
  apply WP.of_runBlock
  simp only [foldA, runBlock_cons, runStep_some, runBlock_nil, exec_logicImm (show imm12 3 by decide),
    exec_logicImm (show imm12 (-4) by decide), exec_shift_d (show 2 < 64 by decide), exec_add,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun h => ?_, ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, and3_toNat']
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    rw [BitVec.toNat_add, andm4_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega_using [h]
  · exact ((((Keeps.refl [H2, T1, T2] s).write _ (by decide)).write _ (by decide)).write _
      (by decide)).write _ (by decide)

theorem mulSmall_ok (s : State) :
    WP isa (.block [.mul T2 H2 R0]) s fun s' =>
      ((s.gpr H2).toNat * (s.gpr R0).toNat < 2 ^ 64 →
        (s'.gpr T2).toNat = (s.gpr H2).toNat * (s.gpr R0).toNat) ∧ Keeps [T2] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mul, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun h => ?_, (Keeps.refl _ _).write _ (by decide)⟩
  rw [RegUpd.gpr_write_self, BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem mul_eq : products ++ combine ++ fold =
    Impl.Words.RISCV64.mulWide X0 X1 H0 R0 ++ (Impl.Words.RISCV64.mulWide Y0 Y1 H0 R1 ++
    (Impl.Words.RISCV64.mulAdd X0 X1 T1 T2 H1 S1 ++ (Impl.Words.RISCV64.mulAdd Y0 Y1 T1 T2 H1 R0 ++
    (Impl.Words.RISCV64.mulAddSmall Y0 Y1 T1 H2 S1 ++ (([.mul T2 H2 R0] : List Instr) ++
    (Impl.Words.RISCV64.add2 Y0 Y1 X1 T2 ++ (foldA ++
    Impl.Words.RISCV64.addW3 H0 H1 H2 X0 Y0 H2 T1))))))) := by
  simp only [products, combine, fold, foldA, List.append_assoc, List.cons_append, List.nil_append]

theorem mul_ok (s₁ : State) {q : Nat}
    (hr0 : (s₁.gpr R0).toNat < 2 ^ 60) (hr1 : (s₁.gpr R1).toNat = 4 * q) (hq : q < 2 ^ 58)
    (hs1 : (s₁.gpr S1).toNat = 5 * q) :
    WP isa (.block (products ++ combine ++ fold)) s₁ fun s' =>
      ((s₁.gpr H2).toNat ≤ 6 →
        hv s' % P = (hv s₁ * ((s₁.gpr R0).toNat + 2 ^ 64 * (s₁.gpr R1).toNat)) % P ∧
        (s'.gpr H2).toNat ≤ 4) ∧ Keeps absorbRegs s₁ s' := by
  rw [mul_eq]
  refine WP.block_append (WP.mono mulWide_ok fun s₂ ⟨e₂, k₂⟩ => ?_)
  refine WP.block_append (WP.mono mulWide_ok fun s₃ ⟨e₃, k₃⟩ => ?_)
  refine WP.block_append (WP.mono mulAdd_ok fun s₄ ⟨e₄, k₄⟩ => ?_)
  refine WP.block_append (WP.mono mulAdd_ok fun s₅ ⟨e₅, k₅⟩ => ?_)
  refine WP.block_append (WP.mono mulAddSmall_ok fun s₆ ⟨e₆, k₆⟩ => ?_)
  refine WP.block_append (WP.mono (mulSmall_ok s₆) fun s₇ ⟨e₇, k₇⟩ => ?_)
  refine WP.block_append (WP.mono add2_ok fun s₈ ⟨e₈, k₈⟩ => ?_)
  refine WP.block_append (WP.mono (foldA_ok s₈) fun s₉ ⟨f₁, f₂, k₉⟩ => ?_)
  refine WP.mono addW3_ok fun s₁₀ ⟨e₁₀, k₁₀⟩ => ?_
  refine ⟨fun a2 => ?_, (((((((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans
    k₈).trans k₉).trans k₁₀)).mono⟩
  have a0 := (s₁.gpr H0).isLt; have a1 := (s₁.gpr H1).isLt
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := absorb_bounds a0 a1 a2 hr0 hq
  -- x = h0 r0, y = h0 r1
  have k₂₃ := k₂.trans k₃
  rw [k₂.gpr' (r := H0), k₂.gpr' (r := R1), hr1] at e₃
  -- x += h1 s1
  rw [k₃.gpr' (r := X0), k₃.gpr' (r := X1), e₂, k₂₃.gpr' (r := H1), k₂₃.gpr' (r := S1), hs1,
    Nat.mod_eq_of_lt (by omega_using [b1, b2])] at e₄
  have k₂₄ := k₂₃.trans k₄
  -- y += h1 r0
  rw [k₄.gpr' (r := Y0), k₄.gpr' (r := Y1), e₃, k₂₄.gpr' (r := H1), k₂₄.gpr' (r := R0),
    Nat.mod_eq_of_lt (by omega_using [b3, b4])] at e₅
  have k₂₅ := k₂₄.trans k₅
  -- y += h2 s1
  rw [e₅, k₂₅.gpr' (r := H2), k₂₅.gpr' (r := S1), hs1, Nat.mod_eq_of_lt (by omega_using [b3, b4, b5])] at e₆
  have e₆ := e₆ b5
  have k₂₆ := k₂₅.trans k₆
  -- h2 r0
  rw [k₂₆.gpr' (r := H2), k₂₆.gpr' (r := R0)] at e₇
  have e₇ := e₇ (by omega_using [hr0, b6])
  -- the top word
  have x0 := (s₄.gpr X0).isLt; have x1 := (s₄.gpr X1).isLt
  have y0 := (s₆.gpr Y0).isLt; have y1 := (s₆.gpr Y1).isLt
  have r14 : s₇.gpr Y0 = s₆.gpr Y0 := k₇.gpr'
  have r15 : s₇.gpr Y1 = s₆.gpr Y1 := k₇.gpr'
  have r13 : s₇.gpr X1 = s₄.gpr X1 := ((k₅.trans k₆).trans k₇).gpr'
  rw [r14, r15, r13, e₇, Nat.mod_eq_of_lt (by omega_using [hr0, e₄, e₆, b1, b2, b3, b4, b5, b6])] at e₈
  have u0 := (s₈.gpr Y0).isLt
  have ht : (s₈.gpr Y1).toNat < 2 ^ 63 := by
    omega_using [hr0, e₄, e₆, b1, b2, b3, b4, b5, b6, e₈, u0]
  have f₂ := f₂ ht
  have hX0 : s₉.gpr X0 = s₄.gpr X0 := ((((k₅.trans k₆).trans k₇).trans k₈).trans k₉).gpr'
  have hY0 : s₉.gpr Y0 = s₈.gpr Y0 := k₉.gpr'
  simp only [val3] at e₁₀
  rw [hX0, hY0, f₁, f₂, Nat.mod_eq_of_lt (by omega_using [hr0, e₄, e₆, b1, b2, b3, b4, b5, b6, e₈, u0, x0])] at e₁₀
  have w0 := (s₁₀.gpr H0).isLt; have w1 := (s₁₀.gpr H1).isLt
  have hu : (s₈.gpr Y0).toNat + 2 ^ 64 * (((s₆.gpr Y0).toNat + (s₄.gpr X1).toNat) / 2 ^ 64) =
      (s₆.gpr Y0).toNat + (s₄.gpr X1).toNat := by
    omega_using [e₈, u0, y0, x1]
  have ht' : (s₈.gpr Y1).toNat = (s₆.gpr Y1).toNat + (s₁.gpr H2).toNat * (s₁.gpr R0).toNat +
      ((s₆.gpr Y0).toNat + (s₄.gpr X1).toNat) / 2 ^ 64 := by
    omega_using [e₈, hu, u0]
  rw [ht'] at e₁₀
  obtain ⟨m, hb⟩ := absorb_arith (q := q)
    (w0 := (s₁₀.gpr H0).toNat) (w1 := (s₁₀.gpr H1).toNat) (w2 := (s₁₀.gpr H2).toNat)
    (x0 := (s₄.gpr X0).toNat) (x1 := (s₄.gpr X1).toNat)
    (y0 := (s₆.gpr Y0).toNat) (y1 := (s₆.gpr Y1).toNat) (u0 := (s₈.gpr Y0).toNat)
    (c1 := ((s₆.gpr Y0).toNat + (s₄.gpr X1).toNat) / 2 ^ 64)
    a0 a1 a2 hr0 hq e₄ x0 e₆ hu u0 (by omega_using [e₁₀]) w0 w1
  refine ⟨?_, hb⟩
  rw [hv, val3, m, hr1]

theorem absorb_ok (s : State) (b : Reg) (off : Nat) (pad : Bool) (wide : Bool) {q : Nat}
    (hr0 : (s.gpr R0).toNat < 2 ^ 60) (hr1 : (s.gpr R1).toNat = 4 * q) (hq : q < 2 ^ 58)
    (hs1 : (s.gpr S1).toNat = 5 * q) (ho : off + 15 < 2048)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 off) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 (off + 8)) 8)
    (hal : wide = true → (s.gpr b + BitVec.ofNat 64 off).toNat % 8 = 0)
    (hb : b ∉ absorbRegs := by decide) :
    WP isa (.block (absorb b off pad wide)) s fun s' =>
      ((s.gpr H2).toNat ≤ 4 →
        hv s' % P = ((hv s + (word s.mem (s.gpr b) off + 2 ^ 64 * word s.mem (s.gpr b) (off + 8) +
          2 ^ 128 * pad.toNat)) * ((s.gpr R0).toNat + 2 ^ 64 * (s.gpr R1).toNat)) % P ∧
        (s'.gpr H2).toNat ≤ 4) ∧ Keeps absorbRegs s s' := by
  rw [show absorb b off pad wide = addBlock b off pad wide ++ (products ++ combine ++ fold) by
    simp only [absorb, List.append_assoc]]
  refine WP.block_append (WP.mono (addBlock_ok s b off pad wide ho h0 h8 hal hb) fun s₁ ⟨e₁, k₁⟩ => ?_)
  have r0₁ : s₁.gpr R0 = s.gpr R0 := k₁.gpr'
  have r1₁ : s₁.gpr R1 = s.gpr R1 := k₁.gpr'
  have s1₁ : s₁.gpr S1 = s.gpr S1 := k₁.gpr'
  refine WP.mono (mul_ok s₁ (by rw [r0₁]; exact hr0) (by rw [r1₁]; exact hr1) hq (by rw [s1₁]; exact hs1))
    fun s' ⟨hm, k⟩ => ⟨fun hh2 => ?_, (k₁.trans k).mono⟩
  have hp1 : pad.toNat ≤ 1 := Bool.toNat_le pad
  have hw0 := (s.mem.readW (s.gpr b + BitVec.ofNat 64 off) 64).isLt
  have hw8 := (s.mem.readW (s.gpr b + BitVec.ofNat 64 (off + 8)) 64).isLt
  have g0 := (s.gpr H0).isLt; have g1 := (s.gpr H1).isLt
  have e₁ := e₁ (by simp only [word, hv, val3]; omega_using [hh2, hp1, hw0, hw8, g0, g1])
  have a0 := (s₁.gpr H0).isLt; have a1 := (s₁.gpr H1).isLt
  obtain ⟨hv', hb'⟩ := hm (add_arith g0 g1 hh2 hw0 hw8 hp1 e₁ a0 a1)
  refine ⟨?_, hb'⟩
  rw [hv', show hv s₁ = _ from e₁, r0₁, r1₁]

end VG.Proof.Poly1305.RISCV64
