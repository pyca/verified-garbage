module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Poly1305.Radix26
public import VerifiedGarbage.Impl.Poly1305.PPC64LE
import VerifiedGarbage.Proof.Framework.Omega
import all Init.Data.Nat.Bitwise.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Poly1305 on PPC64LE: the steps of the code

Each lemma runs a few instructions symbolically and states their effect on the
numbers in the registers, unconditionally (modulo `2⁶⁴` where the code wraps),
as AArch64's do (`Proof/Poly1305/AArch64/Blocks.lean`); the arithmetic is
`Proof/Poly1305/Radix26.lean`'s.
-/

@[expose] public section

namespace VG.Proof.Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.Poly1305.PPC64LE
open VG.Proof.Poly1305.Radix26

/-- Two states agree except on the registers `rs`, in memory and regions. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.gpr' {rs : List Reg} {s s' : State} (h : Keeps rs s s') {r : Reg}
    (hr : r ∉ rs := by decide) : s'.gpr r = s.gpr r := h.1 r hr

theorem Keeps.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keeps rs s₁ s₂)
    (h₂ : Keeps rs' s₂ s₃) : Keeps (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1],
   h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : Keeps rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : Keeps rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem not_mem2 {a b c : Reg} (h₁ : a ≠ b) (h₂ : a ≠ c) : a ∉ [b, c] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h₁, h₂⟩

theorem Keeps.refl (rs : List Reg) (s : State) : Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The value of a register, as a number. -/
abbrev v (s : State) (r : Reg) : Nat := (s.gpr r).toNat

theorem write_gpr (s : State) (d : Reg) (x : BitVec 64) (r : Reg) :
    (s.write d x).gpr r = if r = d then x else s.gpr r := rfl

/-! ## Numbers -/

/-- The mask `2²⁶ - 1`. -/
abbrev M26 : BitVec 64 := 0x3ffffff

theorem and_mask (a : BitVec 64) : (a &&& M26).toNat = a.toNat % 2 ^ 26 := by
  rw [BitVec.toNat_and, show M26.toNat = 2 ^ 26 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem lsr_toNat (a : BitVec 64) (n : Nat) : (a >>> n).toNat = a.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem lsl_toNat (a : BitVec 64) (n : Nat) : (a <<< n).toNat = a.toNat * 2 ^ n % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem add_toNat (a b : BitVec 64) : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 :=
  BitVec.toNat_add a b

theorem mul_toNat (a b : BitVec 64) : (a * b).toNat = a.toNat * b.toNat % 2 ^ 64 :=
  BitVec.toNat_mul a b

theorem sub_toNat (a b : BitVec 64) : (a - b).toNat = (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 :=
  BitVec.toNat_sub a b

theorem ofNat_toNat5 : (BitVec.ofNat 64 5).toNat = 5 := rfl
theorem ofNat_toNat1 : (BitVec.ofNat 64 1).toNat = 1 := rfl

/-- `lis` of `0x3ff` then `ori` of `0xffff`: `2²⁶ - 1`. -/
theorem mask_val :
    ((0x3ff#16 ++ (0 : BitVec 16)).signExtend 64 ||| (0xffff#16).setWidth 64) = M26 := by
  decide

/-- `lis` of `0x100`: `2²⁴`. -/
theorem pad_val : ((0x100#16 ++ (0 : BitVec 16)).signExtend 64) = BitVec.ofNat 64 (2 ^ 24) := by
  decide

set_option simprocs false in
/-- `2²⁶ - 1` into `r20`. -/
theorem mask_ok (s : State) :
    WP isa (.block mask) s fun s' => s'.gpr .r20 = M26 ∧ Keeps [.r20] s s' := by
  apply WP.of_runBlock
  simp only [mask, runBlock_cons, runStep_some, runBlock_nil, exec_lis, exec_ori, write_gpr,
    Option.some.injEq, exists_eq_left', ite_true]
  refine ⟨mask_val, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [write_gpr, hr, ite_false]

set_option simprocs false in
/-- The limbs of `lo + 2⁶⁴ hi` (in `r18, r19`) into `r12, r14, …, r17`. -/
theorem split_ok (s : State) (hm : s.gpr .r20 = M26) :
    WP isa (.block split) s fun s' =>
      v s' .r12 = lim (v s .r18 + 2 ^ 64 * v s .r19) 0 ∧
      v s' .r14 = lim (v s .r18 + 2 ^ 64 * v s .r19) 1 ∧
      v s' .r15 = lim (v s .r18 + 2 ^ 64 * v s .r19) 2 ∧
      v s' .r16 = lim (v s .r18 + 2 ^ 64 * v s .r19) 3 ∧
      v s' .r17 = lim (v s .r18 + 2 ^ 64 * v s .r19) 4 ∧
      Keeps [.r12, .r14, .r15, .r16, .r17, .r0] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [split, runBlock_cons, runStep_some, runBlock_nil,
    exec_logic, exec_lsr_d (show 26 < 64 by decide), exec_lsr_d (show 52 < 64 by decide),
    exec_lsr_d (show 14 < 64 by decide), exec_lsr_d (show 40 < 64 by decide),
    exec_lsl (show 12 < 64 by decide), exec_add, v, write_gpr, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  obtain ⟨a0, a1, a2, a3, a4⟩ := split_arith (v s .r18) (v s .r19) (s.gpr .r18).isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [hm, and_mask, ← a0]
  · rw [hm, and_mask, lsr_toNat, ← a1]
  · rw [hm, and_mask, add_toNat, lsr_toNat, lsl_toNat, ← a2]
  · rw [hm, and_mask, lsr_toNat, ← a3]
  · rw [lsr_toNat, ← a4]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.2.2.2.2.1, hr.2.2.2.1, hr.2.2.1, hr.2.2.2.2.2, hr.2.1, hr.1, ite_false]

/-! ## Sums of products -/

/-- The 32-bit word at `[r3 + off]`, as a number. -/
abbrev word (s : State) (off : Nat) : Nat := (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 off) 32).toNat

theorem lwz_toNat (m : Mem) (a : Addr) : ((m.readW a 32).setWidth 64).toNat = (m.readW a 32).toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (m.readW a 32).isLt (by decide))]

set_option simprocs false in
/-- `d = h · c`, the coefficient `c` loaded into `r18`. -/
theorem mul1_ok (s : State) {d h : Reg} {off : Nat} (hh : h ≠ Reg.r18)
    (ho : off < 2 ^ 15) (hin : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 off) 4) :
    WP isa (.block [.load .w .r18 .r3 off, .mul d h .r18]) s fun s' =>
      v s' d = v s h * word s off % 2 ^ 64 ∧ Keeps [.r18, d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_w (by decide) ho hin, exec_mul, v,
    word, write_gpr, ite_true, Option.some.injEq, exists_eq_left', hh, ite_false]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [mul_toNat, lwz_toNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2, ite_false]

set_option simprocs false in
/-- `d += h · c`, the coefficient `c` loaded into `r18`, the product computed there. -/
theorem mac_ok (s : State) {d h : Reg} {off : Nat} (hh : h ≠ Reg.r18)
    (hd' : d ≠ Reg.r18) (ho : off < 2 ^ 15)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 off) 4) :
    WP isa (.block (mac d h off)) s fun s' =>
      v s' d = (v s d + v s h * word s off) % 2 ^ 64 ∧ Keeps [.r18, d] s s' := by
  apply WP.of_runBlock
  simp only [mac, runBlock_cons, runStep_some, runBlock_nil, exec_load_w (by decide) ho hin, exec_mul,
    exec_add, v, word, write_gpr, ite_true, Option.some.injEq, exists_eq_left', hh, hd', ite_false]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [add_toNat, mul_toNat, lwz_toNat, Nat.mul_comm (s.gpr h).toNat, Nat.add_mod_mod]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2, ite_false]

/-- A chain of `mac`s. -/
theorem macs_ok {d : Reg} (L : List (Reg × Nat)) (s : State) (hd : Reg.r18 ≠ d) (hd0 : Reg.r3 ≠ d)
    (hL : ∀ p ∈ L, p.1 ≠ Reg.r18 ∧ p.1 ≠ d ∧ p.2 < 2 ^ 15 ∧
      InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 p.2) 4) :
    WP isa (.block (L.flatMap fun p => mac d p.1 p.2)) s fun s' =>
      v s' d = (v s d + (L.map fun p => v s p.1 * word s p.2).sum) % 2 ^ 64 ∧ Keeps [.r18, d] s s' := by
  induction L generalizing s with
  | nil =>
    refine WP.block_nil ⟨?_, Keeps.refl _ _⟩
    simp only [List.map_nil, List.sum_nil, Nat.add_zero]
    exact (Nat.mod_eq_of_lt (s.gpr d).isLt).symm
  | cons p L ih =>
    obtain ⟨h1, h2, h3, h4⟩ := hL p List.mem_cons_self
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (mac_ok s h1 (Ne.symm hd) h3 h4) fun s₁ ⟨e₁, k₁⟩ => ?_)
    have x0₁ : s₁.gpr .r3 = s.gpr .r3 := k₁.1 _ (not_mem2 (by decide) hd0)
    have hL' : ∀ q ∈ L, q.1 ≠ Reg.r18 ∧ q.1 ≠ d ∧ q.2 < 2 ^ 15 ∧
        InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r3 + BitVec.ofNat 64 q.2) 4 := by
      intro q hq
      obtain ⟨g1, g2, g3, g4⟩ := hL q (List.mem_cons_of_mem _ hq)
      exact ⟨g1, g2, g3, by rw [k₁.2.2.1, k₁.2.2.2, x0₁]; exact g4⟩
    refine WP.mono (ih s₁ hL') fun s₂ ⟨e₂, k₂⟩ => ⟨?_, (k₁.trans k₂).mono (by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, true_or, or_true, imp_self, implies_true, and_self])⟩
    have hw : (L.map fun q => v s₁ q.1 * word s₁ q.2) = (L.map fun q => v s q.1 * word s q.2) := by
      refine List.map_congr_left fun q hq => ?_
      obtain ⟨g1, g2, -, -⟩ := hL q (List.mem_cons_of_mem _ hq)
      simp only [v, word, x0₁, k₁.2.1, k₁.1 q.1 (not_mem2 g1 g2)]
    rw [e₂, hw, e₁, List.map_cons, List.sum_cons]
    omega_using []

theorem dsum_facts : ∀ k < 5, Reg.r18 ≠ D.getD k .r12 ∧ Reg.r3 ≠ D.getD k .r12 ∧
    coef k 0 < 2 ^ 15 ∧ 72 ≤ coef k 0 ∧ coef k 0 + 4 ≤ 108 ∧
    ∀ i < 4, H.getD (i + 1) .r7 ≠ Reg.r18 ∧ H.getD (i + 1) .r7 ≠ D.getD k .r12 ∧
      coef k (i + 1) < 2 ^ 15 ∧ 72 ≤ coef k (i + 1) ∧ coef k (i + 1) + 4 ≤ 108 := by
  decide

/-- `dk = Σ hi · coef k i`. -/
theorem dsum_ok (s : State) {k : Nat} (hk : k < 5)
    (hc : ∀ off, 72 ≤ off → off + 4 ≤ 108 → InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 off) 4) :
    WP isa (.block (dsum k)) s fun s' =>
      v s' (D.getD k .r12) = (v s .r7 * word s (coef k 0) +
        ((List.range 4).map fun i => v s (H.getD (i + 1) .r7) * word s (coef k (i + 1))).sum) % 2 ^ 64 ∧
      Keeps [.r18, D.getD k .r12] s s' := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := dsum_facts k hk
  rw [dsum, show ((List.range 4).flatMap fun i => mac (D.getD k .r12) (H.getD (i + 1) .r7) (coef k (i + 1))) =
      (((List.range 4).map fun i => (H.getD (i + 1) .r7, coef k (i + 1))).flatMap fun p =>
        mac (D.getD k .r12) p.1 p.2) by rw [List.flatMap_map]]
  refine WP.block_append (WP.mono (mul1_ok s (by decide) f3 (hc _ f4 f5)) fun s₁ ⟨e₁, k₁⟩ => ?_)
  have x0₁ : s₁.gpr .r3 = s.gpr .r3 := k₁.1 _ (not_mem2 (by decide) f2)
  have hL : ∀ p ∈ ((List.range 4).map fun i => (H.getD (i + 1) .r7, coef k (i + 1))),
      p.1 ≠ Reg.r18 ∧ p.1 ≠ D.getD k .r12 ∧ p.2 < 2 ^ 15 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r3 + BitVec.ofNat 64 p.2) 4 := by
    intro p hp
    simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    obtain ⟨g1, g2, g3, g4, g5⟩ := f6 i hi
    exact ⟨g1, g2, g3, by rw [k₁.2.2.1, k₁.2.2.2, x0₁]; exact hc _ g4 g5⟩
  refine WP.mono (macs_ok _ s₁ f1 f2 hL) fun s₂ ⟨e₂, k₂⟩ => ⟨?_, (k₁.trans k₂).mono (by simp only [List.getD_eq_getElem?_getD, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, true_or, or_true, imp_self, implies_true, and_self])⟩
  have hw : (((List.range 4).map fun i => (H.getD (i + 1) .r7, coef k (i + 1))).map fun p =>
      v s₁ p.1 * word s₁ p.2) = ((List.range 4).map fun i => v s (H.getD (i + 1) .r7) * word s (coef k (i + 1))) := by
    rw [List.map_map]
    refine List.map_congr_left fun i hi => ?_
    obtain ⟨g1, g2, -⟩ := f6 i (List.mem_range.mp hi)
    simp only [Function.comp_apply, v, word, x0₁, k₁.2.1, k₁.1 _ (not_mem2 g1 g2)]
  rw [e₂, hw, e₁, Nat.mod_add_mod]

/-! ## Carries, reduction and packing -/

set_option simprocs false in
/-- The carries of `absorb`, from `d0, …, d4` (in `r12`–`r17`) to the new limbs (in `r7`–`r11`). -/
theorem carry_ok (s : State) (hm : s.gpr .r20 = M26) :
    WP isa (.block carry) s fun s' =>
      (v s .r12 < 2 ^ 60 → v s .r14 < 2 ^ 60 → v s .r15 < 2 ^ 60 → v s .r16 < 2 ^ 60 →
        v s .r17 < 2 ^ 60 →
        val5 (v s' .r7) (v s' .r8) (v s' .r9) (v s' .r10) (v s' .r11) % Spec.Poly1305.P =
          val5 (v s .r12) (v s .r14) (v s .r15) (v s .r16) (v s .r17) % Spec.Poly1305.P ∧
        v s' .r7 < 2 ^ 26 ∧ v s' .r8 < 2 ^ 27 ∧ v s' .r9 < 2 ^ 26 ∧ v s' .r10 < 2 ^ 26 ∧
        v s' .r11 < 2 ^ 26) ∧
      Keeps [.r7, .r8, .r9, .r10, .r11, .r14, .r15, .r16, .r17, .r18, .r19] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [carry, carryStep, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    exec_lsr_d (show 26 < 64 by decide), exec_lsl (show 2 < 64 by decide), exec_add, v,
    write_gpr, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun b0 b1 b2 b3 b4 => ?_, fun r hr => ?_, rfl, rfl,
    rfl⟩
  · simp only [hm, and_mask, lsr_toNat, add_toNat, lsl_toNat]
    obtain ⟨e, c0, c1, c2, c3, c4⟩ := carry_arith b0 b1 b2 b3 b4 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
    refine ⟨?_, c0, c1, c2, c3, c4⟩
    rw [← e, Nat.add_mul_mod_self_left]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.1, hr.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2, hr.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.1, ite_false, write_gpr]

set_option simprocs false in
/-- The two words at `[n + off]` into `r18, r19`. -/
theorem load2_ok (s : State) {n : Reg} {off : Nat} (hn : n ≠ Reg.r18) (hn0 : n ≠ Reg.r0)
    (ho : off < 2 ^ 15 ∧ off % 4 = 0) (ho' : off + 8 < 2 ^ 15 ∧ (off + 8) % 4 = 0)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 (off + 8)) 8) :
    WP isa (.block (load2 n off)) s fun s' =>
      s'.gpr .r18 = s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64 ∧
      s'.gpr .r19 = s.mem.readW (s.gpr n + BitVec.ofNat 64 (off + 8)) 64 ∧ Keeps [.r18, .r19] s s' := by
  apply WP.of_runBlock
  simp only [load2, runBlock_cons, runStep_some, exec_load_d hn0 ho h0]
  rw [exec_load_d hn0 ho' (by simp only [write_gpr, hn, ite_false]; exact h8)]
  simp (config := {decide := true}) only [runStep_some, runBlock_nil, write_gpr, hn, ite_true,
    ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [write_gpr, hr.2, hr.1, ite_false]

set_option simprocs false in
/-- `hi += xi`. -/
theorem addLimbs_ok (s : State) :
    WP isa (.block addLimbs) s fun s' =>
      v s' .r7 = (v s .r7 + v s .r12) % 2 ^ 64 ∧ v s' .r8 = (v s .r8 + v s .r14) % 2 ^ 64 ∧
      v s' .r9 = (v s .r9 + v s .r15) % 2 ^ 64 ∧ v s' .r10 = (v s .r10 + v s .r16) % 2 ^ 64 ∧
      v s' .r11 = (v s .r11 + v s .r17) % 2 ^ 64 ∧ Keeps [.r7, .r8, .r9, .r10, .r11] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addLimbs, runBlock_cons, runStep_some, runBlock_nil, exec_add,
    v, write_gpr, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨add_toNat _ _, add_toNat _ _, add_toNat _ _, add_toNat _ _, add_toNat _ _, fun r hr => ?_,
    rfl, rfl,
    rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.2.2.2.2, hr.2.2.2.1, hr.2.2.1, hr.2.1, hr.1, ite_false, write_gpr]

set_option simprocs false in
/-- `h += 2¹²⁸`. -/
theorem padBit_ok (s : State) :
    WP isa (.block padBit) s fun s' =>
      v s' .r11 = (v s .r11 + 2 ^ 24) % 2 ^ 64 ∧ Keeps [.r11, .r0] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [padBit, runBlock_cons, runStep_some, runBlock_nil,
    exec_lis, exec_add, v, write_gpr, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [add_toNat]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2, ite_false]

/-- Normalized limbs of `h mod p`. -/
def Norm (V a0 a1 a2 a3 a4 : Nat) : Prop :=
  val5 a0 a1 a2 a3 a4 = V % Spec.Poly1305.P ∧
    a0 < 2 ^ 26 ∧ a1 < 2 ^ 26 ∧ a2 < 2 ^ 26 ∧ a3 < 2 ^ 26 ∧ a4 < 2 ^ 26

set_option simprocs false in
/-- `normalize` and `plus5`: the mask in `r18` is zero if the limbs of `h mod p` are
`r12`–`r17`, all ones if they are `r7`–`r11`. -/
theorem reduceA_ok (s : State) (hm : s.gpr .r20 = M26) :
    WP isa (.block (normalize ++ plus5)) s fun s' =>
      (v s .r7 < 2 ^ 26 → v s .r8 < 2 ^ 27 → v s .r9 < 2 ^ 26 → v s .r10 < 2 ^ 26 → v s .r11 < 2 ^ 26 →
        (v s' .r18 = 0 ∧
          Norm (val5 (v s .r7) (v s .r8) (v s .r9) (v s .r10) (v s .r11))
            (v s' .r12) (v s' .r14) (v s' .r15) (v s' .r16) (v s' .r17)) ∨
        (v s' .r18 = 2 ^ 64 - 1 ∧
          Norm (val5 (v s .r7) (v s .r8) (v s .r9) (v s .r10) (v s .r11))
            (v s' .r7) (v s' .r8) (v s' .r9) (v s' .r10) (v s' .r11))) ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [normalize, plus5, carryStep, List.cons_append,
    List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    exec_lsr_d (show 26 < 64 by decide), exec_add, exec_addi (show Reg.r7 ≠ .r0 by decide) (show 5 < 2 ^ 15 by decide),
    exec_subi (show Reg.r18 ≠ .r0 by decide) (show 1 ≤ 2 ^ 15 by decide), v,
    write_gpr, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fun b0 b1 b2 b3 b4 => ?_, fun r hr => ?_, rfl,
    rfl, rfl⟩
  · simp only [hm, and_mask, lsr_toNat, add_toNat, sub_toNat, ofNat_toNat5, ofNat_toNat1]
    rcases reduce_arith b0 b1 b2 b3 b4 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl with ⟨hb, e, g⟩ | ⟨hb, e, g⟩
    · left
      rw [hb]
      exact ⟨rfl, e, g⟩
    · right
      rw [hb]
      exact ⟨rfl, e, g⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.1, hr.2.2.1, hr.2.1, hr.1, ite_false, write_gpr]

set_option simprocs false in
/-- Selecting `r12`–`r17` over `r7`–`r11` where the mask `r18` is set. -/
theorem select_ok (s : State) :
    WP isa (.block select) s fun s' =>
      s'.gpr .r7 = s.gpr .r12 ^^^ ((s.gpr .r7 ^^^ s.gpr .r12) &&& s.gpr .r18) ∧
      s'.gpr .r8 = s.gpr .r14 ^^^ ((s.gpr .r8 ^^^ s.gpr .r14) &&& s.gpr .r18) ∧
      s'.gpr .r9 = s.gpr .r15 ^^^ ((s.gpr .r9 ^^^ s.gpr .r15) &&& s.gpr .r18) ∧
      s'.gpr .r10 = s.gpr .r16 ^^^ ((s.gpr .r10 ^^^ s.gpr .r16) &&& s.gpr .r18) ∧
      s'.gpr .r11 = s.gpr .r17 ^^^ ((s.gpr .r11 ^^^ s.gpr .r17) &&& s.gpr .r18) ∧
      Keeps [.r7, .r8, .r9, .r10, .r11, .r19] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [select, selectLimb, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    write_gpr, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl,
    rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.2.2.2.2.1, hr.2.2.2.2.2, hr.2.2.2.1, hr.2.2.1, hr.2.1, hr.1, ite_false, write_gpr]

theorem select_zero (h g : BitVec 64) : g ^^^ ((h ^^^ g) &&& 0) = g := by simp only [BitVec.ofNat_eq_ofNat, BitVec.and_zero, BitVec.xor_zero]
theorem select_ones (h g : BitVec 64) : g ^^^ ((h ^^^ g) &&& BitVec.allOnes 64) = h := by
  rw [BitVec.and_allOnes, BitVec.xor_comm h, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem eq_zero_of_toNat {a : BitVec 64} (h : a.toNat = 0) : a = 0 := BitVec.eq_of_toNat_eq h
theorem eq_ones_of_toNat {a : BitVec 64} (h : a.toNat = 2 ^ 64 - 1) : a = BitVec.allOnes 64 :=
  BitVec.eq_of_toNat_eq (by rw [h]; rfl)

set_option simprocs false in
/-- The limbs `r7`–`r11` packed into the words `r18, r19, r0`. -/
theorem pack_ok (s : State) :
    WP isa (.block pack) s fun s' =>
      (v s .r7 < 2 ^ 26 → v s .r8 < 2 ^ 26 → v s .r9 < 2 ^ 26 → v s .r10 < 2 ^ 26 →
        v s' .r18 = val5 (v s .r7) (v s .r8) (v s .r9) (v s .r10) (v s .r11) % 2 ^ 64 ∧
        v s' .r19 = val5 (v s .r7) (v s .r8) (v s .r9) (v s .r10) (v s .r11) / 2 ^ 64 % 2 ^ 64 ∧
        v s' .r0 = val5 (v s .r7) (v s .r8) (v s .r9) (v s .r10) (v s .r11) / 2 ^ 128) ∧
      Keeps [.r12, .r18, .r19, .r0] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [pack, runBlock_cons, runStep_some, runBlock_nil,
    exec_lsl (show 26 < 64 by decide), exec_lsl (show 52 < 64 by decide),
    exec_lsl (show 14 < 64 by decide), exec_lsl (show 40 < 64 by decide),
    exec_lsr_d (show 12 < 64 by decide), exec_lsr_d (show 24 < 64 by decide), exec_add, v,
    write_gpr, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun b0 b1 b2 b3 => ?_, fun r hr => ?_, rfl, rfl,
    rfl⟩
  · simp only [lsr_toNat, add_toNat, lsl_toNat]
    exact pack_arith b0 b1 b2 b3
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.2.2, hr.2.2.1, hr.1, hr.2.1, ite_false, write_gpr]

set_option simprocs false in
/-- `hi += xi`, with the carries propagated up to `h4`. -/
theorem addCarry_ok (s : State) (hm : s.gpr .r20 = M26) :
    WP isa (.block (addLimbs ++ carryStep .r7 .r7 .r8 ++ normalize)) s fun s' =>
      (v s .r7 < 2 ^ 27 → v s .r8 < 2 ^ 27 → v s .r9 < 2 ^ 27 → v s .r10 < 2 ^ 27 → v s .r11 < 2 ^ 27 →
        v s .r12 < 2 ^ 27 → v s .r14 < 2 ^ 27 → v s .r15 < 2 ^ 27 → v s .r16 < 2 ^ 27 →
        v s .r17 < 2 ^ 27 →
        val5 (v s' .r7) (v s' .r8) (v s' .r9) (v s' .r10) (v s' .r11) =
          val5 (v s .r7) (v s .r8) (v s .r9) (v s .r10) (v s .r11) +
            val5 (v s .r12) (v s .r14) (v s .r15) (v s .r16) (v s .r17) ∧
        v s' .r7 < 2 ^ 26 ∧ v s' .r8 < 2 ^ 26 ∧ v s' .r9 < 2 ^ 26 ∧ v s' .r10 < 2 ^ 26 ∧
        v s' .r11 < 2 ^ 29) ∧
      Keeps [.r7, .r8, .r9, .r10, .r11, .r18] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addLimbs, normalize, carryStep, List.cons_append,
    List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    exec_lsr_d (show 26 < 64 by decide), exec_add, v,
    write_gpr, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 => ?_, fun r hr => ?_, rfl, rfl,
    rfl⟩
  · simp only [hm, and_mask, lsr_toNat, add_toNat]
    obtain ⟨e, g⟩ := addCarry_arith b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 rfl rfl rfl rfl rfl rfl rfl rfl rfl
    exact ⟨e, Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
      Nat.mod_lt _ (by decide), g⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.2.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2, hr.2.2.1, hr.2.1, hr.1, ite_false, write_gpr]

end VG.Proof.Poly1305.PPC64LE
