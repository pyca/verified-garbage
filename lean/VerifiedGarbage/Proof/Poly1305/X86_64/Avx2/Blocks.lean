import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Load
import VerifiedGarbage.Proof.Poly1305.Pair
import VerifiedGarbage.Proof.Poly1305.X86_64.Blocks
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
import VerifiedGarbage.Proof.Poly1305.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Powers`. -/
section

/-!
# Poly1305 on x86-64 with AVX2: the powers of `r`

`powers` leaves `r⁴` in the low doubleword of every quadword of `Y` and
`r^(4-k)` in the high doubleword of lane `k`, each as limbs below `2²⁷`.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx2
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Spec.Poly1305 (P)

/-- The high doublewords of `Y`. -/
def yh (s : State) (k i : Nat) : Nat := (qw s (yreg i) k).toNat / 2 ^ 32

theorem or_lo {x y : Nat} (hy : y < 2 ^ 32) : (x * 2 ^ 32 ||| y) = x * 2 ^ 32 + y := by
  rw [Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt hy]

theorem pick2_toNat (a b : BitVec 64) (l h : Bool) :
    (pick2 a b l h).toNat = (if h then b.toNat / 2 ^ 32 else a.toNat / 2 ^ 32) * 2 ^ 32 +
      (if l then b.toNat % 2 ^ 32 else a.toNat % 2 ^ 32) := by
  have ha := a.isLt
  have hb := b.isLt
  cases l <;> cases h <;>
    simp only [pick2, BitVec.toNat_append, BitVec.extractLsb'_toNat, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow, Bool.false_eq_true, ite_false, ite_true, Nat.pow_zero, Nat.div_one] <;>
    rw [VG.Proof.Poly1305.X86_64.Avx2.or_lo (Nat.mod_lt _ (by decide))] <;> omega

/-- What `blendY sel lo` writes into `Y_i`: `H_i << 32`, or with `lo`
`H_i << 32 | H_i`. -/
def blT (lo : Bool) (i : Nat) : Q :=
  if lo then .or (.shl (.reg (xi (hreg i))) 32) (.reg (xi (hreg i))) else .shl (.reg (xi (hreg i))) 32

/-- The terms `blendY sel lo` computes. -/
structure BlendShape (σ : Sym) (sel : Nat) (lo : Bool) : Prop where
  y : ∀ i < 5, σ.reg (xi (yreg i)) = .blend (.reg (xi (yreg i))) (VG.Proof.Poly1305.X86_64.Avx2.blT lo i) sel
  h : ∀ i < 5, σ.reg (xi (hreg i)) = .reg (xi (hreg i))

theorem blT_toNat {s : State} {lo : Bool} {i k : Nat} (hh : hv s k i < 2 ^ 32) :
    ((VG.Proof.Poly1305.X86_64.Avx2.blT lo i).eval s k).toNat = hv s k i * 2 ^ 32 + (if lo then hv s k i else 0) := by
  rw [natw_ok]
  simp only [hv] at hh ⊢
  cases lo <;> simp only [VG.Proof.Poly1305.X86_64.Avx2.blT, Bool.false_eq_true, ite_false, ite_true, Q.natw, envOf_v]
  · omega
  · rw [show (qw s (hreg i) k).toNat * 2 ^ 32 % 2 ^ 64 = (qw s (hreg i) k).toNat * 2 ^ 32 by omega,
      VG.Proof.Poly1305.X86_64.Avx2.or_lo hh]

/-- `blendY`: the doublewords of `Y` that `sel` selects replaced. -/
theorem blend_ok {σ : Sym} {sel : Nat} {lo : Bool} (hσ : VG.Proof.Poly1305.X86_64.Avx2.BlendShape σ sel lo) {s s' : State}
    (h : SRel σ s s') {k : Nat} (hk : k < 4) {i : Nat} (hi : i < 5) (hh : hv s k i < 2 ^ 32) :
    hv s' k i = hv s k i ∧
      yl s' k i = (if sel.testBit (2 * k) then (if lo then hv s k i else 0) else yl s k i) ∧
      VG.Proof.Poly1305.X86_64.Avx2.yh s' k i = (if sel.testBit (2 * k + 1) then hv s k i else VG.Proof.Poly1305.X86_64.Avx2.yh s k i) := by
  have ey : qw s' (yreg i) k = pick2 (qw s (yreg i) k) ((VG.Proof.Poly1305.X86_64.Avx2.blT lo i).eval s k) (sel.testBit (2 * k))
      (sel.testBit (2 * k + 1)) := by
    rw [h.reg _ k hk, hσ.y i hi]; simp only [Q.eval, xr_xi]
  have hT := VG.Proof.Poly1305.X86_64.Avx2.blT_toNat (lo := lo) hh
  refine ⟨?_, ?_, ?_⟩
  · simp only [hv]; rw [h.reg _ k hk, hσ.h i hi]; simp only [Q.eval, xr_xi]
  · simp only [yl]; rw [ey, VG.Proof.Poly1305.X86_64.Avx2.pick2_toNat, hT]
    have := (qw s (yreg i) k).isLt
    cases sel.testBit (2 * k) <;> cases sel.testBit (2 * k + 1) <;> cases lo <;>
      simp only [ite_true, ite_false, Bool.false_eq_true] <;> omega
  · simp only [VG.Proof.Poly1305.X86_64.Avx2.yh]; rw [ey, VG.Proof.Poly1305.X86_64.Avx2.pick2_toNat, hT]
    have := (qw s (yreg i) k).isLt
    cases sel.testBit (2 * k) <;> cases sel.testBit (2 * k + 1) <;> cases lo <;>
      simp only [ite_true, ite_false, Bool.false_eq_true] <;> omega

/-- Limb functions that agree below 5 and repeat limb 4 above it are equal. -/
theorem ext5 {f g : Nat → Nat} (hf : ∀ j, 4 ≤ j → f j = f 4) (hg : ∀ j, 4 ≤ j → g j = g 4)
    (h : ∀ i < 5, f i = g i) : f = g := by
  funext j
  by_cases hj : j < 5
  · exact h j hj
  · rw [hf j (by omega), hg j (by omega)]; exact h 4 (by decide)

theorem yh_ge (s : State) (k : Nat) {j : Nat} (h : 4 ≤ j) : VG.Proof.Poly1305.X86_64.Avx2.yh s k j = VG.Proof.Poly1305.X86_64.Avx2.yh s k 4 := by
  simp only [VG.Proof.Poly1305.X86_64.Avx2.yh, yreg_ge h]

theorem mul_ge (a b : Nat → Nat) {j : Nat} (h : 4 ≤ j) : Limbs26.mul a b j = Limbs26.mul a b 4 := by
  match j, h with
  | _ + 4, _ => rfl

/-! ## `initY` -/

def initS : Sym := (Sym.init.run false initY).get (by decide +kernel)
theorem initS_eq : Sym.init.run false initY = some VG.Proof.Poly1305.X86_64.Avx2.initS := (Option.some_get _).symm
theorem initS_shape : ∀ i < 5, initS.reg (xi (yreg i)) =
      .or (.reg (xi (hreg i))) (.shl (.reg (xi (hreg i))) 32) ∧
    initS.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

theorem initY_ok {s : State} (hh : ∀ k < 4, ∀ i < 5, hv s k i < 2 ^ 32) :
    WP isa (.block initY) s fun s' => vec s s' = s' ∧ ∀ k < 4, ∀ i < 5,
      hv s' k i = hv s k i ∧ yl s' k i = hv s k i ∧ VG.Proof.Poly1305.X86_64.Avx2.yh s' k i = hv s k i := by
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx2.initS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ?_⟩
  have e : (qw s' (yreg i) k).toNat = hv s k i * 2 ^ 32 + hv s k i := by
    rw [h.natw _ hk, (VG.Proof.Poly1305.X86_64.Avx2.initS_shape i hi).1]
    have := hh k hk i hi
    simp only [Q.natw, envOf_v, hv] at this ⊢
    rw [show (qw s (hreg i) k).toNat * 2 ^ 32 % 2 ^ 64 = (qw s (hreg i) k).toNat * 2 ^ 32 by omega,
      Nat.or_comm, VG.Proof.Poly1305.X86_64.Avx2.or_lo this]
  have := hh k hk i hi
  refine ⟨?_, ?_, ?_⟩
  · simp only [hv]; rw [h.reg _ k hk, (VG.Proof.Poly1305.X86_64.Avx2.initS_shape i hi).2]; simp only [Q.eval, xr_xi]
  · simp only [yl]; rw [e]; omega
  · simp only [VG.Proof.Poly1305.X86_64.Avx2.yh]; rw [e]; omega

/-! ## `blendY` -/

def bl1 : Sym := (Sym.init.run false (blendY 0x2A false)).get (by decide +kernel)
def bl2 : Sym := (Sym.init.run false (blendY 0x0A false)).get (by decide +kernel)
def bl3 : Sym := (Sym.init.run false (blendY 0x57 true)).get (by decide +kernel)
theorem bl1_eq : Sym.init.run false (blendY 0x2A false) = some VG.Proof.Poly1305.X86_64.Avx2.bl1 := (Option.some_get _).symm
theorem bl2_eq : Sym.init.run false (blendY 0x0A false) = some VG.Proof.Poly1305.X86_64.Avx2.bl2 := (Option.some_get _).symm
theorem bl3_eq : Sym.init.run false (blendY 0x57 true) = some VG.Proof.Poly1305.X86_64.Avx2.bl3 := (Option.some_get _).symm

theorem bl1_shape : VG.Proof.Poly1305.X86_64.Avx2.BlendShape VG.Proof.Poly1305.X86_64.Avx2.bl1 0x2A false :=
  ⟨by decide +kernel, by decide +kernel⟩
theorem bl2_shape : VG.Proof.Poly1305.X86_64.Avx2.BlendShape VG.Proof.Poly1305.X86_64.Avx2.bl2 0x0A false :=
  ⟨by decide +kernel, by decide +kernel⟩
theorem bl3_shape : VG.Proof.Poly1305.X86_64.Avx2.BlendShape VG.Proof.Poly1305.X86_64.Avx2.bl3 0x57 true :=
  ⟨by decide +kernel, by decide +kernel⟩

/-! ## `r` into `H` -/

def loadRg : List Instr := [
  .movImm64 .rax 0x0ffffffc0fffffff, .mov .r10 (.mem (at_ .rdi 24)), .alu .and .r10 (.reg .rax),
  .movImm64 .rax 0x0ffffffc0ffffffc, .mov .r11 (.mem (at_ .rdi 32)), .alu .and .r11 (.reg .rax)]
def loadRv : List Instr :=
  bcast (dreg 0) .r10 ++ bcast (dreg 1) .r11 ++ VG.Impl.Poly1305.X86_64.Avx2.split ++
  (List.range 5).map fun i => .vop (.vmovdqa .l256 (hreg i) (dreg i))
theorem loadR_eq : loadR = VG.Proof.Poly1305.X86_64.Avx2.loadRg ++ VG.Proof.Poly1305.X86_64.Avx2.loadRv := rfl

def lrS : Sym := (Sym.init.run false VG.Proof.Poly1305.X86_64.Avx2.loadRv).get (by decide +kernel)
theorem lrS_eq : Sym.init.run false VG.Proof.Poly1305.X86_64.Avx2.loadRv = some VG.Proof.Poly1305.X86_64.Avx2.lrS := (Option.some_get _).symm

section
variable (E : Env) (k : Nat)
theorem lrS_0 : (lrS.reg (xi (hreg 0))).natw E k = E.g .r10 * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_1 : (lrS.reg (xi (hreg 1))).natw E k = E.g .r10 * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_2 : (lrS.reg (xi (hreg 2))).natw E k =
    (E.g .r11 * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.g .r10 / 2 ^ 52) := rfl
theorem lrS_3 : (lrS.reg (xi (hreg 3))).natw E k = E.g .r11 * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_4 : (lrS.reg (xi (hreg 4))).natw E k = E.g .r11 / 2 ^ 40 := rfl
end

/-- `r` as a number, from `r10` and `r11`. -/
def rN (s : State) : Nat := (s.gpr .r10).toNat + 2 ^ 64 * (s.gpr .r11).toNat

theorem loadRv_ok (s : State) :
    WP isa (.block VG.Proof.Poly1305.X86_64.Avx2.loadRv) s fun s' => vec s s' = s' ∧ (∀ k < 4, ∀ i < 5, hv s' k i = hv s' 0 i) ∧
      Limbs26.val (hv s' 0) = VG.Proof.Poly1305.X86_64.Avx2.rN s ∧ ∀ k < 4, ∀ i < 5, hv s' k i < 2 ^ 26 := by
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx2.lrS_eq) fun s' h => ?_
  have e : ∀ k < 4, hv s' k 0 = (s.gpr .r10).toNat * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 1 = (s.gpr .r10).toNat * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 2 = (s.gpr .r11).toNat * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| (s.gpr .r10).toNat / 2 ^ 52 ∧
      hv s' k 3 = (s.gpr .r11).toNat * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 4 = (s.gpr .r11).toNat / 2 ^ 40 := fun k hk =>
    ⟨by rw [hv, h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx2.lrS_0]; rfl, by rw [hv, h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx2.lrS_1]; rfl,
      by rw [hv, h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx2.lrS_2]; rfl, by rw [hv, h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx2.lrS_3]; rfl,
      by rw [hv, h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx2.lrS_4]; rfl⟩
  have l := (s.gpr .r10).isLt
  have m := (s.gpr .r11).isLt
  have e₀ := e 0 (by decide)
  refine ⟨h.eq, fun k hk i hi => ?_, ?_, fun k hk i hi => ?_⟩
  · obtain ⟨a0, a1, a2, a3, a4⟩ := e k hk
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [a0, e₀.1]
    · rw [a1, e₀.2.1]
    · rw [a2, e₀.2.2.1]
    · rw [a3, e₀.2.2.2.1]
    · rw [a4, e₀.2.2.2.2]
  · rw [Limbs26.val, e₀.1, e₀.2.1, e₀.2.2.1, e₀.2.2.2.1, e₀.2.2.2.2, VG.Proof.Poly1305.X86_64.Avx2.rN]
    exact Limbs26.split_val l _
  · obtain ⟨a0, a1, a2, a3, a4⟩ := e k hk
    rw [Limbs26.split_or l] at a2
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [a0]; omega
    · rw [a1]; omega
    · rw [a2]; omega
    · rw [a3]; omega
    · rw [a4]; omega

/-! ## The powers -/

theorem val_congr {f g : Nat → Nat} (h : ∀ i < 5, f i = g i) : Limbs26.val f = Limbs26.val g := by
  simp only [Limbs26.val, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide)]

/-- `mul` of lanes that all hold `A`, times `B`. -/
theorem mul_step {s s' : State} (M : MulPost s s') {A B : Nat → Nat} (hA : ∀ j, 4 ≤ j → A j = A 4)
    (hB : ∀ j, 4 ≤ j → B j = B 4) (hH : ∀ k < 4, ∀ i < 5, hv s k i = A i)
    (hY : ∀ k < 4, ∀ i < 5, yl s k i = B i) :
    ∀ k < 4, ∀ i < 5, hv s' k i = Limbs26.mul A B i ∧ yl s' k i = yl s k i ∧ VG.Proof.Poly1305.X86_64.Avx2.yh s' k i = VG.Proof.Poly1305.X86_64.Avx2.yh s k i := by
  intro k hk i hi
  refine ⟨?_, by simp only [yl, M.y i hi k hk], by simp only [VG.Proof.Poly1305.X86_64.Avx2.yh, M.y i hi k hk]⟩
  rw [M.h k hk i hi, VG.Proof.Poly1305.X86_64.Avx2.ext5 (f := hv s k) (fun _ h => hv_ge s k h) hA (hH k hk),
    VG.Proof.Poly1305.X86_64.Avx2.ext5 (f := yl s k) (fun _ h => yl_ge s k h) hB (hY k hk)]

def powersV : List Instr :=
  VG.Proof.Poly1305.X86_64.Avx2.loadRv ++ (initY ++ (mul ++ (blendY 0x2A false ++ (mul ++ (blendY 0x0A false ++
    (mul ++ blendY 0x57 true))))))

theorem powers_eq : powers = VG.Proof.Poly1305.X86_64.Avx2.loadRg ++ VG.Proof.Poly1305.X86_64.Avx2.powersV := by
  simp only [powers, VG.Proof.Poly1305.X86_64.Avx2.loadR_eq, VG.Proof.Poly1305.X86_64.Avx2.powersV, List.append_assoc]

/-- What `powers` leaves in `Y`, for `r = R`. -/
structure YInv (s : State) (R : Nat) : Prop where
  lo : ∀ k < 4, Limbs26.val (yl s k) ≡ R ^ 4 [MOD P]
  hi : ∀ k < 4, Limbs26.val (VG.Proof.Poly1305.X86_64.Avx2.yh s k) ≡ R ^ (4 - k) [MOD P]
  lob : ∀ k < 4, ∀ i < 5, yl s k i < 2 ^ 27
  hib : ∀ k < 4, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx2.yh s k i < 2 ^ 27

theorem mul_modEq {a b : Nat → Nat} {x y : Nat} (ha : Limbs26.val a ≡ x [MOD P])
    (hb : Limbs26.val b ≡ y [MOD P]) : Limbs26.val (Limbs26.mul a b) ≡ x * y [MOD P] :=
  (Limbs26.mul_mod a b).trans (ha.mul hb)

theorem powersV_ok {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) :
    WP isa (.block VG.Proof.Poly1305.X86_64.Avx2.powersV) s fun s' => vec s s' = s' ∧ VG.Proof.Poly1305.X86_64.Avx2.YInv s' (VG.Proof.Poly1305.X86_64.Avx2.rN s) := by
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.loadRv_ok s) fun s₁ ⟨v₁, U₁, V₁, B₁⟩ => ?_)
  have LL : ∀ j, 4 ≤ j → hv s₁ 0 j = hv s₁ 0 4 := fun j h => hv_ge s₁ 0 h
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.initY_ok fun k hk i hi => by have := B₁ k hk i hi; omega)
    fun s₂ ⟨v₂, I₂⟩ => ?_)
  have h₂ : ∀ k < 4, ∀ i < 5, hv s₂ k i = hv s₁ 0 i ∧ yl s₂ k i = hv s₁ 0 i ∧ VG.Proof.Poly1305.X86_64.Avx2.yh s₂ k i = hv s₁ 0 i := by
    intro k hk i hi; obtain ⟨a, b, c⟩ := I₂ k hk i hi; rw [U₁ k hk i hi] at a b c; exact ⟨a, b, c⟩
  have hb₁ : ∀ i < 5, hv s₁ 0 i < 2 ^ 26 := B₁ 0 (by decide)
  have r8 : ∀ {t : State}, vec s t = t → t.gpr .r8 = 0x3ffffff := fun h => by rw [vec_gpr h, hr8]
  have v₂' := vec_trans v₁ v₂
  refine WP.block_append (WP.mono (mul_ok ⟨r8 v₂', fun k hk i hi => ?_, fun k hk i hi => ?_⟩)
    fun s₃ M₃ => ?_)
  · rw [(h₂ k hk i hi).1]; have := hb₁ i hi; omega
  · rw [(h₂ k hk i hi).2.1]; have := hb₁ i hi; omega
  have m₃ := VG.Proof.Poly1305.X86_64.Avx2.mul_step M₃ LL LL (fun k hk i hi => (h₂ k hk i hi).1) (fun k hk i hi => (h₂ k hk i hi).2.1)
  -- `r²` in `H`; `Y` = `r` in both doublewords.
  refine WP.block_append (WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx2.bl1_eq) fun s₄ h₄ => ?_)
  have e₄ : ∀ k < 4, ∀ i < 5, hv s₄ k i = Limbs26.mul (hv s₁ 0) (hv s₁ 0) i ∧ yl s₄ k i = hv s₁ 0 i ∧
      VG.Proof.Poly1305.X86_64.Avx2.yh s₄ k i = if k < 3 then Limbs26.mul (hv s₁ 0) (hv s₁ 0) i else hv s₁ 0 i := by
    intro k hk i hi
    obtain ⟨a₃, b₃, c₃⟩ := m₃ k hk i hi
    have := M₃.hb k hk i hi
    obtain ⟨a, b, c⟩ := VG.Proof.Poly1305.X86_64.Avx2.blend_ok VG.Proof.Poly1305.X86_64.Avx2.bl1_shape h₄ hk hi (by omega)
    rw [a, b, c, a₃, b₃, c₃, (h₂ k hk i hi).2.1, (h₂ k hk i hi).2.2]
    refine ⟨rfl, ?_⟩
    rcases cases4 hk with rfl | rfl | rfl | rfl <;> simp (config := { decide := true }) only [ite_true, ite_false]
  have v₄ := vec_trans (vec_trans v₂' M₃.vec) h₄.eq
  refine WP.block_append (WP.mono (mul_ok ⟨r8 v₄, fun k hk i hi => ?_, fun k hk i hi => ?_⟩)
    fun s₅ M₅ => ?_)
  · rw [(e₄ k hk i hi).1, ← (m₃ k hk i hi).1]; have := M₃.hb k hk i hi; omega
  · rw [(e₄ k hk i hi).2.1]; have := hb₁ i hi; omega
  have m₅ := VG.Proof.Poly1305.X86_64.Avx2.mul_step (A := Limbs26.mul (hv s₁ 0) (hv s₁ 0)) M₅ (fun _ h => VG.Proof.Poly1305.X86_64.Avx2.mul_ge _ _ h) LL (fun k hk i hi => (e₄ k hk i hi).1)
    (fun k hk i hi => (e₄ k hk i hi).2.1)
  -- `r³` in `H`; `r³` into the high doublewords of lanes 0 and 1.
  refine WP.block_append (WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx2.bl2_eq) fun s₆ h₆ => ?_)
  have e₆ : ∀ k < 4, ∀ i < 5,
      hv s₆ k i = Limbs26.mul (Limbs26.mul (hv s₁ 0) (hv s₁ 0)) (hv s₁ 0) i ∧ yl s₆ k i = hv s₁ 0 i ∧
      VG.Proof.Poly1305.X86_64.Avx2.yh s₆ k i = if k < 2 then Limbs26.mul (Limbs26.mul (hv s₁ 0) (hv s₁ 0)) (hv s₁ 0) i
        else if k < 3 then Limbs26.mul (hv s₁ 0) (hv s₁ 0) i else hv s₁ 0 i := by
    intro k hk i hi
    obtain ⟨a₅, b₅, c₅⟩ := m₅ k hk i hi
    have := M₅.hb k hk i hi
    obtain ⟨a, b, c⟩ := VG.Proof.Poly1305.X86_64.Avx2.blend_ok VG.Proof.Poly1305.X86_64.Avx2.bl2_shape h₆ hk hi (by omega)
    rw [a, b, c, a₅, b₅, c₅, (e₄ k hk i hi).2.1, (e₄ k hk i hi).2.2]
    refine ⟨rfl, ?_⟩
    rcases cases4 hk with rfl | rfl | rfl | rfl <;> simp (config := { decide := true }) only [ite_true, ite_false]
  have v₆ := vec_trans (vec_trans v₄ M₅.vec) h₆.eq
  refine WP.block_append (WP.mono (mul_ok ⟨r8 v₆, fun k hk i hi => ?_, fun k hk i hi => ?_⟩)
    fun s₇ M₇ => ?_)
  · rw [(e₆ k hk i hi).1, ← (m₅ k hk i hi).1]; have := M₅.hb k hk i hi; omega
  · rw [(e₆ k hk i hi).2.1]; have := hb₁ i hi; omega
  have m₇ := VG.Proof.Poly1305.X86_64.Avx2.mul_step (A := Limbs26.mul (Limbs26.mul (hv s₁ 0) (hv s₁ 0)) (hv s₁ 0)) M₇
    (fun _ h => VG.Proof.Poly1305.X86_64.Avx2.mul_ge _ _ h) LL (fun k hk i hi => (e₆ k hk i hi).1)
    (fun k hk i hi => (e₆ k hk i hi).2.1)
  -- `r⁴` into the low doublewords, and the high one of lane 0.
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx2.bl3_eq) fun s₈ h₈ => ?_
  have e₈ : ∀ k < 4, ∀ i < 5,
      yl s₈ k i = hv s₇ 0 i ∧
      VG.Proof.Poly1305.X86_64.Avx2.yh s₈ k i = if k < 1 then hv s₇ 0 i
        else if k < 2 then Limbs26.mul (Limbs26.mul (hv s₁ 0) (hv s₁ 0)) (hv s₁ 0) i
        else if k < 3 then Limbs26.mul (hv s₁ 0) (hv s₁ 0) i else hv s₁ 0 i := by
    intro k hk i hi
    obtain ⟨_, b₇, c₇⟩ := m₇ k hk i hi
    have := M₇.hb k hk i hi
    obtain ⟨_, b, c⟩ := VG.Proof.Poly1305.X86_64.Avx2.blend_ok VG.Proof.Poly1305.X86_64.Avx2.bl3_shape h₈ hk hi (by omega)
    rw [b, c, b₇, c₇, (e₆ k hk i hi).2.2, (m₇ k hk i hi).1, (m₇ 0 (by decide) i hi).1]
    rcases cases4 hk with rfl | rfl | rfl | rfl <;> simp (config := { decide := true }) only [ite_true, ite_false]
  refine ⟨vec_trans (vec_trans v₆ M₇.vec) h₈.eq, ?_⟩
  -- Values and bounds of the powers.
  have q₁ : Limbs26.val (hv s₁ 0) ≡ VG.Proof.Poly1305.X86_64.Avx2.rN s [MOD P] := by rw [V₁]
  have q₂ := VG.Proof.Poly1305.X86_64.Avx2.mul_modEq q₁ q₁
  have q₃ := VG.Proof.Poly1305.X86_64.Avx2.mul_modEq q₂ q₁
  have q₄ : Limbs26.val (hv s₇ 0) ≡ VG.Proof.Poly1305.X86_64.Avx2.rN s ^ 4 [MOD P] := by
    rw [VG.Proof.Poly1305.X86_64.Avx2.val_congr (m₇ 0 (by decide) · · |>.1), show VG.Proof.Poly1305.X86_64.Avx2.rN s ^ 4 = VG.Proof.Poly1305.X86_64.Avx2.rN s * VG.Proof.Poly1305.X86_64.Avx2.rN s * VG.Proof.Poly1305.X86_64.Avx2.rN s * VG.Proof.Poly1305.X86_64.Avx2.rN s by ring]
    exact VG.Proof.Poly1305.X86_64.Avx2.mul_modEq q₃ q₁
  have b₂ : ∀ i < 5, Limbs26.mul (hv s₁ 0) (hv s₁ 0) i < 2 ^ 27 := fun i hi => by
    rw [← (m₃ 0 (by decide) i hi).1]; exact M₃.hb 0 (by decide) i hi
  have b₃ : ∀ i < 5, Limbs26.mul (Limbs26.mul (hv s₁ 0) (hv s₁ 0)) (hv s₁ 0) i < 2 ^ 27 := fun i hi => by
    rw [← (m₅ 0 (by decide) i hi).1]; exact M₅.hb 0 (by decide) i hi
  have b₄ : ∀ i < 5, hv s₇ 0 i < 2 ^ 27 := fun i hi => M₇.hb 0 (by decide) i hi
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_, fun k hk i hi => ?_⟩
  · rw [VG.Proof.Poly1305.X86_64.Avx2.val_congr (e₈ k hk · · |>.1)]; exact q₄
  · rcases cases4 hk with rfl | rfl | rfl | rfl
    · rw [VG.Proof.Poly1305.X86_64.Avx2.val_congr (e₈ 0 (by decide) · · |>.2)]; exact q₄
    · rw [VG.Proof.Poly1305.X86_64.Avx2.val_congr (g := Limbs26.mul (Limbs26.mul (hv s₁ 0) (hv s₁ 0)) (hv s₁ 0)) fun i hi => by
        simp (config := { decide := true }) only [(e₈ 1 (by decide) i hi).2, ite_true, ite_false]]
      simpa only [show VG.Proof.Poly1305.X86_64.Avx2.rN s ^ (4 - 1) = VG.Proof.Poly1305.X86_64.Avx2.rN s * VG.Proof.Poly1305.X86_64.Avx2.rN s * VG.Proof.Poly1305.X86_64.Avx2.rN s by ring] using q₃
    · rw [VG.Proof.Poly1305.X86_64.Avx2.val_congr (g := Limbs26.mul (hv s₁ 0) (hv s₁ 0)) fun i hi => by
        simp (config := { decide := true }) only [(e₈ 2 (by decide) i hi).2, ite_true, ite_false]]
      simpa only [show VG.Proof.Poly1305.X86_64.Avx2.rN s ^ (4 - 2) = VG.Proof.Poly1305.X86_64.Avx2.rN s * VG.Proof.Poly1305.X86_64.Avx2.rN s by ring] using q₂
    · rw [VG.Proof.Poly1305.X86_64.Avx2.val_congr (g := hv s₁ 0) fun i hi => by
        simp (config := { decide := true }) only [(e₈ 3 (by decide) i hi).2, ite_false]]
      simpa only [show VG.Proof.Poly1305.X86_64.Avx2.rN s ^ (4 - 3) = VG.Proof.Poly1305.X86_64.Avx2.rN s by ring] using q₁
  · rw [(e₈ k hk i hi).1]; exact b₄ i hi
  · rw [(e₈ k hk i hi).2]
    have := hb₁ i hi; have := b₂ i hi; have := b₃ i hi; have := b₄ i hi
    split <;> [omega; split <;> [omega; split <;> omega]]

end VG.Proof.Poly1305.X86_64.Avx2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Final`. -/
section

/-!
# Poly1305 on x86-64 with AVX2: the accumulator in and out

`loadH` splits the accumulator into lane 0 of `H`; after the last group,
`sumLanes` adds the lanes into lane 0 and carries, `fullCarry` and `reduce`
reduce it modulo `p`, and `storeH` joins its limbs into words.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx2
open VG.Spec.Poly1305 (P)

/-! ## `loadH` -/

def ldS : Sym := (Sym.init.run false loadH).get (by decide +kernel)
theorem ldS_eq : Sym.init.run false loadH = some VG.Proof.Poly1305.X86_64.Avx2.ldS := (Option.some_get _).symm
theorem ldS_y : ∀ i < 5, ldS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

section
variable (E : Env)
theorem ldS_0 : ∀ k < 4, (ldS.reg (xi (hreg 0))).natw E k =
    (if k = 0 then E.g .r10 else 0) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 := by
  intro k hk; rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem ldS_1 : ∀ k < 4, (ldS.reg (xi (hreg 1))).natw E k =
    (if k = 0 then E.g .r10 else 0) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 := by
  intro k hk; rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem ldS_2 : ∀ k < 4, (ldS.reg (xi (hreg 2))).natw E k =
    ((if k = 0 then E.g .r11 else 0) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 |||
      (if k = 0 then E.g .r10 else 0) / 2 ^ 52) := by
  intro k hk; rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem ldS_3 : ∀ k < 4, (ldS.reg (xi (hreg 3))).natw E k =
    (if k = 0 then E.g .r11 else 0) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 := by
  intro k hk; rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem ldS_4 : ∀ k < 4, (ldS.reg (xi (hreg 4))).natw E k =
    ((if k = 0 then E.g .r11 else 0) / 2 ^ 40 ||| (if k = 0 then E.g .rax else 0) * 2 ^ 24 % 2 ^ 64) := by
  intro k hk; rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
end

/-- The accumulator's words, in `r10`, `r11` and `rax`, as a number. -/
def hN (s : State) : Nat :=
  (s.gpr .r10).toNat + 2 ^ 64 * (s.gpr .r11).toNat + 2 ^ 128 * (s.gpr .rax).toNat

/-- What `loadH` leaves: the accumulator in lane 0 of `H`, zeros in the
other lanes, and `Y` as it was. -/
structure LoadHPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 5, ∀ k < 4, qw s' (yreg i) k = qw s (yreg i) k
  h : ∀ k < 4, Limbs26.val (hv s' k) = if k = 0 then VG.Proof.Poly1305.X86_64.Avx2.hN s else 0
  hb : ∀ k < 4, ∀ i < 5, hv s' k i < 2 ^ 26

theorem loadH_ok {s : State} (hax : (s.gpr .rax).toNat < 4) : WP isa (.block loadH) s (VG.Proof.Poly1305.X86_64.Avx2.LoadHPost s) := by
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx2.ldS_eq) fun s' h => ?_
  have e : ∀ k < 4, hv s' k 0 = (if k = 0 then (s.gpr .r10).toNat else 0) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 1 = (if k = 0 then (s.gpr .r10).toNat else 0) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 2 = ((if k = 0 then (s.gpr .r11).toNat else 0) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 |||
        (if k = 0 then (s.gpr .r10).toNat else 0) / 2 ^ 52) ∧
      hv s' k 3 = (if k = 0 then (s.gpr .r11).toNat else 0) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 4 = ((if k = 0 then (s.gpr .r11).toNat else 0) / 2 ^ 40 |||
        (if k = 0 then (s.gpr .rax).toNat else 0) * 2 ^ 24 % 2 ^ 64) := fun k hk =>
    ⟨by rw [hv, h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx2.ldS_0 _ k hk]; rfl, by rw [hv, h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx2.ldS_1 _ k hk]; rfl,
      by rw [hv, h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx2.ldS_2 _ k hk]; rfl, by rw [hv, h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx2.ldS_3 _ k hk]; rfl,
      by rw [hv, h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx2.ldS_4 _ k hk]; rfl⟩
  have l := (s.gpr .r10).isLt
  have m := (s.gpr .r11).isLt
  have e4 : ((s.gpr .r11).toNat / 2 ^ 40 ||| (s.gpr .rax).toNat * 2 ^ 24 % 2 ^ 64) =
      (s.gpr .r11).toNat / 2 ^ 40 + 2 ^ 24 * (s.gpr .rax).toNat := by
    rw [show (s.gpr .rax).toNat * 2 ^ 24 % 2 ^ 64 = 2 ^ 24 * (s.gpr .rax).toNat by omega, Nat.or_comm,
      ← Nat.two_pow_add_eq_or_of_lt (by omega)]
    omega
  refine ⟨h.eq, fun i hi k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, VG.Proof.Poly1305.X86_64.Avx2.ldS_y i hi]; simp only [Q.eval, xr_xi]
  · obtain ⟨a0, a1, a2, a3, a4⟩ := e k hk
    by_cases hk0 : k = 0
    · subst hk0
      simp only [ite_true] at a0 a1 a2 a3 a4 ⊢
      rw [e4] at a4
      have := Limbs26.split_val l (s.gpr .r11).toNat
      rw [Limbs26.val, a0, a1, a2, a3, a4, VG.Proof.Poly1305.X86_64.Avx2.hN]
      omega
    · simp only [hk0, ite_false, Nat.zero_mul, Nat.zero_mod, Nat.zero_div, Nat.or_self] at a0 a1 a2 a3 a4 ⊢
      rw [Limbs26.val, a0, a1, a2, a3, a4]
  · obtain ⟨a0, a1, a2, a3, a4⟩ := e k hk
    by_cases hk0 : k = 0
    · subst hk0
      simp only [ite_true] at a0 a1 a2 a3 a4
      rw [e4] at a4
      rw [Limbs26.split_or l] at a2
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
      · rw [a0]; omega
      · rw [a1]; omega
      · rw [a2]; omega
      · rw [a3]; omega
      · rw [a4]; omega
    · simp only [hk0, ite_false, Nat.zero_mul, Nat.zero_mod, Nat.zero_div, Nat.or_self] at a0 a1 a2 a3 a4
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
      · rw [a0]; decide
      · rw [a1]; decide
      · rw [a2]; decide
      · rw [a3]; decide
      · rw [a4]; decide

/-! ## `sumLanes` -/

def sumB : Bnds :=
  ⟨fun r => match r with
    | .xmm0 | .xmm1 | .xmm2 | .xmm3 | .xmm4 => 2 ^ 27 - 1
    | _ => 2 ^ 64 - 1,
   fun _ => 2 ^ 32 - 1,
   fun g => if g = .r8 then 2 ^ 26 - 1 else 2 ^ 64 - 1⟩

def smS : Sym := (Sym.init.run false sumLanes).get (by decide +kernel)
theorem smS_eq : Sym.init.run false sumLanes = some VG.Proof.Poly1305.X86_64.Avx2.smS := (Option.some_get _).symm

theorem smS_ok : ∀ i < 5, ∀ k < 4, (smS.reg (xi (hreg i))).ok VG.Proof.Poly1305.X86_64.Avx2.sumB k = true ∧
    (smS.reg (xi (hreg i))).bnd VG.Proof.Poly1305.X86_64.Avx2.sumB k < (if i = 1 then 2 ^ 27 else 2 ^ 26) := by
  decide +kernel

/-- The sum of the lanes of `H`, limb by limb, as `sumLanes` adds them. -/
def lsum (h : Nat → Nat → Nat) (i : Nat) : Nat := h 0 i + h 2 i + (h 1 i + h 3 i)

theorem smS_nat (E : Env) : ∀ i < 5, (smS.reg (xi (hreg i))).nat E 0 =
    Limbs26.carry (VG.Proof.Poly1305.X86_64.Avx2.lsum fun k j => E.v (xi (hreg j)) k) (E.g .r8) i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem sumB_env {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hb : ∀ k < 4, ∀ i < 5, hv s k i < 2 ^ 27) :
    EnvOK s VG.Proof.Poly1305.X86_64.Avx2.sumB := by
  refine ⟨fun r k hk => ?_, fun r k hk => ?_, fun g => ?_⟩
  · have := BitVec.isLt (qw s r k)
    cases r <;> simp only [VG.Proof.Poly1305.X86_64.Avx2.sumB] <;> first
      | omega
      | exact Nat.le_sub_one_of_lt (hb k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 4 (by decide))
  · have := Nat.mod_lt (qw s r k).toNat (show 2 ^ 32 > 0 by decide)
    simp only [VG.Proof.Poly1305.X86_64.Avx2.sumB]; omega
  · have := BitVec.isLt (s.gpr g)
    simp only [VG.Proof.Poly1305.X86_64.Avx2.sumB]
    split
    · subst g; rw [hr8]; decide
    · omega

theorem lsum_val (h : Nat → Nat → Nat) :
    Limbs26.val (VG.Proof.Poly1305.X86_64.Avx2.lsum h) = Limbs26.val (h 0) + Limbs26.val (h 1) + Limbs26.val (h 2) + Limbs26.val (h 3) := by
  simp only [Limbs26.val, VG.Proof.Poly1305.X86_64.Avx2.lsum]; omega

/-- What `sumLanes` leaves in lane 0 of `H`: the sum of the lanes, carried. -/
structure SumPost (s s' : State) : Prop where
  vec : vec s s' = s'
  h : Limbs26.val (hv s' 0) ≡
    Limbs26.val (hv s 0) + Limbs26.val (hv s 1) + Limbs26.val (hv s 2) + Limbs26.val (hv s 3) [MOD P]
  hb : ∀ i < 5, hv s' 0 i < if i = 1 then 2 ^ 27 else 2 ^ 26
  hball : ∀ k < 4, ∀ i < 5, hv s' k i < 2 ^ 27

theorem sumLanes_ok {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hb : ∀ k < 4, ∀ i < 5, hv s k i < 2 ^ 27) :
    WP isa (.block sumLanes) s (VG.Proof.Poly1305.X86_64.Avx2.SumPost s) := by
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx2.smS_eq) fun s' h => ?_
  have hE := VG.Proof.Poly1305.X86_64.Avx2.sumB_env hr8 hb
  have e : ∀ i < 5, hv s' 0 i = Limbs26.carry (VG.Proof.Poly1305.X86_64.Avx2.lsum (hv s)) 0x3ffffff i := fun i hi => by
    obtain ⟨e, -⟩ := h.nat hE (by decide) (VG.Proof.Poly1305.X86_64.Avx2.smS_ok i hi 0 (by decide)).1
    simp only [hv] at e ⊢
    rw [e, VG.Proof.Poly1305.X86_64.Avx2.smS_nat _ i hi]
    simp only [envOf, hr8, xr_xi]
    rfl
  refine ⟨h.eq, ?_, fun i hi => ?_, fun k hk i hi => ?_⟩
  · rw [VG.Proof.Poly1305.X86_64.Avx2.val_congr e, ← VG.Proof.Poly1305.X86_64.Avx2.lsum_val]
    have := Limbs26.carry_val (VG.Proof.Poly1305.X86_64.Avx2.lsum (hv s))
    rw [← this, Nat.ModEq, Nat.add_mul_mod_self_left]
  · obtain ⟨-, b⟩ := h.nat hE (by decide) (VG.Proof.Poly1305.X86_64.Avx2.smS_ok i hi 0 (by decide)).1
    exact Nat.lt_of_le_of_lt b (VG.Proof.Poly1305.X86_64.Avx2.smS_ok i hi 0 (by decide)).2
  · obtain ⟨-, b⟩ := h.nat hE hk (VG.Proof.Poly1305.X86_64.Avx2.smS_ok i hi k hk).1
    have := (VG.Proof.Poly1305.X86_64.Avx2.smS_ok i hi k hk).2
    simp only [hv]
    split at this <;> omega

/-! ## `fullCarry` and `reduce` -/

def finB : Bnds :=
  ⟨fun r => match r with
    | .xmm0 | .xmm1 | .xmm2 | .xmm3 | .xmm4 => 2 ^ 27 - 1
    | _ => 2 ^ 64 - 1,
   fun _ => 2 ^ 32 - 1,
   fun g => match g with
    | .r8 => 2 ^ 26 - 1
    | .rax => 5
    | .r10 => 2 ^ 27 - 1
    | _ => 2 ^ 64 - 1⟩

def fnS : Sym := (Sym.init.run false (fullCarry ++ reduce)).get (by decide +kernel)
theorem fnS_eq : Sym.init.run false (fullCarry ++ reduce) = some VG.Proof.Poly1305.X86_64.Avx2.fnS := (Option.some_get _).symm

theorem fnS_ok : ∀ i < 5, (fnS.reg (xi (hreg i))).ok VG.Proof.Poly1305.X86_64.Avx2.finB 0 = true := by
  decide +kernel

theorem fnS_nat (E : Env) : ∀ i < 5, (fnS.reg (xi (hreg i))).nat E 0 =
    Limbs26.fin (fun j => E.v (xi (hreg j)) 0) (E.g .r8) (E.g .rax) (E.g .r10) i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem finB_env {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hax : s.gpr .rax = 5)
    (hr10 : s.gpr .r10 = 0x7ffffff) (hb : ∀ k < 4, ∀ i < 5, hv s k i < 2 ^ 27) : EnvOK s VG.Proof.Poly1305.X86_64.Avx2.finB := by
  refine ⟨fun r k hk => ?_, fun r k hk => ?_, fun g => ?_⟩
  · have := BitVec.isLt (qw s r k)
    cases r <;> simp only [VG.Proof.Poly1305.X86_64.Avx2.finB] <;> first
      | omega
      | exact Nat.le_sub_one_of_lt (hb k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 4 (by decide))
  · have := Nat.mod_lt (qw s r k).toNat (show 2 ^ 32 > 0 by decide)
    simp only [VG.Proof.Poly1305.X86_64.Avx2.finB]; omega
  · have := BitVec.isLt (s.gpr g)
    cases g <;> simp only [VG.Proof.Poly1305.X86_64.Avx2.finB] <;> first | omega | (rw [hr8]; decide) | (rw [hax]; decide) |
      (rw [hr10]; decide)

/-- What `fullCarry` and `reduce` leave in lane 0 of `H`: `h mod p`. -/
theorem finish_ok {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hax : s.gpr .rax = 5)
    (hr10 : s.gpr .r10 = 0x7ffffff) (hb : ∀ k < 4, ∀ i < 5, hv s k i < 2 ^ 27)
    (hb0 : ∀ i < 5, hv s 0 i < if i = 1 then 2 ^ 27 else 2 ^ 26) :
    WP isa (.block (fullCarry ++ reduce)) s fun s' => vec s s' = s' ∧
      Limbs26.val (hv s' 0) = Limbs26.val (hv s 0) % P ∧ ∀ i < 5, hv s' 0 i < 2 ^ 26 := by
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx2.fnS_eq) fun s' h => ?_
  have hE := VG.Proof.Poly1305.X86_64.Avx2.finB_env hr8 hax hr10 hb
  have e : ∀ i < 5, hv s' 0 i = Limbs26.fin (hv s 0) 0x3ffffff 5 0x7ffffff i := fun i hi => by
    obtain ⟨e, -⟩ := h.nat hE (by decide) (VG.Proof.Poly1305.X86_64.Avx2.fnS_ok i hi)
    simp only [hv] at e ⊢
    rw [e, VG.Proof.Poly1305.X86_64.Avx2.fnS_nat _ i hi]
    simp only [envOf, hr8, hax, hr10, xr_xi]
    rfl
  obtain ⟨v, b⟩ := Limbs26.fin_val (hb0 0 (by decide)) (hb0 1 (by decide)) (hb0 2 (by decide))
    (hb0 3 (by decide)) (hb0 4 (by decide))
  exact ⟨h.eq, by rw [VG.Proof.Poly1305.X86_64.Avx2.val_congr e, v], fun i hi => by rw [e i hi]; exact b i hi⟩

end VG.Proof.Poly1305.X86_64.Avx2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Store`. -/
section

/-!
# Poly1305 on x86-64 with AVX2: storing the accumulator

`storeH` joins the limbs of lane 0 of `H` into three words and stores them in
the state, the first two at byte 0 and the last two at byte 8.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx2
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Proof.Poly1305.X86_64 (off off_eq hR contains_off)

def storeV : List Instr := [
  sll (dreg 1) (hreg 1) 26, sll (dreg 2) (hreg 2) 52, v .vpor (dreg 1) (dreg 1) (hreg 0),
  v .vpor (dreg 1) (dreg 1) (dreg 2),
  srl (dreg 2) (hreg 2) 12, sll (dreg 3) (hreg 3) 14, v .vpor (dreg 2) (dreg 2) (dreg 3),
  sll (dreg 3) (hreg 4) 40, v .vpor (dreg 2) (dreg 2) (dreg 3),
  srl (dreg 3) (hreg 4) 24,
  v .vpunpcklqdq tP (dreg 1) (dreg 2)]

theorem storeH_eq : VG.Impl.Poly1305.X86_64.Avx2.storeH = VG.Proof.Poly1305.X86_64.Avx2.storeV ++ (([.vmovdquStore .l128 (at_ .rdi 0) tP] : List Instr) ++
    (([v .vpunpcklqdq tP (dreg 2) (dreg 3)] : List Instr) ++
      ([.vmovdquStore .l128 (at_ .rdi 8) tP] : List Instr))) := rfl

def svS : Sym := (Sym.init.run false VG.Proof.Poly1305.X86_64.Avx2.storeV).get (by decide +kernel)
theorem svS_eq : Sym.init.run false VG.Proof.Poly1305.X86_64.Avx2.storeV = some VG.Proof.Poly1305.X86_64.Avx2.svS := (Option.some_get _).symm
def upS : Sym := (Sym.init.run false [v .vpunpcklqdq tP (dreg 2) (dreg 3)]).get (by decide +kernel)
theorem upS_eq : Sym.init.run false [v .vpunpcklqdq tP (dreg 2) (dreg 3)] = some VG.Proof.Poly1305.X86_64.Avx2.upS :=
  (Option.some_get _).symm

section
variable (E : Env)
theorem svS_d1 : (svS.reg (xi (dreg 1))).natw E 0 = (E.v (xi (hreg 1)) 0 * 2 ^ 26 % 2 ^ 64 |||
    E.v (xi (hreg 0)) 0 ||| E.v (xi (hreg 2)) 0 * 2 ^ 52 % 2 ^ 64) := rfl
theorem svS_d2 : (svS.reg (xi (dreg 2))).natw E 0 = (E.v (xi (hreg 2)) 0 / 2 ^ 12 |||
    E.v (xi (hreg 3)) 0 * 2 ^ 14 % 2 ^ 64 ||| E.v (xi (hreg 4)) 0 * 2 ^ 40 % 2 ^ 64) := rfl
theorem svS_d3 : (svS.reg (xi (dreg 3))).natw E 0 = E.v (xi (hreg 4)) 0 / 2 ^ 24 := rfl
theorem svS_tP : svS.reg (xi tP) = .unpl (svS.reg (xi (dreg 1))) (svS.reg (xi (dreg 2))) := by
  decide +kernel
theorem upS_t0 : (upS.reg (xi tP)).natw E 0 = E.v (xi (dreg 2)) 0 := rfl
theorem upS_t1 : (upS.reg (xi tP)).natw E 1 = E.v (xi (dreg 3)) 0 := rfl
end

theorem st128_ok (s : State) (d : Nat) (hw : InRegions s.wr (off (s.gpr .rdi) d) 16) :
    WP isa (.block [.vmovdquStore .l128 (at_ .rdi d) tP]) s fun s' =>
      s' = s.setMem (s.mem.writeW (off (s.gpr .rdi) d) (s.xmm tP)) := by
  apply WP.of_runBlock
  have e : s.ea (at_ .rdi d) = off (s.gpr .rdi) d := rfl
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store128_eq, e, hw, ite_true,
    Option.some.injEq, exists_eq_left']

theorem xmm_lo (s : State) (r : XReg) : (s.xmm r).extractLsb' 0 64 = qw s r 0 := rfl
theorem xmm_hi (s : State) (r : XReg) : (s.xmm r).extractLsb' 64 64 = qw s r 1 := rfl

theorem addr0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero _

/-- Reading back two overlapping 16-byte stores, at `p` and `p + 8`. -/
theorem two_writes (m : Mem) (p : Addr) (v₁ v₂ : BitVec 128) :
    ((m.writeW (off p 0) v₁).writeW (off p 8) v₂).readW (off p 0) 64 = v₁.extractLsb' 0 64 ∧
    ((m.writeW (off p 0) v₁).writeW (off p 8) v₂).readW (off p 8) 64 = v₂.extractLsb' 0 64 ∧
    ((m.writeW (off p 0) v₁).writeW (off p 8) v₂).readW (off p 16) 64 = v₂.extractLsb' 64 64 := by
  have z : off p 0 = p := by rw [off_eq, VG.Proof.Poly1305.X86_64.Avx2.addr0]
  have e16 : off p 16 = off p 8 + BitVec.ofNat 64 8 := by rw [off_eq, off_eq, BitVec.add_assoc]; rfl
  have hA := _root_.VG.X86_64.readW_writeW_off (m.writeW p v₁) p v₂ (d := 0) (e := 8) (n := 8) (by omega) (by omega)
    (by omega)
  have hB := readW_writeW_inside m p v₁ (k := 0) (n := 8) (by omega) (by omega)
  have hC := readW_writeW_inside (m.writeW p v₁) (off p 8) v₂ (k := 0) (n := 8) (by omega) (by omega)
  have hD := readW_writeW_inside (m.writeW p v₁) (off p 8) v₂ (k := 8) (n := 8) (by omega) (by omega)
  rw [VG.Proof.Poly1305.X86_64.Avx2.addr0] at hA hB hC
  rw [← off_eq] at hA
  simp only [Nat.reduceMul] at hA hB hC hD
  rw [z, e16]
  exact ⟨hA.trans hB, hC, hD⟩

/-- The limbs of lane 0 of `H`. -/
def h0 (s : State) : Nat → Nat := hv s 0

/-- What `storeH` leaves: the words of lane 0 of `H` in the state's first 24
bytes, and the rest but the vector registers as it was. -/
structure StorePost (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr
  frame : Frame [hR (s.gpr .rdi)] s.mem s'.mem
  w0 : (s'.mem.readW (off (s.gpr .rdi) 0) 64).toNat = Limbs26.w0 (VG.Proof.Poly1305.X86_64.Avx2.h0 s)
  w1 : (s'.mem.readW (off (s.gpr .rdi) 8) 64).toNat = Limbs26.w1 (VG.Proof.Poly1305.X86_64.Avx2.h0 s)
  w2 : (s'.mem.readW (off (s.gpr .rdi) 16) 64).toNat = VG.Proof.Poly1305.X86_64.Avx2.h0 s 4 / 2 ^ 24

theorem storeH_ok {s : State} (hw : ∀ d, d + 16 ≤ 24 → InRegions s.wr (off (s.gpr .rdi) d) 16) :
    WP isa (.block VG.Impl.Poly1305.X86_64.Avx2.storeH) s (VG.Proof.Poly1305.X86_64.Avx2.StorePost s) := by
  rw [VG.Proof.Poly1305.X86_64.Avx2.storeH_eq]
  refine WP.block_append (WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx2.svS_eq) fun s₁ h₁ => ?_)
  have g₁ := h₁.gpr
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.st128_ok s₁ 0 (by rw [h₁.wr, g₁]; exact hw 0 (by omega)))
    fun s₂ e₂ => ?_)
  refine WP.block_append (WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx2.upS_eq) fun s₃ h₃ => ?_)
  have hg₃ : s₃.gpr = s.gpr := by rw [h₃.gpr, e₂, State.setMem_gpr, g₁]
  have hw₃ : InRegions s₃.wr (off (s₃.gpr .rdi) 8) 16 := by
    rw [h₃.wr, e₂, State.setMem_wr, h₁.wr, hg₃]; exact hw 8 (by omega)
  refine WP.mono (VG.Proof.Poly1305.X86_64.Avx2.st128_ok s₃ 8 hw₃) fun s₄ e₄ => ?_
  have hm₃ : s₃.mem = s₁.mem.writeW (off (s.gpr .rdi) 0) (s₁.xmm tP) := by
    rw [h₃.mem, e₂, State.setMem_mem, g₁]
  have m₄ : s₄.mem = (s.mem.writeW (off (s.gpr .rdi) 0) (s₁.xmm tP)).writeW (off (s.gpr .rdi) 8)
      (s₃.xmm tP) := by
    rw [e₄, State.setMem_mem, hm₃, hg₃, h₁.mem]
  -- The words, from the terms.
  have q0 : (qw s₁ tP 0).toNat = Limbs26.w0 (VG.Proof.Poly1305.X86_64.Avx2.h0 s) := by
    rw [h₁.natw _ (by decide), VG.Proof.Poly1305.X86_64.Avx2.svS_tP]
    simp only [Q.natw, Nat.reduceMod, ite_true]
    rw [VG.Proof.Poly1305.X86_64.Avx2.svS_d1]; rfl
  have q1 : (qw s₃ tP 0).toNat = Limbs26.w1 (VG.Proof.Poly1305.X86_64.Avx2.h0 s) := by
    rw [h₃.natw _ (by decide), VG.Proof.Poly1305.X86_64.Avx2.upS_t0, envOf_v, e₂]
    change (qw s₁ (dreg 2) 0).toNat = _
    rw [h₁.natw _ (by decide), VG.Proof.Poly1305.X86_64.Avx2.svS_d2]; rfl
  have q2 : (qw s₃ tP 1).toNat = VG.Proof.Poly1305.X86_64.Avx2.h0 s 4 / 2 ^ 24 := by
    rw [h₃.natw _ (by decide), VG.Proof.Poly1305.X86_64.Avx2.upS_t1, envOf_v, e₂]
    change (qw s₁ (dreg 3) 0).toNat = _
    rw [h₁.natw _ (by decide), VG.Proof.Poly1305.X86_64.Avx2.svS_d3]; rfl
  obtain ⟨r0, r8, r16⟩ := VG.Proof.Poly1305.X86_64.Avx2.two_writes s.mem (s.gpr .rdi) (s₁.xmm tP) (s₃.xmm tP)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e₄, State.setMem_gpr, hg₃]
  · rw [e₄, State.setMem_rd, h₃.rd, e₂, State.setMem_rd, h₁.rd]
  · rw [e₄, State.setMem_wr, h₃.wr, e₂, State.setMem_wr, h₁.wr]
  · have vm : ∀ {a b : State}, vec a b = b → b.mxcsr = a.mxcsr := fun h => by rw [← h]; rfl
    rw [e₄, show ∀ t m, (State.setMem t m).mxcsr = t.mxcsr from fun _ _ => rfl, vm h₃.eq, e₂,
      show ∀ t m, (State.setMem t m).mxcsr = t.mxcsr from fun _ _ => rfl, vm h₁.eq]
  · rw [m₄]
    exact ((Frame.refl [hR (s.gpr .rdi)] s.mem).writeW (List.mem_singleton_self _) _
      (contains_off (by omega) (by omega))).writeW (List.mem_singleton_self _) _
      (contains_off (by omega) (by omega))
  · rw [m₄, r0, VG.Proof.Poly1305.X86_64.Avx2.xmm_lo, q0]
  · rw [m₄, r8, VG.Proof.Poly1305.X86_64.Avx2.xmm_lo, q1]
  · rw [m₄, r16, VG.Proof.Poly1305.X86_64.Avx2.xmm_hi, q2]

end VG.Proof.Poly1305.X86_64.Avx2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Group`. -/
section

/-!
# Poly1305 on x86-64 with AVX2: groups of four blocks

Each group of four blocks is added to the lanes of `H` and multiplied by `r⁴`
(Horner's rule in four lanes, `Horner.lean`); the last group is multiplied
lane by lane by `r⁴`, `r³`, `r²` and `r`, after which the sum of the lanes is
the accumulator.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx2
open VG.Spec.Poly1305 (P leNum bytesAt)
open VG.Proof.Poly1305 (mv lanes absorbAll)

/-- Block `k` of the group at `rsi`. -/
def blk (s : State) (k : Nat) : List Byte := bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (16 * k)) 16

theorem blk_length (s : State) (k : Nat) : (VG.Proof.Poly1305.X86_64.Avx2.blk s k).length = 16 := Poly1305.length_bytesAt _ _ _

theorem blk_mv (s : State) (k : Nat) : mv (VG.Proof.Poly1305.X86_64.Avx2.blk s k) = blo s k + 2 ^ 64 * bhi s k + 2 ^ 128 := by
  rw [mv, Poly1305.leNum_append, VG.Proof.Poly1305.X86_64.Avx2.blk, Poly1305.length_bytesAt, Poly1305.leNum_bytesAt_16]
  have e₁ : s.gpr .rsi + BitVec.ofNat 64 (16 * k) = s.gpr .rsi + BitVec.ofNat 64 (8 * (2 * k)) := by
    rw [show 16 * k = 8 * (2 * k) by omega]
  have e₂ : s.gpr .rsi + BitVec.ofNat 64 (16 * k) + 8 = s.gpr .rsi + BitVec.ofNat 64 (8 * (2 * k + 1)) := by
    rw [BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add,
      show 16 * k + 8 = 8 * (2 * k + 1) by omega]
  rw [e₂, e₁]
  simp only [blo, bhi, envOf]
  rfl

/-- The group at `rsi`, block by block. -/
theorem group_bytes (s : State) :
    bytesAt s.mem (s.gpr .rsi) 64 = VG.Proof.Poly1305.X86_64.Avx2.blk s 0 ++ VG.Proof.Poly1305.X86_64.Avx2.blk s 1 ++ VG.Proof.Poly1305.X86_64.Avx2.blk s 2 ++ VG.Proof.Poly1305.X86_64.Avx2.blk s 3 := by
  rw [show 64 = 48 + 16 from rfl, Poly1305.bytesAt_add, show 48 = 32 + 16 from rfl, Poly1305.bytesAt_add,
    show 32 = 16 + 16 from rfl, Poly1305.bytesAt_add]
  simp only [VG.Proof.Poly1305.X86_64.Avx2.blk]
  rw [show BitVec.ofNat 64 (16 * 0) = 0#64 from rfl, BitVec.add_zero]

/-- What holds of the vector registers between groups: `Y` holds the powers
of `R`, and the lanes of `H` (limbs below `2²⁷`) the accumulator `X`, after
Horner's rule in four lanes. -/
structure LaneInv (R X : Nat) (s : State) : Prop where
  y : VG.Proof.Poly1305.X86_64.Avx2.YInv s R
  hb : ∀ k < 4, ∀ i < 5, hv s k i < 2 ^ 27
  acc : lanes R (Limbs26.val (hv s 0)) (Limbs26.val (hv s 1)) (Limbs26.val (hv s 2))
    (Limbs26.val (hv s 3)) ≡ R ^ 4 * X [MOD P]

theorem YInv.of_y {s s' : State} {R : Nat} (h : VG.Proof.Poly1305.X86_64.Avx2.YInv s R) (hy : ∀ i < 5, ∀ k < 4, qw s' (yreg i) k = qw s (yreg i) k) :
    VG.Proof.Poly1305.X86_64.Avx2.YInv s' R := by
  have el : ∀ k < 4, yl s' k = yl s k := fun k hk => VG.Proof.Poly1305.X86_64.Avx2.ext5 (fun _ h => yl_ge _ _ h) (fun _ h => yl_ge _ _ h)
    fun i hi => by simp only [yl, hy i hi k hk]
  have eh : ∀ k < 4, VG.Proof.Poly1305.X86_64.Avx2.yh s' k = VG.Proof.Poly1305.X86_64.Avx2.yh s k := fun k hk => VG.Proof.Poly1305.X86_64.Avx2.ext5 (fun _ h => VG.Proof.Poly1305.X86_64.Avx2.yh_ge _ _ h) (fun _ h => VG.Proof.Poly1305.X86_64.Avx2.yh_ge _ _ h)
    fun i hi => by simp only [VG.Proof.Poly1305.X86_64.Avx2.yh, hy i hi k hk]
  exact ⟨fun k hk => by rw [el k hk]; exact h.lo k hk, fun k hk => by rw [eh k hk]; exact h.hi k hk,
    fun k hk => by rw [el k hk]; exact h.lob k hk, fun k hk => by rw [eh k hk]; exact h.hib k hk⟩

/-- `addGroup`, then `mul` by `Y`'s low doublewords: lane `k` becomes
`(V_k + m_k) · Y_k`. -/
theorem addMul_ok {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hr9 : s.gpr .r9 = 0x1000000) (hc : VG.Proof.Poly1305.X86_64.Avx2.Ctx s)
    (hb : ∀ k < 4, ∀ i < 5, hv s k i < 2 ^ 27) (hy : ∀ k < 4, ∀ i < 5, yl s k i < 2 ^ 27) :
    WP isa (.block (addGroup ++ mul)) s fun s' => vec s s' = s' ∧
      (∀ i < 5, ∀ k < 4, qw s' (yreg i) k = qw s (yreg i) k) ∧ (∀ k < 4, ∀ i < 5, hv s' k i < 2 ^ 27) ∧
      ∀ k < 4, Limbs26.val (hv s' k) ≡ (Limbs26.val (hv s k) + mv (VG.Proof.Poly1305.X86_64.Avx2.blk s k)) * Limbs26.val (yl s k) [MOD P] := by
  refine WP.block_append (WP.mono (addGroup_ok ⟨hr9, hc, hb⟩) fun s₁ A => ?_)
  have hyl : ∀ k < 4, yl s₁ k = yl s k := fun k hk => VG.Proof.Poly1305.X86_64.Avx2.ext5 (fun _ h => yl_ge _ _ h) (fun _ h => yl_ge _ _ h)
    fun i hi => by simp only [yl, A.y i hi k hk]
  refine WP.mono (mul_ok ⟨by rw [vec_gpr A.vec, hr8], A.hb, fun k hk i hi => by rw [hyl k hk]; exact hy k hk i hi⟩)
    fun s₂ M => ⟨vec_trans A.vec M.vec, fun i hi k hk => by rw [M.y i hi k hk, A.y i hi k hk], M.hb,
      fun k hk => ?_⟩
  rw [VG.Proof.Poly1305.X86_64.Avx2.val_congr (M.h k hk), VG.Proof.Poly1305.X86_64.Avx2.blk_mv, ← A.h k hk, ← hyl k hk]
  exact Limbs26.mul_mod _ _

/-- A group before the last: the invariant for the blocks so far and the group. -/
theorem group_ok {R X : Nat} {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hr9 : s.gpr .r9 = 0x1000000)
    (hc : VG.Proof.Poly1305.X86_64.Avx2.Ctx s) (hI : VG.Proof.Poly1305.X86_64.Avx2.LaneInv R X s) :
    WP isa (.block (addGroup ++ mul)) s fun s' => vec s s' = s' ∧
      VG.Proof.Poly1305.X86_64.Avx2.LaneInv R (absorbAll R X (bytesAt s.mem (s.gpr .rsi) 64)) s' := by
  refine WP.mono (VG.Proof.Poly1305.X86_64.Avx2.addMul_ok hr8 hr9 hc hI.hb hI.y.lob) fun s' ⟨hv', hy, hb, he⟩ => ⟨hv', hI.y.of_y hy, hb, ?_⟩
  rw [VG.Proof.Poly1305.X86_64.Avx2.group_bytes]
  exact Poly1305.horner_step (VG.Proof.Poly1305.X86_64.Avx2.blk_length s 0) (VG.Proof.Poly1305.X86_64.Avx2.blk_length s 1) (VG.Proof.Poly1305.X86_64.Avx2.blk_length s 2) (VG.Proof.Poly1305.X86_64.Avx2.blk_length s 3) hI.acc
    ((he 0 (by decide)).trans (Nat.ModEq.mul_left _ (hI.y.lo 0 (by decide))))
    ((he 1 (by decide)).trans (Nat.ModEq.mul_left _ (hI.y.lo 1 (by decide))))
    ((he 2 (by decide)).trans (Nat.ModEq.mul_left _ (hI.y.lo 2 (by decide))))
    ((he 3 (by decide)).trans (Nat.ModEq.mul_left _ (hI.y.lo 3 (by decide))))

/-! ## The last group -/

def shY : List Instr := (List.range 5).map fun i => srl (yreg i) (yreg i) 32

theorem last_eq : last = addGroup ++ (VG.Proof.Poly1305.X86_64.Avx2.shY ++ mul) := rfl

def shS : Sym := (Sym.init.run false VG.Proof.Poly1305.X86_64.Avx2.shY).get (by decide +kernel)
theorem shS_eq : Sym.init.run false VG.Proof.Poly1305.X86_64.Avx2.shY = some VG.Proof.Poly1305.X86_64.Avx2.shS := (Option.some_get _).symm
theorem shS_shape : ∀ i < 5, shS.reg (xi (yreg i)) = .shr (.reg (xi (yreg i))) 32 ∧
    shS.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

theorem shY_ok (s : State) :
    WP isa (.block VG.Proof.Poly1305.X86_64.Avx2.shY) s fun s' => vec s s' = s' ∧ (∀ k < 4, ∀ i < 5, hv s' k i = hv s k i ∧
      yl s' k i = VG.Proof.Poly1305.X86_64.Avx2.yh s k i) := by
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx2.shS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ⟨?_, ?_⟩⟩
  · simp only [hv]; rw [h.reg _ k hk, (VG.Proof.Poly1305.X86_64.Avx2.shS_shape i hi).2]; simp only [Q.eval, xr_xi]
  · simp only [yl, VG.Proof.Poly1305.X86_64.Avx2.yh]
    rw [h.natw _ hk, (VG.Proof.Poly1305.X86_64.Avx2.shS_shape i hi).1]
    simp only [Q.natw, envOf_v]
    have := (qw s (yreg i) k).isLt
    omega

/-- The last group: lane `k` multiplied by `r^(4-k)`, and the lanes' sum is
the accumulator. -/
theorem last_ok {R X : Nat} {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hr9 : s.gpr .r9 = 0x1000000)
    (hc : VG.Proof.Poly1305.X86_64.Avx2.Ctx s) (hI : VG.Proof.Poly1305.X86_64.Avx2.LaneInv R X s) :
    WP isa (.block last) s fun s' => vec s s' = s' ∧ (∀ k < 4, ∀ i < 5, hv s' k i < 2 ^ 27) ∧
      Limbs26.val (hv s' 0) + Limbs26.val (hv s' 1) + Limbs26.val (hv s' 2) + Limbs26.val (hv s' 3) ≡
        absorbAll R X (bytesAt s.mem (s.gpr .rsi) 64) [MOD P] := by
  rw [VG.Proof.Poly1305.X86_64.Avx2.last_eq]
  refine WP.block_append (WP.mono (addGroup_ok ⟨hr9, hc, hI.hb⟩) fun s₁ A => ?_)
  have Y₁ := hI.y.of_y A.y
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.shY_ok s₁) fun s₂ ⟨v₂, e₂⟩ => ?_)
  have hH : ∀ k < 4, hv s₂ k = hv s₁ k := fun k hk => VG.Proof.Poly1305.X86_64.Avx2.ext5 (fun _ h => hv_ge _ _ h) (fun _ h => hv_ge _ _ h)
    fun i hi => (e₂ k hk i hi).1
  have hY : ∀ k < 4, yl s₂ k = VG.Proof.Poly1305.X86_64.Avx2.yh s₁ k := fun k hk => VG.Proof.Poly1305.X86_64.Avx2.ext5 (fun _ h => yl_ge _ _ h) (fun _ h => VG.Proof.Poly1305.X86_64.Avx2.yh_ge _ _ h)
    fun i hi => (e₂ k hk i hi).2
  refine WP.mono (mul_ok ⟨by rw [vec_gpr v₂, vec_gpr A.vec, hr8], fun k hk i hi => by
      rw [hH k hk]; exact A.hb k hk i hi, fun k hk i hi => by rw [hY k hk]; exact Y₁.hib k hk i hi⟩)
    fun s₃ M => ⟨vec_trans (vec_trans A.vec v₂) M.vec, M.hb, ?_⟩
  have e : ∀ k < 4, Limbs26.val (hv s₃ k) ≡ (Limbs26.val (hv s k) + mv (VG.Proof.Poly1305.X86_64.Avx2.blk s k)) * R ^ (4 - k) [MOD P] := by
    intro k hk
    rw [VG.Proof.Poly1305.X86_64.Avx2.val_congr (M.h k hk), hH k hk, hY k hk, VG.Proof.Poly1305.X86_64.Avx2.blk_mv, ← A.h k hk]
    exact (Limbs26.mul_mod _ _).trans (Nat.ModEq.mul_left _ (Y₁.hi k hk))
  rw [VG.Proof.Poly1305.X86_64.Avx2.group_bytes]
  exact Poly1305.horner_last (VG.Proof.Poly1305.X86_64.Avx2.blk_length s 0) (VG.Proof.Poly1305.X86_64.Avx2.blk_length s 1) (VG.Proof.Poly1305.X86_64.Avx2.blk_length s 2) (VG.Proof.Poly1305.X86_64.Avx2.blk_length s 3) hI.acc
    (e 0 (by decide)) (e 1 (by decide)) (e 2 (by decide)) (by simpa using e 3 (by decide))

end VG.Proof.Poly1305.X86_64.Avx2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Gpr`. -/
section

/-!
# Poly1305 on x86-64 with AVX2: the integer instructions

The short blocks of integer instructions between the vector ones: constants,
the MXCSR prologue and epilogue, loading `r` and the accumulator's words, and
the counters.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx2
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Proof.Poly1305.X86_64 (off off_eq M0 M1)

/-- What a block of integer instructions leaves as it was: the vector
registers, MXCSR and the regions. -/
structure VKeep (s s' : State) : Prop where
  xmm : s'.xmm = s.xmm
  ymmHi : s'.ymmHi = s.ymmHi
  mxcsr : s'.mxcsr = s.mxcsr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem VKeep.qw_eq {s s' : State} (h : VG.Proof.Poly1305.X86_64.Avx2.VKeep s s') (r : XReg) (k : Nat) : qw s' r k = qw s r k := by
  unfold qw State.lane; rw [h.xmm, h.ymmHi]

theorem VKeep.trans {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Poly1305.X86_64.Avx2.VKeep s₁ s₂) (h₂ : VG.Proof.Poly1305.X86_64.Avx2.VKeep s₂ s₃) : VG.Proof.Poly1305.X86_64.Avx2.VKeep s₁ s₃ :=
  ⟨h₂.xmm.trans h₁.xmm, h₂.ymmHi.trans h₁.ymmHi, h₂.mxcsr.trans h₁.mxcsr, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr⟩

theorem vec_keep {s s' : State} (h : vec s s' = s') : s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr :=
  ⟨vec_gpr h, vec_mem h, vec_rd h, vec_wr h, by rw [← h]; rfl⟩

theorem se16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
theorem se32 : BitVec.signExtend 64 (BitVec.ofNat 32 32) = 32 := by decide
theorem se64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
theorem se1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
theorem se3 : BitVec.signExtend 64 (3 : BitVec 32) = 3 := by decide

set_option simprocs false in
theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 minBlocks))]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ VG.Proof.Poly1305.X86_64.Avx2.VKeep s s' ∧
      s'.cf = some (decide ((s.gpr .rdx).toNat < 32)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', minBlocks,
    VG.Proof.Poly1305.X86_64.Avx2.se32]
  exact ⟨trivial, trivial, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

set_option simprocs false in
theorem consts_ok (s : State) :
    WP isa (.block consts) s fun s' =>
      s'.gpr .r8 = 0x3ffffff ∧ s'.gpr .r9 = 0x1000000 ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VG.Proof.Poly1305.X86_64.Avx2.VKeep s s' := by
  apply WP.of_runBlock
  simp only [consts, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc32, State.setReg32, State.setReg, ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, fun r h₁ h₂ => by simp [h₁, h₂], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial

/-- Closes what `simp` leaves of a block of integer instructions. -/
macro "finish_gpr" : tactic => `(tactic| (
  all_goals repeat' first | apply And.intro | apply VKeep.mk
  all_goals first | trivial | rfl | (intros; simp [*])))

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = off (s.gpr b) d := rfl

/-- The memory `mxcsrIn` leaves: MXCSR with bits 31:16 cleared at byte 120,
and `0x1FBF` at byte 124. -/
def mxMem (m : Mem) (st : Addr) (x : BitVec 32) : Mem :=
  ((m.writeW (off st 120) x).writeW (off st 120) (x &&& 0xffff)).writeW (off st 124) (0x1FBF : BitVec 32)

set_option simprocs false in
theorem mxcsrIn_ok (s : State) (w₁ : InRegions s.wr (off (s.gpr .rdi) 120) 4)
    (w₂ : InRegions s.wr (off (s.gpr .rdi) 124) 4) (r₁ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 120) 4)
    (r₂ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 124) 4) :
    WP isa (.block mxcsrIn) s fun s' =>
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = VG.Proof.Poly1305.X86_64.Avx2.mxMem s.mem (s.gpr .rdi) s.mxcsr ∧
      s'.mxcsr = 0x1FBF ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mxcsrIn, runBlock_cons, runStep_some, runBlock_nil, exec,
    VG.Proof.Poly1305.X86_64.Avx2.ea_at, readSrc32, execAlu32, arithFlags, State.load32, State.store32, State.setReg32, State.setReg,
    State.setFlags, w₁, w₂, r₁, r₂, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', Mem.readW_writeW_self32, RegUpd.setWidth_setWidth_32]
  refine ⟨fun r h => by simp [h], ?_, trivial⟩
  rfl

theorem powers_split : consts ++ mxcsrIn ++ powers ++ loadHw ++ loadH ++
    ([.mov .rcx (.reg .rdx), .shift .shr .rcx 2, .alu .sub .rcx (.imm 1)] : List Instr) =
    consts ++ (mxcsrIn ++ (VG.Proof.Poly1305.X86_64.Avx2.loadRg ++ (VG.Proof.Poly1305.X86_64.Avx2.powersV ++ (loadHw ++ (loadH ++
      ([.mov .rcx (.reg .rdx), .shift .shr .rcx 2, .alu .sub .rcx (.imm 1)] : List Instr)))))) := by
  simp only [VG.Proof.Poly1305.X86_64.Avx2.powers_eq, List.append_assoc]

set_option simprocs false in
theorem loadRg_ok (s : State) (r₁ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 24) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 32) 8) :
    WP isa (.block VG.Proof.Poly1305.X86_64.Avx2.loadRg) s fun s' =>
      s'.gpr .r10 = s.mem.readW (off (s.gpr .rdi) 24) 64 &&& M0 ∧
      s'.gpr .r11 = s.mem.readW (off (s.gpr .rdi) 32) 64 &&& M1 ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VG.Proof.Poly1305.X86_64.Avx2.VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Proof.Poly1305.X86_64.Avx2.loadRg, runBlock_cons, runStep_some, runBlock_nil, exec,
    VG.Proof.Poly1305.X86_64.Avx2.ea_at, readSrc, execAlu, arithFlags, State.load64, State.setReg, State.setFlags, r₁, r₂, ite_true,
    ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  finish_gpr

set_option simprocs false in
theorem loadHw_ok (s : State) (r₀ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 0) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 8) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 16) 8) :
    WP isa (.block loadHw) s fun s' =>
      s'.gpr .r10 = s.mem.readW (off (s.gpr .rdi) 0) 64 ∧
      s'.gpr .r11 = s.mem.readW (off (s.gpr .rdi) 8) 64 ∧
      s'.gpr .rax = s.mem.readW (off (s.gpr .rdi) 16) 64 ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VG.Proof.Poly1305.X86_64.Avx2.VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [loadHw, runBlock_cons, runStep_some, runBlock_nil, exec,
    VG.Proof.Poly1305.X86_64.Avx2.ea_at, readSrc, State.load64, State.setReg, r₀, r₁, r₂, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  finish_gpr

set_option simprocs false in
theorem rcx_ok (s : State) :
    WP isa (.block [.mov .rcx (.reg .rdx), .shift .shr .rcx 2, .alu .sub .rcx (.imm 1)]) s fun s' =>
      s'.gpr .rcx = (s.gpr .rdx >>> 2) - 1 ∧ (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      VG.Proof.Poly1305.X86_64.Avx2.VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, execAlu, arithFlags, State.setReg, State.setFlags, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', VG.Proof.Poly1305.X86_64.Avx2.se1]
  finish_gpr

set_option simprocs false in
theorem adv_ok (s : State) :
    WP isa (.block [.alu .add .rsi (.imm 64), .alu .sub .rcx (.imm 1)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rsi + 64 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ (∀ r, r ≠ .rsi → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ VG.Proof.Poly1305.X86_64.Avx2.VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left', VG.Proof.Poly1305.X86_64.Avx2.se1, VG.Proof.Poly1305.X86_64.Avx2.se64]
  finish_gpr

set_option simprocs false in
theorem consts2_ok (s : State) :
    WP isa (.block consts2) s fun s' =>
      s'.gpr .rax = 5 ∧ s'.gpr .r10 = 0x7ffffff ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VG.Proof.Poly1305.X86_64.Avx2.VKeep s s' := by
  apply WP.of_runBlock
  simp only [consts2, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc32, State.setReg32, State.setReg, ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left']
  finish_gpr

set_option simprocs false in
theorem mxcsrOut_ok (s : State) (r₁ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 120) 4)
    (hz : (s.mem.readW (off (s.gpr .rdi) 120) 32).extractLsb' 16 16 = 0) :
    WP isa (.block mxcsrOut) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mem.readW (off (s.gpr .rdi) 120) 32 ∧
      s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [mxcsrOut, runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.Poly1305.X86_64.Avx2.ea_at, State.load32, r₁, hz,
    ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  finish_gpr

set_option simprocs false in
theorem fin3_ok (s : State) :
    WP isa (.block [.vop .vzeroupper, .alu .add .rsi (.imm 64), .alu .and .rdx (.imm 3)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rsi + 64 ∧ s'.gpr .rdx = s.gpr .rdx &&& 3 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [and_self, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, VOp.exec, ite_true,
    Option.bind_some, Option.some.injEq, exists_eq_left', VG.Proof.Poly1305.X86_64.Avx2.se3, VG.Proof.Poly1305.X86_64.Avx2.se64]
  finish_gpr

set_option simprocs false in
theorem test_ok (s : State) :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) s fun s' =>
      s'.zf = some (s.gpr .rdx &&& s.gpr .rdx == 0) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']

end VG.Proof.Poly1305.X86_64.Avx2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit`. -/
section

/-!
# Poly1305 on x86-64 with AVX2: the code as a literal

`blocksAvx2` as a literal (`materialize_code`, `Proof/Framework/Lit.lean`),
which the kernel checks once here and then evaluates in every check of the
code (constant time, `spSafe`, properties of every instruction).
-/

namespace VG

materialize_code Impl.Poly1305.X86_64.Avx2.blocksAvx2

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Blocks`. -/
section

/-!
# Poly1305 on x86-64 with AVX2: `vg_poly1305_blocks_avx2`

The whole function: with fewer than 32 blocks, or for the last `n mod 4`, it
calls `vg_poly1305_blocks`; otherwise it absorbs the blocks four at a time
(see `Impl/Poly1305/X86_64/Avx2.lean`).

The vector code computes the right numbers only if the accumulator on entry
is below `2¹⁹⁴` (its top word below 4), which holds whenever the state
represents a message; it runs, and leaves everything but the vector
registers as the proofs of its blocks say, whatever the state holds. So each
block's effect on the vector registers is established under that
assumption (`hA`), and its execution without it (`guard`).
-/

open VG.Proof.Poly1305.Limbs64

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx2
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Spec.Poly1305 (P leNum bytesAt accumulate Repr clamp)

/-- The contract the proof is written against: `blocksX86_64`'s, with the
8 bytes of stack below the return address that its call uses. -/
def blocksAvx2X86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let blocks : Region := ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 8, 8⟩
    s.rd = [blocks] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧ ret.Disjoint state ∧
      stack.Disjoint state ∧ stack.Disjoint blocks ∧
      (s.gpr .rsi).toNat + 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64
  post := Proof.Poly1305.blocksX86_64.post
  pub s₁ s₂ := Proof.Poly1305.blocksX86_64.pub s₁ s₂ ∧ s₁.gpr .rsp = s₂.gpr .rsp

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [sR (st s₀)]
  st_bl : (sR (st s₀)).Disjoint (blR s₀)
  ret_st : (retR s₀).Disjoint (sR (st s₀))
  stk_st : (below (s₀.gpr .rsp) 8).Disjoint (sR (st s₀))
  stk_bl : (below (s₀.gpr .rsp) 8).Disjoint (blR s₀)
  nowrap : (bp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : blocksAvx2X86_64.pre s₀) : VG.Proof.Poly1305.X86_64.Avx2.APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem APre.bpre {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.APre s₀) : BPre s₀ :=
  ⟨hp.rd, hp.wr, hp.st_bl, hp.ret_st, hp.nowrap⟩

/-- What the function guarantees. -/
def Post (s₀ s : State) : Prop := abiPreserved s₀ s ∧ Proof.Poly1305.blocksX86_64.post s₀ s

/-! ## Executions that establish more under an assumption -/

/-- An execution that satisfies `R`, and `Q` if `A` holds. -/
theorem guard {c : Prog isa} {s : State} {R Q : State → Prop} {A : Prop} (hR : WP isa c s R)
    (hQ : A → WP isa c s Q) : WP isa c s fun s' => R s' ∧ (A → Q s') := by
  obtain ⟨t, s', he, hr⟩ := hR
  refine ⟨t, s', he, hr, fun ha => ?_⟩
  obtain ⟨t', s'', he', hq⟩ := hQ ha
  obtain ⟨-, rfl⟩ := Exec.det he he'
  exact hq

/-- A property of every execution. -/
theorem and_exec {c : Prog isa} {s : State} {Q R : State → Prop} (h : WP isa c s Q)
    (hR : ∀ t s', Exec isa c s t s' → R s') : WP isa c s fun s' => Q s' ∧ R s' := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, hR t s' he⟩

/-! ## Memory outside the state -/

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- A state represents the same message after writes outside it. -/
theorem repr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (sR p).Disjoint r) {key msg : List Byte} (h : Repr m p key msg) :
    Repr m' p key msg := by
  obtain ⟨h1, h2, h3⟩ := h
  have s₁ : Region.Sub ⟨p + 24, 32⟩ (sR p) := by rw [← off_24]; exact sub_sR p (by omega)
  have s₂ : Region.Sub ⟨p, 24⟩ (sR p) := by
    have := sub_sR p (d := 0) (n := 24) (by omega)
    rwa [off_eq, BitVec.add_zero] at this
  refine ⟨h1, ?_, ?_⟩
  · rw [VG.Proof.Poly1305.X86_64.Avx2.bytesAt_frame hf (fun r hr => (hd r hr).sub_left s₁) (by omega), h2]
  · rw [VG.Proof.Poly1305.X86_64.Avx2.bytesAt_frame hf (fun r hr => (hd r hr).sub_left s₂) (by omega), h3]

theorem blks_split (s₀ : State) {i : Nat} (hi : i ≤ nb s₀) :
    blks s₀ i ++ bytesAt s₀.mem (blkAddr s₀ i) (16 * (nb s₀ - i)) = blks s₀ (nb s₀) := by
  simp only [blks, blkAddr]
  rw [← Poly1305.bytesAt_add, show 16 * i + 16 * (nb s₀ - i) = 16 * nb s₀ by omega]

theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (below (s₀.gpr .rsp) 8) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 8) (d := 8) (n := 8) (k := 8)
    (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

/-! ## The call of `vg_poly1305_blocks` -/

/-- Before the call of `vg_poly1305_blocks` for the blocks from block `i`
on (or the return, if there are none). -/
structure TailPre (s₀ : State) (i : Nat) (s : State) : Prop where
  le : i ≤ nb s₀
  rdi : s.gpr .rdi = st s₀
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [hR (st s₀), wR (st s₀)] s₀.mem s.mem
  mxcsr : s.mxcsr.extractLsb' 6 10 = s₀.mxcsr.extractLsb' 6 10
  repr : ∀ key msg, Repr s₀.mem (st s₀) key msg → Repr s.mem (st s₀) key (msg ++ blks s₀ i)

theorem ret_frame {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.APre s₀) : ∀ r ∈ [hR (st s₀), wR (st s₀)], (retR s₀).Disjoint r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hp.ret_st.sub_right (Region.sub_prefix (by omega))
  · exact hp.ret_st.sub_right (sub_sR _ (by omega))

theorem done_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.APre s₀) {s : State} (h : VG.Proof.Poly1305.X86_64.Avx2.TailPre s₀ (nb s₀) s) : VG.Proof.Poly1305.X86_64.Avx2.Post s₀ s :=
  ⟨⟨h.keep, h.frame.readW (Region.contains_self _ _) (VG.Proof.Poly1305.X86_64.Avx2.ret_frame hp) (by decide), h.mxcsr⟩,
    fun key msg hr => h.repr key msg hr⟩

theorem blocks_keeps :
    ((instrs Impl.Poly1305.X86_64.blocks).all fun i => !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem blocks_nosp : NoSp Impl.Poly1305.X86_64.blocks := by
  intro i hi
  simpa using List.all_eq_true.mp VG.Proof.Poly1305.X86_64.Avx2.blocks_keeps i hi

theorem blocks_depth : Impl.Poly1305.X86_64.blocks.depth = 0 := by lit_decide

theorem blocks_mx : ((instrs Impl.Poly1305.X86_64.blocks).all fun i => !loadsMxcsr i) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem scalar_mxcsr {s s' : State} {t : List Leak} (h : Exec isa scalar s t s') : s'.mxcsr = s.mxcsr :=
  Exec.mxcsr (c := scalar) (fun i hi => by simpa using List.all_eq_true.mp VG.Proof.Poly1305.X86_64.Avx2.blocks_mx i hi) h

theorem tail_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.APre s₀) {i : Nat} {s : State} (h : VG.Proof.Poly1305.X86_64.Avx2.TailPre s₀ i s) :
    WP isa scalar s (VG.Proof.Poly1305.X86_64.Avx2.Post s₀) := by
  have hn := hp.bpre.nb_lt
  have hsp : s.gpr .rsp = s₀.gpr .rsp := h.keep .rsp (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  have hdx : (s.gpr .rdx).toNat = nb s₀ - i := by rw [h.rdx, toNat_ofNat_lt (by omega)]
  have hle := h.le
  have tsub : Region.Sub ⟨blkAddr s₀ i, 16 * (nb s₀ - i)⟩ (blR s₀) :=
    Offset.sub_base _ (by omega)
  have stkR : below (s.gpr .rsp) 8 = below (s₀.gpr .rsp) 8 := by rw [hsp]
  refine WP.mono (VG.Proof.Poly1305.X86_64.Avx2.and_exec (Q := fun s' => gprPreserved s₀ s' ∧ Proof.Poly1305.blocksX86_64.post s₀ s')
    ?_ fun _ _ he => VG.Proof.Poly1305.X86_64.Avx2.scalar_mxcsr he) fun s' ⟨⟨g, p⟩, m⟩ => ⟨⟨g.1, g.2, by rw [m]; exact h.mxcsr⟩, p⟩
  refine WP.call (k := Proof.Poly1305.blocksX86_64) blocks_ok VG.Proof.Poly1305.X86_64.Avx2.blocks_nosp (by rw [VG.Proof.Poly1305.X86_64.Avx2.blocks_depth]; decide)
    (rd := [⟨blkAddr s₀ i, 16 * (nb s₀ - i)⟩]) (wr := [sR (st s₀)]) ?_ ?_ ?_ ?_
  · simp only [Proof.Poly1305.blocksX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, hdx, hsp]
    refine ⟨trivial, trivial, hp.st_bl.sub_right tsub, hp.stk_st, ?_⟩
    have := hp.nowrap
    simp only [blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨blR s₀, by simp, 16 * i, rfl, show 16 * i + 16 * (nb s₀ - i) ≤ 16 * nb s₀ by omega⟩
    · exact ⟨sR (st s₀), by simp, 0, by simp, show 0 + 128 ≤ 128 by omega⟩
  · rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨sR (st s₀), by simp, 0, by simp, show 0 + 128 ≤ 128 by omega⟩
  · intro s' _ _ hcs hf _ ⟨s₂, hm₂, _, hpost⟩
    rw [VG.Proof.Poly1305.X86_64.Avx2.blocks_depth, stkR] at hf
    have Fce : Frame [below (s₀.gpr .rsp) 8] s.mem s.callEntry.mem := by
      rw [State.callEntry_mem, hsp]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega))
    simp only [Proof.Poly1305.blocksX86_64, State.withRegions_gpr, State.withRegions_mem,
      hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
      hne _ (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, hdx, hm₂] at hpost
    refine ⟨⟨fun r hr => by rw [hcs r hr]; exact h.keep r hr, ?_⟩, fun key msg hr => ?_⟩
    · refine (hf.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)).trans ?_
      · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact hp.ret_st
        · exact VG.Proof.Poly1305.X86_64.Avx2.ret_stk s₀
      · exact h.frame.readW (Region.contains_self _ _) (VG.Proof.Poly1305.X86_64.Avx2.ret_frame hp) (by decide)
    · have r₁ := VG.Proof.Poly1305.X86_64.Avx2.repr_frame Fce (by simpa using hp.stk_st.symm) (h.repr key msg hr)
      have x := hpost key _ r₁
      have tb : bytesAt s.callEntry.mem (blkAddr s₀ i) (16 * (nb s₀ - i)) =
          bytesAt s₀.mem (blkAddr s₀ i) (16 * (nb s₀ - i)) := by
        rw [VG.Proof.Poly1305.X86_64.Avx2.bytesAt_frame Fce (by simpa using (hp.stk_bl.sub_right tsub).symm) (by omega),
          VG.Proof.Poly1305.X86_64.Avx2.bytesAt_frame h.frame (fun r hr => ?_) (by omega)]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (hp.st_bl.symm.sub_left tsub).sub_right (Region.sub_prefix (by omega))
        · exact (hp.st_bl.symm.sub_left tsub).sub_right (sub_sR _ (by omega))
      rw [tb, List.append_assoc, VG.Proof.Poly1305.X86_64.Avx2.blks_split s₀ hle] at x
      exact x

/-! ## Registers, memory and the vector state -/

theorem cs_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧
    r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem qw_of {s s' : State} (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi) (r : XReg) (k : Nat) :
    qw s' r k = qw s r k := by
  unfold qw State.lane; rw [hx, hy]

theorem LaneInv.of_qw {R X : Nat} {s s' : State} (h : ∀ r k, qw s' r k = qw s r k)
    (hI : VG.Proof.Poly1305.X86_64.Avx2.LaneInv R X s) : VG.Proof.Poly1305.X86_64.Avx2.LaneInv R X s' := by
  have e₁ : hv s' = hv s := by funext k i; simp only [hv, h]
  have e₂ : yl s' = yl s := by funext k i; simp only [yl, h]
  have e₃ : VG.Proof.Poly1305.X86_64.Avx2.yh s' = VG.Proof.Poly1305.X86_64.Avx2.yh s := by funext k i; simp only [VG.Proof.Poly1305.X86_64.Avx2.yh, h]
  obtain ⟨⟨lo, hi, lob, hib⟩, hb, acc⟩ := hI
  exact ⟨⟨by rw [e₂]; exact lo, by rw [e₃]; exact hi, by rw [e₂]; exact lob, by rw [e₃]; exact hib⟩,
    by rw [e₁]; exact hb, by rw [e₁]; exact acc⟩

theorem APre.inW {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.APre s₀) {s : State} (hw : s.wr = s₀.wr)
    (hr : s.gpr .rdi = st s₀) {d n : Nat} (h : d + n ≤ 128) : InRegions s.wr (off (s.gpr .rdi) d) n :=
  ⟨sR (st s₀), by rw [hw, hp.wr]; exact List.mem_singleton_self _, by rw [hr]; exact contains_off h (by omega)⟩

theorem APre.inRW {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.APre s₀) {s : State} (hw : s.wr = s₀.wr)
    (hr : s.gpr .rdi = st s₀) {d n : Nat} (h : d + n ≤ 128) :
    InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) d) n :=
  let ⟨r, hm, hc⟩ := hp.inW hw hr h
  ⟨r, List.mem_append_right _ hm, hc⟩

theorem rd_off (m : Mem) (p : Addr) {w : Nat} (v : BitVec w) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (hk : w / 8 ≤ 16) (h : d + 8 ≤ e ∨ e + w / 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  Mem.readW_writeW_sep (sep_off p hd he (by omega) hk h) (by decide)

theorem mxMem_read (m : Mem) (p : Addr) (x : BitVec 32) {d : Nat} (hd : d + 8 ≤ 120) :
    (VG.Proof.Poly1305.X86_64.Avx2.mxMem m p x).readW (off p d) 64 = m.readW (off p d) 64 := by
  simp only [VG.Proof.Poly1305.X86_64.Avx2.mxMem]
  rw [VG.Proof.Poly1305.X86_64.Avx2.rd_off _ _ _ (by omega) (by omega) (by decide) (by omega),
    VG.Proof.Poly1305.X86_64.Avx2.rd_off _ _ _ (by omega) (by omega) (by decide) (by omega),
    VG.Proof.Poly1305.X86_64.Avx2.rd_off _ _ _ (by omega) (by omega) (by decide) (by omega)]

theorem mxMem_frame (m : Mem) (p : Addr) (x : BitVec 32) : Frame [wR p] m (VG.Proof.Poly1305.X86_64.Avx2.mxMem m p x) :=
  (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (wR_contains p (d := 120) (n := 4) (by omega)
    (by omega))).writeW (List.mem_singleton_self _) _ (wR_contains p (d := 120) (n := 4) (by omega)
    (by omega))).writeW (List.mem_singleton_self _) _ (wR_contains p (d := 124) (n := 4) (by omega)
    (by omega))

theorem mxMem_mx (m : Mem) (p : Addr) (x : BitVec 32) :
    (VG.Proof.Poly1305.X86_64.Avx2.mxMem m p x).readW (off p 120) 32 = x &&& 0xffff := by
  simp only [VG.Proof.Poly1305.X86_64.Avx2.mxMem]
  rw [Mem.readW_writeW_sep (sep_off p (by omega) (by omega) (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self32]

theorem mx_hi (x : BitVec 32) : (x &&& 0xffff).extractLsb' 16 16 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_and]
  rw [show (0xffff : BitVec 32).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, show (0 : BitVec 16).toNat = 0 from rfl]
  have := x.isLt
  omega

theorem mx_bits (x : BitVec 32) : (x &&& 0xffff).extractLsb' 6 10 = x.extractLsb' 6 10 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_and]
  rw [show (0xffff : BitVec 32).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

theorem rcx_val (x : BitVec 64) (h : 4 ≤ x.toNat) : (x >>> 2) - 1 = BitVec.ofNat 64 (x.toNat / 4 - 1) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    show (1 : BitVec 64).toNat = 1 from rfl]
  omega

/-- The top word of the accumulator of a state that represents a message. -/
theorem H2_lt {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) : H2 s₀ < 4 := by
  have := Poly1305.accumulate_lt (clamp (leNum (key.take 16))) msg
  rw [← h.2.2, leNum_acc] at this
  simp only [H2, P] at this ⊢
  omega

/-! ## The prologue -/

/-- Before group `j` of four blocks (the loop's invariant). -/
structure LInv (s₀ : State) (j : Nat) (s : State) : Prop where
  lt : j < nb s₀ / 4
  rdi : s.gpr .rdi = st s₀
  rsi : s.gpr .rsi = blkAddr s₀ (4 * j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (nb s₀ / 4 - 1 - j)
  rdx : s.gpr .rdx = s₀.gpr .rdx
  r8 : s.gpr .r8 = 0x3ffffff
  r9 : s.gpr .r9 = 0x1000000
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = VG.Proof.Poly1305.X86_64.Avx2.mxMem s₀.mem (st s₀) s₀.mxcsr
  acc : H2 s₀ < 4 → VG.Proof.Poly1305.X86_64.Avx2.LaneInv (Rn s₀) (Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ (4 * j))) s

theorem pro_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.APre s₀) (hbig : 32 ≤ nb s₀) {s : State} (hg : s.gpr = s₀.gpr)
    (hm : s.mem = s₀.mem) (hk : VG.Proof.Poly1305.X86_64.Avx2.VKeep s₀ s) :
    WP isa (.block (consts ++ mxcsrIn ++ powers ++ loadHw ++ loadH ++
      ([.mov .rcx (.reg .rdx), .shift .shr .rcx 2, .alu .sub .rcx (.imm 1)] : List Instr))) s
      (VG.Proof.Poly1305.X86_64.Avx2.LInv s₀ 0) := by
  rw [VG.Proof.Poly1305.X86_64.Avx2.powers_split]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.consts_ok s) fun s₁ ⟨r8₁, r9₁, g₁, m₁, k₁⟩ => ?_)
  have rdi₁ : s₁.gpr .rdi = st s₀ := by rw [g₁ _ (by decide) (by decide), hg]
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, hk.wr]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.mxcsrIn_ok s₁ (hp.inW wr₁ rdi₁ (by omega)) (hp.inW wr₁ rdi₁ (by omega))
    (hp.inRW wr₁ rdi₁ (by omega)) (hp.inRW wr₁ rdi₁ (by omega)))
    fun s₂ ⟨g₂, m₂, _, x₂, y₂, rd₂, wr₂⟩ => ?_)
  have rdi₂ : s₂.gpr .rdi = st s₀ := by rw [g₂ _ (by decide), rdi₁]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  have mm₂ : s₂.mem = VG.Proof.Poly1305.X86_64.Avx2.mxMem s₀.mem (st s₀) s₀.mxcsr := by rw [m₂, m₁, hm, rdi₁, k₁.mxcsr, hk.mxcsr]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.loadRg_ok s₂ (hp.inRW wr₂' rdi₂ (by omega)) (hp.inRW wr₂' rdi₂ (by omega)))
    fun s₃ ⟨r10₃, r11₃, g₃, m₃, k₃⟩ => ?_)
  have r8₃ : s₃.gpr .r8 = 0x3ffffff := by rw [g₃ _ (by decide) (by decide) (by decide), g₂ _ (by decide), r8₁]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.powersV_ok r8₃) fun s₄ ⟨v₄, Y₄⟩ => ?_)
  obtain ⟨vg₄, vm₄, vrd₄, vwr₄, -⟩ := VG.Proof.Poly1305.X86_64.Avx2.vec_keep v₄
  have rdi₄ : s₄.gpr .rdi = st s₀ := by rw [vg₄, g₃ _ (by decide) (by decide) (by decide), rdi₂]
  have wr₄ : s₄.wr = s₀.wr := by rw [vwr₄, k₃.wr, wr₂']
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.loadHw_ok s₄ (hp.inRW wr₄ rdi₄ (by omega)) (hp.inRW wr₄ rdi₄ (by omega))
    (hp.inRW wr₄ rdi₄ (by omega))) fun s₅ ⟨a₅, b₅, c₅, g₅, m₅, k₅⟩ => ?_)
  have mm₄ : s₄.mem = VG.Proof.Poly1305.X86_64.Avx2.mxMem s₀.mem (st s₀) s₀.mxcsr := by rw [vm₄, m₃, mm₂]
  have ax₅ : (s₅.gpr .rax).toNat = H2 s₀ := by
    rw [c₅, rdi₄, mm₄, VG.Proof.Poly1305.X86_64.Avx2.mxMem_read _ _ _ (by omega)]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.guard (R := fun s' => vec s₅ s' = s') (A := H2 s₀ < 4)
    (WP.mono (run_ok (fun h => by cases h) VG.Proof.Poly1305.X86_64.Avx2.ldS_eq) fun _ h => h.eq)
    fun hA => VG.Proof.Poly1305.X86_64.Avx2.loadH_ok (by rw [ax₅]; exact hA)) fun s₆ ⟨v₆, L₆⟩ => ?_)
  obtain ⟨vg₆, vm₆, vrd₆, vwr₆, -⟩ := VG.Proof.Poly1305.X86_64.Avx2.vec_keep v₆
  refine WP.mono (VG.Proof.Poly1305.X86_64.Avx2.rcx_ok s₆) fun s₇ ⟨c₇, g₇, m₇, k₇⟩ => ?_
  have gk : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
      s₇.gpr r = s₀.gpr r := by
    intro r a c e f g h
    rw [g₇ r c, vg₆, g₅ r a g h, vg₄, g₃ r a g h, g₂ r a, g₁ r e f, hg]
  have hq₇ : ∀ r k, qw s₇ r k = qw s₆ r k := fun r k => k₇.qw_eq r k
  have hb' := hbig
  simp only [nb] at hb'
  refine ⟨by simp only [nb]; omega, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, fun hA => ?_⟩
  · exact gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [blkAddr]
  · rw [c₇, vg₆, g₅ _ (by decide) (by decide) (by decide), vg₄, g₃ _ (by decide) (by decide) (by decide),
      g₂ _ (by decide), g₁ _ (by decide) (by decide), hg, VG.Proof.Poly1305.X86_64.Avx2.rcx_val _ (by omega), nb, Nat.sub_zero]
  · exact gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [g₇ _ (by decide), vg₆, g₅ _ (by decide) (by decide) (by decide), vg₄,
      g₃ _ (by decide) (by decide) (by decide), g₂ _ (by decide), r8₁]
  · rw [g₇ _ (by decide), vg₆, g₅ _ (by decide) (by decide) (by decide), vg₄,
      g₃ _ (by decide) (by decide) (by decide), g₂ _ (by decide), r9₁]
  · obtain ⟨a, c, -, -, e, f, g, h⟩ := VG.Proof.Poly1305.X86_64.Avx2.cs_ne hr
    exact gk r a c e f g h
  · rw [k₇.rd, vrd₆, k₅.rd, vrd₄, k₃.rd, rd₂, k₁.rd, hk.rd]
  · rw [k₇.wr, vwr₆, k₅.wr, wr₄]
  · rw [m₇, vm₆, m₅, mm₄]
  · -- The accumulator in lane 0, `Y` from `powers`.
    have L := L₆ hA
    have rN₃ : VG.Proof.Poly1305.X86_64.Avx2.rN s₃ = Rn s₀ := by
      simp only [VG.Proof.Poly1305.X86_64.Avx2.rN, Rn, R0, R1]
      rw [r10₃, r11₃, rdi₂, mm₂, VG.Proof.Poly1305.X86_64.Avx2.mxMem_read _ _ _ (by omega), VG.Proof.Poly1305.X86_64.Avx2.mxMem_read _ _ _ (by omega)]
    have hN₅ : VG.Proof.Poly1305.X86_64.Avx2.hN s₅ = A0 s₀ := by
      simp only [VG.Proof.Poly1305.X86_64.Avx2.hN, A0]
      rw [a₅, b₅, c₅, rdi₄, mm₄, VG.Proof.Poly1305.X86_64.Avx2.mxMem_read _ _ _ (by omega), VG.Proof.Poly1305.X86_64.Avx2.mxMem_read _ _ _ (by omega),
        VG.Proof.Poly1305.X86_64.Avx2.mxMem_read _ _ _ (by omega), leNum_acc]
    have Y₆ : VG.Proof.Poly1305.X86_64.Avx2.YInv s₆ (Rn s₀) := by
      rw [← rN₃]
      exact (Y₄.of_y fun i hi k hk => k₅.qw_eq _ _).of_y L.y
    refine LaneInv.of_qw (fun r k => (hq₇ r k)) ⟨Y₆, fun k hk i hi => by have := L.hb k hk i hi; omega, ?_⟩
    simp only [Nat.mul_zero, blks_zero, Poly1305.absorbAll_nil]
    rw [L.h 0 (by decide), L.h 1 (by decide), L.h 2 (by decide), L.h 3 (by decide), hN₅]
    simp only [reduceCtorEq, ↓reduceIte, lanes, Nat.mul_zero, Nat.add_zero]
    exact Nat.ModEq.refl _

/-! ## The loop -/

theorem grp_sub {s₀ : State} {j : Nat} (hj : 4 * j + 4 ≤ nb s₀) :
    Region.Sub ⟨blkAddr s₀ (4 * j), 64⟩ (blR s₀) :=
  Offset.sub_base _ (by omega)

theorem ctx_of {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.APre s₀) {s : State} (hrd : s.rd = s₀.rd) {j : Nat}
    (hsi : s.gpr .rsi = blkAddr s₀ (4 * j)) (hj : 4 * j + 4 ≤ nb s₀) : Ctx s := by
  intro i hi
  have := hp.bpre.nb_lt
  refine ⟨blR s₀, by rw [hrd, hp.rd]; simp, ?_⟩
  rw [hsi, blkAddr, Offset.add_add]
  exact Offset.contains_base _ (by rcases hi with rfl | rfl <;> omega) (by rcases hi with rfl | rfl <;> omega)

/-- The group of blocks at `rsi`, from the memory the prologue leaves. -/
theorem grp_bytes {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.APre s₀) {j : Nat} (hj : 4 * j + 4 ≤ nb s₀) :
    bytesAt (VG.Proof.Poly1305.X86_64.Avx2.mxMem s₀.mem (st s₀) s₀.mxcsr) (blkAddr s₀ (4 * j)) 64 = bytesAt s₀.mem (blkAddr s₀ (4 * j)) 64 :=
  VG.Proof.Poly1305.X86_64.Avx2.bytesAt_frame (VG.Proof.Poly1305.X86_64.Avx2.mxMem_frame _ _ _) (by
    simpa using (hp.st_bl.symm.sub_left (VG.Proof.Poly1305.X86_64.Avx2.grp_sub hj)).sub_right (sub_sR _ (by omega))) (by omega)

theorem absorb_grp (s₀ : State) (R X : Nat) (j : Nat) :
    Poly1305.absorbAll R (Poly1305.absorbAll R X (blks s₀ (4 * j))) (bytesAt s₀.mem (blkAddr s₀ (4 * j)) 64) =
      Poly1305.absorbAll R X (blks s₀ (4 * (j + 1))) := by
  rw [← Poly1305.absorbAll_append (by simp only [blks, Poly1305.length_bytesAt]; omega)]
  simp only [blks, blkAddr]
  rw [← Poly1305.bytesAt_add, show 16 * (4 * j) + 64 = 16 * (4 * (j + 1)) by omega]

theorem add64 (s₀ : State) (j : Nat) : blkAddr s₀ (4 * j) + 64 = blkAddr s₀ (4 * (j + 1)) := by
  simp only [blkAddr]
  rw [show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, Offset.add_add,
    show 16 * (4 * j) + 64 = 16 * (4 * (j + 1)) by omega]

theorem group_body_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.APre s₀) {j : Nat} (hj : j + 1 < nb s₀ / 4) {s : State}
    (h : VG.Proof.Poly1305.X86_64.Avx2.LInv s₀ j s) :
    WP isa groupBody s fun s' => VG.Proof.Poly1305.X86_64.Avx2.LInv s₀ (j + 1) s' ∧ s'.zf = some (decide (nb s₀ / 4 - 1 - j = 1)) := by
  have hb := hp.bpre.nb_lt
  have hc := VG.Proof.Poly1305.X86_64.Avx2.ctx_of hp h.rd h.rsi (j := j) (by omega)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.guard (R := fun s' => vec s s' = s') (A := H2 s₀ < 4) ?_
    fun hA => VG.Proof.Poly1305.X86_64.Avx2.group_ok h.r8 h.r9 hc (h.acc hA)) fun s₁ ⟨v₁, G₁⟩ => ?_)
  · exact WP.block_append (WP.mono (run_ok (fun _ => hc) addS_eq) fun s₁ h₁ =>
      WP.mono (run_ok (fun h => by cases h) mulS_eq) fun s₂ h₂ => vec_trans h₁.eq h₂.eq)
  obtain ⟨vg₁, vm₁, vrd₁, vwr₁, -⟩ := VG.Proof.Poly1305.X86_64.Avx2.vec_keep v₁
  refine WP.mono (VG.Proof.Poly1305.X86_64.Avx2.adv_ok s₁) fun s₂ ⟨si₂, cx₂, zf₂, g₂, m₂, k₂⟩ => ?_
  have gk : ∀ r, r ≠ .rsi → r ≠ .rcx → s₂.gpr r = s.gpr r := fun r a b => by rw [g₂ r a b, vg₁]
  have hcx : s₁.gpr .rcx = BitVec.ofNat 64 (nb s₀ / 4 - 1 - j) := by rw [vg₁, h.rcx]
  refine ⟨⟨hj, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, fun hA => ?_⟩, ?_⟩
  · rw [gk _ (by decide) (by decide), h.rdi]
  · rw [si₂, vg₁, h.rsi, VG.Proof.Poly1305.X86_64.Avx2.add64]
  · rw [cx₂, hcx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega),
      Nat.sub_sub]
  · rw [gk _ (by decide) (by decide), h.rdx]
  · rw [gk _ (by decide) (by decide), h.r8]
  · rw [gk _ (by decide) (by decide), h.r9]
  · obtain ⟨-, c, -, e, -⟩ := VG.Proof.Poly1305.X86_64.Avx2.cs_ne hr
    rw [gk r e c, h.keep r hr]
  · rw [k₂.rd, vrd₁, h.rd]
  · rw [k₂.wr, vwr₁, h.wr]
  · rw [m₂, vm₁, h.mem]
  · have G := (G₁ hA).2
    rw [h.mem, h.rsi, VG.Proof.Poly1305.X86_64.Avx2.grp_bytes hp (by omega), VG.Proof.Poly1305.X86_64.Avx2.absorb_grp] at G
    exact LaneInv.of_qw (fun r k => k₂.qw_eq r k) G
  · rw [zf₂, hcx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]

theorem loop_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.APre s₀) (hG : 1 < nb s₀ / 4) {s : State} (h₀ : VG.Proof.Poly1305.X86_64.Avx2.LInv s₀ 0 s) :
    WP isa (.loop groupBody .ne) s (VG.Proof.Poly1305.X86_64.Avx2.LInv s₀ (nb s₀ / 4 - 1)) := by
  let Inv : Nat → State → Prop := fun n s => ∃ j, n = nb s₀ / 4 - 1 - j ∧ j < nb s₀ / 4 - 1 ∧ VG.Proof.Poly1305.X86_64.Avx2.LInv s₀ j s
  have hstep : ∀ n s, Inv n s → WP isa groupBody s (fun s' =>
      (eval .ne s' = some false ∧ VG.Proof.Poly1305.X86_64.Avx2.LInv s₀ (nb s₀ / 4 - 1) s') ∨
      (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨j, rfl, hj, hI⟩
    refine WP.mono (VG.Proof.Poly1305.X86_64.Avx2.group_body_ok hp (by omega) hI) fun s' ⟨h', hz⟩ => ?_
    by_cases e : nb s₀ / 4 - 1 - j = 1
    · have e' : j + 1 = nb s₀ / 4 - 1 := by omega
      exact .inl ⟨by simp [eval, hz, e], e' ▸ h'⟩
    · exact .inr ⟨by simp [eval, hz, e], nb s₀ / 4 - 1 - (j + 1), by omega, j + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep _ s ⟨0, rfl, by omega, h₀⟩

/-! ## The epilogue -/

theorem epi_eq : consts2 ++ last ++ sumLanes ++ fullCarry ++ reduce ++ mxcsrOut ++
    Impl.Poly1305.X86_64.Avx2.storeH ++
    ([.vop .vzeroupper, .alu .add .rsi (.imm 64), .alu .and .rdx (.imm 3)] : List Instr) =
    consts2 ++ (last ++ (sumLanes ++ ((fullCarry ++ reduce) ++ (mxcsrOut ++
      (Impl.Poly1305.X86_64.Avx2.storeH ++
        ([.vop .vzeroupper, .alu .add .rsi (.imm 64), .alu .and .rdx (.imm 3)] : List Instr)))))) := by
  simp only [List.append_assoc]

theorem epi_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.APre s₀) {s : State} (h : VG.Proof.Poly1305.X86_64.Avx2.LInv s₀ (nb s₀ / 4 - 1) s) :
    WP isa (.block (consts2 ++ last ++ sumLanes ++ fullCarry ++ reduce ++ mxcsrOut ++
      Impl.Poly1305.X86_64.Avx2.storeH ++
      ([.vop .vzeroupper, .alu .add .rsi (.imm 64), .alu .and .rdx (.imm 3)] : List Instr))) s
      (VG.Proof.Poly1305.X86_64.Avx2.TailPre s₀ (4 * (nb s₀ / 4))) := by
  have hb := hp.bpre.nb_lt
  have hlt := h.lt
  have h1 : 1 ≤ nb s₀ / 4 := by omega
  rw [VG.Proof.Poly1305.X86_64.Avx2.epi_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.consts2_ok s) fun s₁ ⟨ax₁, r10₁, g₁, m₁, k₁⟩ => ?_)
  have gk₁ : ∀ r, r ≠ .rax → r ≠ .r10 → s₁.gpr r = s.gpr r := g₁
  have hc : Ctx s₁ := VG.Proof.Poly1305.X86_64.Avx2.ctx_of hp (by rw [k₁.rd, h.rd]) (by rw [gk₁ _ (by decide) (by decide), h.rsi])
    (by omega)
  have r8₁ : s₁.gpr .r8 = 0x3ffffff := by rw [gk₁ _ (by decide) (by decide), h.r8]
  have r9₁ : s₁.gpr .r9 = 0x1000000 := by rw [gk₁ _ (by decide) (by decide), h.r9]
  -- The last group.
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.guard (R := fun s' => vec s₁ s' = s') (A := H2 s₀ < 4) ?_
    fun hA => VG.Proof.Poly1305.X86_64.Avx2.last_ok r8₁ r9₁ hc ((h.acc hA).of_qw fun r k => k₁.qw_eq r k)) fun s₂ ⟨v₂, L₂⟩ => ?_)
  · rw [VG.Proof.Poly1305.X86_64.Avx2.last_eq]
    exact WP.block_append (WP.mono (run_ok (fun _ => hc) addS_eq) fun _ h₁ =>
      WP.block_append (WP.mono (run_ok (fun h => by cases h) VG.Proof.Poly1305.X86_64.Avx2.shS_eq) fun _ h₂ =>
        WP.mono (run_ok (fun h => by cases h) mulS_eq) fun _ h₃ => vec_trans h₁.eq (vec_trans h₂.eq h₃.eq)))
  obtain ⟨vg₂, vm₂, vrd₂, vwr₂, vx₂⟩ := VG.Proof.Poly1305.X86_64.Avx2.vec_keep v₂
  have r8₂ : s₂.gpr .r8 = 0x3ffffff := by rw [vg₂, r8₁]
  -- The sum of the lanes.
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.guard (R := fun s' => vec s₂ s' = s') (A := H2 s₀ < 4)
    (WP.mono (run_ok (fun h => by cases h) VG.Proof.Poly1305.X86_64.Avx2.smS_eq) fun _ h => h.eq)
    fun hA => VG.Proof.Poly1305.X86_64.Avx2.sumLanes_ok r8₂ (L₂ hA).2.1) fun s₃ ⟨v₃, S₃⟩ => ?_)
  obtain ⟨vg₃, vm₃, vrd₃, vwr₃, vx₃⟩ := VG.Proof.Poly1305.X86_64.Avx2.vec_keep v₃
  -- `h mod p`.
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.guard (R := fun s' => vec s₃ s' = s') (A := H2 s₀ < 4)
    (WP.mono (run_ok (fun h => by cases h) VG.Proof.Poly1305.X86_64.Avx2.fnS_eq) fun _ h => h.eq)
    fun hA => VG.Proof.Poly1305.X86_64.Avx2.finish_ok (by rw [vg₃, r8₂]) (by rw [vg₃, vg₂, ax₁]) (by rw [vg₃, vg₂, r10₁])
      (S₃ hA).hball (S₃ hA).hb) fun s₄ ⟨v₄, F₄⟩ => ?_)
  obtain ⟨vg₄, vm₄, vrd₄, vwr₄, vx₄⟩ := VG.Proof.Poly1305.X86_64.Avx2.vec_keep v₄
  have g₄ : ∀ r, r ≠ .rax → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r a b => by
    rw [vg₄, vg₃, vg₂, gk₁ r a b]
  have rdi₄ : s₄.gpr .rdi = st s₀ := by rw [g₄ _ (by decide) (by decide), h.rdi]
  have wr₄ : s₄.wr = s₀.wr := by rw [vwr₄, vwr₃, vwr₂, k₁.wr, h.wr]
  have mm₄ : s₄.mem = VG.Proof.Poly1305.X86_64.Avx2.mxMem s₀.mem (st s₀) s₀.mxcsr := by rw [vm₄, vm₃, vm₂, m₁, h.mem]
  -- MXCSR restored.
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.mxcsrOut_ok s₄ (hp.inRW wr₄ rdi₄ (by omega))
    (by rw [mm₄, rdi₄, VG.Proof.Poly1305.X86_64.Avx2.mxMem_mx]; exact VG.Proof.Poly1305.X86_64.Avx2.mx_hi _)) fun s₅ ⟨g₅, m₅, mx₅, x₅, y₅, rd₅, wr₅⟩ => ?_)
  have rdi₅ : s₅.gpr .rdi = st s₀ := by rw [g₅, rdi₄]
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄]
  -- The accumulator stored.
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.storeH_ok fun d hd => hp.inW wr₅' rdi₅ (by omega)) fun s₆ sp₆ => ?_)
  refine WP.mono (VG.Proof.Poly1305.X86_64.Avx2.fin3_ok s₆) fun s₇ ⟨si₇, dx₇, g₇, m₇, mx₇, rd₇, wr₇⟩ => ?_
  have g₆ : ∀ r, r ≠ .rax → r ≠ .r10 → s₆.gpr r = s.gpr r := fun r a b => by
    rw [sp₆.gpr, g₅, g₄ r a b]
  have hmx : s₇.mxcsr = s₀.mxcsr &&& 0xffff := by
    rw [mx₇, sp₆.mxcsr, mx₅, mm₄, rdi₄, VG.Proof.Poly1305.X86_64.Avx2.mxMem_mx]
  have hframe : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₇.mem := by
    rw [m₇]
    refine ((VG.Proof.Poly1305.X86_64.Avx2.mxMem_frame s₀.mem (st s₀) s₀.mxcsr).mono (by simp)).trans ?_
    rw [← mm₄, ← m₅]
    exact sp₆.frame.mono (by rw [rdi₅]; simp)
  refine ⟨by omega, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, hframe, by rw [hmx, VG.Proof.Poly1305.X86_64.Avx2.mx_bits], fun key msg hr => ?_⟩
  · rw [g₇ _ (by decide) (by decide), g₆ _ (by decide) (by decide), h.rdi]
  · rw [si₇, g₆ _ (by decide) (by decide), h.rsi, VG.Proof.Poly1305.X86_64.Avx2.add64, Nat.sub_add_cancel h1]
  · rw [dx₇, g₆ _ (by decide) (by decide), h.rdx]
    apply BitVec.eq_of_toNat_eq
    rw [and3_toNat, toNat_ofNat_lt (by omega)]
    simp only [nb]
    omega
  · obtain ⟨a, -, c, d, -, -, g, -⟩ := VG.Proof.Poly1305.X86_64.Avx2.cs_ne hr
    rw [g₇ r d c, g₆ r a g, h.keep r hr]
  · rw [rd₇, sp₆.rd, rd₅, vrd₄, vrd₃, vrd₂, k₁.rd, h.rd]
  · rw [wr₇, sp₆.wr, wr₅']
  · -- The accumulator represents the blocks absorbed.
    have hA := VG.Proof.Poly1305.X86_64.Avx2.H2_lt hr
    obtain ⟨hlen, hkey, hacc⟩ := hr
    have hkey' : bytesAt s₀.mem (off (st s₀) 24) 32 = key := by rw [off_24]; exact hkey
    have hA0 : accumulate (Rn s₀) msg = A0 s₀ := by rw [A0, hacc, ← hkey', clamp_key]
    have hlt : A0 s₀ < P := by rw [← hA0]; exact Poly1305.accumulate_lt _ _
    have L := (L₂ hA).2.2
    have S := (S₃ hA).h
    obtain ⟨-, F, Fb⟩ := F₄ hA
    rw [gk₁ _ (by decide) (by decide), h.rsi, m₁, h.mem, VG.Proof.Poly1305.X86_64.Avx2.grp_bytes hp (by omega), VG.Proof.Poly1305.X86_64.Avx2.absorb_grp, Nat.sub_add_cancel h1] at L
    have e₅ : VG.Proof.Poly1305.X86_64.Avx2.h0 s₅ = hv s₄ 0 := by
      funext i; simp only [VG.Proof.Poly1305.X86_64.Avx2.h0, hv, VG.Proof.Poly1305.X86_64.Avx2.qw_of x₅ y₅]
    obtain ⟨W, -, -⟩ := Limbs26.words_val (o := VG.Proof.Poly1305.X86_64.Avx2.h0 s₅) (by rw [e₅]; exact Fb)
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_append, Poly1305.length_bytesAt]; omega
    · rw [← off_24, key_frame hframe, hkey']
    · rw [leNum_acc, m₇, ← rdi₅, sp₆.w0, sp₆.w1, sp₆.w2, W, e₅, F, ← hkey', clamp_key,
        Poly1305.accumulate_append hlen]
      change _ = Poly1305.absorbAll (Rn s₀) (accumulate (Rn s₀) msg) _
      rw [hA0, (S.trans L : _ ≡ _ [MOD P]),
        Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _)]

/-! ## The whole function -/

theorem body_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.APre s₀) (hbig : 32 ≤ nb s₀) {s : State} (hg : s.gpr = s₀.gpr)
    (hm : s.mem = s₀.mem) (hk : VG.Proof.Poly1305.X86_64.Avx2.VKeep s₀ s) :
    WP isa body s (VG.Proof.Poly1305.X86_64.Avx2.TailPre s₀ (4 * (nb s₀ / 4))) :=
  WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.pro_ok hp hbig hg hm hk) fun _ h₁ =>
    WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.loop_ok hp (by omega) h₁) fun _ h₂ => VG.Proof.Poly1305.X86_64.Avx2.epi_ok hp h₂))

theorem TailPre.congr {s₀ s s' : State} {i : Nat} (h : VG.Proof.Poly1305.X86_64.Avx2.TailPre s₀ i s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hx : s'.mxcsr = s.mxcsr) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.Poly1305.X86_64.Avx2.TailPre s₀ i s' :=
  ⟨h.le, by rw [hg, h.rdi], by rw [hg, h.rsi], by rw [hg, h.rdx], fun r hr => by rw [hg, h.keep r hr],
    by rw [hrd, h.rd], by rw [hwr, h.wr], by rw [hm]; exact h.frame, by rw [hx]; exact h.mxcsr,
    fun key msg hr => by rw [hm]; exact h.repr key msg hr⟩

theorem correct {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx2.APre s₀) : WP isa blocksAvx2 s₀ (VG.Proof.Poly1305.X86_64.Avx2.Post s₀) := by
  have hb := hp.bpre.nb_lt
  refine WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.cmp_ok s₀) fun s₁ ⟨g₁, m₁, k₁, cf₁⟩ => ?_)
  refine WP.ite (decide (nb s₀ < 32)) (by simp [eval, cf₁]) (fun hlt => ?_) (fun hge => ?_)
  · refine VG.Proof.Poly1305.X86_64.Avx2.tail_ok hp (i := 0) ⟨by omega, by rw [g₁], by rw [g₁]; simp [blkAddr], ?_,
      fun r _ => by rw [g₁], k₁.rd, k₁.wr, by rw [m₁]; exact Frame.refl _ _, by rw [k₁.mxcsr],
      fun key msg hr => by rw [m₁, blks_zero, List.append_nil]; exact hr⟩
    rw [g₁, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    refine WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.body_ok hp hge g₁ m₁ k₁) fun s₂ h₂ => ?_)
    refine WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.Avx2.test_ok s₂) fun s₃ ⟨z₃, g₃, m₃, mx₃, rd₃, wr₃⟩ => ?_)
    have h₃ := h₂.congr g₃ m₃ mx₃ rd₃ wr₃
    refine WP.ite (s₃.gpr .rdx &&& s₃.gpr .rdx == 0) (by simp [eval, z₃, g₃]) (fun h => ?_)
      (fun _ => VG.Proof.Poly1305.X86_64.Avx2.tail_ok hp h₃)
    have e : 4 * (nb s₀ / 4) = nb s₀ := by
      have := h₃.rdx
      simp only [BitVec.and_self, beq_iff_eq] at h
      rw [h] at this
      have := congrArg BitVec.toNat this
      rw [toNat_ofNat_lt (by omega)] at this
      rw [show (0 : BitVec 64).toNat = 0 from rfl] at this
      simp only [nb] at this ⊢
      omega
    exact WP.block_nil (M := isa) (VG.Proof.Poly1305.X86_64.Avx2.done_ok hp (e ▸ h₃))

theorem blocksAvx2_ok (s : State) (hs : blocksAvx2X86_64.pre s) :
    ∃ t s', Exec isa blocksAvx2 s t s' ∧ abiPreserved s s' ∧ blocksAvx2X86_64.post s s' :=
  VG.Proof.Poly1305.X86_64.Avx2.correct (APre.of s hs)

/-! ## Constant time -/

theorem blocksAvx2_ct : ConstantTime isa blocksAvx2X86_64.pre blocksAvx2X86_64.pub blocksAvx2 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨⟨h1, h2, h3⟩, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (with no blocks). -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩]

theorem blocksAvx2_verified :
    Verified X86_64.target blocksAvx2 (Spec.Poly1305.blocksContract X86_64.abi 8) :=
  Verified.of_correct VG.Proof.Poly1305.X86_64.Avx2.blocksAvx2_ok VG.Proof.Poly1305.X86_64.Avx2.blocksAvx2_ct (by
    sig_implies [Spec.Poly1305.blocksContract, Spec.Poly1305.blocksSig, VG.Proof.Poly1305.X86_64.Avx2.blocksAvx2X86_64,
      Proof.Poly1305.blocksX86_64, X86_64.abi, X86_64.argRegs] [sat] using VG.Proof.Poly1305.X86_64.Avx2.sat)

end VG.Proof.Poly1305.X86_64.Avx2

end
