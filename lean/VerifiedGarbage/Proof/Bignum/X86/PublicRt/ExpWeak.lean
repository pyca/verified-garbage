module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Exponentiate
import Mathlib.Data.Int.GCD
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Key
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Double
import VerifiedGarbage.Proof.Mont.X86.ExponentShift

/-! ### `Bignum.X86.PrecomputedRt.Checks`, which the modules that import this one used -/

section

/-! # The checks of the precomputed values

`checks`: ZF clear exactly if one (number 3) and `R² mod M` (number 4) are
below the modulus (number 0), and the modulus is odd (`checks_ok`). Their
outcome is public, as the values are.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputedRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt
open VG.Impl.Bignum.X86.PrecomputedRt VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.PublicRt

theorem and_one_zero (w : BitVec 32) : (w &&& 1 == 0) = !decide (w.toNat % 2 = 1) := by
  have hw : (w &&& 1).toNat = w.toNat % 2 := by
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
  by_cases hp : w.toNat % 2 = 1
  · have ne : w &&& 1 ≠ 0 := fun h => by rw [h] at hw; simp at hw; omega_using [hp, hw]
    have e : (w &&& 1 == 0) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact ne
    rw [e]; simp [hp]
  · have eq : w &&& 1 = 0 := BitVec.eq_of_toNat_eq (by rw [hw]; simp; omega_using [hp])
    have e : (w &&& 1 == 0) = true := by simp only [beq_iff_eq]; exact eq
    rw [e]; simp [hp]

theorem checks_zero (c₁ c₂ : Bool) (w : BitVec 32) :
    (cmask c₂ &&& cmask c₁ &&& (w &&& 1) == 0) = !(c₁ && c₂ && decide (w.toNat % 2 = 1)) := by
  cases c₁ <;> cases c₂
  · simp [cmask]
  · simp [cmask]
  · simp [cmask]
  · show (BitVec.allOnes 32 &&& BitVec.allOnes 32 &&& (w &&& 1) == 0) = !(true && true && decide (w.toNat % 2 = 1))
    rw [BitVec.allOnes_and, BitVec.allOnes_and, Bool.true_and, Bool.true_and]
    exact and_one_zero w

/-- The checks' outcome: one and `R² mod M` below `M`, and `M` odd. -/
def Accepted (M T : Nat) : Bool := decide (1 < M) && decide (T < M) && decide (M % 2 = 1)

theorem checks_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) (one : val32 s.mem base (numAt len 3) (nw len) = 1) :
    WP isa checks s fun u =>
      u.zf = some (!Accepted (val32 s.mem base (numAt len 0) (nw len)) (val32 s.mem base (numAt len 4) (nw len))) ∧
      Outside base checkOffset 4 s.mem u.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .esi] s u := by
  have f0 := (h.fits (j := 0) (by decide)).1
  have nw' := h.scratch.nowrap
  have dims := h.dimensions
  have n0 : numAt len 0 = 256 := by simp [numAt, numOff]
  have wl := wb_ge h.lower
  unfold checks
  refine WP.seq (WP.mono (compareAt_ok h (a := 3) (b := 0) (by decide) (by decide)) fun u₁ ⟨m₁, c₁, K₁⟩ => ?_)
  have h₁ := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine WP.seq (wp_storeS (h₁.scratch.ea (d := 148) (by rw [n0] at f0; omega_using [f0]))
    (h₁.scratch.write (d := 148) (n := 4) (by rw [n0] at f0; omega_using [f0])) fun u₂ m₂ => WP.block_nil ?_)
  have O₂ : Outside base 148 4 s.mem u₂.mem := by rw [m₂.mem, m₁]; exact writeW32_outside _ _ _ (by omega_using [])
  have h₂ := h₁.keep (m₂.keeps []) (by decide) (by decide) (by rw [m₂.mem]; exact (writeW32_outside _ _ _ (by omega_using [])).mono (by omega_using []) (by omega_using [f0, n0]))
  have V₀ : ∀ j, j ≤ 4 → val32 u₂.mem base (numAt len j) (nw len) = val32 s.mem base (numAt len j) (nw len) :=
    fun j hj => O₂.val32 (.inr (by simp only [numAt, numOff]; omega_using [])) (by
      have := (h.fits (j := j) (by omega_using [hj])).1; simp only [nw, wb] at *; omega_using [nw', this])
  refine WP.seq (WP.mono (compareAt_ok h₂ (a := 4) (b := 0) (by decide) (by decide)) fun u₃ ⟨m₃, c₃, K₃⟩ => ?_)
  rw [V₀ 4 (by decide), V₀ 0 (by decide)] at c₃
  have h₃ := h₂.keep K₃ (by decide) (by decide) (by rw [m₃]; exact Outside.refl _ _ _ _)
  refine wp_movS (readSrc_sc h₃.scratch (d := 148) (by rw [n0] at f0; omega_using [f0])) fun u₄ e₄ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun u₅ e₅ => ?_
  refine wp_movS (readSrc_sc ((h₃.scratch.of_keeps e₄.keeps (by decide) (by decide)).of_keeps e₅.keeps
    (by decide) (by decide)) (d := numOff) (by rw [n0] at f0; simp only [numOff]; omega_using [f0, wl])) fun u₆ e₆ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun u₇ e₇ => ?_
  refine wp_logicS (.inl rfl) rfl fun u₈ e₈ => ?_
  refine wp_cmpS rfl fun t F z => WP.block_nil ⟨?_, ?_, ?_⟩
  · have mem₃ : u₃.mem = u₂.mem := m₃
    have edx₄ : u₄.gpr .edx = cmask (decide (1 < val32 s.mem base (numAt len 0) (nw len))) := by
      rw [e₄.gpr, mem₃, m₂.mem, Mem.readW_writeW_self32, c₁, one]
    have ecx₄ : u₄.gpr .ecx = cmask (decide (val32 s.mem base (numAt len 4) (nw len) <
        val32 s.mem base (numAt len 0) (nw len))) := by rw [e₄.other _ (by decide), c₃]
    have eax₇ : u₇.gpr .eax = u₂.mem.readW (off base numOff) 32 &&& 1 := by
      rw [e₇.gpr]
      show u₆.gpr .eax &&& 1 = _
      rw [e₆.gpr, e₅.mem, e₄.mem, mem₃]
    have ecx₇ : u₇.gpr .ecx = cmask (decide (val32 s.mem base (numAt len 4) (nw len) <
        val32 s.mem base (numAt len 0) (nw len))) &&& cmask (decide (1 < val32 s.mem base (numAt len 0) (nw len))) := by
      rw [e₇.other _ (by decide), e₆.other _ (by decide), e₅.gpr]
      show u₄.gpr .ecx &&& u₄.gpr .edx = _
      rw [ecx₄, edx₄]
    have par : (u₂.mem.readW (off base numOff) 32).toNat % 2 = val32 s.mem base (numAt len 0) (nw len) % 2 := by
      obtain ⟨k, hk⟩ : ∃ k, nw len = k + 1 := ⟨nw len - 1, by simp only [nw]; omega_using [dims]⟩
      have n0' : numAt len 0 = numOff := by simp [numAt]
      rw [← V₀ 0 (by decide), hk, VG.Proof.Mont.X86.Dynamic.val32_parity, n0']
    have e₈' : u₈.gpr .ecx = u₇.gpr .ecx &&& u₇.gpr .eax := e₈.gpr
    rw [z, e₈']
    have sz : ∀ x : BitVec 32, x - 0 = x := fun x => by simp
    rw [sz, ecx₇, eax₇, checks_zero, par]
    rfl
  · show Outside base 148 4 s.mem t.mem
    rw [F.mem, e₈.mem, e₇.mem, e₆.mem, e₅.mem, e₄.mem, m₃]
    exact O₂
  · exact ((((((((K₁.trans ((m₂.keeps []).mono (by decide))).trans K₃).trans (e₄.keeps.mono (by decide))).trans
      (e₅.keeps.mono (by decide))).trans (e₆.keeps.mono (by decide))).trans (e₇.keeps.mono (by decide))).trans
      (e₈.keeps.mono (by decide))).trans (F.keeps _))

end VG.Proof.Bignum.X86.PrecomputedRt

end

end

/-! # The exponentiation from any `R²` below the modulus

`exponentiate` from any number 4 below `M` (`exponentiate_any_ok`): it ends,
in `Env`, changing only `Chg`. Its value is `exponentiate_ok`'s when number 4
is `R² mod M`, and unspecified otherwise, as when `pre` holds the values of
no modulus.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- `y` with `y R ≡ X`, for `R` invertible modulo `M > 1`. -/
theorem exists_mont {R M : Nat} (hR : Nat.Coprime R M) (hM : 1 < M) (X : Nat) :
    ∃ y, X % M = y * R % M := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hR hM
  refine ⟨X * m, ?_⟩
  rw [Nat.mul_assoc, Nat.mul_mod, Nat.mul_comm m R, hm, Nat.mul_one, Nat.mod_mod]

theorem exponentiate_any_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat}
    (E : Env base bytes len args M s) (_hbase : (args 8).toNat = base.toNat) (hbytes : bytes = (args 9).toNat * 8)
    (hM1 : 1 < M) (hT : val32 s.mem base (numAt len 4) (nw len) < M)
    (hO : val32 s.mem base (numAt len 3) (nw len) = 1) :
    WP isa exponentiate s fun t =>
      Env base bytes len args M t ∧ Frame (Chg base len bytes (s.gpr .esp)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have h := E.pi
  have nw' := h.scratch.nowrap
  have dims := h.dimensions
  have wbe := wb_eq len
  have f5 := (h.fits (j := 5) (by decide)).2
  have f1 := (h.fits (j := 1) (by decide)).1
  have f2 := (h.fits (j := 2) (by decide)).1
  have e1 : numAt len 1 = 256 + wb len := by simp only [numAt, numOff] <;> omega_using []
  have e2 : numAt len 2 = 256 + 2 * wb len := by simp only [numAt, numOff] <;> omega
  have e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp only [numAt, numOff] <;> omega
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega
  have hR := E.coprime (32 * nw len)
  unfold exponentiate
  refine WP.seq (WP.mono (mulRaw_ok E hbytes (o := 1) (a := 1) (b := 4) (by decide) (by decide) (by decide)
    (by decide) hT) fun u₁ ⟨E₁, C₁, cs₁, F₁, L₁, _⟩ => ?_)
  have O₁ : val32 u₁.mem base (numAt len 3) (nw len) = val32 s.mem base (numAt len 3) (nw len) :=
    mulFrame_val32 E.room nw' F₁ (.inr (by omega_using [e1, e3])) (by omega_using [wbe, e3, e5]) (by omega_using [wbe, f5, e3, e5]) f1 f5
  refine WP.seq (WP.mono (seed_ok E₁ hbytes L₁ (by rw [O₁, hO]; exact hM1))
    fun u₂ ⟨E₂, C₂, cs₂, L₂, pv₂, _, _⟩ => ?_)
  have Y₂ : val32 u₂.mem base (numAt len 2) (nw len) < M := L₂
  have X₂ : val32 u₂.mem base (numAt len 1) (nw len) < M := by rw [pv₂ 1 (by decide) (by decide)]; exact L₁
  have O₂ := pv₂ 3 (by decide) (by decide)
  have sp₁ : u₁.gpr .esp = s.gpr .esp := cs₁.1 _ (by decide)
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (cs₂.1 _ (by decide)).trans sp₁
  obtain ⟨y, hy⟩ := exists_mont hR hM1 (val32 u₂.mem base (numAt len 2) (nw len))
  obtain ⟨b, hb⟩ := exists_mont hR hM1 (val32 u₂.mem base (numAt len 1) (nw len))
  rw [Nat.mod_eq_of_lt Y₂] at hy
  rw [Nat.mod_eq_of_lt X₂] at hb
  have I₀ : LoopInv base bytes len args M ((y * b ^ val32 u₂.mem base 128 2) % M) u₂ u₂ :=
    ⟨E₂, Frame.refl _ _, ⟨y, b, hy, hb, rfl⟩, Keeps.refl _ _, rfl⟩
  refine WP.seq (WP.mono (sparseLoop_ok hbytes I₀) fun u₄ ⟨I, _⟩ => ?_)
  have O₄ : val32 u₄.mem base (numAt len 3) (nw len) = 1 := by rw [I.one, O₂, O₁, hO]
  refine WP.mono (mulRaw_ok I.env hbytes (o := 2) (a := 2) (b := 3) (by decide) (by decide) (by decide)
    (by decide) (by rw [O₄]; exact hM1)) fun t ⟨Et, Ct, cst, _, _, _⟩ => ?_
  have sp₄ : u₄.gpr .esp = s.gpr .esp := by rw [I.keeps.1 _ (by decide), sp₂]
  refine ⟨Et, ?_, ?_⟩
  · have G₂ : Frame (Chg base len bytes (s.gpr .esp)) u₁.mem u₂.mem := by rw [← sp₁]; exact C₂
    have G₄ : Frame (Chg base len bytes (s.gpr .esp)) u₂.mem u₄.mem := by
      have := I.frame; rwa [sp₂] at this
    have Gt : Frame (Chg base len bytes (s.gpr .esp)) u₄.mem t.mem := by rw [← sp₄]; exact Ct
    exact ((C₁.trans G₂).trans G₄).trans Gt
  · exact ((cs₁.mono (by decide)).trans (cs₂.mono (by decide))).trans (I.keeps.trans (cst.mono (by decide)))

/-- `exponentiate_ok`'s value when number 4 is `R² mod M`, from any number 4 below `M`. -/
theorem exponentiate_cond_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat}
    (E : Env base bytes len args M s) (_hbase : (args 8).toNat = base.toNat) (hbytes : bytes = (args 9).toNat * 8)
    (hM1 : 1 < M) (hT : val32 s.mem base (numAt len 4) (nw len) < M)
    (hO : val32 s.mem base (numAt len 3) (nw len) = 1) :
    WP isa exponentiate s fun t =>
      Env base bytes len args M t ∧ Frame (Chg base len bytes (s.gpr .esp)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      (val32 s.mem base (numAt len 4) (nw len) = 2 ^ (32 * nw len) * 2 ^ (32 * nw len) % M →
        val32 t.mem base (numAt len 2) (nw len) =
          val32 s.mem base (numAt len 1) (nw len) ^ val32 s.mem base 128 2 % M) := by
  by_cases hx : val32 s.mem base (numAt len 4) (nw len) = 2 ^ (32 * nw len) * 2 ^ (32 * nw len) % M
  · exact WP.mono (exponentiate_ok E _hbase hbytes hM1 hx hO) fun _ ⟨a, b, c, d⟩ => ⟨a, b, d, fun _ => c⟩
  · exact WP.mono (exponentiate_any_ok E _hbase hbytes hM1 hT hO) fun _ ⟨a, b, d⟩ =>
      ⟨a, b, d, fun h => absurd h hx⟩

end VG.Proof.Bignum.X86.PublicRt
