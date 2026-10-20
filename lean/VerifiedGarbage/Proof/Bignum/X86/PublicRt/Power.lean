module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Reduce
import VerifiedGarbage.Proof.Framework.Omega

/-! # `R² mod M` in public RSA at a run-time width

`doubleStep` doubles number 4 modulo `M` (`doubleStep_ok`); `powerTwo`
leaves `2^(16 B) mod M` in it (`powerTwo_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- `Keeps` of registers and `edi`, which is back to its value. -/
theorem Keeps.drop_edi {rs : List Reg} {s t : State} (K : Keeps (rs ++ ([.edi] : List Reg)) s t)
    (he : t.gpr .edi = s.gpr .edi) : Keeps rs s t := by
  refine ⟨fun r hr => ?_, K.2.1, K.2.2⟩
  by_cases h : r = .edi
  · subst h; exact he
  · exact K.1 r (by simp [hr, h])

/-- The selection of the conditional subtraction, by the mask of a borrow below the top word. -/
theorem select_mod' {Tl D top X M : Nat} {c : Bool} (hX : M < X) (hD : D < X) (hV : Tl + X * top < 2 * M)
    (he : D + M = Tl + X * c.toNat) :
    (if decide (top < c.toNat) then Tl else D) = (Tl + X * top) % M := by
  rw [← select_mod hX hD hV he]
  by_cases h : top < c.toNat <;> simp [h]

theorem doubleStep_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) (hbase : (args 8).toNat = base.toNat)
    (hT : val32 s.mem base (numAt len 4) (nw len) < val32 s.mem base (numAt len 0) (nw len)) :
    WP isa doubleStep s fun u =>
      Outside base (numAt len 4) (2 * wb len + 4) s.mem u.mem ∧
      val32 u.mem base (numAt len 4) (nw len) =
        (val32 s.mem base (numAt len 4) (nw len) + val32 s.mem base (numAt len 4) (nw len)) %
          val32 s.mem base (numAt len 0) (nw len) ∧
      u.gpr .esi = s.gpr .esi - 1 ∧ u.zf = some (s.gpr .esi - 1 == 0) ∧ u.gpr .edi = s.gpr .edi ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s u := by
  have f5 := (h.fits (j := 5) (by decide)).2
  have wbe := wb_eq len
  have e45 : numAt len 5 = numAt len 4 + wb len := numAt_succ len 4
  have e04 : numAt len 4 = numAt len 0 + 4 * wb len := by simp only [numAt]; omega
  have nw' := h.scratch.nowrap
  unfold doubleStep
  refine WP.seq (WP.mono (double_ok h) fun u₁ ⟨O₁, ⟨c, top₁, V₁⟩, K₁⟩ => ?_)
  have O₁' : Outside base 0 bytes s.mem u₁.mem := O₁.mono (Nat.zero_le _) (by omega)
  have h₁ := h.keep K₁ (by decide) (by decide) O₁'
  have M₁ : val32 u₁.mem base (numAt len 0) (nw len) = val32 s.mem base (numAt len 0) (nw len) :=
    O₁.val32 (by omega_using [e45, e04, wbe]) (by omega_using [f5, nw', e45, e04, wbe])
  refine WP.seq (WP.mono (reduce_ok h₁ hbase) fun u₂ ⟨O₂, ⟨b, V₂, ec₂⟩, edi₂, K₂⟩ => ?_)
  have O₂' : Outside base 0 bytes u₁.mem u₂.mem := O₂.mono (Nat.zero_le _) (by omega)
  have h₂ := h₁.keep (Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp]) K₂ edi₂) (by decide) (by decide) O₂'
  have S₂ : val32 u₂.mem base (numAt len 5) (nw len) = val32 u₁.mem base (numAt len 5) (nw len) :=
    O₂.val32 (by omega_using [e45, wbe]) (by omega_using [f5, nw', e45, wbe])
  refine WP.seq (WP.mono (select_ok h₂ hbase (x := 5) (d := 4) (by decide) (by decide) (by decide) ec₂)
    fun u₃ ⟨O₃, V₃, edi₃, K₃⟩ => ?_)
  refine wp_subZ rfl fun u₄ e₄ z₄ => WP.block_nil ?_
  have esi₃ : u₃.gpr .esi = s.gpr .esi := by
    rw [K₃.1 _ (by decide), K₂.1 _ (by decide), K₁.1 _ (by decide)]
  refine ⟨?_, ?_, by rw [e₄.gpr, esi₃], by rw [z₄, esi₃], ?_, ?_⟩
  · rw [e₄.mem]
    exact ((O₁.mono (by omega) (by omega)).trans (O₂.mono (Nat.le_refl _) (by omega))).trans
      (O₃.mono (Nat.le_refl _) (by omega))
  · have key := select_mod' (X := 2 ^ (32 * nw len)) (Tl := val32 u₁.mem base (numAt len 5) (nw len))
      (D := val32 u₂.mem base (numAt len 4) (nw len)) (top := c.toNat) (c := b)
      (M := val32 s.mem base (numAt len 0) (nw len)) (val32_lt _ _ _ _) (val32_lt _ _ _ _)
      (by rw [V₁]; omega) (by rw [← M₁, V₂])
    rw [e₄.mem, V₃, S₂, top₁, key, V₁]
  · rw [e₄.other _ (by decide), edi₃, edi₂, K₁.1 _ (by decide)]
  · exact (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      (e₄.keeps.mono (by decide))

/-- A count down by one: ZF when it reaches zero. -/
theorem count1_zf {x : BitVec 32} {N j : Nat} (hx : x.toNat = N - j) (hj : j < N) :
    (x - 1).toNat = N - (j + 1) ∧ (x - 1 == 0) = decide (j + 1 = N) := by
  have h1 : (x - 1).toNat = N - (j + 1) := by
    rw [BitVec.toNat_sub, hx, show (1 : BitVec 32).toNat = 1 from rfl]
    have := x.isLt
    omega
  refine ⟨h1, ?_⟩
  by_cases h : j + 1 = N
  · simp only [h, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [h1]; simp; omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro hz
    have := congrArg BitVec.toNat hz
    rw [h1] at this
    simp at this
    omega

theorem powerTwo_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) (hbase : (args 8).toNat = base.toNat)
    (hM : 1 < val32 s.mem base (numAt len 0) (nw len)) :
    WP isa powerTwo s fun u =>
      Outside base (numAt len 4) (2 * wb len + 4) s.mem u.mem ∧
      val32 u.mem base (numAt len 4) (nw len) = 2 ^ (16 * wb len) % val32 s.mem base (numAt len 0) (nw len) ∧
      u.gpr .edi = s.gpr .edi ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s u := by
  have f5 := (h.fits (j := 5) (by decide)).2
  have wbe := wb_eq len
  have wbl := wb_le h.upper
  have wbg := wb_ge h.lower
  have e04 : numAt len 4 = numAt len 0 + 4 * wb len := by simp only [numAt]; omega
  have e45 : numAt len 5 = numAt len 4 + wb len := numAt_succ len 4
  have nw' := h.scratch.nowrap
  unfold powerTwo
  refine WP.seq (WP.mono (setOne_ok h (j := 4) (by decide)) fun u₀ ⟨O₀, V₀, K₀⟩ => ?_)
  have h₀ := h.keep K₀ (by decide) (by decide) (O₀.mono (Nat.zero_le _) (by omega))
  have M₀ : val32 u₀.mem base (numAt len 0) (nw len) = val32 s.mem base (numAt len 0) (nw len) :=
    O₀.val32 (by omega_using [e04, wbe]) (by omega_using [f5, nw', e04, e45, wbe])
  refine WP.seq (widthB_ok (k := 0) (r := .esi) h₀.width h.upper fun u₁ K₁ m₁ e₁ => ?_)
  refine wp_addS rfl fun u₂ a₂ _ => wp_addS rfl fun u₃ a₃ _ => wp_addS rfl fun u₄ a₄ _ => ?_
  refine wp_addS rfl fun u₅ a₅ _ => WP.block_nil ?_
  have K₅ : Keeps [.esi] u₀ u₅ := (((K₁.trans a₂.keeps).trans a₃.keeps).trans a₄.keeps).trans a₅.keeps
  have m₅ : u₅.mem = u₀.mem := by rw [a₅.mem, a₄.mem, a₃.mem, a₂.mem, m₁]
  have esi₅ : (u₅.gpr .esi).toNat = 16 * wb len := by
    rw [a₅.gpr, a₄.gpr, a₃.gpr, a₂.gpr, e₁]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have h₅ := h₀.keep (K₅.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₀ u₅) (by decide)
    (by decide) (by rw [m₅]; exact Outside.refl _ _ _ _)
  let M := val32 s.mem base (numAt len 0) (nw len)
  let I : Nat → State → Prop := fun j t =>
    Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] u₅ t ∧ t.gpr .edi = u₅.gpr .edi ∧
      Outside base (numAt len 4) (2 * wb len + 4) u₅.mem t.mem ∧
      val32 t.mem base (numAt len 4) (nw len) = 2 ^ j % M ∧ (t.gpr .esi).toNat = 16 * wb len - j
  have I₀ : I 0 u₅ := ⟨Keeps.refl _ _, rfl, Outside.refl _ _ _ _,
    by rw [m₅, V₀, Nat.pow_zero, Nat.mod_eq_of_lt hM], by rw [esi₅]; rfl⟩
  refine WP.mono (countLoop (N := 16 * wb len) (by omega) I ?_ I₀) fun t ⟨Kt, edit, Ot, Vt, _⟩ => ?_
  · rintro j t hj ⟨Kt, edit, Ot, Vt, esit⟩
    have Ot' : Outside base 0 bytes u₅.mem t.mem := Ot.mono (Nat.zero_le _) (by omega)
    have ht := h₅.keep (Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp, .esi]) Kt edit) (by decide)
      (by decide) Ot'
    have Mt : val32 t.mem base (numAt len 0) (nw len) = M := by
      rw [Ot.val32 (by omega_using [e04, wbe]) (by omega_using [f5, nw', e04, e45, wbe]), m₅, M₀]
    have hM' : 0 < M := by omega
    refine WP.mono (doubleStep_ok ht hbase (by rw [Vt, Mt]; exact Nat.mod_lt _ hM'))
      fun u ⟨Ou, Vu, esiu, zu, ediu, Ku⟩ => ?_
    obtain ⟨c₁, c₂⟩ := count1_zf esit hj
    refine ⟨⟨Kt.trans Ku, by rw [ediu, edit], Ot.trans Ou, ?_, by rw [esiu]; exact c₁⟩, by rw [zu, c₂]⟩
    rw [Vu, Vt, Mt, ← Nat.add_mod, ← Nat.two_mul, Nat.mul_comm, ← Nat.pow_succ]
  · have K₅s : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s u₅ :=
      (K₀.mono (by decide)).trans (K₅.mono (by decide))
    refine ⟨?_, Vt, by rw [edit, K₅.1 _ (by decide), K₀.1 _ (by decide)], K₅s.trans Kt⟩
    rw [← m₅] at O₀
    exact (O₀.mono (Nat.le_refl _) (by omega)).trans Ot

end VG.Proof.Bignum.X86.PublicRt
