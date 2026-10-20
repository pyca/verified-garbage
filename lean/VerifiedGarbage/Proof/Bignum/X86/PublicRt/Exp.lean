module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulEnv
public import VerifiedGarbage.Proof.Bignum.X86.ExponentBits
public import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.ByteWords

/-! # A step of the exponentiation of public RSA at a run-time width

`sparseRound`: with the result `y R` (number 2), the base `b R` (number 1)
and the exponent's remaining bits `E` (two words at 128), the result times
the base where `E` is odd (`product_ok`), the base squared, `E` halved, and
`zf` set once `E` is gone (`sparseRound_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Mont.X86.Dynamic

theorem Env.pos {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat} {s : State}
    (E : Env base bytes len args M s) : 0 < M := by
  have := E.inv
  rcases Nat.eq_zero_or_pos M with rfl | h
  · simp at this
  · exact h

/-- The product of a set bit: the result `y R` times the base where the exponent is odd. -/
theorem product_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat}
    (E : Env base bytes len args M s) (hbytes : bytes = (args 9).toNat * 8)
    {y b : Nat} (hY : val32 s.mem base (numAt len 2) (nw len) = y * 2 ^ (32 * nw len) % M)
    (hX : val32 s.mem base (numAt len 1) (nw len) = b * 2 ^ (32 * nw len) % M) :
    WP isa (.seq (.block PublicContext.bitTest) (.ite .e (.block []) (PublicRt.mul 2 2 1))) s fun t =>
      Env base bytes len args M t ∧ Frame (Chg base len bytes (s.gpr .esp)) s.mem t.mem ∧
      val32 t.mem base (numAt len 2) (nw len) =
        (if val32 s.mem base 128 2 % 2 = 1 then y * b else y) * 2 ^ (32 * nw len) % M ∧
      val32 t.mem base (numAt len 1) (nw len) = val32 s.mem base (numAt len 1) (nw len) ∧
      val32 t.mem base 128 2 = val32 s.mem base 128 2 ∧ Keeps [.eax, .ecx, .edx] s t ∧
      val32 t.mem base (numAt len 3) (nw len) = val32 s.mem base (numAt len 3) (nw len) := by
  have h := E.pi
  have nw' := h.scratch.nowrap
  have dims := h.dimensions
  have wbe := wb_eq len
  have hM := E.pos
  have f5 := (h.fits (j := 5) (by decide)).2
  have f2 := (h.fits (j := 2) (by decide)).1
  have e1 : numAt len 1 = 256 + wb len := by simp only [numAt, numOff] <;> omega
  have e2 : numAt len 2 = 256 + 2 * wb len := by simp only [numAt, numOff] <;> omega
  have e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega
  refine WP.seq (WP.mono (PublicContext.bitTest_ok h.scratch (by omega)) fun u ⟨M₁, K₁, Z₁⟩ => ?_)
  have E₁ := E.keep K₁ (by decide) (by decide) (by rw [M₁]; exact Frame.refl _ _)
  have K₁' : Keeps [.eax, .ecx, .edx] s u := K₁.mono (by decide)
  have par : val32 s.mem base 128 2 % 2 = w32 s.mem base 128 % 2 := val32_parity _ _ _ _
  by_cases bit : w32 s.mem base 128 % 2 = 0
  · refine WP.ite true (by change u.zf = _; rw [Z₁, decide_eq_true bit]) (fun _ => WP.block_nil ?_)
      (fun e => nomatch e)
    refine ⟨E₁, by rw [M₁]; exact Frame.refl _ _, ?_, by rw [M₁], by rw [M₁], K₁', by rw [M₁]⟩
    rw [M₁, hY, ite_eq_right (by omega)]
  · refine WP.ite false (by change u.zf = _; rw [Z₁, decide_eq_false bit]) (fun e => nomatch e)
      (fun _ => ?_)
    refine WP.mono (mulEnv_ok E₁ hbytes (o := 2) (a := 2) (b := 1) (by decide) (by decide) (by decide)
      (by decide) (x := y) (y := b) (by rw [M₁, hY, Nat.mod_mod]) (by rw [M₁, hX, Nat.mod_mod])
      (by rw [M₁, hX]; exact Nat.mod_lt _ hM)) fun t ⟨Et, Ct, cst, Ft, Tt⟩ => ?_
    have sp₁ : u.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
    refine ⟨Et, ?_, ?_, ?_, ?_, K₁'.trans cst, ?_⟩
    · rw [← M₁, ← sp₁]; exact Ct
    · rw [Tt, ite_eq_left (by omega)]
    · rw [mulFrame_val32 E₁.room nw' Ft (.inl (by omega)) (by omega) (by omega) f2 f5, M₁]
    · rw [← read_eq_val32, ← read_eq_val32, mulFrame_hdr E₁.room nw' Ft (by decide) (by omega) f2 f5, M₁]
    · rw [mulFrame_val32 E₁.room nw' Ft (.inr (by omega)) (by omega) (by omega) f2 f5, M₁]

theorem sparseRound_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat}
    (E : Env base bytes len args M s) (hbytes : bytes = (args 9).toNat * 8)
    {y b : Nat} (hY : val32 s.mem base (numAt len 2) (nw len) = y * 2 ^ (32 * nw len) % M)
    (hX : val32 s.mem base (numAt len 1) (nw len) = b * 2 ^ (32 * nw len) % M) :
    WP isa sparseRound s fun t =>
      Env base bytes len args M t ∧ Frame (Chg base len bytes (s.gpr .esp)) s.mem t.mem ∧
      t.zf = some (decide (val32 s.mem base 128 2 / 2 = 0)) ∧
      val32 t.mem base (numAt len 2) (nw len) =
        (if val32 s.mem base 128 2 % 2 = 1 then y * b else y) * 2 ^ (32 * nw len) % M ∧
      val32 t.mem base (numAt len 1) (nw len) = (b * b) * 2 ^ (32 * nw len) % M ∧
      val32 t.mem base 128 2 = val32 s.mem base 128 2 / 2 ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      val32 t.mem base (numAt len 3) (nw len) = val32 s.mem base (numAt len 3) (nw len) := by
  have h := E.pi
  have nw' := h.scratch.nowrap
  have dims := h.dimensions
  have wbe := wb_eq len
  have hM := E.pos
  have f5 := (h.fits (j := 5) (by decide)).2
  have f1 := (h.fits (j := 1) (by decide)).1
  have e1 : numAt len 1 = 256 + wb len := by simp only [numAt, numOff] <;> omega
  have e2 : numAt len 2 = 256 + 2 * wb len := by simp only [numAt, numOff] <;> omega
  have e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega
  unfold sparseRound
  refine WP.seq (WP.mono (product_ok E hbytes hY hX) fun u₁ ⟨E₁, C₁, Y₁, X₁, W₁, K₁, O₁⟩ => ?_)
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  -- The base squared.
  refine WP.seq (WP.mono (mulEnv_ok E₁ hbytes (o := 1) (a := 1) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (x := b) (y := b) (by rw [X₁, hX, Nat.mod_mod]) (by rw [X₁, hX, Nat.mod_mod])
    (by rw [X₁, hX]; exact Nat.mod_lt _ hM)) fun u₂ ⟨E₂, C₂, cs₂, F₂, X₂⟩ => ?_)
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (cs₂.1 _ (by decide)).trans sp₁
  have Y₂ : val32 u₂.mem base (numAt len 2) (nw len) = val32 u₁.mem base (numAt len 2) (nw len) :=
    mulFrame_val32 E₁.room nw' F₂ (.inr (by omega)) (by omega) (by omega) f1 f5
  have O₂ : val32 u₂.mem base (numAt len 3) (nw len) = val32 u₁.mem base (numAt len 3) (nw len) :=
    mulFrame_val32 E₁.room nw' F₂ (.inr (by omega)) (by omega) (by omega) f1 f5
  have W₂ : val32 u₂.mem base 128 2 = val32 u₁.mem base 128 2 := by
    rw [← read_eq_val32, ← read_eq_val32, mulFrame_hdr E₁.room nw' F₂ (by decide) (by omega) f1 f5]
  -- The exponent halved, and whether any of it is left.
  refine WP.block_append (WP.mono (shiftExponent_ok E₂.pi.scratch 2 128 (by omega)) fun u₃ ⟨O₃, V₃, K₃⟩ => ?_)
  have E₃ := E₂.keep K₃ (by decide) (by decide) (Outside.chg O₃ (.inl ⟨by decide, by decide⟩))
  refine WP.mono (PublicContext.exponentLeft_ok E₃.pi.scratch (by omega)) fun t ⟨M₄, K₄, Z₄⟩ => ?_
  have W₃ : val32 u₃.mem base 128 2 = val32 s.mem base 128 2 / 2 := by rw [V₃, W₂, W₁]
  refine ⟨E₃.keep K₄ (by decide) (by decide) (by rw [M₄]; exact Frame.refl _ _), ?_, by rw [Z₄, W₃], ?_, ?_,
    by rw [M₄, W₃], ?_, ?_⟩
  · have G₂ : Frame (Chg base len bytes (s.gpr .esp)) u₁.mem u₂.mem := by rw [← sp₁]; exact C₂
    have G₃ : Frame (Chg base len bytes (s.gpr .esp)) u₂.mem t.mem := by
      rw [M₄]; exact Outside.chg O₃ (.inl ⟨by decide, by decide⟩)
    exact (C₁.trans G₂).trans G₃
  · rw [M₄, O₃.val32 (.inr (by omega)) (by omega), Y₂, Y₁]
  · rw [M₄, O₃.val32 (.inr (by omega)) (by omega), X₂]
  · exact (((K₁.mono (by decide)).trans (cs₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      (K₄.mono (by decide))
  · rw [M₄, O₃.val32 (.inr (by omega)) (by omega), O₂, O₁]

end VG.Proof.Bignum.X86.PublicRt
