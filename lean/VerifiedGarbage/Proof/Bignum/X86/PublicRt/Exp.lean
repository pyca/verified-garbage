module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulEnv
public import VerifiedGarbage.Proof.Mont.X86.ExponentMask
public import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Framework.Omega

/-! # A step of the exponentiation of public RSA at a run-time width

`expStep`: with the result `y R` (number 2), the base `b R` (number 1) and
the exponent's remaining bits `E` (two words at 128), the result times the
base where `E` is odd, the base squared, `E` halved and `esi` down one
(`expStep_ok`).
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

theorem expStep_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat}
    (E : Env base bytes len args M s) (hbase : (args 8).toNat = base.toNat) (hbytes : bytes = (args 9).toNat * 8)
    {y b k : Nat} (hY : val32 s.mem base (numAt len 2) (nw len) = y * 2 ^ (32 * nw len) % M)
    (hX : val32 s.mem base (numAt len 1) (nw len) = b * 2 ^ (32 * nw len) % M)
    (hk : 0 < k) (hk32 : k < 2 ^ 32) (hc : s.gpr .esi = BitVec.ofNat 32 k) :
    WP isa expStep s fun t =>
      Env base bytes len args M t ∧ Frame (Chg base len bytes (s.gpr .esp)) s.mem t.mem ∧
      t.gpr .esi = BitVec.ofNat 32 (k - 1) ∧ t.zf = some (decide (k = 1)) ∧
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
  have e1 : numAt len 1 = 256 + wb len := by simp only [numAt, numOff] <;> omega
  have e2 : numAt len 2 = 256 + 2 * wb len := by simp only [numAt, numOff] <;> omega
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp only [numAt, numOff] <;> omega
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega
  have n0 : numOff = 256 := rfl
  unfold expStep
  -- The mask of the exponent's low bit, at 136.
  refine WP.seq (WP.mono (exponentMask_ok h.scratch (exp := 128) (mask := 136) (by omega) (by omega))
    fun u₁ ⟨O₁, M₁, K₁⟩ => ?_)
  have E₁ := E.keep K₁ (by decide) (by decide) (Outside.chg O₁ (.inl ⟨by decide, by decide⟩))
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  have Y₁ := O₁.val32 (d := numAt len 2) (k := nw len) (.inr (by omega)) (by omega)
  have X₁ := O₁.val32 (d := numAt len 1) (k := nw len) (.inr (by omega)) (by omega)
  have W₁ := O₁.val32 (d := 128) (k := 2) (.inl (by decide)) (by decide)
  have e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega
  have O3₁ := O₁.val32 (d := numAt len 3) (k := nw len) (.inr (by omega)) (by omega)
  -- `T = y b R`.
  refine WP.seq (WP.mono (mulEnv_ok E₁ hbytes (o := 4) (a := 2) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (x := y) (y := b) (by rw [Y₁, hY, Nat.mod_mod]) (by rw [X₁, hX, Nat.mod_mod])
    (by rw [X₁, hX]; exact Nat.mod_lt _ hM)) fun u₂ ⟨E₂, C₂, cs₂, F₂, T₂⟩ => ?_)
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (cs₂.1 _ (by decide)).trans sp₁
  have f4 := (h.fits (j := 4) (by decide)).1
  have Y₂ : val32 u₂.mem base (numAt len 2) (nw len) = val32 s.mem base (numAt len 2) (nw len) := by
    rw [mulFrame_val32 E₁.room nw' F₂ (.inl (by omega)) (by omega) (by omega) f4 f5, Y₁]
  have X₂ : val32 u₂.mem base (numAt len 1) (nw len) = val32 s.mem base (numAt len 1) (nw len) := by
    rw [mulFrame_val32 E₁.room nw' F₂ (.inl (by omega)) (by omega) (by omega) f4 f5, X₁]
  have O3₂ : val32 u₂.mem base (numAt len 3) (nw len) = val32 s.mem base (numAt len 3) (nw len) := by
    rw [mulFrame_val32 E₁.room nw' F₂ (.inl (by omega)) (by omega) (by omega) f4 f5, O3₁]
  have M₂ : u₂.mem.readW (off base 136) 32 = u₁.mem.readW (off base 136) 32 := by
    simp only [Mem.readW]
    rw [mulFrame_hdr E₁.room nw' F₂ (by decide) (by omega) f4 f5]
  have W₂ : val32 u₂.mem base 128 2 = val32 s.mem base 128 2 := by
    rw [← W₁, ← read_eq_val32, ← read_eq_val32, mulFrame_hdr E₁.room nw' F₂ (by decide) (by omega) f4 f5]
  -- The mask into `ecx`, and the selection.
  refine WP.seq (wp_movS (readSrc_sc E₂.pi.scratch (d := 136) (by omega)) fun u₃ e₃ _ => WP.block_nil ?_)
  have E₃ := E₂.keep e₃.keeps (by decide) (by decide) (by rw [e₃.mem]; exact Frame.refl _ _)
  have sp₃ : u₃.gpr .esp = s.gpr .esp := (e₃.other _ (by decide)).trans sp₂
  have hk₃ : u₃.gpr .ecx = cmask (decide (w32 s.mem base 128 % 2 = 1)) := by
    rw [e₃.gpr, M₂, M₁]
    by_cases hp : w32 s.mem base 128 % 2 = 1 <;> simp [hp, cmask]
  refine WP.seq (WP.mono (select_ok E₃.pi hbase (x := 4) (d := 2) (by decide) (by decide) (by decide) hk₃)
    fun u₄ ⟨O₄, V₄, edi₄, K₄⟩ => ?_)
  have E₄ := E₃.keep (Keeps.drop_edi (rs := [.eax, .ebx, .edx, .ebp]) K₄ edi₄) (by decide) (by decide)
    (Outside.chg O₄ (.inr ⟨by omega, by omega⟩))
  have sp₄ : u₄.gpr .esp = s.gpr .esp := (K₄.1 _ (by decide)).trans sp₃
  have X₄ : val32 u₄.mem base (numAt len 1) (nw len) = val32 s.mem base (numAt len 1) (nw len) := by
    rw [O₄.val32 (.inl (by omega)) (by omega), e₃.mem, X₂]
  have O3₄ : val32 u₄.mem base (numAt len 3) (nw len) = val32 s.mem base (numAt len 3) (nw len) := by
    rw [O₄.val32 (.inr (by omega)) (by omega), e₃.mem, O3₂]
  have W₄ : val32 u₄.mem base 128 2 = val32 s.mem base 128 2 := by
    rw [O₄.val32 (.inl (by omega)) (by omega), e₃.mem, W₂]
  -- The base squared.
  refine WP.seq (WP.mono (mulEnv_ok E₄ hbytes (o := 1) (a := 1) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (x := b) (y := b) (by rw [X₄, hX, Nat.mod_mod]) (by rw [X₄, hX, Nat.mod_mod])
    (by rw [X₄, hX]; exact Nat.mod_lt _ hM)) fun u₅ ⟨E₅, C₅, cs₅, F₅, X₅⟩ => ?_)
  have sp₅ : u₅.gpr .esp = s.gpr .esp := (cs₅.1 _ (by decide)).trans sp₄
  have f1 := (h.fits (j := 1) (by decide)).1
  have Y₅ : val32 u₅.mem base (numAt len 2) (nw len) = val32 u₄.mem base (numAt len 2) (nw len) :=
    mulFrame_val32 E₄.room nw' F₅ (.inr (by omega)) (by omega) (by omega) f1 f5
  have O3₅ : val32 u₅.mem base (numAt len 3) (nw len) = val32 s.mem base (numAt len 3) (nw len) := by
    rw [mulFrame_val32 E₄.room nw' F₅ (.inr (by omega)) (by omega) (by omega) f1 f5, O3₄]
  have W₅ : val32 u₅.mem base 128 2 = val32 s.mem base 128 2 := by
    rw [← W₄, ← read_eq_val32, ← read_eq_val32, mulFrame_hdr E₄.room nw' F₅ (by decide) (by omega) f1 f5]
  -- The exponent halved, and the count.
  refine WP.block_append (WP.mono (shiftExponent_ok E₅.pi.scratch 2 128 (by omega)) fun u₆ ⟨O₆, V₆, K₆⟩ => ?_)
  refine wp_subZ rfl fun t e₇ z₇ => WP.block_nil ?_
  have E₆ := E₅.keep K₆ (by decide) (by decide) (Outside.chg O₆ (.inl ⟨by decide, by decide⟩))
  have sp₆ : u₆.gpr .esp = s.gpr .esp := (K₆.1 _ (by decide)).trans sp₅
  have esi₆ : u₆.gpr .esi = BitVec.ofNat 32 k := by
    rw [K₆.1 _ (by decide), cs₅.1 _ (by decide), K₄.1 _ (by decide), e₃.other _ (by decide),
      cs₂.1 _ (by decide), K₁.1 _ (by decide), hc]
  have esiT : t.gpr .esi = BitVec.ofNat 32 (k - 1) := by
    rw [e₇.gpr, esi₆, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  refine ⟨E₆.keep e₇.keeps (by decide) (by decide) (by rw [e₇.mem]; exact Frame.refl _ _), ?_, esiT, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · have G₁ : Frame (Chg base len bytes (s.gpr .esp)) s.mem u₁.mem := Outside.chg O₁ (.inl ⟨by decide, by decide⟩)
    have G₂ : Frame (Chg base len bytes (s.gpr .esp)) u₁.mem u₂.mem := by rw [← sp₁]; exact C₂
    have G₄ : Frame (Chg base len bytes (s.gpr .esp)) u₂.mem u₄.mem := by
      have := Outside.chg (len := len) (bytes := bytes) (sp := s.gpr .esp) O₄ (.inr ⟨by omega, by omega⟩)
      rwa [e₃.mem] at this
    have G₅ : Frame (Chg base len bytes (s.gpr .esp)) u₄.mem u₅.mem := by rw [← sp₄]; exact C₅
    have G₆ : Frame (Chg base len bytes (s.gpr .esp)) u₅.mem t.mem := by
      rw [e₇.mem]; exact Outside.chg O₆ (.inl ⟨by decide, by decide⟩)
    exact (((G₁.trans G₂).trans G₄).trans G₅).trans G₆
  · rw [z₇, esi₆, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show k - 1 = 0 ↔ k = 1 by omega]
  · rw [e₇.mem, O₆.val32 (.inr (by omega)) (by omega), Y₅, V₄, e₃.mem, T₂, Y₂, hY, ← val32_parity s.mem base 128 1]
    by_cases hp : val32 s.mem base 128 (1 + 1) % 2 = 1 <;> simp [hp]
  · rw [e₇.mem, O₆.val32 (.inr (by omega)) (by omega), X₅]
  · rw [e₇.mem, V₆, W₅]
  · exact ((((((K₁.mono (by decide)).trans (cs₂.mono (by decide))).trans (e₃.keeps.mono (by decide))).trans
      ((Keeps.drop_edi (rs := [.eax, .ebx, .edx, .ebp]) K₄ edi₄).mono (by decide))).trans
      (cs₅.mono (by decide))).trans (K₆.mono (by decide))).trans (e₇.keeps.mono (by decide))
  · rw [e₇.mem, O₆.val32 (.inr (by omega)) (by omega), O3₅]

end VG.Proof.Bignum.X86.PublicRt
