module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
import VerifiedGarbage.Proof.Framework.Omega

/-! # The loops of private CRT at a run-time width that public RSA's lack

The sum of two numbers (`addLoop_ok`), the shift of a number up by four bits
(`shiftLoop_ok`) and a row of a product (`rowLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (countLoop ptr4 wp_carry)

/-! ## Sum -/

theorem addLoop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {a m d N : Nat} (hN : 0 < N)
    (ha : a + 4 * N ≤ L) (hm : m + 4 * N ≤ L) (hd : d + 4 * N ≤ L)
    (hda : d ≤ a ∨ a + 4 * N ≤ d) (hdm : d ≤ m ∨ m + 4 * N ≤ d)
    (hebp : PtrAt t₀ W .ebp a) (hebx : PtrAt t₀ W .ebx m) (hedi : PtrAt t₀ W .edi d)
    (hedx : (t₀.gpr .edx).toNat = 4 * N) (hecx : t₀.gpr .ecx = cmask false) :
    WP isa (.loop (.block [.mov .eax (.mem (at_ .ebp 0)), .alu .add .ecx (.reg .ecx),
      .alu .adc .eax (.mem (at_ .ebx 0)), .store (at_ .edi 0) .eax, .alu .sbb .ecx (.reg .ecx),
      .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4), .alu .add .edi (.imm 4),
      .alu .sub .edx (.imm 4)]) .ne) t₀
      fun u => Outside W d (4 * N) t₀.mem u.mem ∧ PtrAt u W .ebp (a + 4 * N) ∧ PtrAt u W .edi (d + 4 * N) ∧
        (∃ c : Bool, u.gpr .ecx = cmask c ∧
          val32 u.mem W d N + 2 ^ (32 * N) * c.toNat = val32 t₀.mem W a N + val32 t₀.mem W m N) ∧
        Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] t₀ u := by
  have hn := hw.nowrap
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] t₀ t ∧
      PtrAt t W .ebp (a + 4 * j) ∧ PtrAt t W .ebx (m + 4 * j) ∧ PtrAt t W .edi (d + 4 * j) ∧
      (t.gpr .edx).toNat = 4 * (N - j) ∧ Outside W d (4 * j) t₀.mem t.mem ∧ ∃ c : Bool, t.gpr .ecx = cmask c ∧
        val32 t.mem W d j + 2 ^ (32 * j) * c.toNat = val32 t₀.mem W a j + val32 t₀.mem W m j) ?_
    ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hebx, by simpa using hedi, by simpa using hedx,
      Outside.refl _ _ _ _, false, hecx, by simp [val32]⟩)
    fun u ⟨K, ebp, _, edi, _, O, V⟩ => ⟨O, ebp, edi, V, K⟩
  rintro j t hj ⟨Kt, ebp, ebx, edi, edx, O, c, ec, V⟩
  have ht := hw.of_keeps Kt
  have aw : w32 t.mem W (a + 4 * j) = w32 t₀.mem W (a + 4 * j) :=
    O.w32 (by omega_using [hda, hj]) (by omega_using [ha, hj, hn])
  have mw : w32 t.mem W (m + 4 * j) = w32 t₀.mem W (m + 4 * j) :=
    O.w32 (by omega_using [hdm, hj]) (by omega_using [hm, hj, hn])
  refine wp_movS (readSrc_ptr ht ebp (d := 0) (by omega_using [ha, hj])) fun s₁ u₁ _ => ?_
  refine wp_carry (by rw [u₁.other _ (by decide), ec]) fun s₂ u₂ c₂ => ?_
  have K₂ : Keeps [.eax, .ecx] t s₂ := (u₁.keeps.mono (by decide)).widen u₂.keeps
  have ht₂ := ht.of_keeps K₂
  have ebx₂ : PtrAt s₂ W .ebx (m + 4 * j) := by rw [PtrAt, K₂.1 _ (by decide)]; exact ebx
  refine wp_adcS (readSrc_ptr ht₂ ebx₂ (d := 0) (by omega_using [hm, hj])) c₂ fun s₃ u₃ c₃ => ?_
  have K₃ : Keeps [.eax, .ecx] t s₃ := K₂.widen u₃.keeps
  have ht₃ := ht.of_keeps K₃
  have edi₃ : PtrAt s₃ W .edi (d + 4 * j) := by rw [PtrAt, K₃.1 _ (by decide)]; exact edi
  refine wp_storeS (ea_ptr ht₃ edi₃ (d := 0) (by omega_using [hd, hj]))
    (ws_write ht₃ (y := d + 4 * j + 0) (n := 4) (by omega_using [hd, hj])) fun s₄ m₄ => ?_
  refine wp_sbb_self (by rw [m₄.cf]; exact c₃) fun s₅ u₅ => ?_
  refine wp_addS rfl fun s₆ u₆ _ => wp_addS rfl fun s₇ u₇ _ => wp_addS rfl fun s₈ u₈ _ => ?_
  refine wp_subZ rfl fun s₉ u₉ z₉ => WP.block_nil ?_
  obtain ⟨c₁, c₂'⟩ := count_zf edx hj
  have K₅ : Keeps [.eax, .ecx] t s₅ := (K₃.widen (m₄.keeps [])).widen u₅.keeps
  have r₅ : ∀ r, r = .ebp ∨ r = .ebx ∨ r = .edi ∨ r = .edx → s₅.gpr r = t.gpr r := by
    intro r hr; apply K₅.1; rcases hr with rfl | rfl | rfl | rfl <;> decide
  have m₂ : s₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  have eax₂ : (s₂.gpr .eax).toNat = w32 t₀.mem W (a + 4 * j) := by
    rw [u₂.other _ (by decide), u₁.gpr, Nat.add_zero, ← aw]
  have src₂ : (s₂.mem.readW (off W (m + 4 * j + 0)) 32).toNat = w32 t₀.mem W (m + 4 * j) := by
    rw [m₂, Nat.add_zero, ← mw]
  refine ⟨⟨Kt.trans ((((K₅.mono (by decide)).widen u₆.keeps).widen u₇.keeps |>.widen u₈.keeps).widen u₉.keeps),
    ?_, ?_, ?_, ?_, ?_,
    decide (2 ^ 32 ≤ (s₂.gpr .eax).toNat + (s₂.mem.readW (off W (m + 4 * j + 0)) 32).toNat + c.toNat),
    ?_, ?_⟩, ?_⟩
  · rw [PtrAt, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
      r₅ _ (.inl rfl)]; exact ptr4 ebp
  · rw [PtrAt, u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
      r₅ _ (.inr (.inl rfl))]; exact ptr4 ebx
  · rw [PtrAt, u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
      r₅ _ (.inr (.inr (.inl rfl)))]; exact ptr4 edi
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      r₅ _ (.inr (.inr (.inr rfl)))]; exact c₁
  · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄.mem, u₃.mem, m₂, Nat.add_zero]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hd, hj, hn])).mono (by omega_using []) (by omega_using []))
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄.mem, u₃.mem, m₂, Nat.add_zero,
      val32_store hn (by omega_using [hd, hj]), val32_succ t₀.mem W m, val32_succ t₀.mem W a, pow32_succ, u₃.gpr]
    have h := adc_rel (s₂.gpr .eax) (s₂.mem.readW (off W (m + 4 * j + 0)) 32) c
    rw [eax₂, src₂] at h
    rw [show (t.mem.readW (off W (m + 4 * j + 0)) 32).toNat = w32 t₀.mem W (m + 4 * j) by
      rw [← m₂]; exact src₂]
    rw [eax₂] at *
    exact chain_add_step V h
  · rw [z₉, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      r₅ _ (.inr (.inr (.inr rfl))), c₂']

end VG.Proof.Bignum.X86.CrtRt
