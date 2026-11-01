module

import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Mont.X86.ExponentWord
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt

/-! # A number's words halved through a pointer

`shiftDownLoop_ok`: the `N` words at `ebp` each shifted down by a bit,
bringing in the low bit of the word above (`Dynamic.shiftDown`'s loop, at a
run-time width).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (countLoop ptr4 wp_shr)

theorem shiftDownLoop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Rt.Ws t₀ W L) {x N : Nat} (hN : 0 < N)
    (hx : x + 4 * N + 4 ≤ L) (hebp : PtrAt t₀ W .ebp x) (hedx : (t₀.gpr .edx).toNat = 4 * N) :
    WP isa shiftDownLoop t₀ fun u => Outside W x (4 * N) t₀.mem u.mem ∧ PtrAt u W .ebp (x + 4 * N) ∧
      (∀ i < N, w32 u.mem W (x + 4 * i) =
        w32 t₀.mem W (x + 4 * i) / 2 + 2 ^ 31 * (w32 t₀.mem W (x + 4 * (i + 1)) % 2)) ∧
      Keeps [.eax, .ecx, .edx, .ebp] t₀ u := by
  have hn := hw.nowrap
  unfold shiftDownLoop
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ecx, .edx, .ebp] t₀ t ∧ PtrAt t W .ebp (x + 4 * j) ∧
      (t.gpr .edx).toNat = 4 * (N - j) ∧ Outside W x (4 * j) t₀.mem t.mem ∧
      ∀ i < j, w32 t.mem W (x + 4 * i) =
        w32 t₀.mem W (x + 4 * i) / 2 + 2 ^ 31 * (w32 t₀.mem W (x + 4 * (i + 1)) % 2)) ?_
    ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hedx, Outside.refl _ _ _ _,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun u ⟨K, P, _, O, V⟩ => ⟨O, P, V, K⟩
  rintro j t hj ⟨Kt, ebp, edx, O, V⟩
  have ht := hw.of_keeps Kt
  refine wp_movS (readSrc_ptr ht ebp (d := 4) (by omega_using [hx, hj])) fun s₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₂ u₂ => wp_ror (by decide) fun s₃ u₃ => ?_
  have K₃ : Keeps [.eax] t s₃ := (u₁.keeps.trans u₂.keeps).trans u₃.keeps
  have ht₃ := ht.of_keeps K₃
  have ebp₃ : PtrAt s₃ W .ebp (x + 4 * j) := by rw [PtrAt, K₃.1 _ (by decide)]; exact ebp
  refine wp_movS (readSrc_ptr ht₃ ebp₃ (d := 0) (by omega_using [hx, hj])) fun s₄ u₄ _ => ?_
  refine wp_shr (by decide) fun s₅ u₅ => wp_addS rfl fun s₆ u₆ _ => ?_
  have K₆ : Keeps [.eax, .ecx] t s₆ := ((K₃.mono (by decide)).widen u₄.keeps |>.widen u₅.keeps).widen u₆.keeps
  have ht₆ := ht.of_keeps K₆
  have ebp₆ : PtrAt s₆ W .ebp (x + 4 * j) := by rw [PtrAt, K₆.1 _ (by decide)]; exact ebp
  have mem₆ : s₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine wp_storeS (ea_ptr ht₆ ebp₆ (d := 0) (by omega_using [hx, hj]))
    (ws_write ht₆ (y := x + 4 * j + 0) (n := 4) (by omega_using [hx, hj])) fun s₇ m₇ => ?_
  refine wp_addS rfl fun s₈ u₈ _ => wp_subZ rfl fun s₉ u₉ z₉ => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count_zf edx hj
  have edx₈ : s₈.gpr .edx = t.gpr .edx := by
    rw [u₈.other _ (by decide), m₇.gpr, K₆.1 _ (by decide)]
  have word : (s₆.gpr .ecx).toNat = w32 t.mem W (x + 4 * j) / 2 + 2 ^ 31 * (w32 t.mem W (x + 4 * (j + 1)) % 2) := by
    rw [u₆.gpr, u₅.gpr, u₅.other .eax (by decide), u₄.gpr, u₄.other .eax (by decide),
      u₃.gpr, u₂.gpr, u₁.gpr, ite_eq_left rfl, u₃.mem, u₂.mem, u₁.mem, VG.Proof.Mont.X86.Dynamic.shifted_word, Nat.add_zero,
      show x + 4 * j + 4 = x + 4 * (j + 1) by omega_arith]
  refine ⟨⟨Kt.trans ((((K₆.mono (by decide)).widen (m₇.keeps [])).widen u₈.keeps).widen u₉.keeps), ?_,
    by rw [u₉.gpr, edx₈]; exact c₁, ?_, ?_⟩, by rw [z₉, edx₈, c₂]⟩
  · rw [PtrAt, u₉.other _ (by decide), u₈.gpr, m₇.gpr, K₆.1 _ (by decide)]; exact ptr4 ebp
  · rw [u₉.mem, u₈.mem, m₇.mem, mem₆, Nat.add_zero]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hx, hj, hn])).mono (by omega_using []) (by omega_using []))
  · intro i hi
    rw [u₉.mem, u₈.mem, m₇.mem, mem₆, Nat.add_zero]
    by_cases hij : i < j
    · rw [(writeW32_outside t.mem W (d := x + 4 * j) _ (by omega_arith)).w32 (by omega_arith) (by omega_arith)]
      exact V i hij
    · obtain rfl : i = j := by omega_arith
      rw [w32_write_self, word, O.w32 (d := x + 4 * i) (by omega_arith) (by omega_arith),
        O.w32 (d := x + 4 * (i + 1)) (by omega_arith) (by omega_arith)]

end VG.Proof.Rsa.X86.KeyRt
