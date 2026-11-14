module

import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Mont.X86.ExponentWord
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
import VerifiedGarbage.Proof.Mont.X86.ShiftDown
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! ### `Rsa.X86.KeyRt.ShiftDown`, which only this module used -/

section

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

end

end


/-! # An array of the key workspace halved at a run-time width

`half_ok` states `Keys.half_ok`'s result for the run-time width's `half`:
`ebx` stored as the array's word `w`, its `w + 1` words shifted down by a bit
(`shiftDownLoop_ok`, then the top word).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S)

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem half_ok {s : State} (h : RtWs L s B Z len N) {j : Nat} (hj : j < N) (bit : (s.gpr .ebx).toNat ≤ 1) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.half L j) s fun t => RtWs L t B Z len N ∧ Keep B (kw len) [j] [] s.mem t.mem ∧
      num t.mem B (kw len) j = (num s.mem B (kw len) j + 2 ^ (32 * kw len) * (s.gpr .ebx).toNat) / 2 ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have fit := h.ws.arr_fit hj
  simp only [S] at fit
  have nw := h.ws.workspace.nowrap
  have wpos := h.kw_pos
  have hl := lenSrc h
  have hle := h.lenLe
  have hw := h.rt
  unfold VG.Impl.Rsa.X86.KeyRt.half
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- The top word, then the pointer back at the array.
  refine WP.seq (arrPtr_ok hl hle h.edi (by decide) (by decide) (by omega_arith) fun u₁ K₁ m₁ p₁ _ => ?_)
  have hl₁ := hl.keep K₁ (by decide) m₁
  refine bytesB_ok hl₁ hle fun u₂ K₂ m₂ e₂ => wp_addS rfl fun u₃ U₃ _ => ?_
  have K₃ : Keeps [.edx, .ebp] s u₃ := ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (U₃.keeps.mono (by decide))
  have p₃ : PtrAt u₃ B .ebp (arr (kw len) j + 4 * kw len) := by
    rw [PtrAt, U₃.gpr, VG.Proof.Mont.X86.Rt.ptr_add (by rw [PtrAt, K₂.1 _ (by decide)]; exact p₁), e₂]
  have hw₃ := hw.of_keeps K₃
  refine wp_storeS (ea_ptr hw₃ p₃ (d := 0) (by omega_arith)) (ws_write hw₃ (y := arr (kw len) j + 4 * kw len + 0) (n := 4)
    (by omega_arith)) fun u₄ m₄ => ?_
  have ebx₄ : u₃.gpr .ebx = s.gpr .ebx := K₃.1 _ (by decide)
  have mu₃ : u₃.mem = s.mem := by rw [U₃.mem, m₂, m₁]
  have hl₄ : LenSrc L u₄ len := by
    obtain ⟨a, l, e, c⟩ := h.lenArg
    refine ⟨a, l, e, ?_⟩
    rw [lenOp_eq h.layLen]; exact (c.keep (K₃.widen (m₄.keeps [])) (by decide) (by
      rw [m₄.mem, mu₃]; exact (writeW32_outside _ _ _ (by omega_arith)).mono (Nat.zero_le _) (by omega_arith))).readSrc
  have edi₄ : (u₄.gpr .edi).toNat = B.toNat := by rw [m₄.gpr, K₃.1 _ (by decide)]; exact h.edi
  refine arrPtr_ok hl₄ hle edi₄ (by decide) (by decide) (by omega_arith) fun u₅ K₅ m₅ p₅ _ => ?_
  have hl₅ := hl₄.keep K₅ (by decide) m₅
  rw [show bytesB L .edx = bytesB L .edx ++ [] from (List.append_nil _).symm]
  refine bytesB_ok hl₅ hle fun t₀ K₆ m₆ e₆ => WP.block_nil ?_
  have K₀ : Keeps [.edx, .ebp] s t₀ :=
    ((K₃.widen (m₄.keeps [])).trans (K₅.mono (by decide))).trans (K₆.mono (by decide))
  have mt₀ : t₀.mem = u₄.mem := m₆.trans m₅
  have stored : Outside B (arr (kw len) j + 4 * kw len) 4 s.mem t₀.mem := by
    rw [mt₀, m₄.mem, mu₃, Nat.add_zero]; exact writeW32_outside _ _ _ (by omega_arith)
  have top₀ : w32 t₀.mem B (arr (kw len) j + 4 * kw len) = (s.gpr .ebx).toNat := by
    rw [mt₀, m₄.mem, mu₃, Nat.add_zero, w32_write_self, ebx₄]
  -- The low words, then the top word.
  refine WP.seq (WP.mono (shiftDownLoop_ok (hw.of_keeps K₀) (x := arr (kw len) j) (N := kw len) wpos (by omega_arith)
    (by rw [PtrAt, K₆.1 _ (by decide)]; exact p₅) (by rw [e₆])) fun u ⟨O, P, W, Ku⟩ => ?_)
  have hwu := hw.of_keeps ((K₀.mono (rs' := [.eax, .ecx, .edx, .ebp]) (by decide)).trans Ku)
  refine wp_movS (readSrc_ptr hwu P (d := 0) (by omega_arith)) fun v₁ V₁ _ => wp_shr (by decide) fun v₂ V₂ _ => ?_
  have K₂' : Keeps [.eax] u v₂ := V₁.keeps.trans V₂.keeps
  have hwv := hwu.of_keeps K₂'
  have Pv : PtrAt v₂ B .ebp (arr (kw len) j + 4 * kw len) := by rw [PtrAt, K₂'.1 _ (by decide)]; exact P
  refine wp_storeS (ea_ptr hwv Pv (d := 0) (by omega_arith)) (ws_write hwv (y := arr (kw len) j + 4 * kw len + 0) (n := 4)
    (by omega_arith)) fun t T => WP.block_nil ?_
  have mv : v₂.mem = u.mem := V₂.mem.trans V₁.mem
  have topT : w32 t.mem B (arr (kw len) j + 4 * kw len) = (s.gpr .ebx).toNat / 2 := by
    rw [T.mem, Nat.add_zero, w32_write_self, V₂.gpr, V₁.gpr, Nat.add_zero, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    change w32 u.mem B _ / 2 ^ 1 = _
    rw [O.w32 (by omega_arith) (by omega_arith), top₀]
  have lastT : Outside B (arr (kw len) j + 4 * kw len) 4 u.mem t.mem := by
    rw [T.mem, mv, Nat.add_zero]; exact writeW32_outside _ _ _ (by omega_arith)
  -- The frame and the value.
  have Kall : Keeps [.eax, .ecx, .edx, .ebp] s t :=
    (K₀.mono (by decide)).trans (Ku.trans ((K₂'.mono (by decide)).trans (T.keeps [] |>.mono (by decide))))
  have Os : Outside B (arr (kw len) j) (4 * kw len + 4) s.mem t.mem :=
    ((stored.mono (by omega_arith) (by omega_arith)).trans (O.mono (Nat.le_refl _) (by omega_arith))).trans (lastT.mono (by omega_arith) (by omega_arith))
  refine ⟨h.keep Kall (by decide) (by decide) (Os.mono (Nat.zero_le _) (by omega_arith)),
    Keep.of_arr (d := 0) (by simpa using Os) (by simp only [S]; omega_arith) (by simp), ?_, Kall⟩
  have original : val32 t₀.mem B (arr (kw len) j) (kw len + 1) =
      num s.mem B (kw len) j + 2 ^ (32 * kw len) * (s.gpr .ebx).toNat := by
    rw [val32_succ, top₀, stored.val32 (by omega_arith) (by omega_arith)]
  have halved : val32 t.mem B (arr (kw len) j) (kw len + 1) = val32 t₀.mem B (arr (kw len) j) (kw len + 1) / 2 := by
    refine VG.Proof.Mont.X86.Dynamic.val32_halve t₀.mem t.mem B (kw len + 1) (arr (kw len) j) fun i hi => ?_
    by_cases hik : i + 1 = kw len + 1
    · obtain rfl : i = kw len := by omega_arith
      rw [ite_eq_left hik, topT, Nat.mul_zero, Nat.add_zero, top₀]
    · rw [ite_eq_right hik, lastT.w32 (by omega_arith) (by omega_arith)]
      exact W i (by omega_arith)
  rw [original] at halved
  have bound := val32_lt s.mem B (arr (kw len) j) (kw len)
  have small : (num s.mem B (kw len) j + 2 ^ (32 * kw len) * (s.gpr .ebx).toNat) / 2 < 2 ^ (32 * kw len) := by
    have mul : 2 ^ (32 * kw len) * (s.gpr .ebx).toNat ≤ 2 ^ (32 * kw len) := by
      simpa using Nat.mul_le_mul_left (2 ^ (32 * kw len)) bit
    unfold num
    omega_arith
  have lower := val32_lt t.mem B (arr (kw len) j) (kw len)
  rw [val32_succ] at halved
  have topZero : w32 t.mem B (arr (kw len) j + 4 * kw len) = 0 := by
    by_contra ne
    have ge := Nat.mul_le_mul_left (2 ^ (32 * kw len)) (show 1 ≤ w32 t.mem B (arr (kw len) j + 4 * kw len) by omega_arith)
    simp only [Nat.mul_one] at ge
    omega_arith
  rw [topZero, Nat.mul_zero, Nat.add_zero] at halved
  exact halved

end VG.Proof.Rsa.X86.KeyRt
