module

import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.ShiftDown
import VerifiedGarbage.Proof.Mont.X86.ShiftDown
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

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
