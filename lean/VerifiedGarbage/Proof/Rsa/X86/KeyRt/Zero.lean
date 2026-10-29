module

import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Framework.Omega
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Spec.Weierstrass

/-! # The key workspace's arrays zeroed at a run-time width, and its bit count

`zeroWide_ok`: an array's `w + 1` words zeroed; `zeroArrays_ok`: the first
`n` arrays, from the first's start; `bits_ok`: `esi = 32 w`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S arr_mono)

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem zeroWide_ok {s : State} (h : RtWs L s B Z len N) {j : Nat} (hj : j < N) :
    WP isa (zeroWide L j) s fun t => RtWs L t B Z len N ∧ Keep B (kw len) [j] [] s.mem t.mem ∧
      val32 t.mem B (arr (kw len) j) (kw len + 1) = 0 ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have fit := h.ws.arr_fit hj
  have nw := h.ws.workspace.nowrap
  have wpos := h.kw_pos
  simp only [S] at fit
  have hl := lenSrc h
  have hle := h.lenLe
  unfold zeroWide
  simp only [List.append_assoc]
  refine WP.seq (arrPtr_ok hl hle h.edi (by decide) (by decide) (by omega) fun u₁ K₁ m₁ p₁ _ => ?_)
  have hl₁ := hl.keep K₁ (by decide) m₁
  refine count_ok hl₁ hle fun u₂ K₂ m₂ c₂ => wp_movS rfl fun u₃ U₃ _ => WP.block_nil ?_
  have K : Keeps [.eax, .ecx, .edx, .ebp] s u₃ :=
    ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (U₃.keeps.mono (by decide))
  have m : u₃.mem = s.mem := by rw [U₃.mem, m₂, m₁]
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.zeroLoop_ok (h.rt.of_keeps K) (x := arr (kw len) j)
    (N := kw len + 1) (by omega) (by omega)
    (by rw [PtrAt, U₃.other _ (by decide), K₂.1 _ (by decide)]; exact p₁)
    (by rw [U₃.other _ (by decide), c₂]; simp) U₃.gpr) fun t ⟨O, V, Kt⟩ => ?_
  rw [m] at O
  have Kall : Keeps [.eax, .ecx, .edx, .ebp] s t := K.trans (Kt.mono (by decide))
  exact ⟨h.keep Kall (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega)),
    Keep.of_arr (d := 0) (by simpa using O) (by simp only [S]; omega) (by simp), V, Kall⟩

theorem zeroArrays_ok {s : State} (h : RtWs L s B Z len N) {n : Nat} (hn : 0 < n) (hnN : n ≤ N) :
    WP isa (zeroArrays L n) s fun t => RtWs L t B Z len N ∧
      Outside B (arr (kw len) 0) (4 * (n * (kw len + 2))) s.mem t.mem ∧
      (∀ j < n, val32 t.mem B (arr (kw len) j) (kw len + 2) = 0) ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have fits : 160 + 4 * (N * (kw len + 2)) ≤ Z := by
    have := h.ws.fits
    simp only [arr, S, VG.Impl.Rsa.X86.Keys.hdr] at this
    rwa [Nat.mul_left_comm] at this
  have le : n * (kw len + 2) ≤ N * (kw len + 2) := Nat.mul_le_mul_right _ hnN
  have pos : 1 ≤ n * (kw len + 2) := Nat.mul_pos hn (by omega)
  have e8 : n * (4 * kw len + 8) = 4 * (n * (kw len + 2)) := by
    rw [show 4 * kw len + 8 = 4 * (kw len + 2) by omega, Nat.mul_left_comm]
  have a0 : arr (kw len) 0 = 160 := by simp [arr, VG.Impl.Rsa.X86.Keys.hdr]
  have nw := h.ws.workspace.nowrap
  have hl := lenSrc h
  have hle := h.lenLe
  unfold zeroArrays
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (arrPtr_ok hl hle h.edi (by decide) (by decide) (by rw [a0]; decide)
    fun u₁ K₁ m₁ p₁ e₁ => wp_movS rfl fun u₂ U₂ _ => ?_)
  refine VG.Proof.Bignum.X86.PublicRt.adds_ok (r := .ecx) (t := .edx) (by decide) n fun u₃ K₃ m₃ e₃ =>
    wp_movS rfl fun u₄ U₄ _ => WP.block_nil ?_
  have K : Keeps [.eax, .ecx, .edx, .ebp] s u₄ :=
    (((K₁.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (K₃.mono (by decide))).trans
      (U₄.keeps.mono (by decide))
  have m : u₄.mem = s.mem := by rw [U₄.mem, m₃, U₂.mem, m₁]
  have edx₂ : (u₂.gpr .edx).toNat = 4 * kw len + 8 := by rw [U₂.other _ (by decide)]; exact e₁
  have ecx : (u₄.gpr .ecx).toNat = 4 * (n * (kw len + 2)) := by
    rw [U₄.other _ (by decide), e₃, U₂.gpr, edx₂]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [show (0 : BitVec 32).toNat = 0 from rfl]
    rw [e8, Nat.mod_eq_of_lt (a := 4 * (n * (kw len + 2))) (by omega)]
    simp only [Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.zeroLoop_ok (h.rt.of_keeps K) (x := arr (kw len) 0)
    (N := n * (kw len + 2)) pos (by rw [a0]; omega)
    (by rw [PtrAt, U₄.other _ (by decide), K₃.1 _ (by decide), U₂.other _ (by decide)]; exact p₁)
    ecx U₄.gpr) fun t ⟨O, V, Kt⟩ => ?_
  rw [m] at O
  have Kall : Keeps [.eax, .ecx, .edx, .ebp] s t := K.trans (Kt.mono (by decide))
  refine ⟨h.keep Kall (by decide) (by decide) (O.mono (Nat.zero_le _) (by rw [a0]; omega)), O, ?_, Kall⟩
  intro j hj
  have bound := Nat.mul_le_mul_right (kw len + 2) (show j + 1 ≤ n by omega)
  rw [Nat.add_mul, Nat.one_mul] at bound
  have part := VG.Proof.Rsa.KeyWorkspace.val32_zero_part V (a := j * (kw len + 2)) (c := kw len + 2) bound
  have e : arr (kw len) 0 + 4 * (j * (kw len + 2)) = arr (kw len) j := by
    simp only [arr, S, Nat.zero_mul, Nat.add_zero, Nat.mul_left_comm j 4]
  rwa [e] at part

/-- `esi = 32 w`. -/
theorem bits_ok {s : State} {is : List Instr} {Q : State → Prop} (h : RtWs L s B Z len N)
    (k : ∀ t, Keeps [.esi] s t → t.mem = s.mem → t.gpr .esi = BitVec.ofNat 32 (32 * kw len) →
      WP isa (.block is) t Q) :
    WP isa (.block (bits L ++ is)) s Q := by
  have hw := kw_bound h.lenLe
  unfold bits
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine bytesB_ok (lenSrc h) h.lenLe fun u₁ K₁ m₁ e₁ => wp_addS rfl fun u₂ U₂ _ => wp_addS rfl fun u₃ U₃ _ =>
    wp_addS rfl fun t T _ => k t (((K₁.trans U₂.keeps).trans U₃.keeps).trans T.keeps)
      (by rw [T.mem, U₃.mem, U₂.mem, m₁]) ?_
  apply BitVec.eq_of_toNat_eq
  rw [T.gpr, U₃.gpr, U₂.gpr]
  simp only [BitVec.toNat_add, e₁, BitVec.toNat_ofNat]
  omega

end VG.Proof.Rsa.X86.KeyRt
