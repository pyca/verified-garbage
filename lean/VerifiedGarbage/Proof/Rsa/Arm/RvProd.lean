module

public import VerifiedGarbage.Proof.Rsa.Arm.RvNumbers
public import VerifiedGarbage.Proof.Rsa.Arm.MulMod
public import VerifiedGarbage.Proof.Rsa.Octets
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: `M = d e`

After the loads, the arrays read with `W` words hold `0`, `e`, `d` (`AW1`);
`setTop` makes the modulus `2^(32 W - 1)`, and `mulMod` over the `8 e_len`
bits of `e` leaves `d e` (`prod_vp`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

theorem bytes_lt (m : Mem) (a : Addr) (k : Nat) : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m a k) < 2 ^ (8 * k) := by
  have := VG.Proof.Rsa.lt_of_os2ip (Spec.Rsa.bytesAt m a k)
  rwa [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this

/-- `setTop j`: the top word of `[j]` := `2^31`. -/
theorem setTop_ok {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) (hw : 1 ≤ w) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → Keep B w [j] [] s.mem t.mem →
      num t.mem B w j = val32 s.mem (State.addr B) (arr w j) (w - 1) + 2 ^ (32 * (w - 1)) * 2 ^ 31 →
      Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (setTop j ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have wl := h.wle
  unfold setTop
  rw [List.append_assoc]
  refine ptr_ok h (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  have e3 : s3.gpr .r0 = B + BitVec.ofNat 32 (arr w j + 4 * (w - 1)) := by
    rw [u3.gpr, dpVal, u2.gpr, dpVal, p1, h1.r9]
    have : BitVec.ofNat 32 w <<< 2 = BitVec.ofNat 32 (4 * w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    rw [this, BitVec.add_assoc, ← BitVec.ofNat_add,
      show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_sub32 _ (by omega)]
    congr 2; omega
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
  have h4 : Ws s4 B Z w N :=
    ((h1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide) (by decide) (by decide)).of_upd u4
      (by decide) (by decide) (by decide)
  have a0 : State.addr (s4.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w j + 4 * (w - 1)) := by
    rw [u4.other _ (by decide), e3, BitVec.add_zero]; exact h.addr (by omega)
  refine wp_str (by decide) a0 (h4.write (by omega)) fun t u5 => ?_
  have ht := h4.of_mupd u5
  have mt : t.mem = s.mem.writeW (off (State.addr B) (arr w j + 4 * (w - 1))) (0x80000000 : BitVec 32) := by
    rw [u5.mem, u4.gpr, u4.mem, u3.mem, u2.mem, m1]
  have o1 := writeW32_outside s.mem (State.addr B) (d := arr w j + 4 * (w - 1)) (0x80000000 : BitVec 32)
    (by omega)
  rw [← mt] at o1
  refine k t ht (Keep.of_arr (d := 4 * (w - 1)) o1 (by omega) (by simp)) ?_
    ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans (u5.rest _)))))
  change val32 _ _ _ _ = _
  have e := val32_succ t.mem (State.addr B) (arr w j) (w - 1)
  rw [show w - 1 + 1 = w by omega] at e
  rw [e, o1.val32 (by omega) (by omega)]
  congr 2
  simp only [w32]; rw [mt, Mem.readW_writeW_self32]; rfl

/-- The arrays with `W` words after the loads. -/
def AW1 (P : RP) (σ : State) : Nat → Nat := upd (upd (fun _ => 0) wE P.e) wD (dv P σ)

/-- After the loads: the stage. -/
theorem LS.ks {P : RP} {σ s : State} (h : LS P σ (Aload P σ) s) :
    KS P σ (Aload P σ) [aN] (AW1 P σ) [wZ, wE, wD, wM, wMod] (fun _ => 0) [] s := by
  have sz := h.bs.pre.sizes
  have kw := sz.kw
  have hn : P.n < 2 ^ (32 * P.w) := by
    have := h.bs.pre.nB ▸ bytes_lt σ.mem (State.addr P.nP) P.K
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  have he : Spec.Rsa.os2ip P.eB < 2 ^ (32 * P.w) := by
    have hb := h.bs.pre.eB ▸ bytes_lt σ.mem (State.addr P.eP) P.el
    have := h.bs.pre.el2
    exact Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (n := 2) (by decide) (show 8 * P.el ≤ 32 * P.w by omega))
  have hd : dv P σ < 2 ^ (32 * P.w) := by
    have hb := bytes_lt σ.mem (State.addr P.dP) P.dl
    have := h.bs.pre.dl2
    exact Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (n := 2) (by decide) (show 8 * P.dl ≤ 32 * P.w by omega))
  have nw : ∀ j < nArr, Aload P σ j < 2 ^ (32 * P.w) → num s.mem P.B P.w j = Aload P σ j := fun j hj hl => by
    rw [← h.full j hj] at hl ⊢
    exact VG.Proof.Rsa.Arm.CrtValues.val32_low2 hl
  have z : ∀ j < nArr, j ≠ aN → j ≠ 2 * wE → j ≠ 2 * wD → num s.mem P.B P.w j = 0 := fun j hj a b c => by
    rw [nw j hj (by simp only [Aload, upd, a, b, c, ↓reduceIte]; exact Nat.two_pow_pos _)]
    simp only [Aload, upd, a, b, c, ↓reduceIte]
  refine ⟨h.bs, h.ws.r8, h.cnt, ?_, ?_, by simp, by simp only [List.mem_singleton]; rintro j rfl; decide,
    by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro j (rfl | rfl | rfl | rfl | rfl) <;> decide,
    by simp⟩
  · intro j hj; simp only [List.mem_singleton] at hj; subst hj
    exact (nw aN (by decide) (by simp only [Aload, upd]; simp; exact hn)).trans rfl
  · intro j hj
    have zz : ∀ i, i = 1 ∨ i = 3 ∨ i = 5 ∨ i = 7 ∨ i = 9 → num s.mem P.B P.w i = 0 := fun i hi => by
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact z _ (by decide) (by decide) (by decide) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl
    all_goals refine (numW_of (h.full _ (by decide)) (zz _ (by decide))).trans ?_
    all_goals simp [Aload, AW1, upd, aN, wE, wD, wZ, wM, wMod]

end VG.Proof.Rsa.Arm.Recover
