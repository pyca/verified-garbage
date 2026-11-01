module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbOps
public import VerifiedGarbage.Proof.Divstep.Alg32Def
public import Mathlib.Algebra.Order.Ring.Abs
import VerifiedGarbage.Proof.Divstep.Mred32
import VerifiedGarbage.Proof.Divstep.Tc32Red
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The batched inverse on PPC64LE: the reduction

`mred_ok`: `mred t o` leaves in array `o` the number
`Proof/Divstep/Alg32Def.lean`'s `mred p iv T` of the signed `T` in array
`t`, for the odd `p < 2^(32 n)` in array 2 and `iv = -p⁻¹ mod 2^32` in the
window: `k = T iv mod 2^32` from `T`'s low digit, `T + k p` (`mac`), its top
digit fixed by the carry, which leaves `2^32 R`, `R = mredRaw p iv T`, then
`R + p` (in `(0, 3p)`) and two conditional subtractions.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop seqs)
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S num slot arr_disj)

/-- The arithmetic of the reduction: from the words the code leaves (see
the module doc), `R + p`, and the low digit zero. -/
theorem mred_arith {T V0 V2 V' X3 P A : Int} {p iv k C C2 d0 j0 j2 : Int} {D3 : Int}
    (hA : A = 2 ^ 32 * P) (hpP : p < P) (hp0 : 0 < p) (hm : (p * iv + 1) % 2 ^ 32 = 0)
    (hk : k = (T * iv) % 2 ^ 32) (hT : T = V0 + A * d0) (hmac : V2 + A * C = V0 + k * p)
    (hD3 : D3 - d0 - C = 2 ^ 32 * j0) (hlow : V2 + A * D3 = j2 + 2 ^ 32 * V')
    (hj2 : 0 ≤ j2) (hj2' : j2 < 2 ^ 32) (hR : X3 + A * C2 = V' + p) (hX0 : 0 ≤ X3) (hX1 : X3 < A)
    (hTr : |T| ≤ 2 ^ 31 * p) :
    X3 = Divstep.W32.mredRaw p iv T + p := by
  have spec := Divstep.W32.mredRaw_spec (t := T) hm
  have rng := Divstep.W32.mredRaw_range (t := T) hp0 hm hTr
  rw [← hk] at spec
  generalize Divstep.W32.mredRaw p iv T = R at spec rng ⊢
  -- `V2 + A D3 = 2^32 (R + A j0)`.
  have e1 : V2 + A * D3 = 2 ^ 32 * (R + A * j0) := by
    have : D3 = d0 + C + 2 ^ 32 * j0 := by omega
    rw [this]
    grind
  have hP0 : 0 < P := by omega
  have hA0 : 0 < A := by rw [hA]; omega
  -- The low digit is zero, so `V' = R + A j0`.
  have e2 : j2 = 2 ^ 32 * (R + A * j0 - V') := by grind
  have z := mul_small (H := 2 ^ 32) (d := R + A * j0 - V') (by decide) (by omega) (by omega)
  have e3 : V' = R + A * j0 := by omega
  -- `X3 = R + p + A (j0 - C2)` within `[0, A)`.
  have e4 : A * (j0 - C2) = X3 - (R + p) := by grind
  have bnd : 3 * p < A := by
    rw [hA]
    have : (3 : Int) * P ≤ 2 ^ 32 * P := Int.mul_le_mul_of_nonneg_right (by decide) (by omega)
    omega
  have := mul_small (H := A) (d := j0 - C2) hA0 (by omega) (by omega)
  rw [this, Int.mul_zero] at e4
  omega

/-- `norm p (R)` from `R + p` and two conditional subtractions. -/
theorem norm_twice {p R : Int} (X0 : Nat) (hX0 : (X0 : Int) = R + p) (P : Nat)
    (hP : (P : Int) = p) :
    ((if P ≤ (if P ≤ X0 then X0 - P else X0) then (if P ≤ X0 then X0 - P else X0) - P
      else (if P ≤ X0 then X0 - P else X0) : Nat) : Int) = Divstep.W32.norm p R := by
  unfold Divstep.W32.norm
  split_ifs <;> omega

/-- `mred t o`: `[o] = mred p iv T` for `T` the signed number of `n + 2`
digits in `[t]`. -/
theorem mred_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) {t o : Nat}
    (ht : t < N) (ho : o < N) (hN : N ≤ 256) (h3 : aT3 < N) (hm : aMz < N) (htm : t ≠ aMz)
    (ht3 : t ≠ aT3) (h3m : aT3 ≠ aMz) (ho3 : o ≠ aT3) (hot : o ≠ t) {p iv : Nat} {T : Int}
    (hp : val32 s.mem B (arr w aMz) (n + 1) = p) (hpA : p < 2 ^ (32 * n)) (hp0 : 0 < p)
    (hiv : (s.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv) (hinv : (p * iv + 1) % 2 ^ 32 = 0)
    (hT : sv s.mem B (arr w t) (n + 1) = T) (hTr : |T| ≤ 2 ^ 31 * p) :
    WP isa (mred t o) s fun u => Ctx u B Z w N n c ∧ KeyWorkspace.Keep B w [o, t, aT3] [] s.mem u.mem ∧
      (val32 u.mem B (arr w o) (n + 1) : Int) = Divstep.W32.mred p iv T ∧ Keep kRegs s u := by
  have ft := h.ws.arr_fit ht
  have f3 := h.ws.arr_fit h3
  have fm := h.ws.arr_fit hm
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nw
  have := h.npos
  have := h.ws.wle
  have hnw := h.ws.nowrap
  rw [mred]; simp only [seqs]; rw [WP.seq_iff]
  -- 1: `k = T₀ iv mod 2^32` into `r11`.
  have hb1 : WP isa (.block (ptr .r5 t ++ ldW .r3 wIv ++
      ([.load .w .r0 .r5 0, .mul .r11 .r0 .r3, .lsr .w .r11 .r11 0] : List Instr))) s fun u =>
      Ctx u B Z w N n c ∧ u.mem = s.mem ∧ (u.gpr .r11).toNat = (w32 s.mem B (arr w t) * iv) % 2 ^ 32 ∧
      Keep kRegs s u := by
    rw [List.append_assoc]
    refine ptr_ok h.ws (by decide) (by decide) (by decide) (by omega) ?_
    refine ldW_ok (h.of_keep ((Keep.write _ .r5 _).mono (by decide))) (by decide) (by decide) (by decide)
      (by decide) (by decide) ?_
    refine WP.mono (WP.keep [.r0, .r11] (Q := fun u => (u.gpr .r11).toNat = (w32 s.mem B (arr w t) * iv) % 2 ^ 32 ∧
      u.mem = s.mem) ?_ (by decide)) fun u ⟨⟨u11, um⟩, ku⟩ => ?_
    · prun [mem_write, h.ws.scr.ld (show arr w t + 4 ≤ Z by omega)]
      rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_zero, BitVec.toNat_setWidth,
        BitVec.toNat_mul, toNat_ext32, hiv]
      generalize (s.mem.readW (off B (arr w t)) 32).toNat * iv = P
      omega
    have k0 : Keep kRegs s u := (((Keep.write _ .r5 _).trans (Keep.write _ .r3 _)).trans ku).mono (by decide)
    exact ⟨h.of_keep k0, um, u11, k0⟩
  refine WP.mono hb1 fun t1 ⟨h1, m1, k11, k1⟩ => ?_
  rw [WP.seq_iff]
  -- 2: `[t] += k m`.
  refine WP.mono (mac_ok h1 (fun u hu => cntN1_ok hu) (K := n + 1) (by omega) (by omega) ht ht hm hN
    (by rw [k11]; exact Nat.mod_lt _ (by decide))) fun t2 ⟨h2, kp2, mac2, c2, p5, _, out2, k2⟩ => ?_
  rw [WP.seq_iff]
  -- 3: the top digit plus the carry.
  have d0 : w32 t2.mem B (arr w t + 4 * (n + 1)) = w32 s.mem B (arr w t + 4 * (n + 1)) := by
    rw [out2.w32 (by omega) (by omega), m1]
  refine WP.mono (WP.keep [.r0] (Q := fun u => u.mem = t2.mem.writeW (off B (arr w t + 4 * (n + 1)))
      (((t2.mem.readW (off B (arr w t + 4 * (n + 1))) 32).setWidth 64 + t2.gpr .r9).setWidth 32)) ?_ (by decide))
    fun t3 ⟨m3, k3⟩ => ?_
  · prun [p5, h2.ws.scr.ld (show arr w t + 4 * (n + 1) + 4 ≤ Z by omega),
      h2.ws.scr.st (show arr w t + 4 * (n + 1) + 4 ≤ Z by omega)]
  have h3' := h2.of_keep (k3.mono (by decide))
  rw [WP.seq_iff]
  -- 4: `[aT3] = R + p`.
  have hb4 : WP isa (.block (ptr .r5 aT3 ++ ptr .r6 t ++ ptr .r7 aMz ++
      ([.addi .r6 .r6 4, .li .r11 1] : List Instr) ++ cntN1 ++ ([.li .r9 0] : List Instr))) t3 fun u =>
      Ctx u B Z w N n c ∧ u.mem = t3.mem ∧ u.gpr .r5 = off B (arr w aT3) ∧ u.gpr .r6 = off B (arr w t + 4) ∧
      u.gpr .r7 = off B (arr w aMz) ∧ u.gpr .r8 = BitVec.ofNat 64 (n + 1) ∧ u.gpr .r9 = 0 ∧
      u.gpr .r11 = 1#64 ∧ Keep kRegs t3 u := by
    rw [show ptr .r5 aT3 ++ ptr .r6 t ++ ptr .r7 aMz ++ ([.addi .r6 .r6 4, .li .r11 1] : List Instr) ++ cntN1 ++
      ([.li .r9 0] : List Instr) = ptr .r5 aT3 ++ ptr .r6 t ++ ptr .r7 aMz ++
        (([.addi .r6 .r6 4, .li .r11 1] : List Instr) ++ cntN1 ++ ([.li .r9 0] : List Instr)) by
          simp only [List.append_assoc]]
    refine ptr3_ok h3'.ws (by omega) (by omega) (by omega) fun u q5 q6 q7 ku mu => ?_
    have hu := h3'.of_keep (ku.mono (by decide))
    refine WP.mono (WP.keep [.r6, .r8, .r9, .r11] (Q := fun y => y.gpr .r6 = off B (arr w t + 4) ∧
      y.gpr .r8 = BitVec.ofNat 64 (n + 1) ∧ y.gpr .r9 = 0 ∧ y.gpr .r11 = 1#64 ∧ y.mem = u.mem) ?_ (by decide))
      fun y ⟨⟨y6, y8, y9, y11, ym⟩, ky⟩ => ?_
    · prun [cntN1, cntN, hu.cnt, ofNat_succ, q6]
      rfl
    have k0 : Keep kRegs t3 y := (ku.trans ky).mono (by decide)
    refine ⟨h3'.of_keep k0, ym.trans mu, ?_, y6, ?_, y8, y9, y11, k0⟩
    · rw [ky.gpr _ (by decide)]; exact q5
    · rw [ky.gpr _ (by decide)]; exact q7
  refine WP.mono hb4 fun t4 ⟨h4, m4, q5, q6, q7, q8, q9, q11, k4⟩ => ?_
  rw [WP.seq_iff]
  have dt3 := arr_disj (w := w) ht3
  have d3m := arr_disj (w := w) h3m
  refine WP.mono (macLoop_ok h4.ws.scr q5 q6 q7 q8 (by rw [q9]; decide) (by rw [q11]; decide) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by unfold VG.Proof.Rsa.PPC64LE.Loops.Ahead; omega)
    (by unfold VG.Proof.Rsa.PPC64LE.Loops.Ahead; omega)) fun t5 ⟨c5, mac5, _, out5, k5⟩ => ?_
  have h5 := h4.of_keep (k5.mono (by decide))
  -- The frame so far.
  have K3 : KeyWorkspace.Keep B w [t] [] t2.mem t3.mem := by
    rw [m3]
    exact KeyWorkspace.Keep.of_arr (d := 4 * (n + 1)) (writeW32_outside _ B _ (by omega)) (by omega) (by simp)
  have K5 : KeyWorkspace.Keep B w [t, aT3] [] s.mem t5.mem := by
    rw [← m1]
    exact (kp2.mono (by simp)).trans ((K3.mono (by simp)).trans (by
      rw [← m4]
      exact KeyWorkspace.Keep.of_arr (o := aT3) (d := 0) (by simpa only [Nat.add_zero] using out5) (by omega)
        (by simp)))
  have pm5 : val32 t5.mem B (arr w aMz) (n + 1) = p := by
    rw [keep_val K5 (by omega) (by simp; omega) (by simp) (by omega), hp]
  rw [WP.seq_iff]
  refine WP.mono (csub_ok h5 h3 h3 ht hm hN ht3 htm ht3.symm pm5 rfl) fun t6 ⟨h6, K6, v6, k6⟩ => ?_
  have pm6 : val32 t6.mem B (arr w aMz) (n + 1) = p := by
    rw [keep_val K6 (by omega) (by simp; omega) (by simp) (by omega), pm5]
  refine WP.mono (csub_ok h6 ho h3 ht hm hN ht3 htm hot pm6 v6) fun t7 ⟨h7, K7, v7, k7⟩ => ?_
  have k : Keep kRegs s t7 := ((((((k1.trans' k2).trans' (k3.mono (by decide))).trans' k4).trans'
    (k5.mono (by decide))).trans' k6).trans' k7)
  refine ⟨h.of_keep k, (K5.mono (by simp)).trans ((K6.mono (by simp)).trans (K7.mono (by simp))), ?_, k⟩
  rw [v7]
  -- The arithmetic.
  have pm3 : val32 t3.mem B (arr w aMz) (n + 1) = p := by
    have K := (show KeyWorkspace.Keep B w [t] [] s.mem t2.mem by rw [← m1]; exact kp2).trans K3
    rw [keep_val K (by omega) (by simp; omega) (by simp) (by omega), hp]
  have dd : t2.mem.readW (off B (arr w t + 4 * (n + 1))) 32 = s.mem.readW (off B (arr w t + 4 * (n + 1))) 32 := by
    rw [Outside.readW32 out2 (by omega) (by omega), m1]
  have v3 : val32 t3.mem B (arr w t) (n + 1 + 1) = val32 t2.mem B (arr w t) (n + 1) +
      2 ^ (32 * (n + 1)) * (((t2.mem.readW (off B (arr w t + 4 * (n + 1))) 32).setWidth 64 +
        t2.gpr .r9).setWidth 32).toNat := by
    rw [m3, val32_write_top _ _ _ _ _ (by omega)]
  have eD3 : (((t2.mem.readW (off B (arr w t + 4 * (n + 1))) 32).setWidth 64 + t2.gpr .r9).setWidth 32).toNat =
      ((s.mem.readW (off B (arr w t + 4 * (n + 1))) 32).toNat + (t2.gpr .r9).toNat) % 2 ^ 32 := by
    rw [dd, BitVec.toNat_setWidth, BitVec.toNat_add, toNat_ext32]
    have := (s.mem.readW (off B (arr w t + 4 * (n + 1))) 32).isLt
    omega
  have v3' : val32 t3.mem B (arr w t) (n + 1 + 1) =
      w32 t3.mem B (arr w t) + 2 ^ 32 * val32 t3.mem B (arr w t + 4) (n + 1) := rfl
  rw [m1, k11, hp] at mac2
  rw [m4, pm3, q11, q9, show (1#64 : BitVec 64).toNat = 1 from rfl, show (0 : BitVec 64).toNat = 0 from rfl,
    Nat.one_mul, Nat.add_zero] at mac5
  have hTs := hT
  unfold sv at hTs
  -- `k ≡ T iv`.
  have hk : (((w32 s.mem B (arr w t) * iv) % 2 ^ 32 : Nat) : Int) = (T * iv) % 2 ^ 32 := by
    have e0 : val32 s.mem B (arr w t) (n + 1) = w32 s.mem B (arr w t) + 2 ^ 32 * val32 s.mem B (arr w t + 4) n := rfl
    have hW := (s.mem.readW (off B (arr w t)) 32).isLt
    have eT : T = (w32 s.mem B (arr w t) : Int) + 2 ^ 32 * ((val32 s.mem B (arr w t + 4) n : Int) +
        2 ^ (32 * n) * (s.mem.readW (off B (arr w t + 4 * (n + 1))) 32).toInt) := by
      rw [← hTs, e0, show 32 * (n + 1) = 32 + 32 * n by omega, Int.pow_add]
      push_cast
      grind
    have hTmod : T % 2 ^ 32 = (w32 s.mem B (arr w t) : Int) := by
      rw [eT, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by omega) (by simp only [w32]; omega)
    rw [Int.natCast_emod, Int.natCast_mul, Int.mul_emod, Int.mul_emod T, hTmod]
    push_cast
    rw [Int.emod_eq_of_lt (a := (w32 s.mem B (arr w t) : Int)) (by omega) (by simp only [w32]; omega)]
  have hd0 := toInt_cond (s.mem.readW (off B (arr w t + 4 * (n + 1))) 32)
  have hdl := (s.mem.readW (off B (arr w t + 4 * (n + 1))) 32).isLt
  have X := mred_arith (T := T) (V0 := val32 s.mem B (arr w t) (n + 1)) (V2 := val32 t2.mem B (arr w t) (n + 1))
    (V' := val32 t3.mem B (arr w t + 4) (n + 1)) (X3 := val32 t5.mem B (arr w aT3) (n + 1))
    (P := 2 ^ (32 * n)) (A := 2 ^ (32 * (n + 1))) (p := p) (iv := iv)
    (k := (((w32 s.mem B (arr w t) * iv) % 2 ^ 32 : Nat) : Int)) (C := (t2.gpr .r9).toNat)
    (C2 := (t5.gpr .r9).toNat) (d0 := (s.mem.readW (off B (arr w t + 4 * (n + 1))) 32).toInt)
    (j0 := (if 2 ^ 31 ≤ (s.mem.readW (off B (arr w t + 4 * (n + 1))) 32).toNat then 1 else 0) -
      ((((s.mem.readW (off B (arr w t + 4 * (n + 1))) 32).toNat + (t2.gpr .r9).toNat) / 2 ^ 32 : Nat) : Int))
    (j2 := w32 t3.mem B (arr w t))
    (D3 := ((((s.mem.readW (off B (arr w t + 4 * (n + 1))) 32).toNat + (t2.gpr .r9).toNat) % 2 ^ 32 : Nat) : Int))
    (by rw [show 32 * (n + 1) = 32 + 32 * n by omega, Int.pow_add]) (by exact_mod_cast hpA)
    (by exact_mod_cast hp0) (by exact_mod_cast hinv) hk hTs.symm (by exact_mod_cast mac2)
    (by rw [hd0]; split <;> omega)
    (by rw [← eD3]; exact_mod_cast (v3.symm.trans v3'))
    (by omega) (by exact_mod_cast (t3.mem.readW (off B (arr w t)) 32).isLt) (by exact_mod_cast mac5) (by omega)
    (by exact_mod_cast val32_lt _ _ _ _) hTr
  exact norm_twice _ X _ rfl

end VG.Proof.Rsa.PPC64LE.InvBatch
