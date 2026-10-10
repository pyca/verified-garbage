import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
import VerifiedGarbage.Proof.Divstep.Early

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass

/-- Finishing at any batch count whose remainder is already zero. The scale depends
on the actual batch count, including when the input itself is zero. -/
theorem finish_early_ok {P : InvCfg} {base : Addr} {size m X : Nat} [NeZero m]
    (hpr : m.Prime) (hT : InvToM m) (hL : InvLay P size)
    (hm2 : 2 < m) (hR : UnitMod m (2 ^ (64 * P.M.n))) {s : State}
    (hs : Scr s base size) (hM : ModOkA P.M size m s.mem base)
    (hX : X < m)
    (hI : IInv P base (Divstep.invRun 59 m P.M.minv.toNat X P.B) s)
    (hz : (Divstep.invRun 59 m P.M.minv.toNat X P.B).g = 0)
    (hCeq : P.C = 2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3 % m)
    (hCpos : 0 < P.C) (hCneq : P.Cn = m-P.C) :
    WP isa (.block P.finish) s fun t =>
      KeepRegs (powClob P.M.n) s t ∧ Unch base (invW P) s.mem t.mem ∧
      wordsVal t.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal t.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) X ^ (m-2) := by
  have hm2' : m % 2 = 1 := by
    rcases Nat.even_or_odd m with ⟨k,hk⟩ | ⟨k,hk⟩
    · have := hpr.eq_one_or_self_of_dvd 2 ⟨k, by omega_arith⟩
      omega_arith
    · omega_arith
  have hCm : P.C < m := by rw [hCeq]; exact Nat.mod_lt _ (by omega_arith)
  have hCnm : P.Cn < m := by rw [hCneq]; omega_arith
  refine WP.mono (finish_ok hL hs hM hI hCm hCnm) fun t ⟨Cs,hf1,hfm1,lt,ev,K,U⟩ =>
    ⟨K,U,lt,?_⟩
  let I := Divstep.invRun 59 m P.M.minv.toNat X P.B
  have hmi : ((m : Int) * (P.M.minv.toNat : Int) + 1) % 2 ^ 64 = 0 := by exact_mod_cast hM.inv
  have ha : (wordsVal s.mem base P.sA P.M.n : Int) = I.a := hI.a
  have spec : X ≠ 0 → (I.f = 1 ∨ I.f = -1) ∧ (X : Int) * (I.f * I.a) * 2 ^ ((64 - 59) * P.B) ≡ 1 [ZMOD m] :=
    fun hX0 => Divstep.invRun_spec (N := 59) (B := P.B) (by decide) (by exact_mod_cast hm2') (by exact_mod_cast hpr.one_lt) hmi
      (Divstep.invRun_done_of_g_zero (by exact_mod_cast hm2') hz) (by
        rw [Int.gcd_natCast_natCast]
        rcases hpr.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_left m X) with h | h
        · exact h
        · have hd := Nat.gcd_dvd_right m X
          rw [h] at hd
          have := Nat.le_of_dvd (by omega_arith) hd
          omega_arith)
  refine hT (K := 2 ^ (5 * P.B)) (f := I.f) (a := wordsVal s.mem base P.sA P.M.n) (Cs := Cs) hm2 hR hX
    ?_ ?_ ?_ ev
  · intro hX0
    have h := (Divstep.invRun_zero (N := 59) (p := m) (m := P.M.minv.toNat) (by omega_arith) P.B).2
    have hIa : I.a = 0 := by dsimp only [I]; rw [hX0, Nat.cast_zero]; exact h
    have : (wordsVal s.mem base P.sA P.M.n : Int) = 0 := by rw [ha, hIa]
    exact_mod_cast this
  · intro hX0
    have h := (spec hX0).2
    rw [ha, show (64 - 59) * P.B = 5 * P.B by omega_arith] at *
    push_cast
    exact h
  · intro hX0
    rcases (spec hX0).1 with h | h
    · rw [hf1 h, hCeq, h]; push_cast; rw [Int.emod_emod_of_dvd _ (dvd_refl _)]; ring_nf
    · rw [hfm1 h, hCneq, h, Nat.cast_sub hCm.le]
      have hc : (P.C : Int) ≡ ((2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3 : Nat) : Int) [ZMOD m] := by
        rw [hCeq]; push_cast; exact Int.emod_emod_of_dvd _ (dvd_refl _)
      have hm0 : (m : Int) ≡ 0 [ZMOD m] := Int.emod_self.trans (Int.zero_emod _).symm
      have := hm0.sub hc
      push_cast at this ⊢
      rw [show (-1 : Int) * (2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3) =
        0 - 2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3 by ring]
      exact this

/-- A zero word representation cannot hide a nonzero signed remainder in range. -/
theorem IInv.g_zero_of_words {P : InvCfg} {base : Addr} {I : Divstep.IState} {s : State}
    (hI : IInv P base I s) (hg : |I.g| < (2 ^ (64 * P.L) : Nat))
    (hz : wordsVal s.mem base P.sG P.L=0) : I.g=0 := by
  have h := hI.g
  rw [hz, Nat.cast_zero, Int.zero_emod] at h
  have hd := Int.dvd_of_emod_eq_zero h.symm
  obtain ⟨k,hk⟩ := hd
  have hpos : (0 : Int) < (2 ^ (64 * P.L) : Nat) := by positivity
  rw [abs_lt] at hg
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · have : k≤-1 := by omega_arith
    nlinarith
  · simp only [hk0,mul_zero] at hk
    exact hk
  · have : 1≤k := by omega_arith
    nlinarith

end VG.Proof.Weierstrass.AArch64
