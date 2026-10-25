module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCandSet
import VerifiedGarbage.Proof.Rsa.PPC64LE.MulMod
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Rsa.RecoverFusedMont
import VerifiedGarbage.Proof.Rsa.RecoverExp
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_rsa_recover_primes` on PPC64LE: `x g`

`multiply_ok`: the square `x` (in Montgomery form) times the candidate `g =
j + 2`: twice `x`, then `x` added once more for `g = 3`, by `addMod`; a
Montgomery product with `g R mod n` for the others.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (multiply mmul mBase mG mXm mX aN aZ aW nArr iXm iX iG)
open VG.Impl.Rsa.PPC64LE.Keys (seqs addMod sC)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The arrays `multiply` writes. -/
abbrev mulJ : List Nat := [22, 23, 26, 37, 38, 39]

theorem two_n_le {s0 : State} : 2 * nV s0 ≤ 2 ^ (32 * ww (kK s0)) := by
  have := nV_lt (s0 := s0)
  have e : 2 ^ (32 * ww (kK s0)) = 2 ^ (32 * (2 * wm (kK s0))) * 2 ^ 64 := by
    have hww : ww (kK s0) = 2 * wm (kK s0) + 2 := rfl
    rw [← Nat.pow_add, show 32 * ww (kK s0) = 32 * (2 * wm (kK s0)) + 64 by omega]
  rw [e]
  have : 2 ≤ 2 ^ 64 := by decide
  calc 2 * nV s0 ≤ 2 ^ 64 * nV s0 := Nat.mul_le_mul_right _ this
    _ ≤ 2 ^ (32 * (2 * wm (kK s0))) * 2 ^ 64 := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega)

/-- `[mXm] := x g`. -/
theorem multiply_ok {s0 u : State} (hn : NOk s0) (c : CF s0 u) {j x : Nat} (h24 : u.gpr .r24 = BitVec.ofNat 64 j)
    (hj : j < 100) (hX : num u.mem (rvB s0) (ww (kK s0)) mX = x * RR s0 % nV s0)
    (hG : num u.mem (rvB s0) (ww (kK s0)) mG = (j + 2) * RR s0 % nV s0) :
    WP isa multiply u fun t => CF s0 t ∧ KeyWorkspace.Keep (rvB s0) (ww (kK s0)) mulJ [sC] u.mem t.mem ∧
      num t.mem (rvB s0) (ww (kK s0)) mXm = x * (j + 2) % nV s0 * RR s0 % nV s0 ∧ Keep mmRegs u t := by
  have hn0 : 0 < nV s0 := by have := hn.big; omega
  have fit : ∀ j < nArr, arr (ww (kK s0)) j + S (ww (kK s0)) ≤ 2 ^ 64 := fun _ hj => c.ws.fit64 hj
  have z0 : num u.mem (rvB s0) (ww (kK s0)) aZ = 0 := val32_zeros fun i hi => c.zZ i (by omega)
  have Xl : num u.mem (rvB s0) (ww (kK s0)) mX < nV s0 := by rw [hX]; exact Nat.mod_lt _ hn0
  have tn := two_n_le (s0 := s0)
  unfold multiply
  refine WP.ite (decide (j = 0)) (eval_zero_ofNat u .r24 (by omega) h24) (fun h0 => ?_) (fun h0 => ?_)
  · -- `g = 2`.
    have j0 : j = 0 := of_decide_eq_true h0
    refine WP.mono (addMod_ok c.ws (o := mXm) (a := mX) (b := mX) (m := aN) (z := aZ) (t := aW) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      fun t ⟨ws1, kk1, k1, v1⟩ => ⟨c.of_keep kk1 (by decide) (by decide) k1 ws1,
        kk1.mono (by decide) (by decide), ?_, k1.mono (by decide)⟩
    rw [v1 z0 (by rw [c.vN]; exact Xl) (by rw [c.vN]; exact Xl) (by rw [c.vN]; exact tn), c.vN, hX, j0,
      ← Nat.mul_two, FusedMont.scale]
  · have j0 : j ≠ 0 := fun e => by rw [e] at h0; exact absurd h0 (by decide)
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r0] (Q := fun x => x.gpr .r0 = BitVec.ofNat 64 (j - 1) ∧ x.mem = u.mem) ?_
      (by decide)) fun u1 ⟨⟨a0, m1⟩, k0⟩ => ?_
    · prun [h24]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    have c1 := c.of_keep (show KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [] [] u.mem u1.mem by
      rw [m1]; exact KeyWorkspace.Keep.refl _ _ _ _ _) (by simp) (by simp) k0 (c.ws.of_keep k0)
    have X1 : num u1.mem (rvB s0) (ww (kK s0)) mX = x * RR s0 % nV s0 := by rw [m1]; exact hX
    have G1 : num u1.mem (rvB s0) (ww (kK s0)) mG = (j + 2) * RR s0 % nV s0 := by rw [m1]; exact hG
    have z1 : num u1.mem (rvB s0) (ww (kK s0)) aZ = 0 := by rw [m1]; exact z0
    have Xl1 : num u1.mem (rvB s0) (ww (kK s0)) mX < nV s0 := by rw [X1]; exact Nat.mod_lt _ hn0
    refine WP.ite (decide (j - 1 = 0)) (eval_zero_ofNat u1 .r0 (by omega) a0) (fun h1 => ?_) (fun h1 => ?_)
    · -- `g = 3`.
      have j1 : j = 1 := by have := of_decide_eq_true h1; omega
      rw [wp_seqs_append (by simp [addMod]) (by simp [addMod])]
      refine WP.mono (addMod_ok c1.ws (o := mXm) (a := mX) (b := mX) (m := aN) (z := aZ) (t := aW) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        fun u2 ⟨ws2, kk2, k2, v2⟩ => ?_
      have c2 := c1.of_keep kk2 (by decide) (by decide) k2 ws2
      have N1 := c1.vN
      have X2 : num u2.mem (rvB s0) (ww (kK s0)) mX = x * RR s0 % nV s0 := by
        rw [kk2.num (by decide) (by decide) (fit mX (by decide))]; exact X1
      have V2 := v2 z1 (by rw [N1]; exact Xl1) (by rw [N1]; exact Xl1) (by rw [N1]; exact tn)
      rw [N1, X1] at V2
      refine WP.mono (addMod_ok ws2 (o := mXm) (a := mXm) (b := mX) (m := aN) (z := aZ) (t := aW) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        fun t ⟨ws3, kk3, k3, v3⟩ => ⟨c2.of_keep kk3 (by decide) (by decide) k3 ws3,
          by rw [m1] at kk2; exact KeyWorkspace.Keep.trans (kk2.mono (js' := mulJ) (ds' := [sC]) (by decide)
            (by decide)) (kk3.mono (by decide) (by decide)), ?_,
          ((k0.mono (rs' := mmRegs) (by decide)).trans ((k2.trans k3).mono (rs' := mmRegs) (by decide))).mono
            (by decide)⟩
      have z2 : num u2.mem (rvB s0) (ww (kK s0)) aZ = 0 := val32_zeros fun i hi => c2.zZ i (by omega)
      rw [v3 z2 (by rw [c2.vN, V2]; exact Nat.mod_lt _ hn0) (by rw [c2.vN, X2]; exact Nat.mod_lt _ hn0)
        (by rw [c2.vN]; exact tn), c2.vN, V2, X2, j1, Nat.mod_add_mod, ← Nat.mul_two, ← Nat.mul_add_one,
        FusedMont.scale]
    · -- The others: a Montgomery product.
      have Gl : num u1.mem (rvB s0) (ww (kK s0)) mG < nV s0 := by rw [G1]; exact Nat.mod_lt _ hn0
      refine WP.mono (mmul_ok c1.base c1.ws (o := iXm) (a := iX) (b := iG) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) c1.r12 c1.inv
        (by rw [c1.vMN]; change lowV u1.mem s0 mG < _; rw [low_of_lt Gl]; exact Gl))
        fun t ⟨_, ws2, kk2, lt2, eq2, k2⟩ => ⟨c1.of_keep kk2 (by decide) (by simp) k2 ws2,
          (show KeyWorkspace.Keep (rvB s0) (ww (kK s0)) mulJ [sC] u.mem t.mem by
            rw [m1] at kk2; exact kk2.mono (by decide) (by simp)), ?_,
          ((k0.mono (rs' := mmRegs) (by decide)).trans k2).mono (by decide)⟩
      change num t.mem (rvB s0) (ww (kK s0)) mXm < lowV u1.mem s0 mBase at lt2
      change num t.mem (rvB s0) (ww (kK s0)) mXm * RR s0 % lowV u1.mem s0 mBase =
        lowV u1.mem s0 mX * lowV u1.mem s0 mG % lowV u1.mem s0 mBase at eq2
      rw [c1.vMN, low_of_lt Xl1, low_of_lt Gl, X1, G1, ← mont_sq_eq] at eq2
      rw [c1.vMN] at lt2
      have := VG.Proof.Bignum.mont_cancel hn.coprime eq2
      rwa [Nat.mod_eq_of_lt lt2, Nat.mod_mod] at this

end VG.Proof.Rsa.PPC64LE.Recover
