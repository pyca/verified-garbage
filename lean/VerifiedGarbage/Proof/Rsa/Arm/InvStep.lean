module

public import VerifiedGarbage.Proof.Rsa.Arm.InvU
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `inverse` on ARMv7: one step is `invStep` -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm
open VG.Proof.Rsa (subMod halfMod)

/-- The bank at `j`: `(u, v, x₁, x₂)`. -/
def bank (m : Mem) (B : BitVec 32) (w j : Nat) : Nat × Nat × Nat × Nat :=
  (num m B w j, num m B w (j + 1), num m B w (j + 2), num m B w (j + 3))

/-- The selections of `x₁` and `x₂`. -/
def invX (A D : Nat) : List (Prog isa) :=
  [sel (D + 3) (A + 3) (A + 2) sC, sel aT1 aT3 aT2 sC, sel aT3 (A + 2) aT1 sOdd]

theorem invStep_eq (A D : Nat) : VG.Impl.Rsa.Arm.Keys.invStep A D =
    seqs (invU A D ++ (subModP aT3 (A + 2) (A + 3) ++ (subModP aT2 (A + 3) (A + 2) ++
      (invX A D ++ halfModP (D + 2))))) := rfl

theorem invStep_arith {u v x₁ x₂ M : Nat} :
    (if u % 2 = 1 then (if u < v then (v - u) / 2 else (u - v) / 2) else u / 2,
     (if u % 2 = 1 ∧ u < v then u else v),
     halfMod M (if (u % 2) = 0 then x₁ else
       if (if u % 2 = 1 ∧ u < v then 1 else 0) = 0 then subMod M x₁ x₂ else subMod M x₂ x₁),
     (if (if u % 2 = 1 ∧ u < v then 1 else 0) = 0 then x₂ else x₁)) =
    VG.Proof.Rsa.invStep M (u, v, x₁, x₂) := by
  unfold VG.Proof.Rsa.invStep
  by_cases e : u % 2 = 1 <;> by_cases f : u < v <;>
  simp [e, f, show u % 2 = 0 ↔ ¬ u % 2 = 1 by omega]

theorem invStep_ok {s : State} {B : BitVec 32} {Z w N A D : Nat} (h : Ws s B Z w N)
    (hN15 : 15 ≤ N) (hN : N ≤ 256) (hb : (A = 0 ∧ D = 4) ∨ (A = 4 ∧ D = 0)) :
    WP isa (VG.Impl.Rsa.Arm.Keys.invStep A D) s fun t => Ws t B Z w N ∧
      Keep B w [D, D + 1, D + 2, D + 3, aT1, aT2, aT3, aT4] [sOdd, sB, sC] s.mem t.mem ∧
      (num s.mem B w aNM + num s.mem B w aM = 2 ^ (32 * w) → num s.mem B w aZero = 0 →
        num s.mem B w (A + 2) < num s.mem B w aM → num s.mem B w (A + 3) < num s.mem B w aM →
        bank t.mem B w D = VG.Proof.Rsa.invStep (num s.mem B w aM) (bank s.mem B w A)) ∧
      Rest opRegs s t := by
  have hsOdd : sOdd + 4 ≤ hdr := by decide
  have hsC : sC + 4 ≤ hdr := by decide
  have fA2 := h.fit64 (j := A + 2) (by idx)
  have fA3 := h.fit64 (j := A + 3) (by idx)
  have fM := h.fit64 (j := aM) (by idx)
  have fNM := h.fit64 (j := aNM) (by idx)
  have fZ := h.fit64 (j := aZero) (by idx)
  have fT1 := h.fit64 (j := aT1) (by idx)
  have fT2 := h.fit64 (j := aT2) (by idx)
  have fT3 := h.fit64 (j := aT3) (by idx)
  have fD := h.fit64 (j := D) (by idx)
  have fD1 := h.fit64 (j := D + 1) (by idx)
  have fD3 := h.fit64 (j := D + 3) (by idx)
  rw [invStep_eq, wp_seqs_append (by unfold invU; exact List.cons_ne_nil _ _) (by unfold subModP; exact List.cons_ne_nil _ _)]
  refine WP.mono (invU_ok h hN15 hN hb) fun t1 ⟨h1, k1, o1, c1, v1, u1, r1⟩ => ?_
  rw [wp_seqs_append (by unfold subModP; exact List.cons_ne_nil _ _) (by unfold subModP; exact List.cons_ne_nil _ _)]
  refine WP.mono (subModP_ok h1 hN15 hN (by idx) (by idx) (by idx) (by idx) (by idx) (by idx) (by idx))
    fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  rw [wp_seqs_append (by unfold subModP; exact List.cons_ne_nil _ _) (by unfold invX; exact List.cons_ne_nil _ _)]
  refine WP.mono (subModP_ok h2 hN15 hN (by idx) (by idx) (by idx) (by idx) (by idx) (by idx) (by idx))
    fun t3 ⟨h3, k3, e3, r3⟩ => ?_
  rw [wp_seqs_append (by unfold invX; exact List.cons_ne_nil _ _) (by unfold halfModP; exact List.cons_ne_nil _ _)]
  unfold invX
  have cs3 : slot t3.mem B sC = slot t1.mem B sC := by
    rw [k3.slot hsC (by decide), k2.slot hsC (by decide)]
  have cb3 : slot t3.mem B sC ≤ 1 := by rw [cs3, c1]; split <;> omega
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h3 (by idx) (by idx) (by idx) hN (by idx) (by idx) hsC cb3) fun t4 ⟨h4, k4, e4, r4⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h4 (by idx) (by idx) (by idx) hN (by idx) (by idx) hsC
    (by rw [k4.slot hsC (by simp)]; exact cb3)) fun t5 ⟨h5, k5, e5, r5⟩ => ?_
  have od5 : slot t5.mem B sOdd = slot t1.mem B sOdd := by
    rw [k5.slot hsOdd (by simp), k4.slot hsOdd (by simp), k3.slot hsOdd (by decide), k2.slot hsOdd (by decide)]
  refine WP.mono (sel_ok h5 (by idx) (by idx) (by idx) hN (by idx) (by idx) hsOdd
    (by rw [od5, o1]; omega)) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  refine WP.mono (halfModP_ok h6 hN15 hN (by idx) (by idx) (by idx)) fun t ⟨h7, k7, e7, r7⟩ => ?_
  refine ⟨h7, k1.mono.trans (k2.mono.trans (k3.mono.trans (k4.mono.trans (k5.mono.trans (k6.mono.trans
    k7.mono))))), fun hNM hZ l2 l3 => ?_, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans r7)))))⟩
  -- What each step left that the others keep.
  have m1 : num t1.mem B w aM = num s.mem B w aM := k1.num (by idx) (by idx) fM
  have nm1 : num t1.mem B w aNM = num s.mem B w aNM := k1.num (by idx) (by idx) fNM
  have z1 : num t1.mem B w aZero = num s.mem B w aZero := k1.num (by idx) (by idx) fZ
  have x1 : num t1.mem B w (A + 2) = num s.mem B w (A + 2) := k1.num (by idx) (by idx) fA2
  have x2 : num t1.mem B w (A + 3) = num s.mem B w (A + 3) := k1.num (by idx) (by idx) fA3
  have m2 : num t2.mem B w aM = num s.mem B w aM := by rw [k2.num (by idx) (by idx) fM, m1]
  have nm2 : num t2.mem B w aNM = num s.mem B w aNM := by rw [k2.num (by idx) (by idx) fNM, nm1]
  have z2 : num t2.mem B w aZero = num s.mem B w aZero := by rw [k2.num (by idx) (by idx) fZ, z1]
  have x12 : num t2.mem B w (A + 2) = num s.mem B w (A + 2) := by rw [k2.num (by idx) (by idx) fA2, x1]
  have x22 : num t2.mem B w (A + 3) = num s.mem B w (A + 3) := by rw [k2.num (by idx) (by idx) fA3, x2]
  have E1 := e2 (by rw [nm1, m1]; exact hNM) (by rw [z1]; exact hZ) (by rw [x1, m1]; exact l2) (by rw [x2, m1]; exact l3)
  have E2 := e3 (by rw [nm2, m2]; exact hNM) (by rw [z2]; exact hZ) (by rw [x22, m2]; exact l3)
    (by rw [x12, m2]; exact l2)
  rw [m1, x1, x2] at E1
  rw [m2, x12, x22] at E2
  -- The state at `t6`, and the halving.
  have m6 : num t6.mem B w aM = num s.mem B w aM := by
    rw [k6.num (by idx) (by idx) fM, k5.num (by idx) (by idx) fM, k4.num (by idx) (by idx) fM,
      k3.num (by idx) (by idx) fM, m2]
  have nm6 : num t6.mem B w aNM = num s.mem B w aNM := by
    rw [k6.num (by idx) (by idx) fNM, k5.num (by idx) (by idx) fNM, k4.num (by idx) (by idx) fNM,
      k3.num (by idx) (by idx) fNM, nm2]
  have z6 : num t6.mem B w aZero = num s.mem B w aZero := by
    rw [k6.num (by idx) (by idx) fZ, k5.num (by idx) (by idx) fZ, k4.num (by idx) (by idx) fZ,
      k3.num (by idx) (by idx) fZ, z2]
  have H := e7 (by rw [nm6, m6]; exact hNM) (by rw [z6]; exact hZ)
  rw [m6, e6, od5, o1, k5.num (by idx) (by idx) fA2, k4.num (by idx) (by idx) fA2, k3.num (by idx) (by idx) fA2,
    x12, e5, k4.slot hsC (by simp), cs3, c1, k4.num (by idx) (by idx) fT3, k4.num (by idx) (by idx) fT2,
    k3.num (by idx) (by idx) fT3, E1, E2] at H
  have U : num t.mem B w D = num t1.mem B w D := by
    rw [k7.num (by idx) (by idx) fD, k6.num (by idx) (by idx) fD, k5.num (by idx) (by idx) fD,
      k4.num (by idx) (by idx) fD, k3.num (by idx) (by idx) fD, k2.num (by idx) (by idx) fD]
  have V : num t.mem B w (D + 1) = num t1.mem B w (D + 1) := by
    rw [k7.num (by idx) (by idx) fD1, k6.num (by idx) (by idx) fD1, k5.num (by idx) (by idx) fD1,
      k4.num (by idx) (by idx) fD1, k3.num (by idx) (by idx) fD1, k2.num (by idx) (by idx) fD1]
  have X2 : num t.mem B w (D + 3) = num t4.mem B w (D + 3) := by
    rw [k7.num (by idx) (by idx) fD3, k6.num (by idx) (by idx) fD3, k5.num (by idx) (by idx) fD3]
  rw [e4, cs3, c1, k3.num (by idx) (by idx) fA3, k3.num (by idx) (by idx) fA2, x12, x22] at X2
  rw [bank, bank, U, V, X2, u1, v1, show D + 2 = D + 2 from rfl, H]
  exact invStep_arith

end VG.Proof.Rsa.Arm.Keys
