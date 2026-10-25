module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFinY
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLoop
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Framework.Block

/-!
# `vg_rsa_recover_primes` on PPC64LE: `p = gcd(y - 1, n)`

`gcd_ok`: `gcdSet` and `inverse`: array 1 is `gcd(x, n)` for the `x` that
is `y - 1` when `y ≥ 1`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (gcdSet mY aN aOne aZ nArr)
open VG.Impl.Rsa.PPC64LE.Keys (seqs setOne aM aNM aZero inverse)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- `gcdSet` and `inverse`. -/
theorem gcd_ok {s0 u : State} (hn : NOk s0) (h : FF s0 u) (hy : num u.mem (rvB s0) (ww (kK s0)) mY = yV s0) :
    WP isa (.seq gcdSet inverse) u fun t => FF s0 t ∧
      ∃ x, num t.mem (rvB s0) (ww (kK s0)) 1 = Nat.gcd x (nV s0) ∧ (1 ≤ yV s0 → x = yV s0 - 1) := by
  have z := h.base.sz
  have w1 := z.w1
  have hn0 : 0 < nV s0 := by have := hn.big; omega_arith
  have hn1 : 1 < nV s0 := by have := hn.big; omega_arith
  have fit : ∀ j < nArr, arr (ww (kK s0)) j + S (ww (kK s0)) ≤ 2 ^ 64 := fun _ hj => h.ws.fit64 hj
  have nb : nV s0 < 2 ^ (32 * ww (kK s0)) :=
    Nat.lt_of_lt_of_le nV_lt (Nat.pow_le_pow_right (by decide) (by simp only [ww, wm]; omega_arith))
  have zA : ∀ {t : State}, FF s0 t → num t.mem (rvB s0) (ww (kK s0)) aZ = 0 := fun f =>
    val32_zeros fun i hi => f.zZ i (by omega_arith)
  rw [WP.seq_iff]
  unfold gcdSet
  -- 1: `y - 1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h.ws (o := 0) (a := mY) (b := aOne) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun u1 ⟨ws1, kk1, v1, b1, k1⟩ => ?_
  have f1 := h.of_keep kk1 (by decide) (by simp) k1 ws1
  rw [h.vOne, hy] at v1
  -- 2–7.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws1 (o := 1) (a := aN) (by decide) (by decide) (by decide) (by decide))
    fun u2 ⟨ws2, kk2, v2, k2, _⟩ => ?_
  have f2 := f1.of_keep kk2 (by decide) (by simp) k2 ws2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws2 (o := aM) (a := aN) (by decide) (by decide) (by decide) (by decide))
    fun u3 ⟨ws3, kk3, v3, k3, _⟩ => ?_
  have f3 := f2.of_keep kk3 (by decide) (by simp) k3 ws3
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws3 (o := 2) (a := aZ) (by decide) (by decide) (by decide) (by decide))
    fun u4 ⟨ws4, kk4, v4, k4, _⟩ => ?_
  have f4 := f3.of_keep kk4 (by decide) (by simp) k4 ws4
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil (setOne 2)]
  refine setOne_ok ws4 (j := 2) (by decide) (by decide) fun u5 ws5 kk5 v5 k5 => WP.block_nil ?_
  have f5 := f4.of_keep kk5 (by decide) (by simp) k5 ws5
  rw [v4, zA f3] at v5
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws5 (o := 3) (a := aZ) (by decide) (by decide) (by decide) (by decide))
    fun u6 ⟨ws6, kk6, v6, k6, _⟩ => ?_
  have f6 := f5.of_keep kk6 (by decide) (by simp) k6 ws6
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws6 (o := aZero) (a := aZ) (by decide) (by decide) (by decide) (by decide))
    fun u7 ⟨ws7, kk7, v7, k7, _⟩ => ?_
  have f7 := f6.of_keep kk7 (by decide) (by simp) k7 ws7
  -- 8: `2^(32 w) - n`.
  rw [show seqs [VG.Impl.Rsa.PPC64LE.Keys.sub3 aNM aZero aM] = VG.Impl.Rsa.PPC64LE.Keys.sub3 aNM aZero aM from rfl]
  refine WP.mono (sub3_ok ws7 (o := aNM) (a := aZero) (b := aM) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun u8 ⟨ws8, kk8, v8, b8, k8⟩ => ?_
  have f8 := f7.of_keep kk8 (by decide) (by simp) k8 ws8
  -- The values at `u8`.
  have N : ∀ {a b : State} {js : List Nat} (kk : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) js [] a.mem b.mem) (j : Nat),
      j < nArr → (∀ k ∈ js, k ≠ j) → num b.mem (rvB s0) (ww (kK s0)) j = num a.mem (rvB s0) (ww (kK s0)) j :=
    fun kk j hj hk => kk.num hk (by simp) (fit j hj)
  have aM7 : num u7.mem (rvB s0) (ww (kK s0)) aM = nV s0 := by
    rw [N kk7 aM (by decide) (by decide), N kk6 aM (by decide) (by decide), N kk5 aM (by decide) (by decide),
      N kk4 aM (by decide) (by decide), v3]; exact f2.vN
  have z7 : num u7.mem (rvB s0) (ww (kK s0)) aZero = 0 := by rw [v7]; exact zA f6
  rw [z7, aM7] at v8
  have lt8 := val32_lt u8.mem (rvB s0) (arr (ww (kK s0)) aNM) (ww (kK s0))
  change num u8.mem (rvB s0) (ww (kK s0)) aNM < _ at lt8
  have nm8 : num u8.mem (rvB s0) (ww (kK s0)) aNM + num u8.mem (rvB s0) (ww (kK s0)) aM = 2 ^ (32 * ww (kK s0)) := by
    rw [N kk8 aM (by decide) (by decide), aM7]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b8 with e | e <;> rw [e] at v8 <;> omega_arith
  have bank8 : bank u8.mem (rvB s0) (ww (kK s0)) 0 =
      (num u8.mem (rvB s0) (ww (kK s0)) 0, num u8.mem (rvB s0) (ww (kK s0)) aM, 1, 0) := by
    have e1 : num u8.mem (rvB s0) (ww (kK s0)) 1 = nV s0 := by
      rw [N kk8 1 (by decide) (by decide), N kk7 1 (by decide) (by decide), N kk6 1 (by decide) (by decide),
        N kk5 1 (by decide) (by decide), N kk4 1 (by decide) (by decide), N kk3 1 (by decide) (by decide), v2]
      exact f1.vN
    have e2 : num u8.mem (rvB s0) (ww (kK s0)) 2 = 1 := by
      rw [N kk8 2 (by decide) (by decide), N kk7 2 (by decide) (by decide), N kk6 2 (by decide) (by decide), v5]
    have e3 : num u8.mem (rvB s0) (ww (kK s0)) 3 = 0 := by
      rw [N kk8 3 (by decide) (by decide), N kk7 3 (by decide) (by decide), v6]; exact zA f5
    simp only [bank, e1, e2, e3, N kk8 aM (by decide) (by decide), aM7]
  have x8 : num u8.mem (rvB s0) (ww (kK s0)) 0 = num u1.mem (rvB s0) (ww (kK s0)) 0 := by
    rw [N kk8 0 (by decide) (by decide), N kk7 0 (by decide) (by decide), N kk6 0 (by decide) (by decide),
      N kk5 0 (by decide) (by decide), N kk4 0 (by decide) (by decide), N kk3 0 (by decide) (by decide),
      N kk2 0 (by decide) (by decide)]
  -- `inverse`.
  refine WP.mono (inverse_ok ws8 (by decide) (by decide)) fun t ⟨wst, kkt, kt, vt⟩ => ?_
  have ft := f8.of_keep kkt (by decide) (by decide) kt wst
  have aM8 : num u8.mem (rvB s0) (ww (kK s0)) aM = nV s0 := by rw [N kk8 aM (by decide) (by decide), aM7]
  obtain ⟨g, -, -⟩ := vt nm8 (by rw [N kk8 aZero (by decide) (by decide), z7]) (by rw [aM8]; exact hn.odd)
    (by rw [aM8]; exact hn1) bank8
  refine ⟨ft, num u1.mem (rvB s0) (ww (kK s0)) 0, by rw [g, x8, aM8], fun hy1 => ?_⟩
  have lt1 := val32_lt u1.mem (rvB s0) (arr (ww (kK s0)) 0) (ww (kK s0))
  change num u1.mem (rvB s0) (ww (kK s0)) 0 < _ at lt1
  have yl := yV_lt hn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b1 with e | e <;> rw [e] at v1 <;> omega_arith

end VG.Proof.Rsa.PPC64LE.Recover
