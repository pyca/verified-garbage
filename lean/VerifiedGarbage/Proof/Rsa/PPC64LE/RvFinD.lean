module

import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFinG
import VerifiedGarbage.Proof.Rsa.PPC64LE.DivLoop
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvTop
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFF

/-!
# `vg_rsa_recover_primes` on PPC64LE: `q = n / p`, and the order

`divOrder_ok`: `divide` and `order`: `max(p, q)` in array 5 and `min(p, q)`
in array 6.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (divide order clrW aN aQ aRm aDv aDt aW nArr sLt)
open VG.Impl.Rsa.PPC64LE.Keys (seqs stBorrow)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- `divide` and `order`, for `p` in array 1 dividing `n`. -/
theorem divOrder_ok {s0 u : State} (h : FF s0 u) {p : Nat}
    (hp : num u.mem (rvB s0) (ww (kK s0)) 1 = p) (hp0 : 0 < p) :
    WP isa (.seq divide order) u fun t => FF s0 t ∧
      num t.mem (rvB s0) (ww (kK s0)) 5 = max p (nV s0 / p) ∧
      num t.mem (rvB s0) (ww (kK s0)) 6 = min p (nV s0 / p) := by
  have fit : ∀ j < nArr, arr (ww (kK s0)) j + S (ww (kK s0)) ≤ 2 ^ 64 := fun _ hj => h.ws.fit64 hj
  have hS : S (ww (kK s0)) = 4 * (ww (kK s0) + 2) := rfl
  have N : ∀ {a b : State} {js ds : List Nat} (kk : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) js ds a.mem b.mem)
      (j : Nat), j < nArr → (∀ k ∈ js, k ≠ j) → (∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) →
      num b.mem (rvB s0) (ww (kK s0)) j = num a.mem (rvB s0) (ww (kK s0)) j :=
    fun kk j hj hk hd => kk.num hk hd (fit j hj)
  rw [WP.seq_iff]
  unfold divide
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h.ws (o := aQ) (a := aN) (by decide) (by decide) (by decide) (by decide))
    fun u1 ⟨ws1, kk1, v1, k1, _⟩ => ?_
  have f1 := h.of_keep kk1 (by decide) (by simp) k1 ws1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws1 (o := aDv) (a := 1) (by decide) (by decide) (by decide) (by decide))
    fun u2 ⟨ws2, kk2, v2, k2, _⟩ => ?_
  have f2 := f1.of_keep kk2 (by decide) (by simp) k2 ws2
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil (clrW aDv)]
  refine clrW_ok ws2 (j := aDv) (by decide) (by decide) fun u3 ws3 kk3 o3 z3 k3 => WP.block_nil ?_
  have f3 := f2.of_keep kk3 (by decide) (by simp) k3 ws3
  have d3 : num u3.mem (rvB s0) (ww (kK s0)) aDv = p := by
    have := fit aDv (by decide)
    refine (Outs.val32 (Outs.of_outside o3 (List.mem_singleton_self _)) (fun r hr => ?_) (by omega)).trans ?_
    · simp only [List.mem_singleton] at hr; subst hr; dsimp only; omega
    · change num u2.mem (rvB s0) (ww (kK s0)) aDv = p
      rw [v2, N kk1 1 (by decide) (by decide) (by simp)]; exact hp
  have q3 : num u3.mem (rvB s0) (ww (kK s0)) aQ = nV s0 := by
    rw [N kk3 aQ (by decide) (by decide) (by simp), N kk2 aQ (by decide) (by decide) (by simp), v1]; exact h.vN
  have p3 : num u3.mem (rvB s0) (ww (kK s0)) 1 = p := by
    rw [N kk3 1 (by decide) (by decide) (by simp), N kk2 1 (by decide) (by decide) (by simp),
      N kk1 1 (by decide) (by decide) (by simp)]; exact hp
  rw [show seqs [VG.Impl.Rsa.PPC64LE.Div.div aQ aRm aDv aDt] = VG.Impl.Rsa.PPC64LE.Div.div aQ aRm aDv aDt from rfl]
  refine WP.mono (div_ok ws3 (q := aQ) (r := aRm) (d := aDv) (t := aDt) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) z3)
    fun u4 ⟨ws4, kk4, k4, v4⟩ => ?_
  have f4 := f3.of_keep kk4 (by decide) (by simp) k4 ws4
  have q4 : num u4.mem (rvB s0) (ww (kK s0)) aQ = nV s0 / p := by
    rw [(v4 (by rw [d3]; exact hp0)).1, q3, d3]
  have p4 : num u4.mem (rvB s0) (ww (kK s0)) 1 = p := by rw [N kk4 1 (by decide) (by decide) (by simp), p3]
  -- The order.
  unfold order
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok ws4 (o := aW) (a := 1) (b := aQ) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun u5 ⟨ws5, kk5, v5, b5, k5⟩ => ?_
  have f5 := f4.of_keep kk5 (by decide) (by simp) k5 ws5
  rw [p4, q4] at v5
  have lt5 := val32_lt u5.mem (rvB s0) (arr (ww (kK s0)) aW) (ww (kK s0))
  change num u5.mem (rvB s0) (ww (kK s0)) aW < _ at lt5
  have pl : p < 2 ^ (32 * ww (kK s0)) := by
    rw [← p4]; exact val32_lt _ _ _ _
  have ql : nV s0 / p < 2 ^ (32 * ww (kK s0)) := by
    rw [← q4]; exact val32_lt _ _ _ _
  have bit : (u5.gpr .r9).toNat = if p < nV s0 / p then 1 else 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b5 with e | e <;> rw [e] at v5 ⊢ <;> split <;> omega
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil (stBorrow sLt)]
  refine stBorrow_ok ws5 (sl := sLt) (by decide) b5 fun u6 ws6 kk6 s6 k6 => WP.block_nil ?_
  have f6 := f5.of_keep kk6 (by simp) (by decide) k6 ws6
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have b6 : slot u6.mem (rvB s0) sLt ≤ 1 := by rw [s6]; exact b5
  refine WP.mono (sel_ok ws6 (o := 5) (a := 1) (b := aQ) (sl := sLt) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) b6) fun u7 ⟨ws7, kk7, v7, k7⟩ => ?_
  have f7 := f6.of_keep kk7 (by decide) (by simp) k7 ws7
  rw [show seqs [VG.Impl.Rsa.PPC64LE.Keys.sel 6 aQ 1 sLt] = VG.Impl.Rsa.PPC64LE.Keys.sel 6 aQ 1 sLt from rfl]
  have b7 : slot u7.mem (rvB s0) sLt ≤ 1 := by rw [kk7.slot (e := sLt) (by decide) (by simp)]; exact b6
  refine WP.mono (sel_ok ws7 (o := 6) (a := aQ) (b := 1) (sl := sLt) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) b7) fun t ⟨wst, kkt, vt, kt⟩ => ?_
  have ft := f7.of_keep kkt (by decide) (by simp) kt wst
  have p6 : num u6.mem (rvB s0) (ww (kK s0)) 1 = p := by
    rw [N kk6 1 (by decide) (by simp) (by decide), N kk5 1 (by decide) (by decide) (by simp), p4]
  have q6 : num u6.mem (rvB s0) (ww (kK s0)) aQ = nV s0 / p := by
    rw [N kk6 aQ (by decide) (by simp) (by decide), N kk5 aQ (by decide) (by decide) (by simp), q4]
  refine ⟨ft, ?_, ?_⟩
  · rw [N kkt 5 (by decide) (by decide) (by simp), v7, s6, bit, p6, q6]
    by_cases hl : p < nV s0 / p
    · simp only [hl, ite_true, Nat.one_ne_zero, ite_false, Nat.max_def]; split <;> omega
    · simp only [hl, ite_false, ite_true, Nat.max_def]; split <;> omega
  · rw [vt, kk7.slot (e := sLt) (by decide) (by simp), s6, bit, N kk7 aQ (by decide) (by decide) (by simp),
      N kk7 1 (by decide) (by decide) (by simp), p6, q6]
    by_cases hl : p < nV s0 / p
    · simp only [hl, ite_true, Nat.one_ne_zero, ite_false, Nat.min_def]; split <;> omega
    · simp only [hl, ite_false, ite_true, Nat.min_def]; split <;> omega

end VG.Proof.Rsa.PPC64LE.Recover
