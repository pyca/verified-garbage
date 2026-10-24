module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCand
import VerifiedGarbage.Proof.Framework.Block

/-!
# `vg_rsa_recover_primes` on PPC64LE: what the finish keeps

`FF`: after the candidates, `n`, 0 and 1 in their arrays, the mask of `ok`
and the outputs' registers. `FF.of_keep`: a step on other arrays and the
slots `ffD` keeps it.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (aN aOne aZ nArr sMask sLt)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The last candidate tried, whether it found the factors, and its `y`. -/
abbrev jL (s0 : State) : Nat := nt s0 - 1
abbrev okB (s0 : State) : Bool := (sqst s0 (jL s0) (cB s0)).2.2
abbrev yV (s0 : State) : Nat := (sqst s0 (jL s0) (cB s0)).1

/-- The slots the finish writes but the mask. -/
abbrev ffD : List Nat := [VG.Impl.Rsa.PPC64LE.Keys.sOdd, VG.Impl.Rsa.PPC64LE.Keys.sB, VG.Impl.Rsa.PPC64LE.Keys.sC, sLt]

/-- What the finish keeps. -/
structure FF (s0 t : State) : Prop where
  base : RBase s0 t
  ws : Ws t (rvB s0) (rvZ s0) (ww (kK s0)) nArr
  r21 : t.gpr .r21 = s0.gpr .r3
  r23 : t.gpr .r23 = s0.gpr .r5
  r25 : t.gpr .r25 = s0.gpr .r8
  vN : num t.mem (rvB s0) (ww (kK s0)) aN = nV s0
  vOne : num t.mem (rvB s0) (ww (kK s0)) aOne = 1
  zZ : ∀ i < ww (kK s0) + 2, w32 t.mem (rvB s0) (arr (ww (kK s0)) aZ + 4 * i) = 0
  mask : slot t.mem (rvB s0) sMask = b2n (okB s0)

/-- A step on other arrays and the slots `ffD` keeps `FF`. -/
theorem FF.of_keep {s0 u v : State} (h : FF s0 u) {js ds : List Nat}
    (kk : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) js ds u.mem v.mem) (hj : ∀ j ∈ js, j < 32 ∨ 35 ≤ j ∧ j < nArr)
    (hd : ∀ d ∈ ds, d ∈ ffD) {rs : List Reg} (k : Keep rs u v)
    (hw : Ws v (rvB s0) (rvZ s0) (ww (kK s0)) nArr)
    (hr : ∀ r ∈ rs, r ∉ [.r21, .r23, .r25, .r31] := by decide) : FF s0 v := by
  have z := h.base.sz
  have svw := z.svw
  have fit : ∀ j < nArr, arr (ww (kK s0)) j + S (ww (kK s0)) ≤ 2 ^ 64 := fun _ hj => h.ws.fit64 hj
  have hd4 : ∀ d ∈ ds, d + 4 ≤ 160 := fun d hd' => by
    have := hd d hd'; simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl <;> decide
  have nj : ∀ j, 32 ≤ j → j < 35 → ∀ k ∈ js, k ≠ j := fun j h1 h2 k hk e => by
    have := hj k hk; omega
  have g : ∀ r, r ∈ [.r21, .r23, .r25, .r31] → v.gpr r = u.gpr r := fun r hr' =>
    k.gpr r fun hm => hr r hm hr'
  refine ⟨h.base.of_keep kk (fun j hj' => ?_) (fun d hd' => hd4 d hd') k (fun hm => hr _ hm (by simp)), hw,
    by rw [g _ (by simp)]; exact h.r21, by rw [g _ (by simp)]; exact h.r23, by rw [g _ (by simp)]; exact h.r25,
    by rw [kk.num (nj aN (by decide) (by decide)) (fun d hd' => hd4 d hd') (fit aN (by decide))]; exact h.vN,
    by rw [kk.num (nj aOne (by decide) (by decide)) (fun d hd' => hd4 d hd') (fit aOne (by decide))]; exact h.vOne,
    fun i hi => ?_, ?_⟩
  · have : j < nArr := by have := hj j hj'; simp only [nArr] at this ⊢; omega
    rw [svw]; exact VG.Proof.Rsa.KeyWorkspace.arr_end this
  · have := keep_in' kk (nj aZ (by decide) (by decide)) hd4 (i := i) (n := 1) (by omega) (fit aZ (by decide))
    simp only [val32, Nat.mul_zero, Nat.add_zero] at this
    rw [this]; exact h.zZ i hi
  · rw [kk.slot (e := sMask) (by decide) fun d hd' => .inr (by
      have := hd d hd'; simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl <;> decide)]
    exact h.mask

end VG.Proof.Rsa.PPC64LE.Recover
