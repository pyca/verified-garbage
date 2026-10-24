module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvMont
import VerifiedGarbage.Proof.Framework.Block

/-!
# `vg_rsa_recover_primes` on PPC64LE: what the candidates keep

`CF`: the facts of the Montgomery setup (`MontS`) that every step of the
candidates keeps, but for `r24`, the candidate. `CF.of_keep`: a step that
writes only the candidates' working arrays (`wrJ`) and slots (`wrD`), and no
register `CF` names, keeps it. `keepW_key`: what a step on the `W` view
keeps, on the key arrays.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (mBase mR2 aN aOne aZ aO aNg nArr sTc sK sDone sOk sBit sLive sE1 sE2 sMask wR)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The candidates' working arrays: Montgomery arrays 2–7, `r`'s copy (in
the `W` view) and the copy of `y`. -/
abbrev wrJ : List Nat := [22, 23, 24, 25, 26, 27, 30, 31, 38]

/-- The slots of the candidates, and the mask. -/
abbrev wrD : List Nat := [sK, sDone, sOk, sBit, sLive, sE1, sE2, sMask]

/-- What the candidates keep. -/
structure CF (s0 t : State) : Prop where
  base : RBase s0 t
  ws : Ws t (rvB s0) (rvZ s0) (ww (kK s0)) nArr
  r21 : t.gpr .r21 = s0.gpr .r3
  r23 : t.gpr .r23 = s0.gpr .r5
  r25 : t.gpr .r25 = s0.gpr .r8
  r26 : t.gpr .r26 = BitVec.ofNat 64 (cB s0)
  r12 : (t.gpr .r12).toNat < 2 ^ 32
  inv : (w32 t.mem (rvB s0) (arr (ww (kK s0)) mBase) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0
  vN : num t.mem (rvB s0) (ww (kK s0)) aN = nV s0
  vMN : lowV t.mem s0 mBase = nV s0
  vR2 : lowV t.mem s0 mR2 = RR s0 * RR s0 % nV s0
  vO : num t.mem (rvB s0) (ww (kK s0)) aO = RR s0 % nV s0
  vNg : num t.mem (rvB s0) (ww (kK s0)) aNg = nV s0 - RR s0 % nV s0
  vOne : num t.mem (rvB s0) (ww (kK s0)) aOne = 1
  zZ : ∀ i < ww (kK s0) + 2, w32 t.mem (rvB s0) (arr (ww (kK s0)) aZ + 4 * i) = 0
  vR : num t.mem (rvB s0) (wW (kK s0)) wR = (Spec.Rsa.splitTwos (mV s0)).2
  vT : slot t.mem (rvB s0) sTc = (Spec.Rsa.splitTwos (mV s0)).1
  odd : dV s0 * eV s0 % 2 = 1
  two : 2 ≤ dV s0 * eV s0

theorem MontS.cf {s0 t : State} (h : MontS s0 t) : CF s0 t :=
  ⟨h.base, h.ws, h.r21, h.r23, h.r25, h.r26, h.r12, h.inv, h.vN, h.vMN, h.vR2, h.vO, h.vNg, h.vOne, h.zZ, h.vR,
    h.vT, h.odd, h.two⟩

/-- Digits of one array, kept by a step on other arrays and slots. -/
theorem keep_in' {B : Addr} {v : Nat} {js ds : List Nat} {m m' : Mem}
    (k : KeyWorkspace.Keep B v js ds m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ 160)
    {i n : Nat} (hin : i + n ≤ v + 2) (fit : arr v j + S v ≤ 2 ^ 64) :
    val32 m' B (arr v j + 4 * i) n = val32 m B (arr v j + 4 * i) n := by
  have hS : S v = 4 * (v + 2) := rfl
  have h160 : 160 ≤ arr v j := Nat.le_add_right _ _
  refine keep_apart k (fun l hl => ?_) (fun e he => .inl (Nat.le_trans (hd e he) (by omega))) (by omega)
  rcases Nat.lt_or_gt_of_ne (hj l hl) with h | h
  · have := VG.Proof.Rsa.KeyWorkspace.arr_end (w := v) h; omega
  · have := VG.Proof.Rsa.KeyWorkspace.arr_end (w := v) h; omega

/-- A step on the candidates' arrays and slots keeps `CF`. -/
theorem CF.of_keep {s0 u v : State} (h : CF s0 u) {js ds : List Nat}
    (kk : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) js ds u.mem v.mem) (hj : ∀ j ∈ js, j ∈ wrJ)
    (hd : ∀ d ∈ ds, d ∈ wrD) {rs : List Reg} (k : Keep rs u v)
    (hw : Ws v (rvB s0) (rvZ s0) (ww (kK s0)) nArr)
    (hr : ∀ r ∈ rs, r ∉ [.r12, .r21, .r23, .r25, .r26, .r31] := by decide) : CF s0 v := by
  have z := h.base.sz
  have w1 := z.w1; have svw := z.svw
  have hww : ww (kK s0) = 2 * wm (kK s0) + 2 := rfl
  have fit : ∀ j < nArr, arr (ww (kK s0)) j + S (ww (kK s0)) ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have hd4 : ∀ d ∈ ds, d + 4 ≤ 160 := fun d hd' => by
    have := hd d hd'; simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have nj : ∀ j, j ∉ wrJ → ∀ k ∈ js, k ≠ j := fun j hj' k hk e => hj' (e ▸ hj k hk)
  have g : ∀ r, r ∈ [.r12, .r21, .r23, .r25, .r26, .r31] → v.gpr r = u.gpr r := fun r hr' =>
    k.gpr r fun hm => hr r hm hr'
  have low : ∀ j, j ∉ wrJ → j < nArr → lowV v.mem s0 j = lowV u.mem s0 j := fun j hj' hn => by
    have := keep_in' kk (nj j hj') hd4 (i := 0) (n := 2 * wm (kK s0)) (by omega) (fit j hn)
    simpa only [Nat.mul_zero, Nat.add_zero] using this
  have nm : ∀ j, j ∉ wrJ → j < nArr → num v.mem (rvB s0) (ww (kK s0)) j = num u.mem (rvB s0) (ww (kK s0)) j :=
    fun j hj' hn => kk.num (nj j hj') (fun d hd' => hd4 d hd') (fit j hn)
  refine ⟨h.base.of_keep kk (fun j hj' => ?_) (fun d hd' => hd4 d hd') k (fun hm => hr _ hm (by simp)), hw,
    by rw [g _ (by simp)]; exact h.r21, by rw [g _ (by simp)]; exact h.r23, by rw [g _ (by simp)]; exact h.r25,
    by rw [g _ (by simp)]; exact h.r26, by rw [g _ (by simp)]; exact h.r12, ?_,
    by rw [nm aN (by decide) (by decide)]; exact h.vN, by rw [low mBase (by decide) (by decide)]; exact h.vMN,
    by rw [low mR2 (by decide) (by decide)]; exact h.vR2, by rw [nm aO (by decide) (by decide)]; exact h.vO,
    by rw [nm aNg (by decide) (by decide)]; exact h.vNg, by rw [nm aOne (by decide) (by decide)]; exact h.vOne,
    fun i hi => ?_, ?_, ?_, h.odd, h.two⟩
  · have := hj j hj'
    have : j < nArr := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [svw]; exact VG.Proof.Rsa.KeyWorkspace.arr_end this
  · rw [g _ (by simp)]
    have := keep_in' kk (nj mBase (by decide)) hd4 (i := 0) (n := 1) (by omega) (fit mBase (by decide))
    simp only [val32, Nat.mul_zero, Nat.add_zero] at this
    rw [this]; exact h.inv
  · have := keep_in' kk (nj aZ (by decide)) hd4 (i := i) (n := 1) (by omega) (fit aZ (by decide))
    simp only [val32, Nat.mul_zero, Nat.add_zero] at this
    rw [this]; exact h.zZ i hi
  · have hW : wW (kK s0) = 2 * ww (kK s0) + 2 := rfl
    have e1 := arrW14 (ww (kK s0)); have e2 := arrW14_end (ww (kK s0))
    have e3 := VG.Proof.Rsa.KeyWorkspace.arr_end (w := ww (kK s0)) (show 30 < 31 by decide)
    have f31 := fit 31 (by decide)
    have hjs : ∀ j ∈ js, j < 28 ∨ 30 ≤ j := fun j hj' => by
      have := hj j hj'; simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have := h.vR
    change val32 v.mem (rvB s0) (arr (wW (kK s0)) 14) (wW (kK s0)) = _
    change val32 u.mem (rvB s0) (arr (wW (kK s0)) 14) (wW (kK s0)) = _ at this
    rw [hW, e1] at this ⊢
    rw [keep_apart kk (fun j hj' => arr_apart (hjs j hj') (Nat.le_refl _) e2)
      (fun e he => .inl (Nat.le_trans (hd4 e he) (Nat.le_add_right _ _)))
      (Nat.le_trans e2 (Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) e3) (Nat.le_trans (Nat.le_add_right _ _) f31)))]
    exact this
  · have := hd4
    rw [kk.slot (e := sTc) (by decide) fun d hd' => .inl (by
      have := hd d hd'; simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    exact h.vT

/-- What a step on the `W` view keeps, on the key arrays. -/
theorem keepW_key {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (k : KeyWorkspace.Keep B (2 * w + 2) js ds m m') :
    KeyWorkspace.Keep B w (js.flatMap fun j => [2 * j, 2 * j + 1]) ds m m' := by
  intro x hx
  refine k x fun r hr => ?_
  simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
  · have a0 := hx _ (by
      simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map, List.mem_flatMap]
      exact .inl ⟨2 * j, ⟨j, hj, by simp⟩, rfl⟩)
    have a1 := hx _ (by
      simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map, List.mem_flatMap]
      exact .inl ⟨2 * j + 1, ⟨j, hj, by simp⟩, rfl⟩)
    dsimp only at a0 a1 ⊢
    have e0 : arr (2 * w + 2) j = arr w (2 * j) := by simp only [arr, S]; grind
    have e1 : arr w (2 * j + 1) = arr w (2 * j) + S w := VG.Proof.Rsa.KeyWorkspace.arr_succ _ _
    have e2 : S (2 * w + 2) = 2 * S w := by simp only [S]; omega
    rw [e0, e2]; rw [e1] at a1
    generalize arr w (2 * j) = A at *
    generalize S w = T at *
    omega
  · exact hx _ (by simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map]; exact .inr ⟨d, hd, rfl⟩)

end VG.Proof.Rsa.PPC64LE.Recover
