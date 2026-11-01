module

public import VerifiedGarbage.Proof.Weierstrass.Arm.PointFn
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Impl.Weierstrass.Arm.LadderP
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# The ladder by calls of the point functions, on 32-bit ARM: copies and calls

`copyPt n o a` copies the point at `a` to `o` (`copyPt_ok`), and
`ptCall S dbl` calls `vg_<curve>_point_double` or `vg_<curve>_point_add` on
the working space at `r12` (`ptCall_ok`): it changes only `r0`–`r3` and
`r10`, `O` and the point functions' own working space, and `O` then holds
`rcbAdd` of what `a`, `3b`, `P` and `Q` (or `P`) stood for (`fn_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
  VG.Proof.Weierstrass.Arm.Mont
open VG.Proof.X25519.Arm (Rest Upd wp_mov op2_reg)

/-- `o = a`, for points whose slots (`n` 64-bit words) are in the working
space, with `o`'s apart from each other and from `a`'s. -/
theorem copyPt_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n : Nat} {o a : Pt}
    (hin : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z], d + 8 * n ≤ size)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hoa : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [a.x, a.y, a.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (copyPt n o a)) s fun s' =>
      wordsVal s'.mem base o.x n = wordsVal s.mem base a.x n ∧
      wordsVal s'.mem base o.y n = wordsVal s.mem base a.y n ∧
      wordsVal s'.mem base o.z n = wordsVal s.mem base a.z n ∧
      Rest [.r4] s s' ∧ Outs base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem s'.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hoa
  obtain ⟨iox, ioy, ioz, iax, iay, iaz⟩ := hin
  obtain ⟨⟨xax, xay, xaz⟩, ⟨yax, yay, yaz⟩, ⟨zax, zay, zaz⟩⟩ := hoa
  obtain ⟨xy, xz, yz⟩ := hoo
  simp only [wordsVal_eq_val32]
  rw [copyPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok (2 * n) hs (by omega_using [iox]) (by omega_using [iax]) (by omega_using [xax]))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_rest k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * n) hs₁ (by omega_using [ioy]) (by omega_using [iay]) (by omega_using [yay]))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_rest k₂ (by decide)
  refine WP.mono (copy_ok (2 * n) hs₂ (by omega_using [ioz]) (by omega_using [iaz]) (by omega_using [zaz]))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.val32 (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.val32 (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.val32 (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.val32 (d := a.y) (by omega_using [xay]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.val32 (d := a.z) (by omega_using [yaz]) (by omega_using [iaz, hn]),
      O₁.val32 (d := a.z) (by omega_using [xaz]) (by omega_using [iaz, hn])]
  · rw [show 4 * (2 * n) = 8 * n by omega] at O₁ O₂ O₃
    exact ((Outs.of_outside O₁ (by simp)).trans (Outs.of_outside O₂ (by simp))).trans
      (Outs.of_outside O₃ (by simp))

/-- What the slot of number `x` stands for, in the working space at `base`. -/
def Eb (k m : Nat) [NeZero m] (dbl : Bool) (mem : Mem) (base : Addr) (x : Nat) : Fin m :=
  toM m (2 ^ (64 * k)) (wordsVal mem base (enc k dbl x) k)

/-- What the point function `ptName S a0 dbl` computes from the values of
the slots: Algorithm 9 or 8 for `a0`, else Algorithm 1. -/
def ptVal {m : Nat} [NeZero m] (a0 dbl : Bool) (E : Nat → Fin m) : Fin m × Fin m × Fin m :=
  if a0 then
    (if dbl then Impl.Weierstrass.Point.rcbDbl0 (E 10) (E 3) (E 4) (E 5)
    else Impl.Weierstrass.Point.rcbAdd0m (E 10) (E 3) (E 4) (E 5) (E 6) (E 7))
  else VG.Proof.Weierstrass.rcbAdd (E 9) (E 10) (E 3) (E 4) (E 5) (E 6) (E 7) (E 8)

theorem ptOps_opsOk (a0 dbl : Bool) : OpsOk (ptOps a0 dbl) := by
  cases a0
  · exact rcbIds_opsOk
  · exact ops0_opsOk dbl

theorem ptOps_run {m : Nat} [NeZero m] (E : Nat → Fin m) (a0 dbl : Bool) :
    (runOps (ptOps a0 dbl) E 0, runOps (ptOps a0 dbl) E 1, runOps (ptOps a0 dbl) E 2) =
      ptVal a0 dbl E := by
  cases a0
  · exact rcb_run rcbIds_apart E
  · exact ops0_run E dbl

theorem fnOps_noFrames (S : Impl.Weierstrass.Mont.Modulus) (dbl : Bool) (ops : List FOp) (u : Bool := false) :
    (fnOps S dbl ops u).noFrames = true := by
  have mul : (Mont.mulFnWith u S.k S.m).noFrames = true := by
    unfold Mont.mulFnWith Mont.mulFnU Mont.mulFn
    cases u <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> (try split) <;> rfl
  have fields (op : FOp) : (opCodeR (enc S.k dbl) S u op).noFrames = true := by
    cases op <;> simp only [opCodeR, callR, Code.noFrames, Bool.true_and, mul] <;> rfl
  have seqs : ∀ ps : List (Prog isa), (∀ p ∈ ps, p.noFrames = true) → (progs ps).noFrames = true := by
    intro ps
    induction ps with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro hp
      cases ps with
      | nil => exact hp p (by simp)
      | cons q qs =>
        change p.noFrames && (progs (q :: qs)).noFrames = true
        rw [hp p (by simp), ih (fun r hr => hp r (by simp [hr]))]
        rfl
  have prog : (fprogR (enc S.k dbl) S ops u).noFrames = true := by
    apply seqs
    intro p hp
    obtain ⟨op, _, rfl⟩ := List.mem_map.mp hp
    exact fields op
  simpa only [Impl.Weierstrass.Arm.Point.fnOps, Code.noFrames, Bool.true_and, Bool.and_true] using prog

theorem fn_noFrames (S : Impl.Weierstrass.Mont.Modulus) (dbl : Bool) (u : Bool := false) :
    (fn S dbl u).noFrames = true :=
  fnOps_noFrames S dbl _ u

/-- A call of a point function, from the working space at `r12`: only
`r0`–`r3`, `r10`, `O` and the own working space change, and `O` holds
`ptVal` of what the constants and the operands stood for. -/
theorem ptCall_ok {S : Impl.Weierstrass.Mont.Modulus} {m k : Nat} [NeZero m] (hm : S.m = m) (hk : S.k = k)
    (hM : ModOk k m) (hodd : m % 2 = 1) (hk6 : k ≤ 6) (dbl : Bool) {a0 : Bool} {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hf : Far s base 8192)
    (hlt : ∀ x ∈ rIds, wordsVal s.mem base (enc k dbl x) k < m) {u : Bool} :
    WP isa (ptCall S dbl a0 u) s fun s' => Rest [.r10, .r0, .r1, .r2, .r3] s s' ∧
      Outs base [(Impl.Weierstrass.Point.oAt k, 3 * Impl.Weierstrass.Point.elemBytes k),
        (Impl.Weierstrass.Point.ownAt k, 4096 - Impl.Weierstrass.Point.ownAt k)] s.mem s'.mem ∧
      (∀ j < 3, wordsVal s'.mem base (enc k dbl j) k < m) ∧
      (Eb k m dbl s'.mem base 0, Eb k m dbl s'.mem base 1, Eb k m dbl s'.mem base 2) =
        ptVal a0 dbl (Eb k m dbl s.mem base) := by
  obtain ⟨c, w, m', k', d⟩ := S
  dsimp only at hm hk
  subst hm hk
  rw [ptCall]
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => WP.block_nil ?_)
  have k₂ : Rest [.r10, .r0] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have g10 : s₂.gpr .r10 = s.gpr .lr := by rw [u₂.other _ (by decide), u₁.gpr]
  have g0 : s₂.gpr .r0 = s.gpr .r12 := by rw [u₂.gpr, u₁.other _ (by decide)]
  have hf₂ : Far s₂ base 8192 := hf.of_rest k₂
  have hcov : Covers [⟨base, 8192⟩] s₂.wr := by
    have h := hf₂.write (d := 0) (n := 8192) (by omega)
    simp only [off, BitVec.add_zero] at h
    exact Covers.one h
  have e0 : ∀ t : State, t.gpr .r0 = s.gpr .r12 → State.addr (t.gpr .r0) = base := fun t h => by
    rw [h]; exact hs.wb
  refine WP.seq (WP.callCalls (k := ⟨fun t => PrePt k' m' dbl t ∧ t.gpr .r0 = s.gpr .r12 ∧ t.mem = s.mem,
      fun t t' => Outs (State.addr (t.gpr .r0)) [(Impl.Weierstrass.Point.oAt k', 3 * Impl.Weierstrass.Point.elemBytes k'),
          (Impl.Weierstrass.Point.ownAt k', 4096 - Impl.Weierstrass.Point.ownAt k')] t.mem t'.mem ∧
        t'.gpr .r12 = t.gpr .r0 ∧
        (∀ j < 3, wordsVal t'.mem (State.addr (t.gpr .r0)) (enc k' dbl j) k' < m') ∧
        (Eb k' m' dbl t'.mem (State.addr (t.gpr .r0)) 0, Eb k' m' dbl t'.mem (State.addr (t.gpr .r0)) 1,
          Eb k' m' dbl t'.mem (State.addr (t.gpr .r0)) 2) =
        ptVal a0 dbl (Eb k' m' dbl t.mem (State.addr (t.gpr .r0))),
      fun _ _ => True⟩)
    (fun t ⟨hp, _, _⟩ => by
      obtain ⟨tr, t', he, A, O, R, L, E⟩ := fnOps_ok (S := ⟨c, w, m', k', d⟩) hM hodd (ptOps_opsOk a0 dbl) hp
      exact ⟨tr, t', he, A, O, R, L, E.trans (ptOps_run _ a0 dbl)⟩)
    (rd := []) (wr := [⟨base, 8192⟩])
    ⟨⟨rfl, by rw [State.withRegions_wr, State.withRegions_gpr, State.callEntry_gpr _ (by decide),
        e0 _ g0],
      by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g0, hs.wb_toNat]; exact hf.nowrap,
      hM.n3, hk6,
      fun x hx => by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), e0 _ g0, State.withRegions_mem,
          State.callEntry_mem, m₂]
        exact hlt x hx⟩,
      by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g0],
      by rw [State.withRegions_mem, State.callEntry_mem, m₂]⟩
    (Covers.right hcov) hcov ?_ (fnOps_noFrames _ _ _ u))
  intro s₇ r₇ w₇ p₇ _ hp₇ _ ⟨O, R, L, E⟩
  simp only [State.withRegions_mem, State.callEntry_mem, m₂, State.withRegions_gpr] at O R L E
  rw [State.callEntry_gpr _ (by decide), g0] at R
  rw [State.callEntry_gpr _ (by decide), e0 _ g0] at O L E
  refine wp_mov (op2_reg _ _) fun s₈ u₈ => WP.block_nil ?_
  have hm : s₈.mem = s₇.mem := u₈.mem
  refine ⟨⟨fun r hr => ?_, by rw [u₈.rd, r₇, k₂.rd], by rw [u₈.wr, w₇, k₂.wr],
    by rw [u₈.sp, p₇, k₂.sp]⟩, by rw [hm]; exact O, by rw [hm]; exact L, by rw [hm]; exact E⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h10, h0, h1, h2, h3⟩ := hr
  by_cases hlr : r = .lr
  · subst hlr
    rw [u₈.gpr, hp₇ _ (by decide) (by decide), g10]
  by_cases h12 : r = .r12
  · subst h12
    rw [u₈.other _ (by decide), R]
  have hpres : r ∈ preserved := by revert h10 h0 h1 h2 h3 h12 hlr; cases r <;> decide
  rw [u₈.other _ hlr, hp₇ r hpres hlr, k₂.gpr r (by simp [h10, h0])]

end VG.Proof.Weierstrass.Arm.Point
