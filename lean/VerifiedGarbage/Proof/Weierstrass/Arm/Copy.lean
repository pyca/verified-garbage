import VerifiedGarbage.Proof.Weierstrass.Arm.Fprog
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Short Weierstrass curves on 32-bit ARM: copies and selections

`copy k o a` writes `[a]` to `[o]` (`copy_ok`, `k` 32-bit words), `sel k o a
b` writes `[a]` or `[b]` to `[o]` by the mask `r10` (`sel_ok`; `o` may be `a`
or `b`), `selPt` does so for the three coordinates of a point
(`selPt_ok`). Each changes only `[o]` and `r4` (and `r5` for the
selections), and keeps the regions. Constants are in `Const.lean`.
-/

namespace VG.Proof.Weierstrass.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
  VG.Proof.Mont.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_ldr wp_str wp_dp wp_movw op2_reg)

/-- `[o] = [a]`, for `o` at or below `a` or apart from it. -/
theorem copy_ok {size : Nat} : ∀ (k : Nat) {s : State} {base : Addr} {o a : Nat},
    Scr s base size → o + 4 * k ≤ size → a + 4 * k ≤ size → (o ≤ a ∨ a + 4 * k ≤ o) →
    WP isa (.block (copy k o a)) s fun s' =>
      val32 s'.mem base o k = val32 s.mem base a k ∧ Rest [.r4] s s' ∧
      Outside base o (4 * k) s.mem s'.mem
  | 0, _, _, _, _, _, _, _, _ => WP.block_nil ⟨rfl, Rest.refl _ _, VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, s, base, o, a, hs, ho, ha, hsep => by
    have hn := hs.nowrap
    rw [copy, List.cons_append, List.cons_append, List.nil_append]
    refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read (d := a) (n := 4) (by omega)) fun s₁ u₁ => ?_
    have hs₁ := hs.of_rest (u₁.rest (ws := [.r4]) (by simp)) (by decide)
    refine wp_str (hs.off_lt (by omega)) (hs₁.ea (by omega)) (hs₁.write (d := o) (n := 4) (by omega))
      fun s₂ m₂ => ?_
    have k₂ : Rest [.r4] s s₂ := (u₁.rest (by simp)).trans (m₂.rest _)
    have hs₂ := hs.of_rest k₂ (by decide)
    have O₂ : Outside base o 4 s.mem s₂.mem := by
      rw [m₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega)
    refine WP.mono (copy_ok k hs₂ (o := o + 4) (a := a + 4) (by omega) (by omega) (by omega))
      fun s₃ ⟨e₃, k₃, O₃⟩ => ⟨?_, k₂.trans k₃, (O₂.mono (Nat.le_refl _) (by omega)).trans
        (O₃.mono (by omega) (by omega))⟩
    rw [val32, val32, O₃.w32 (by omega) (by omega), e₃, O₂.val32 (by omega) (by omega), m₂.mem,
      w32_write_self, u₁.gpr]

/-- `[o] = [b]` if the mask `r10` is all ones (`c`), `[a]` if it is zero; `o`
at or below `a` and `b`, or apart from them. -/
theorem sel_ok {size : Nat} (c : Bool) : ∀ (k : Nat) {s : State} {base : Addr} {o a b : Nat},
    Scr s base size → s.gpr .r10 = (if c then BitVec.allOnes 32 else 0) →
    o + 4 * k ≤ size → a + 4 * k ≤ size → b + 4 * k ≤ size →
    (o ≤ a ∨ a + 4 * k ≤ o) → (o ≤ b ∨ b + 4 * k ≤ o) →
    WP isa (.block (sel k o a b)) s fun s' =>
      val32 s'.mem base o k = (if c then val32 s.mem base b k else val32 s.mem base a k) ∧
      Rest [.r4, .r5] s s' ∧ Outside base o (4 * k) s.mem s'.mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨by cases c <;> rfl, Rest.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, s, base, o, a, b, hs, hc, ho, ha, hb, hsa, hsb => by
    have hn := hs.nowrap
    rw [sel]
    simp only [List.cons_append, List.nil_append]
    refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read (d := a) (n := 4) (by omega)) fun s₁ u₁ => ?_
    have hs₁ := hs.of_rest (u₁.rest (ws := [.r4]) (by simp)) (by decide)
    refine wp_ldr (hs.off_lt (by omega)) (hs₁.ea (by omega)) (hs₁.read (d := b) (n := 4) (by omega))
      fun s₂ u₂ => ?_
    refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
    refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
    refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
    have k₅ : Rest [.r4, .r5] s s₅ := (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans
      ((u₃.rest (by simp)).trans ((u₄.rest (by simp)).trans (u₅.rest (by simp)))))
    have hs₅ := hs.of_rest k₅ (by decide)
    refine wp_str (hs.off_lt (by omega)) (hs₅.ea (by omega)) (hs₅.write (d := o) (n := 4) (by omega))
      fun s₆ m₆ => ?_
    have k₆ : Rest [.r4, .r5] s s₆ := k₅.trans (m₆.rest _)
    have hs₆ := hs.of_rest k₆ (by decide)
    have mem₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    have O₆ : Outside base o 4 s.mem s₆.mem := by
      rw [m₆.mem, mem₅]; exact writeW32_outside _ _ _ (by omega)
    have a2 : s₂.gpr .r4 = s.mem.readW (off base a) 32 := by rw [u₂.other _ (by decide), u₁.gpr]
    have d2 : s₂.gpr .r5 = s.mem.readW (off base b) 32 := by rw [u₂.gpr, u₁.mem]
    have c2 : s₂.gpr .r10 = s.gpr .r10 := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
    have d3 : s₃.gpr .r5 = s.mem.readW (off base b) 32 ^^^ s.mem.readW (off base a) 32 := by
      rw [u₃.gpr, VG.Proof.X25519.Arm.dpVal, d2, a2]
    have d4 : s₄.gpr .r5 = (s.mem.readW (off base b) 32 ^^^ s.mem.readW (off base a) 32) &&&
        (if c then BitVec.allOnes 32 else 0) := by
      rw [u₄.gpr, VG.Proof.X25519.Arm.dpVal, d3, u₃.other _ (by decide), c2, hc]
    have r4₅ : s₅.gpr .r4 = s.mem.readW (off base a) 32 ^^^
        ((s.mem.readW (off base b) 32 ^^^ s.mem.readW (off base a) 32) &&&
          (if c then BitVec.allOnes 32 else 0)) := by
      rw [u₅.gpr, VG.Proof.X25519.Arm.dpVal, d4, u₄.other _ (by decide), u₃.other _ (by decide), a2]
    rw [select_val] at r4₅
    refine WP.mono (sel_ok c k hs₆ (o := o + 4) (a := a + 4) (b := b + 4)
      (by rw [k₆.gpr _ (by decide), hc]) (by omega) (by omega) (by omega) (by omega) (by omega))
      fun s₇ ⟨e₇, k₇, O₇⟩ => ⟨?_, k₆.trans k₇, (O₆.mono (Nat.le_refl _) (by omega)).trans
        (O₇.mono (by omega) (by omega))⟩
    have hw : w32 s₆.mem base o =
        (if c then s.mem.readW (off base b) 32 else s.mem.readW (off base a) 32).toNat := by
      rw [m₆.mem, mem₅, w32_write_self, r4₅]
    have ha' : val32 s₆.mem base (a + 4) k = val32 s.mem base (a + 4) k := O₆.val32 (by omega) (by omega)
    have hb' : val32 s₆.mem base (b + 4) k = val32 s.mem base (b + 4) k := O₆.val32 (by omega) (by omega)
    rw [val32, O₇.w32 (by omega) (by omega), e₇, hw, ha', hb']
    cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true, val32]

/-- `o = b` if the mask `r10` is all ones (`c`), `a` if it is zero, for points
whose slots (`n` 64-bit words) are in the working space, with `o`'s apart
from each other and from `a`'s and `b`'s. -/
theorem selPt_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (c : Bool)
    (hc : s.gpr .r10 = (if c then BitVec.allOnes 32 else 0)) {n : Nat} {o a b : Pt}
    (hin : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z, b.x, b.y, b.z], d + 8 * n ≤ size)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hab : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [a.x, a.y, a.z, b.x, b.y, b.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (selPt n o a b)) s fun s' =>
      wordsVal s'.mem base o.x n = (if c then wordsVal s.mem base b.x n else wordsVal s.mem base a.x n) ∧
      wordsVal s'.mem base o.y n = (if c then wordsVal s.mem base b.y n else wordsVal s.mem base a.y n) ∧
      wordsVal s'.mem base o.z n = (if c then wordsVal s.mem base b.z n else wordsVal s.mem base a.z n) ∧
      Rest [.r4, .r5] s s' ∧
      Outs base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem s'.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hab
  obtain ⟨iox, ioy, ioz, iax, iay, iaz, ibx, iby, ibz⟩ := hin
  obtain ⟨⟨xax, xay, xaz, xbx, xby, xbz⟩, ⟨yax, yay, yaz, ybx, yby, ybz⟩, ⟨zax, zay, zaz, zbx, zby, zbz⟩⟩ := hab
  obtain ⟨xy, xz, yz⟩ := hoo
  simp only [wordsVal_eq_val32]
  -- `omega` would split every disjunction of the context: give it the facts it needs.
  rw [selPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sel_ok c (2 * n) hs hc (by omega_using [iox]) (by omega_using [iax]) (by omega_using [ibx])
    (by omega_using [xax]) (by omega_using [xbx])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_rest k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok c (2 * n) hs₁ (by rw [k₁.gpr _ (by decide), hc]) (by omega_using [ioy])
    (by omega_using [iay]) (by omega_using [iby]) (by omega_using [yay]) (by omega_using [yby]))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_rest k₂ (by decide)
  refine WP.mono (sel_ok c (2 * n) hs₂ (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hc])
    (by omega_using [ioz]) (by omega_using [iaz]) (by omega_using [ibz]) (by omega_using [zaz])
    (by omega_using [zbz])) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.val32 (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.val32 (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.val32 (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.val32 (d := b.y) (by omega_using [xby]) (by omega_using [iby, hn]),
      O₁.val32 (d := a.y) (by omega_using [xay]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.val32 (d := b.z) (by omega_using [ybz]) (by omega_using [ibz, hn]),
      O₂.val32 (d := a.z) (by omega_using [yaz]) (by omega_using [iaz, hn]),
      O₁.val32 (d := b.z) (by omega_using [xbz]) (by omega_using [ibz, hn]),
      O₁.val32 (d := a.z) (by omega_using [xaz]) (by omega_using [iaz, hn])]
  · rw [show 4 * (2 * n) = 8 * n by omega] at O₁ O₂ O₃
    exact ((Outs.of_outside O₁ (by simp)).trans (Outs.of_outside O₂ (by simp))).trans
      (Outs.of_outside O₃ (by simp))

end VG.Proof.Weierstrass.Arm
