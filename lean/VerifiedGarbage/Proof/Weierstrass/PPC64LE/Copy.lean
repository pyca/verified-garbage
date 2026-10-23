module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Mont.PPC64LE.Csub
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Short Weierstrass curves on PPC64LE: copies and selections

`copy k o a` writes `[a]` to `[o]` (`copy_ok`, `k` 64-bit words), `sel k o a
b` writes `[a]` or `[b]` to `[o]` by the mask `r10` (`sel_ok`; `o` may be `a`
or `b`), `selPt` does so for the three coordinates of a point
(`selPt_ok`), as on 32-bit ARM (`Proof/Weierstrass/Arm/Copy.lean`). Each
changes only `[o]` and `r4` (and `r5` for the selections).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE

open VG VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE

/-- `std t, d(r)` with `r` at the working space's base. -/
theorem std0_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {t r : Reg} {d : Nat}
    (hr : At s base r 0) (hr0 : r ≠ .r0) (hd4 : d % 4 = 0) (hd : d + 8 ≤ size) :
    exec (.store .d t r d) s = some { s with mem := s.mem.writeW (off base d) (s.gpr t) } := by
  rw [std_ok hs hr hr0 hd4 (by omega), Nat.zero_add]

/-- A word of `[a]` to `[o]`. -/
theorem copyWord_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {o a : Nat}
    (h3 : At s base .r3 0) (ho4 : o % 4 = 0) (ha4 : a % 4 = 0) (ho : o + 8 ≤ size) (ha : a + 8 ≤ size) :
    WP isa (.block [.load .d .r4 wb a, .store .d .r4 wb o]) s fun u =>
      u.mem = s.mem.writeW (off base o) (word s.mem base a) ∧ Kp [.r4] s u := by
  refine wp_step (ld0_ok hs h3 (by decide) ha4 ha) ?_
  refine wp_step (std0_ok (hs.write _ _) (h3.write _) (by decide) ho4 ho) (WP.block_nil ?_)
  exact ⟨rfl, (Kp.write s _ (by decide)).trans (Kp.store _ _ _)⟩

/-- `[o] = [a]`, for `o` at or below `a` or apart from it. -/
theorem copy_ok {size : Nat} : ∀ (k : Nat) {s : State} {base : Addr} {o a : Nat},
    Ws s base size → At s base .r3 0 → o % 4 = 0 → a % 4 = 0 → o + 8 * k ≤ size → a + 8 * k ≤ size →
    (o ≤ a ∨ a + 8 * k ≤ o) →
    WP isa (.block (copy k o a)) s fun s' =>
      wordsVal s'.mem base o k = wordsVal s.mem base a k ∧ Kp [.r4] s s' ∧
      Outside base o (8 * k) s.mem s'.mem
  | 0, _, _, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨rfl, Kp.refl _ _, Outside.refl _ _ _ _⟩
  | k + 1, s, base, o, a, hs, h3, ho4, ha4, ho, ha, hsep => by
    have hn := hs.nowrap
    rw [copy, show ∀ (x y : Instr) (l : List Instr), [x, y] ++ l = [x, y] ++ l from fun _ _ _ => rfl]
    refine wp_append (WP.mono (copyWord_ok hs h3 ho4 ha4 (by omega) (by omega)) fun s₁ ⟨m₁, K₁⟩ => ?_)
    have O₁ : Outside base o 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (copy_ok k (K₁.ws hs) (K₁.at h3) (o := o + 8) (a := a + 8) (by omega) (by omega)
      (by omega) (by omega) (by omega)) fun s₂ ⟨e₂, K₂, O₂⟩ => ⟨?_, K₁.trans K₂,
        (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rw [wordsVal, wordsVal, O₂.word (by omega) (by omega), e₂, O₁.wordsVal (by omega) (by omega), m₁,
      word_writeW_self]

/-- A word of `[a]` or `[b]` to `[o]` by the mask `r10`. -/
theorem selWord'_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {o a b : Nat}
    (h3 : At s base .r3 0) (ho4 : o % 4 = 0) (ha4 : a % 4 = 0) (hb4 : b % 4 = 0) (ho : o + 8 ≤ size)
    (ha : a + 8 ≤ size) (hb : b + 8 ≤ size) :
    WP isa (.block [.load .d .r4 wb a, .load .d .r5 wb b, .logic .xor .r5 .r5 .r4, .logic .and .r5 .r5 .r10,
      .logic .xor .r4 .r4 .r5, .store .d .r4 wb o]) s fun u =>
      u.mem = s.mem.writeW (off base o) (word s.mem base a ^^^
        ((word s.mem base b ^^^ word s.mem base a) &&& s.gpr .r10)) ∧ Kp [.r4, .r5] s u := by
  refine wp_step (ld0_ok hs h3 (by decide) ha4 ha) ?_
  refine wp_step (ld0_ok (hs.write _ _) (h3.write _) (by decide) hb4 hb) ?_
  refine wp_step exec_logic ?_
  refine wp_step exec_logic ?_
  refine wp_step exec_logic ?_
  refine wp_step (std0_ok ((((hs.write _ _).write _ _).write _ _).write _ _ |>.write _ _)
    (((((h3.write _).write _).write _).write _).write _) (by decide) ho4 ho) (WP.block_nil ?_)
  simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [write_gpr, hr.1, hr.2, ite_false]

/-- `[o] = [b]` if the mask `r10` is all ones (`c`), `[a]` if it is zero; `o`
at or below `a` and `b`, or apart from them. -/
theorem sel_ok {size : Nat} (c : Bool) : ∀ (k : Nat) {s : State} {base : Addr} {o a b : Nat},
    Ws s base size → At s base .r3 0 → s.gpr .r10 = (if c then BitVec.allOnes 64 else 0) →
    o % 4 = 0 → a % 4 = 0 → b % 4 = 0 → o + 8 * k ≤ size → a + 8 * k ≤ size → b + 8 * k ≤ size →
    (o ≤ a ∨ a + 8 * k ≤ o) → (o ≤ b ∨ b + 8 * k ≤ o) →
    WP isa (.block (sel k o a b)) s fun s' =>
      wordsVal s'.mem base o k = (if c then wordsVal s.mem base b k else wordsVal s.mem base a k) ∧
      Kp [.r4, .r5] s s' ∧ Outside base o (8 * k) s.mem s'.mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨by cases c <;> rfl, Kp.refl _ _,
      Outside.refl _ _ _ _⟩
  | k + 1, s, base, o, a, b, hs, h3, hc, ho4, ha4, hb4, ho, ha, hb, hsa, hsb => by
    have hn := hs.nowrap
    rw [sel, show ∀ (x₁ x₂ x₃ x₄ x₅ x₆ : Instr) (l : List Instr), [x₁, x₂, x₃, x₄, x₅, x₆] ++ l =
      [x₁, x₂, x₃, x₄, x₅, x₆] ++ l from fun _ _ _ _ _ _ _ => rfl]
    refine wp_append (WP.mono (selWord'_ok hs h3 ho4 ha4 hb4 (by omega) (by omega) (by omega))
      fun s₁ ⟨m₁, K₁⟩ => ?_)
    have hmk : s.gpr .r10 = 0 ∨ s.gpr .r10 = BitVec.allOnes 64 := by
      cases c
      · exact .inl hc
      · exact .inr hc
    rw [sel_mask _ _ hmk] at m₁
    have O₁ : Outside base o 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (sel_ok c k (K₁.ws hs) (K₁.at h3) (by rw [K₁.g]; exact hc) (o := o + 8) (a := a + 8)
      (b := b + 8) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)) fun s₂ ⟨e₂, K₂, O₂⟩ => ⟨?_, K₁.trans K₂,
        (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    have ea : wordsVal s₁.mem base (a + 8) k = wordsVal s.mem base (a + 8) k :=
      O₁.wordsVal (by omega) (by omega)
    have eb : wordsVal s₁.mem base (b + 8) k = wordsVal s.mem base (b + 8) k :=
      O₁.wordsVal (by omega) (by omega)
    rw [wordsVal, O₂.word (by omega) (by omega), e₂, ea, eb, m₁, word_writeW_self, hc]
    cases c <;> simp [wordsVal]

/-- `o = b` if the mask `r10` is all ones (`c`), `a` if it is zero, for points
whose slots (`n` 64-bit words, at multiples of 4) are in the working space,
with `o`'s apart from each other and from `a`'s and `b`'s. -/
theorem selPt_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    (c : Bool) (hc : s.gpr .r10 = (if c then BitVec.allOnes 64 else 0)) {n : Nat} {o a b : Pt}
    (h4 : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z, b.x, b.y, b.z], d % 4 = 0)
    (hin : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z, b.x, b.y, b.z], d + 8 * n ≤ size)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hab : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [a.x, a.y, a.z, b.x, b.y, b.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (selPt n o a b)) s fun s' =>
      wordsVal s'.mem base o.x n = (if c then wordsVal s.mem base b.x n else wordsVal s.mem base a.x n) ∧
      wordsVal s'.mem base o.y n = (if c then wordsVal s.mem base b.y n else wordsVal s.mem base a.y n) ∧
      wordsVal s'.mem base o.z n = (if c then wordsVal s.mem base b.z n else wordsVal s.mem base a.z n) ∧
      Kp [.r4, .r5] s s' ∧
      Outs base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem s'.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hab h4
  obtain ⟨iox, ioy, ioz, iax, iay, iaz, ibx, iby, ibz⟩ := hin
  obtain ⟨⟨xax, xay, xaz, xbx, xby, xbz⟩, ⟨yax, yay, yaz, ybx, yby, ybz⟩, ⟨zax, zay, zaz, zbx, zby, zbz⟩⟩ := hab
  obtain ⟨xy, xz, yz⟩ := hoo
  obtain ⟨fox, foy, foz, fax, fay, faz, fbx, fby, fbz⟩ := h4
  -- `omega` would split every disjunction of the context: give it the facts it needs.
  rw [selPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sel_ok c n hs h3 hc fox fax fbx (by omega_using [iox]) (by omega_using [iax])
    (by omega_using [ibx]) (by omega_using [xax]) (by omega_using [xbx])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok c n (k₁.ws hs) (k₁.at h3) (by rw [k₁.g, hc]) foy fay fby (by omega_using [ioy])
    (by omega_using [iay]) (by omega_using [iby]) (by omega_using [yay]) (by omega_using [yby]))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  refine WP.mono (sel_ok c n (k₂.ws (k₁.ws hs)) (k₂.at (k₁.at h3)) (by rw [k₂.g, k₁.g, hc]) foz faz fbz
    (by omega_using [ioz]) (by omega_using [iaz]) (by omega_using [ibz]) (by omega_using [zaz])
    (by omega_using [zbz])) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.wordsVal (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.wordsVal (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.wordsVal (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.wordsVal (d := b.y) (by omega_using [xby]) (by omega_using [iby, hn]),
      O₁.wordsVal (d := a.y) (by omega_using [xay]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.wordsVal (d := b.z) (by omega_using [ybz]) (by omega_using [ibz, hn]),
      O₂.wordsVal (d := a.z) (by omega_using [yaz]) (by omega_using [iaz, hn]),
      O₁.wordsVal (d := b.z) (by omega_using [xbz]) (by omega_using [ibz, hn]),
      O₁.wordsVal (d := a.z) (by omega_using [xaz]) (by omega_using [iaz, hn])]
  · exact ((Outs.of_outside O₁ (by simp)).trans (Outs.of_outside O₂ (by simp))).trans
      (Outs.of_outside O₃ (by simp))

end VG.Proof.Weierstrass.PPC64LE
