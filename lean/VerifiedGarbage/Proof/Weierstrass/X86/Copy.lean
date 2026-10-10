import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Short Weierstrass curves on x86 (32-bit): copies, selections and constants

`copy k o a` writes `[a]` to `[o]` (`copy_ok`, `k` 32-bit words), `sel k o a
b` writes `[a]` or `[b]` to `[o]` by the mask `ecx` (`sel_ok`; `o` may be `a`
or `b`), `selPt` does so for the three coordinates of a point
(`selPt_ok`), and `setConst n o x` writes `x` (`setConst_ok`). Each changes
only `[o]` and `eax` (and `edx` for the selections), and keeps the regions.
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont

/-- `[o] = [a]`, for `o` at or below `a` or apart from it. -/
theorem copy_ok {size : Nat} : ∀ (k : Nat) {s : State} {base : Addr} {o a : Nat},
    Scr s base size → o + 4 * k ≤ size → a + 4 * k ≤ size → (o ≤ a ∨ a + 4 * k ≤ o) →
    WP isa (.block (copy k o a)) s fun s' =>
      val32 s'.mem base o k = val32 s.mem base a k ∧ Keeps [.eax] s s' ∧
      Outside base o (4 * k) s.mem s'.mem
  | 0, _, _, _, _, _, _, _, _ => WP.block_nil ⟨rfl, Keeps.refl _ _, VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, s, base, o, a, hs, ho, ha, hsep => by
    have hn := hs.nowrap
    rw [copy, List.cons_append, List.cons_append, List.nil_append]
    refine wp_movS (readSrc_sc hs (d := a) (by omega_arith)) fun s₁ u₁ _ => ?_
    have hs₁ := hs.of_keeps u₁.keeps (by decide)
    refine wp_storeS (hs₁.ea (d := o) (by omega_arith)) (hs₁.write (d := o) (n := 4) (by omega_arith)) fun s₂ m₂ => ?_
    have k₂ : Keeps [.eax] s s₂ := u₁.keeps.trans (m₂.keeps _)
    have hs₂ := hs.of_keeps k₂ (by decide)
    have O₂ : Outside base o 4 s.mem s₂.mem := by
      rw [m₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega_arith)
    refine WP.mono (copy_ok k hs₂ (o := o + 4) (a := a + 4) (by omega_arith) (by omega_arith) (by omega_arith))
      fun s₃ ⟨e₃, k₃, O₃⟩ => ⟨?_, k₂.trans k₃, (O₂.mono (Nat.le_refl _) (by omega_arith)).trans
        (O₃.mono (by omega_arith) (by omega_arith))⟩
    rw [val32, val32, O₃.w32 (by omega_arith) (by omega_arith), e₃, O₂.val32 (by omega_arith) (by omega_arith), m₂.mem,
      w32_write_self, u₁.gpr]

/-- `[o] = [b]` if the mask `ecx` is all ones (`c`), `[a]` if it is zero; `o`
at or below `a` and `b`, or apart from them. -/
theorem sel_ok {size : Nat} (c : Bool) : ∀ (k : Nat) {s : State} {base : Addr} {o a b : Nat},
    Scr s base size → s.gpr .ecx = (if c then BitVec.allOnes 32 else 0) →
    o + 4 * k ≤ size → a + 4 * k ≤ size → b + 4 * k ≤ size →
    (o ≤ a ∨ a + 4 * k ≤ o) → (o ≤ b ∨ b + 4 * k ≤ o) →
    WP isa (.block (sel k o a b)) s fun s' =>
      val32 s'.mem base o k = (if c then val32 s.mem base b k else val32 s.mem base a k) ∧
      Keeps [.eax, .edx] s s' ∧ Outside base o (4 * k) s.mem s'.mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨by cases c <;> rfl, Keeps.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, s, base, o, a, b, hs, hc, ho, ha, hb, hsa, hsb => by
    have hn := hs.nowrap
    rw [sel]
    simp only [List.cons_append, List.nil_append]
    refine wp_movS (readSrc_sc hs (d := a) (by omega_arith)) fun s₁ u₁ _ => ?_
    have hs₁ := hs.of_keeps u₁.keeps (by decide)
    refine wp_movS (readSrc_sc hs₁ (d := b) (by omega_arith)) fun s₂ u₂ _ => ?_
    refine wp_logicS (.inr rfl) rfl fun s₃ u₃ => ?_
    refine wp_logicS (.inl rfl) rfl fun s₄ u₄ => ?_
    refine wp_logicS (.inr rfl) rfl fun s₅ u₅ => ?_
    have k₅ : Keeps [.eax, .edx] s s₅ :=
      ((((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen u₄.keeps).widen u₅.keeps
    have hs₅ := hs.of_keeps k₅ (by decide)
    refine wp_storeS (hs₅.ea (d := o) (by omega_arith)) (hs₅.write (d := o) (n := 4) (by omega_arith)) fun s₆ m₆ => ?_
    have k₆ : Keeps [.eax, .edx] s s₆ := k₅.trans (m₆.keeps _)
    have hs₆ := hs.of_keeps k₆ (by decide)
    have mem₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    have O₆ : Outside base o 4 s.mem s₆.mem := by
      rw [m₆.mem, mem₅]; exact writeW32_outside _ _ _ (by omega_arith)
    have a2 : s₂.gpr .eax = s.mem.readW (off base a) 32 := by rw [u₂.other _ (by decide), u₁.gpr]
    have d2 : s₂.gpr .edx = s.mem.readW (off base b) 32 := by rw [u₂.gpr, u₁.mem]
    have c2 : s₂.gpr .ecx = s.gpr .ecx := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
    have d3 : s₃.gpr .edx = s.mem.readW (off base b) 32 ^^^ s.mem.readW (off base a) 32 := by
      rw [u₃.gpr, d2, a2]; simp only [reduceCtorEq, ite_false]
    have d4 : s₄.gpr .edx = (s.mem.readW (off base b) 32 ^^^ s.mem.readW (off base a) 32) &&&
        (if c then BitVec.allOnes 32 else 0) := by
      rw [u₄.gpr, d3, u₃.other _ (by decide), c2, hc]; simp only [ite_true]
    have eax₅ : s₅.gpr .eax = s.mem.readW (off base a) 32 ^^^
        ((s.mem.readW (off base b) 32 ^^^ s.mem.readW (off base a) 32) &&&
          (if c then BitVec.allOnes 32 else 0)) := by
      rw [u₅.gpr, d4, u₄.other _ (by decide), u₃.other _ (by decide), a2]; simp only [reduceCtorEq, ite_false]
    rw [select_val] at eax₅
    refine WP.mono (sel_ok c k hs₆ (o := o + 4) (a := a + 4) (b := b + 4)
      (by rw [k₆.1 _ (by decide), hc]) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
      fun s₇ ⟨e₇, k₇, O₇⟩ => ⟨?_, k₆.trans k₇, (O₆.mono (Nat.le_refl _) (by omega_arith)).trans
        (O₇.mono (by omega_arith) (by omega_arith))⟩
    have hw : w32 s₆.mem base o = (if c then s.mem.readW (off base b) 32 else s.mem.readW (off base a) 32).toNat := by
      rw [m₆.mem, mem₅, w32_write_self, eax₅]
    have ha' : val32 s₆.mem base (a + 4) k = val32 s.mem base (a + 4) k := O₆.val32 (by omega_arith) (by omega_arith)
    have hb' : val32 s₆.mem base (b + 4) k = val32 s.mem base (b + 4) k := O₆.val32 (by omega_arith) (by omega_arith)
    rw [val32, O₇.w32 (by omega_arith) (by omega_arith), e₇, hw, ha', hb']
    cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true, val32]

/-- `o = b` if the mask `ecx` is all ones (`c`), `a` if it is zero, for points
whose slots (`n` 64-bit words) are in the working space, with `o`'s apart
from each other and from `a`'s and `b`'s. -/
theorem selPt_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (c : Bool)
    (hc : s.gpr .ecx = (if c then BitVec.allOnes 32 else 0)) {n : Nat} {o a b : Pt}
    (hin : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z, b.x, b.y, b.z], d + 8 * n ≤ size)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hab : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [a.x, a.y, a.z, b.x, b.y, b.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (selPt n o a b)) s fun s' =>
      wordsVal s'.mem base o.x n = (if c then wordsVal s.mem base b.x n else wordsVal s.mem base a.x n) ∧
      wordsVal s'.mem base o.y n = (if c then wordsVal s.mem base b.y n else wordsVal s.mem base a.y n) ∧
      wordsVal s'.mem base o.z n = (if c then wordsVal s.mem base b.z n else wordsVal s.mem base a.z n) ∧
      Keeps [.eax, .edx] s s' ∧
      Outs base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem s'.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hab
  obtain ⟨iox, ioy, ioz, iax, iay, iaz, ibx, iby, ibz⟩ := hin
  obtain ⟨⟨xax, xay, xaz, xbx, xby, xbz⟩, ⟨yax, yay, yaz, ybx, yby, ybz⟩, ⟨zax, zay, zaz, zbx, zby, zbz⟩⟩ := hab
  obtain ⟨xy, xz, yz⟩ := hoo
  simp only [wordsVal_eq_val32]
  -- `omega_arith` would split every disjunction of the context: give it the facts it needs.
  rw [selPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sel_ok c (2 * n) hs hc (by omega_using [iox]) (by omega_using [iax]) (by omega_using [ibx])
    (by omega_using [xax]) (by omega_using [xbx])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok c (2 * n) hs₁ (by rw [k₁.1 _ (by decide), hc]) (by omega_using [ioy])
    (by omega_using [iay]) (by omega_using [iby]) (by omega_using [yay]) (by omega_using [yby]))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (sel_ok c (2 * n) hs₂ (by rw [k₂.1 _ (by decide), k₁.1 _ (by decide), hc])
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
  · rw [show 4 * (2 * n) = 8 * n by omega_arith] at O₁ O₂ O₃
    exact ((Outs.of_outside O₁ (by simp)).trans (Outs.of_outside O₂ (by simp))).trans
      (Outs.of_outside O₃ (by simp))

/-! ## Constants -/

/-- The words of `x`, word by word, are `x`. -/
theorem val32_of_shifts (m : Mem) (base : Addr) : ∀ (o k x : Nat), x < 2 ^ (32 * k) →
    (∀ j < k, w32 m base (o + 4 * j) = (x >>> (32 * j)) % 2 ^ 32) → val32 m base o k = x
  | _, 0, x, hx, _ => by simp only [Nat.mul_zero, Nat.pow_zero] at hx; simp only [val32]; omega_arith
  | o, k + 1, x, hx, h => by
    have h0 := h 0 (by omega_arith)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.shiftRight_zero] at h0
    have hr := val32_of_shifts m base (o + 4) k (x >>> 32) (by
        rw [Nat.shiftRight_eq_div_pow]
        rw [pow32_succ] at hx
        exact Nat.div_lt_of_lt_mul hx) fun j hj => by
      rw [show o + 4 + 4 * j = o + 4 * (j + 1) by omega_arith, h (j + 1) (by omega_arith), ← Nat.shiftRight_add,
        show 32 + 32 * j = 32 * (j + 1) by omega_arith]
    rw [val32, hr, h0, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_add_div x _

/-- One word of `setConst`. -/
def constStep (o x j : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 (x >>> (32 * j)))), .store (sc (o + 4 * j)) .eax]

theorem setConst_eq (n o x : Nat) : setConst n o x = (List.range (2 * n)).flatMap (constStep o x) := rfl

theorem constSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o x : Nat} :
    ∀ k, o + 4 * k ≤ size →
    WP isa (.block ((List.range k).flatMap (constStep o x))) s fun s' =>
      (∀ j < k, w32 s'.mem base (o + 4 * j) = (x >>> (32 * j)) % 2 ^ 32) ∧
      Keeps [.eax] s s' ∧ Outside base o (4 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Keeps.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (constSteps_ok hs k (by omega_arith)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    have hs₁ := hs.of_keeps k₁ (by decide)
    rw [constStep]
    refine wp_movS rfl fun s₂ u₂ _ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    refine wp_storeS (hs₂.ea (d := o + 4 * k) (by omega_arith)) (hs₂.write (d := o + 4 * k) (n := 4) (by omega_arith))
      fun s₃ m₃ => WP.block_nil ?_
    have O₂ : Outside base (o + 4 * k) 4 s₁.mem s₃.mem := by
      rw [m₃.mem, u₂.mem]; exact writeW32_outside _ _ _ (by omega_arith)
    refine ⟨fun j hj => ?_, (k₁.trans u₂.keeps).trans (m₃.keeps _),
      (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.w32 (by omega_arith) (by omega_arith), e₁ j h]
    · obtain rfl : j = k := by omega_arith
      rw [m₃.mem, u₂.mem, w32_write_self, u₂.gpr, BitVec.toNat_ofNat]

/-- `[o] = x`. -/
theorem setConst_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o x : Nat}
    (ho : o + 8 * n ≤ size) (hx : x < 2 ^ (64 * n)) :
    WP isa (.block (setConst n o x)) s fun s' =>
      wordsVal s'.mem base o n = x ∧ Keeps [.eax] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [setConst_eq]
  refine WP.mono (constSteps_ok hs (2 * n) (by omega_arith)) fun s' ⟨e, k, O⟩ =>
    ⟨?_, k, by rw [show 8 * n = 4 * (2 * n) by omega_arith]; exact O⟩
  rw [wordsVal_eq_val32]
  exact val32_of_shifts _ _ o (2 * n) x (by rw [show 32 * (2 * n) = 64 * n by omega_arith]; exact hx) e

end VG.Proof.Weierstrass.X86
