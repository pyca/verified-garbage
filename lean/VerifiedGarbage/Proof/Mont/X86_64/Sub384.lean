import VerifiedGarbage.Proof.Mont.X86_64.OpsReg

/-!
# P-384 field subtraction on x86-64

The difference of six words, and P-384's `p` masked by its borrow added back,
the mask's words in `rcx`, `rdx`, `rbp` and `rax` (`p384Mask_ok`,
`p384Add_ok`): no temporary memory is written. The inputs may alias the
output.
-/

namespace VG.Proof.Mont.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- Subtraction modulo P-384's `p`. -/
theorem sub384_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hn6 : M.n = 6)
    (hm : m =
      39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319)
    {o a b : Nat} (ho : o + 8 * M.n ≤ size) (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (sub384 o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m := by
  simp only [hn6] at ho ha hb hA hB ⊢
  have hf : Fresh (low 6) := (fresh_top_low (n := 6) (by decide)).tail
  have hl : (low 6).length = 6 := rfl
  have hsub : ∀ r ∈ low 6, r ∈ clob M.n := by rw [hn6]; decide
  have hW : 2 ^ (64 * 6) = 2 ^ 128 * 2 ^ 256 :=
    calc 2 ^ (64 * 6) = 2 ^ (128 + 256) := congrArg (2 ^ ·) rfl
      _ = 2 ^ 128 * 2 ^ 256 := Nat.pow_add 2 128 256
  rw [sub384, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok (low 6) hs (a := a) (by simpa only [hl] using ha) hf)
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (chainSub_ok hs₁ (t := .r8) (ts := [.r9, .r10, .r11, .r12, .r13]) (b := b) hb hf)
    fun s₂ ⟨c, c₂, e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sbbMask_ok s₂ c₂) fun s₃ ⟨x₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (p384Mask_ok s₃ c x₃) fun s₄ ⟨e₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (p384Add_ok s₄ hl hf) fun s₅ ⟨c', _, e₅, k₅⟩ => ?_
  have hs₅ := ((hs₂.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)).of_keeps k₅ (by decide)
  refine WP.mono (stores_ok (low 6) hs₅ (o := o) (by simpa only [hl] using ho) hf.1)
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  rw [hl] at e₁ e₆ O₆
  have hR₄ : regsVal s₄ (low 6) = regsVal s₂ (low 6) := by
    apply regsVal_congr
    intro r hr
    rw [k₄.1 r (by revert r; decide), k₃.1 r (by revert r; decide)]
  rw [hR₄, e₄, ← hm] at e₅
  have hlow : low 6 = [.r8, .r9, .r10, .r11, .r12, .r13] := rfl
  rw [← hlow, hl, e₁, k₁.2.1, hW] at e₂
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx _ => ?_⟩, ?_⟩
  · have hr' : r ∉ low 6 := fun h => hr (hsub r h)
    have h4 : r ∉ [.rcx, .rdx, .rbp] := by
      intro h; apply hr; rw [hn6]
      exact (by decide : ∀ r : Reg, r ∈ [.rcx, .rdx, .rbp] → r ∈ clob 6) r h
    have h3 : r ∉ [.rax] := by
      intro h; apply hr; rw [hn6]
      exact (by decide : ∀ r : Reg, r ∈ [.rax] → r ∈ clob 6) r h
    rw [k₆.gpr r (by simp), k₅.1 r hr', k₄.1 r h4, k₃.1 r h3, k₂.1 r hr', k₁.1 r hr']
  · rw [k₆.rd, k₅.2.2.1, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
  · rw [k₆.wr, k₅.2.2.2, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  · rw [O₆ x (by simpa only [hn6] using hx), k₅.2.1, k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
  · rw [e₆]
    have hR₂ := regsVal_lt s₂ (low 6)
    have hR₅ := regsVal_lt s₅ (low 6)
    rw [hl, hW] at hR₂ hR₅
    subst hm
    cases c <;> cases c' <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero,
      Nat.mul_one, Nat.add_zero, Bool.false_eq_true, ite_false, ite_true] at e₂ e₅ <;> omega

end VG.Proof.Mont.X86_64
