import VerifiedGarbage.Proof.Weierstrass.X86.TCombEntry

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

/-- `o = a` unless `c`, in place: `selPt n o a o`, for `o`'s words apart from
each other and from `a`'s. -/
theorem selPtKeep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (c : Bool)
    (hc : s.gpr .ecx = (if c then BitVec.allOnes 32 else 0)) {n : Nat} {o a : Pt}
    (hin : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z], d + 8 * n ≤ size)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hab : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [a.x, a.y, a.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (selPt n o a o)) s fun s' =>
      wordsVal s'.mem base o.x n = (if c then wordsVal s.mem base o.x n else wordsVal s.mem base a.x n) ∧
      wordsVal s'.mem base o.y n = (if c then wordsVal s.mem base o.y n else wordsVal s.mem base a.y n) ∧
      wordsVal s'.mem base o.z n = (if c then wordsVal s.mem base o.z n else wordsVal s.mem base a.z n) ∧
      KeepRegs [.eax, .edx] s s' ∧
      ∀ x, (ofs base x < o.x ∨ o.x + 8 * n ≤ ofs base x) → (ofs base x < o.y ∨ o.y + 8 * n ≤ ofs base x) →
        (ofs base x < o.z ∨ o.z + 8 * n ≤ ofs base x) → s'.mem x = s.mem x := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hab
  obtain ⟨iox, ioy, ioz, iax, iay, iaz⟩ := hin
  obtain ⟨⟨xax, xay, xaz⟩, ⟨yax, yay, yaz⟩, ⟨zax, zay, zaz⟩⟩ := hab
  obtain ⟨xy, xz, yz⟩ := hoo
  rw [selPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (selWords_ok hs c hc iox iax iox (by omega_using [xax]) (Or.inl (Nat.le_refl _)))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (selWords_ok hs₁ c (by rw [k₁.gpr _ (by decide), hc]) ioy iay ioy (by omega_using [yay])
    (Or.inl (Nat.le_refl _))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (selWords_ok hs₂ c (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hc]) ioz iaz ioz
    (by omega_using [zaz]) (Or.inl (Nat.le_refl _))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, fun x h₁ h₂ h₃ => by rw [O₃ x h₃, O₂ x h₂, O₁ x h₁]⟩
  · rw [O₃.wordsVal (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.wordsVal (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.wordsVal (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.wordsVal (d := o.y) (by omega_using [xy]) (by omega_using [ioy, hn]),
      O₁.wordsVal (d := a.y) (by omega_using [xay]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.wordsVal (d := o.z) (by omega_using [yz]) (by omega_using [ioz, hn]),
      O₂.wordsVal (d := a.z) (by omega_using [yaz]) (by omega_using [iaz, hn]),
      O₁.wordsVal (d := o.z) (by omega_using [xz]) (by omega_using [ioz, hn]),
      O₁.wordsVal (d := a.z) (by omega_using [xaz]) (by omega_using [iaz, hn])]

end VG.Proof.Weierstrass.X86
