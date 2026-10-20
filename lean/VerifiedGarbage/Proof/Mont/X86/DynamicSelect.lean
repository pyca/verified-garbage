module

public import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # In-place masked selection for modular exponentiation -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont
open VG.Proof.Mont.X86

/-- `[o] = [tmp]` if `k`, else `[src]`, under the mask `eax` (`k + 1` words). -/
theorem selects_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {src o tmp : Nat} (k : Bool)
    (hm : s.gpr .eax = if k then BitVec.allOnes 32 else 0) :
    ∀ n, src + 4 * n ≤ size → tmp + 4 * n ≤ size → o + 4 * n ≤ size →
    (o = src ∨ o + 4 * n ≤ src ∨ src + 4 * n ≤ o) → (o = tmp ∨ o + 4 * n ≤ tmp ∨ tmp + 4 * n ≤ o) →
    WP isa (.block (selK src o tmp n)) s fun u =>
      Outside base o (4 * n) s.mem u.mem ∧
      val32 u.mem base o n = val32 s.mem base (if k then tmp else src) n ∧
      Keeps [.ebx, .edx] s u
  | 0, _, _, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, rfl, Keeps.refl _ _⟩
  | n + 1, hsrc, htmp, ho, hso, hto => by
    have hn := hs.nowrap
    rw [selK_succ]
    refine WP.block_append (WP.mono (selects_ok hs k hm n (by omega) (by omega) (by omega) (by omega) (by omega))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    refine wp_movS (readSrc_sc hs₁ (d := src + 4 * n) (by omega)) fun s₂ u₂ _ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    refine wp_movS (readSrc_sc hs₂ (d := tmp + 4 * n) (by omega)) fun s₃ u₃ _ => ?_
    have hs₃ := hs₂.of_keeps u₃.keeps (by decide)
    refine wp_logicS (.inr rfl) rfl fun s₄ u₄ => ?_
    refine wp_logicS (.inl rfl) rfl fun s₅ u₅ => ?_
    refine wp_logicS (.inr rfl) rfl fun s₆ u₆ => ?_
    have k₆ : Keeps [.ebx, .edx] s s₆ := (((K₁.widen u₂.keeps).widen u₃.keeps).widen u₄.keeps |>.widen
      u₅.keeps).widen u₆.keeps
    have hs₆ := hs.of_keeps k₆ (by decide)
    refine wp_storeS (hs₆.ea (d := o + 4 * n) (by omega)) (hs₆.write (d := o + 4 * n) (n := 4) (by omega))
      fun s₇ m₇ => WP.block_nil ?_
    have mem₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    have W : Outside base (o + 4 * n) 4 s₁.mem s₇.mem := by
      rw [m₇.mem, mem₆]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨(O₁.mono (o' := o) (n' := 4 * (n + 1)) (Nat.le_refl _) (by omega)).trans
      (W.mono (o' := o) (n' := 4 * (n + 1)) (by omega) (by omega)), ?_,
      k₆.trans (m₇.keeps _)⟩
    have eax₄ : s₄.gpr .eax = s.gpr .eax := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), K₁.1 _ (by decide)]
    have ebx₆ : s₆.gpr .ebx = s₁.mem.readW (off base (src + 4 * n)) 32 ^^^
        ((s₁.mem.readW (off base (tmp + 4 * n)) 32 ^^^ s₁.mem.readW (off base (src + 4 * n)) 32) &&&
          (if k then BitVec.allOnes 32 else 0)) := by
      rw [u₆.gpr, u₅.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₄.gpr, eax₄, hm,
        u₃.other _ (by decide), u₃.gpr, u₂.gpr, u₂.mem]
      rfl
    rw [select_val] at ebx₆
    rw [val32_succ, val32_succ, ← V₁, m₇.mem, mem₆,
      (writeW32_outside s₁.mem base (d := o + 4 * n) (s₆.gpr .ebx) (by omega)).val32 (by omega) (by omega),
      w32_write_self, ebx₆]
    congr 1
    cases k
    · exact congrArg (2 ^ (32 * n) * ·) (O₁.w32 (by omega) (by omega))
    · exact congrArg (2 ^ (32 * n) * ·) (O₁.w32 (by omega) (by omega))

end VG.Proof.Mont.X86.Dynamic
