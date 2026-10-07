import VerifiedGarbage.Proof.Weierstrass.X86.InvSignMask
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath

/-! # One output word of the divstep arithmetic shift -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem shr_word32 (lo hi : BitVec 32) :
    (lo >>> 30 + ((hi + hi) + (hi + hi))).toNat =
      (lo.toNat / 2 ^ 30 + 4 * hi.toNat) % 2 ^ 32 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem shrTail_ok {s : State} {base : Addr} {size dst : Nat}
    (hs : Scr s base size) (hd : dst + 4 ≤ size) :
    WP isa (.block (shrTail dst)) s fun u =>
      w32 u.mem base dst = ((s.gpr .eax).toNat / 2 ^ 30 + 4 * (s.gpr .ebx).toNat) % 2 ^ 32 ∧
      Keeps [.eax, .ebx] s u ∧ Outside base dst 4 s.mem u.mem := by
  have hn := hs.nowrap
  unfold shrTail
  refine wp_shr (by decide) fun s₁ U₁ _ => ?_
  refine wp_addS rfl fun s₂ U₂ _ => ?_
  refine wp_addS rfl fun s₃ U₃ _ => ?_
  refine wp_addS rfl fun s₄ U₄ _ => ?_
  have K : Keeps [.eax, .ebx] s s₄ :=
    (((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
      (U₃.keeps.mono (by decide))).trans (U₄.keeps.mono (by decide))
  have hs₄ := hs.of_keeps K (by decide)
  refine wp_storeS (hs₄.ea (by omega)) (hs₄.write hd) fun u U₅ => WP.block_nil ?_
  refine ⟨?_, K.trans (U₅.keeps _), ?_⟩
  · rw [U₅.mem, w32_write_self, U₄.gpr, U₃.other _ (by decide), U₂.other _ (by decide),
      U₁.gpr, U₃.gpr, U₂.gpr, U₁.other _ (by decide)]
    exact shr_word32 _ _
  · rw [U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]
    exact writeW32_outside _ _ _ (by omega)

theorem shrStep_ok {s : State} {base : Addr} {size dst src j : Nat}
    (hs : Scr s base size) (hd : dst + 4 * j + 4 ≤ size) (ha : src + 4 * (j + 1) + 4 ≤ size) :
    WP isa (.block (shrStep dst src j)) s fun u =>
      w32 u.mem base (dst + 4 * j) =
        (w32 s.mem base (src + 4 * j) / 2 ^ 30 + 4 * w32 s.mem base (src + 4 * (j + 1))) % 2 ^ 32 ∧
      Keeps [.eax, .ebx] s u ∧ Outside base (dst + 4 * j) 4 s.mem u.mem := by
  unfold shrStep
  refine WP.block_append ?_
  refine wp_movS (readSrc_sc hs (by omega)) fun s₁ U₁ _ => ?_
  have hs₁ := hs.of_keeps U₁.keeps (by decide)
  refine wp_movS (readSrc_sc hs₁ ha) fun s₂ U₂ _ => WP.block_nil ?_
  have K : Keeps [.eax, .ebx] s s₂ :=
    (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  refine WP.mono (shrTail_ok (hs.of_keeps K (by decide)) hd) fun u ⟨V, K', O⟩ => ⟨?_, K.trans K', ?_⟩
  · rw [V, U₂.other _ (by decide), U₁.gpr, U₂.gpr, U₁.mem]
  · rw [U₂.mem, U₁.mem] at O
    exact O

end VG.Proof.Weierstrass.X86.Inv
