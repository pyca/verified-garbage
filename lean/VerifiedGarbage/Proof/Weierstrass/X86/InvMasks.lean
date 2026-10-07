import VerifiedGarbage.Proof.Weierstrass.X86.InvPair

/-! # The odd/swap masks and delta of a word divstep -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem masks_ok {s : State} {base : Addr} {size t : Nat} (hs : Scr s base size)
    (ht : t + 12 ≤ size) :
    let D := s.mem.readW (off base t) 32
    let G := s.mem.readW (off base (t + 8)) 32
    WP isa (.block (masks t)) s fun u =>
      u.gpr .ecx = oddMask G ∧ u.gpr .edx = swapMask D G ∧
      u.mem.readW (off base t) 32 = nextDelta D G ∧
      Keeps [.eax, .ebx, .ecx, .edx] s u ∧ Outside base t 4 s.mem u.mem := by
  dsimp only
  have hn := hs.nowrap
  unfold masks
  refine WP.block_append (WP.block_append ?_)
  refine wp_movS (readSrc_sc hs (by omega)) fun s₁ U₁ _ => ?_
  have hs₁ := hs.of_keeps U₁.keeps (by decide)
  refine wp_movS (readSrc_sc hs₁ (by omega)) fun s₂ U₂ _ => WP.block_nil ?_
  have K₀ : Keeps [.eax, .ebx, .ecx, .edx] s s₂ :=
    (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  have M₀ : s₂.mem = s.mem := U₂.mem.trans U₁.mem
  refine WP.mono (maskRegs_ok s₂) fun s₃ ⟨C, D, A, K, M⟩ => ?_
  have hs₃ := (hs.of_keeps K₀ (by decide)).of_keeps K (by decide)
  refine wp_storeS (hs₃.ea (by omega)) (hs₃.write (by omega)) fun u U => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, (K₀.trans K).trans (U.keeps _), ?_⟩
  · rw [U.gpr, C, U₂.other _ (by decide), U₁.gpr]
  · rw [U.gpr, D, U₂.gpr, U₁.mem, U₂.other _ (by decide), U₁.gpr]
  · apply BitVec.eq_of_toNat_eq
    change w32 u.mem base t = _
    rw [U.mem, w32_write_self, A, U₂.gpr, U₁.mem, U₂.other _ (by decide), U₁.gpr]
  · rw [U.mem, M, M₀]
    exact writeW32_outside _ _ _ (by omega)

end VG.Proof.Weierstrass.X86.Inv
