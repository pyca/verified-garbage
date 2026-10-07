import VerifiedGarbage.Proof.Weierstrass.X86.InvStep

/-! # A pair of divstep words in the working space -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem pairShift_ok (s : State) (matrix : Bool) :
    WP isa (.block (if matrix then [.alu .add .ebx (.reg .ebx)] else [.shift .shr .eax 1])) s fun u =>
      u.gpr .ebx = (if matrix then s.gpr .ebx + s.gpr .ebx else s.gpr .ebx) ∧
      u.gpr .eax = (if matrix then s.gpr .eax else s.gpr .eax >>> 1) ∧
      Keeps [.eax, .ebx] s u ∧ u.mem = s.mem := by
  cases matrix with
  | false =>
    exact wp_shr (by decide) fun u U _ => WP.block_nil
      ⟨U.other _ (by decide), U.gpr, U.keeps.mono (by decide), U.mem⟩
  | true =>
    exact wp_addS rfl fun u U _ => WP.block_nil
      ⟨U.gpr, U.other _ (by decide), U.keeps.mono (by decide), U.mem⟩

theorem storePair_ok {s : State} {base : Addr} {size left right : Nat} (hs : Scr s base size)
    (hl : left + 4 ≤ size) (hr : right + 4 ≤ size) (sep : left + 4 ≤ right ∨ right + 4 ≤ left) :
    WP isa (.block [.store (sc left) .ebx, .store (sc right) .eax]) s fun u =>
      u.mem.readW (off base left) 32 = s.gpr .ebx ∧
      u.mem.readW (off base right) 32 = s.gpr .eax ∧
      Keeps [] s u ∧ Unch base [(left, 4), (right, 4)] s.mem u.mem := by
  have hn := hs.nowrap
  refine wp_storeS (hs.ea (by omega)) (hs.write hl) fun s₁ U₁ => ?_
  have hs₁ := hs.of_keeps (U₁.keeps []) (by decide)
  refine wp_storeS (hs₁.ea (by omega)) (hs₁.write hr) fun u U₂ => WP.block_nil ?_
  refine ⟨?_, ?_, (U₁.keeps []).trans (U₂.keeps []), ?_⟩
  · apply BitVec.eq_of_toNat_eq
    change w32 u.mem base left = _
    rw [U₂.mem, w32_write_ne hn hr hl sep, U₁.mem, w32_write_self]
  · apply BitVec.eq_of_toNat_eq
    change w32 u.mem base right = _
    rw [U₂.mem, w32_write_self, U₁.gpr]
  · have O₁ := writeW32_outside s.mem base (d := left) (s.gpr .ebx) (by omega)
    have O₂ := writeW32_outside s₁.mem base (d := right) (s₁.gpr .eax) (by omega)
    intro x hx
    rw [U₂.mem, O₂ x (hx (right, 4) (by simp)), U₁.mem, O₁ x (hx (left, 4) (by simp))]

theorem pair_ok {s : State} {base : Addr} {size left right : Nat} (hs : Scr s base size)
    (hl : left + 4 ≤ size) (hr : right + 4 ≤ size) (sep : left + 4 ≤ right ∨ right + 4 ≤ left)
    (matrix : Bool) :
    let L := s.mem.readW (off base left) 32
    let R := pairRight L (s.mem.readW (off base right) 32) (s.gpr .ecx) (s.gpr .edx)
    let F := L + (R &&& s.gpr .edx)
    WP isa (.block (pair left right matrix)) s fun u =>
      u.mem.readW (off base left) 32 = (if matrix then F + F else F) ∧
      u.mem.readW (off base right) 32 = (if matrix then R else R >>> 1) ∧
      Keeps [.eax, .ebx, .ebp] s u ∧ Unch base [(left, 4), (right, 4)] s.mem u.mem := by
  dsimp only
  unfold pair
  refine WP.block_append (WP.block_append (WP.block_append ?_))
  refine wp_movS (readSrc_sc hs hl) fun s₁ U₁ _ => ?_
  have hs₁ := hs.of_keeps U₁.keeps (by decide)
  refine wp_movS (readSrc_sc hs₁ hr) fun s₂ U₂ _ => WP.block_nil ?_
  have K₀ : Keeps [.eax, .ebx, .ebp] s s₂ :=
    (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  have M₀ : s₂.mem = s.mem := U₂.mem.trans U₁.mem
  refine WP.mono (pairRegs_ok s₂) fun s₃ ⟨R₃, L₃, K₃, M₃⟩ => ?_
  have hs₃ := ((hs.of_keeps K₀ (by decide)).of_keeps K₃ (by decide))
  refine WP.mono (pairShift_ok s₃ matrix) fun s₄ ⟨L₄, R₄, K₄, M₄⟩ => ?_
  refine WP.mono (storePair_ok (hs₃.of_keeps K₄ (by decide)) hl hr sep) fun u ⟨L, R, K, U⟩ => ?_
  refine ⟨?_, ?_, ((K₀.trans K₃).trans (K₄.mono (by decide))).trans (K.mono (by decide)), ?_⟩
  · rw [L, L₄, L₃, U₂.other _ (by decide), U₁.gpr, U₂.gpr, U₁.mem,
      K₀.1 .ecx (by decide), K₀.1 .edx (by decide)]
  · rw [R, R₄, R₃, U₂.other _ (by decide), U₁.gpr, U₂.gpr, U₁.mem,
      K₀.1 .ecx (by decide), K₀.1 .edx (by decide)]
  · intro x hx
    rw [U x hx, M₄, M₃, M₀]

end VG.Proof.Weierstrass.X86.Inv
