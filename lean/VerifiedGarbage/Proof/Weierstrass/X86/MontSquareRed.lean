import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Impl.Weierstrass.X86.Mont

/-! # Sparse Montgomery reduction of a full-width x86 square -/
namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem square_clear_ok {s : State} {base : Addr} {size : Nat} (hb : Bx s base size)
    {acc w extra : Nat}
    (hw : acc = w) (hsz : w + (4 * (10 + extra)) ≤ size) :
    WP isa (.block [.mov .eax (.imm 0), .store { base := .ebp, disp := acc } .eax]) s fun u =>
      Outside base w (4 * (10 + extra)) s.mem u.mem ∧
      val32 u.mem base w (10 + extra) + w32 s.mem base w = val32 s.mem base w (10 + extra) ∧ Keeps [.eax] s u := by
  have hn := hb.nowrap
  refine wp_movS rfl fun s₁ u₁ _ => ?_
  have hb₁ := hb.of_keeps u₁.keeps (by decide)
  refine wp_storeS (hb₁.ea (d := acc) (by omega_arith)) (hb₁.write (n := 4) (by omega_arith))
    fun u m => WP.block_nil ?_
  have hm : u.mem = s.mem.writeW (off base w) (0 : BitVec 32) := by rw [m.mem, u₁.mem, u₁.gpr, hw]
  have O := writeW32_outside s.mem base (d := w) (0 : BitVec 32) (by omega_arith)
  rw [← hm] at O
  refine ⟨O.mono (Nat.le_refl _) (by omega_arith), ?_, u₁.keeps.trans (m.keeps _)⟩
  rw [show 10 + extra = (9 + extra) + 1 by omega_arith]
  change w32 u.mem base w + 2 ^ 32 * val32 u.mem base (w + 4) (9 + extra) + _ =
    w32 s.mem base w + 2 ^ 32 * val32 s.mem base (w + 4) (9 + extra)
  rw [O.val32 (by omega_arith) (by omega_arith), hm, w32_write_self]
  change 0 + _ + _ = _
  omega_arith

theorem square_positive_ok {s : State} {base : Addr} {size : Nat} (hb : Bx s base size)
    {w extra : Nat} (he : extra ≤ 7) (hsz : w + 4 * (10 + extra) ≤ size) :
    WP isa (.block (multiChain (w + 12) positiveMask (7 + extra))) s fun u =>
      Outside base w (4 * (10 + extra)) s.mem u.mem ∧
      (∃ c : Bool, val32 u.mem base w (10 + extra) + 2 ^ (32 * (10 + extra)) * c.toNat =
        val32 s.mem base w (10 + extra) + (s.gpr .ecx).toNat *
          (2 ^ 96 + 2 ^ 192 + 2 ^ 256)) ∧ Keeps [.eax] s u := by
  have hn := hb.nowrap
  have hlen : 7 + extra = (6 + extra) + 1 := by omega_arith
  rw [hlen]
  refine WP.mono (multiChainB_ok hb rfl positiveMask (6 + extra) (by omega_arith))
    fun u ⟨O, ⟨c, _, V⟩, K⟩ => ⟨O.mono (by omega_arith) (by omega_arith), ⟨c, ?_⟩, K⟩
  have hv : multiWeight positiveMask ((6 + extra) + 1) = 1 + 2 ^ 96 + 2 ^ 160 := by
    have h : ∀ e < 8, multiWeight positiveMask ((6 + e) + 1) = 1 + 2 ^ 96 + 2 ^ 160 := by decide +kernel
    exact h extra (by omega_arith)
  rw [hv] at V
  have heq : 10 + extra = 3 + ((6 + extra) + 1) := by omega_arith
  rw [heq, val32_append u.mem base w 3 _, val32_append s.mem base w 3 _,
    O.val32 (d := w) (k := 3) (by omega_arith) (by omega_arith)]
  rcases (show extra = 0 ∨ extra = 1 ∨ extra = 2 ∨ extra = 3 ∨ extra = 4 ∨ extra = 5 ∨ extra = 6 ∨ extra = 7 by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reduceAdd, Nat.reduceMul] at V ⊢ <;> omega_arith

theorem squareRed_ok {s : State} {base : Addr} {size : Nat} (hb : Bx s base size)
    {w extra : Nat} (he : extra ≤ 7) (hsz : w + 4 * (10 + extra) ≤ size)
    (hq : (s.gpr .ecx).toNat = w32 s.mem base w)
    (hlt : val32 s.mem base w (10 + extra) + (s.gpr .ecx).toNat *
      (2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1) < 2 ^ (32 * (10 + extra))) :
    WP isa (.block (squareRed w extra)) s fun u =>
      Outside base w (4 * (10 + extra)) s.mem u.mem ∧
      val32 u.mem base w (10 + extra) = val32 s.mem base w (10 + extra) +
        (s.gpr .ecx).toNat * (2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1) ∧ Keeps [.eax] s u := by
  simp only [squareRed, List.append_assoc]
  refine WP.block_append (WP.mono (square_clear_ok hb rfl hsz) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have hb₁ := hb.of_keeps K₁ (by decide)
  refine WP.block_append (WP.mono (square_positive_ok hb₁ he hsz)
    fun s₂ ⟨O₂, ⟨c₂, V₂⟩, K₂⟩ => ?_)
  have hb₂ := hb₁.of_keeps K₂ (by decide)
  have hlen : 3 + extra = (2 + extra) + 1 := by omega_arith
  rw [hlen]
  refine WP.mono (sparseShiftSubB_ok hb₂ rfl (N := 10 + extra) (j := 7) (k := 2 + extra) (by omega_arith) hsz)
    fun u ⟨O₃, ⟨c₃, V₃⟩, K₃⟩ => ⟨(O₁.trans O₂).trans O₃, ?_, (K₁.trans K₂).trans K₃⟩
  rw [K₁.1 .ecx (by decide)] at V₂
  rw [K₂.1 .ecx (by decide), K₁.1 .ecx (by decide)] at V₃
  have hu := val32_lt u.mem base w (10 + extra)
  rcases (show extra = 0 ∨ extra = 1 ∨ extra = 2 ∨ extra = 3 ∨ extra = 4 ∨ extra = 5 ∨ extra = 6 ∨ extra = 7 by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reduceAdd, Nat.reduceMul] at V₁ V₂ V₃ hu hlt ⊢ <;> omega_arith

end VG.Proof.Weierstrass.X86.Mont
