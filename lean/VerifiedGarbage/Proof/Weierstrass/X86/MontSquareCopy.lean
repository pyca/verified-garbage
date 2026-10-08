import VerifiedGarbage.Proof.Weierstrass.X86.MontBase
import VerifiedGarbage.Impl.Weierstrass.X86.MontSquare

/-! # Copying a square's operand into the existing Montgomery temporary area -/
namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

variable {s : State} {base : Addr}

theorem squareCopy_ok (hb : Bx s base 8192) {a : Nat} (hp : Ptr s .esi a)
    (ha : a + 32 ≤ own 4) : ∀ j, j ≤ 8 →
    WP isa (.block (squareCopy j)) s fun u =>
      Outside base (tmpAt 4) (4 * j) s.mem u.mem ∧ Keeps [.eax] s u ∧
      ∀ i < j, w32 u.mem base (tmpAt 4 + 4 * i) = w32 s.mem base (a + 4 * i)
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, Keeps.refl _ _, by omega⟩
  | j + 1, hj => by
    have hn := hb.nowrap
    have htmp : tmpAt 4 = 3908 := rfl
    have hown : own 4 = 3840 := rfl
    rw [squareCopy]
    refine WP.block_append (WP.mono (squareCopy_ok hb hp ha j (by omega)) fun t ⟨O, K, V⟩ => ?_)
    have hbt := hb.of_keeps K (by decide)
    have hpt := hp.of_keeps K (by decide) (by decide)
    refine wp_movS (readSrc_ptr hbt hpt (d := 4 * j) (by omega)) fun v R _ => ?_
    have hbv := hbt.of_keeps R.keeps (by decide)
    refine wp_storeS (hbv.ea (d := tmpAt 4 + 4 * j) (by omega)) (hbv.write (n := 4) (by omega))
      fun u M => WP.block_nil ?_
    have hm : u.mem = t.mem.writeW (off base (tmpAt 4 + 4 * j))
        (t.mem.readW (off base (a + 4 * j)) 32) := by rw [M.mem, R.mem, R.gpr]
    have U := writeW32_outside t.mem base (d := tmpAt 4 + 4 * j)
      (t.mem.readW (off base (a + 4 * j)) 32) (by omega)
    rw [← hm] at U
    refine ⟨(O.mono (Nat.le_refl _) (by omega)).trans (U.mono (by omega) (by omega)),
      (K.trans R.keeps).trans (M.keeps _), ?_⟩
    intro i hi
    by_cases hij : i = j
    · subst i
      rw [hm, w32_write_self]
      exact O.w32 (by omega) (by omega)
    · rw [U.w32 (by omega) (by omega)]
      exact V i (by omega)

end VG.Proof.Weierstrass.X86.Mont
