module
public import VerifiedGarbage.Proof.Mont.Words

import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Exact header writes for the factor-product loop controls -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

def crtProductMem (m : Mem) (base : Addr) (p q prod cmp pad : BitVec 32) : Mem :=
  ((((m.writeW (off base 128) p).writeW (off base 132) q).writeW (off base 136) prod).writeW
    (off base 140) cmp).writeW (off base 144) pad

theorem crtProductMem_ok (m : Mem) (base : Addr) (p q prod cmp pad : BitVec 32) :
    let m' := crtProductMem m base p q prod cmp pad
    m'.readW (off base 128) 32 = p ∧ m'.readW (off base 132) 32 = q ∧
    m'.readW (off base 136) 32 = prod ∧ m'.readW (off base 140) 32 = cmp ∧
    m'.readW (off base 144) 32 = pad ∧ Outside base 128 20 m m' := by
  let m1 := m.writeW (off base 128) p
  let m2 := m1.writeW (off base 132) q
  let m3 := m2.writeW (off base 136) prod
  let m4 := m3.writeW (off base 140) cmp
  have a := writeW32_outside m base (d := 128) p (by decide)
  have b := writeW32_outside m1 base (d := 132) q (by decide)
  have c := writeW32_outside m2 base (d := 136) prod (by decide)
  have d := writeW32_outside m3 base (d := 140) cmp (by decide)
  have e := writeW32_outside m4 base (d := 144) pad (by decide)
  change (m4.writeW (off base 144) pad).readW (off base 128) 32 = p ∧ _
  refine ⟨?_, ?_, ?_, ?_, Mem.readW_writeW_self32 _ _ _, ?_⟩
  · rw [outside_read32 e (d := 128) (by decide) (by decide),
      outside_read32 d (d := 128) (by decide) (by decide),
      outside_read32 c (d := 128) (by decide) (by decide),
      outside_read32 b (d := 128) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · change (m4.writeW (off base 144) pad).readW (off base 132) 32 = _
    rw [outside_read32 e (d := 132) (by decide) (by decide),
      outside_read32 d (d := 132) (by decide) (by decide),
      outside_read32 c (d := 132) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · change (m4.writeW (off base 144) pad).readW (off base 136) 32 = _
    rw [outside_read32 e (d := 136) (by decide) (by decide), outside_read32 d (d := 136) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · change (m4.writeW (off base 144) pad).readW (off base 140) 32 = _
    rw [outside_read32 e (d := 140) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · exact (a.mono (by decide) (by decide)).trans ((b.mono (by decide) (by decide)).trans
      ((c.mono (by decide) (by decide)).trans ((d.mono (by decide) (by decide)).trans (e.mono (by decide) (by decide)))))

end VG.Proof.Bignum.Arm
