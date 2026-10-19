module
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Mont.Words

import VerifiedGarbage.Proof.Bignum.Arm.Workspace

/-! # Exact header writes for the five CRT buffer links -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

def crtLinkMem (m : Mem) (base : Addr) (p q prod cmp pad : BitVec 32) : Mem :=
  ((((m.writeW (off base 224) p).writeW (off base 228) q).writeW (off base 232) prod).writeW
    (off base 236) cmp).writeW (off base 240) pad

theorem crtLinkMem_ok (m : Mem) (base : Addr) (p q prod cmp pad : BitVec 32) :
    let m' := crtLinkMem m base p q prod cmp pad
    m'.readW (off base 224) 32 = p ∧ m'.readW (off base 228) 32 = q ∧
    m'.readW (off base 232) 32 = prod ∧ m'.readW (off base 236) 32 = cmp ∧
    m'.readW (off base 240) 32 = pad ∧ Outside base 224 20 m m' := by
  let m1 := m.writeW (off base 224) p
  let m2 := m1.writeW (off base 228) q
  let m3 := m2.writeW (off base 232) prod
  let m4 := m3.writeW (off base 236) cmp
  have a := writeW32_outside m base (d := 224) p (by decide)
  have b := writeW32_outside m1 base (d := 228) q (by decide)
  have c := writeW32_outside m2 base (d := 232) prod (by decide)
  have d := writeW32_outside m3 base (d := 236) cmp (by decide)
  have e := writeW32_outside m4 base (d := 240) pad (by decide)
  change (m4.writeW (off base 240) pad).readW (off base 224) 32 = p ∧ _
  refine ⟨?_, ?_, ?_, ?_, Mem.readW_writeW_self32 _ _ _, ?_⟩
  · rw [outside_read32 e (d := 224) (by decide) (by decide),
      outside_read32 d (d := 224) (by decide) (by decide),
      outside_read32 c (d := 224) (by decide) (by decide),
      outside_read32 b (d := 224) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · change (m4.writeW (off base 240) pad).readW (off base 228) 32 = _
    rw [outside_read32 e (d := 228) (by decide) (by decide),
      outside_read32 d (d := 228) (by decide) (by decide),
      outside_read32 c (d := 228) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · change (m4.writeW (off base 240) pad).readW (off base 232) 32 = _
    rw [outside_read32 e (d := 232) (by decide) (by decide), outside_read32 d (d := 232) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · change (m4.writeW (off base 240) pad).readW (off base 236) 32 = _
    rw [outside_read32 e (d := 236) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · exact (a.mono (by decide) (by decide)).trans ((b.mono (by decide) (by decide)).trans
      ((c.mono (by decide) (by decide)).trans ((d.mono (by decide) (by decide)).trans (e.mono (by decide) (by decide)))))

end VG.Proof.Bignum.Arm
