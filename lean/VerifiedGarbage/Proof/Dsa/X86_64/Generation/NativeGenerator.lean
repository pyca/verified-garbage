module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorBody
import VerifiedGarbage.Proof.Framework.Omega

/-! # Complete native generator search against the byte-tape specification -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86_64.Generation (generatorTape)

theorem nativeGenerator_ok (M : Mont) (Sq : MontS)
    {p : GeneratorSearchPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorSearchMemory p W s) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorSearch Sq.mm M.mm p.core.len) s
      (GeneratorFinished p (p.remaining 0) s) := by
  let I := GeneratorInvariant p (p.remaining 0) s
  let Q := GeneratorFinished p (p.remaining 0) s
  have hw : 0 < p.core.len ∧ p.core.len < 2 ^ 31 := by
    rcases p.core.width with hh | hh | hh <;> omega
  have driver : TapeDriver generatorTape p.core.F p.core.S p.core.len p.tape.length
      (Impl.Dsa.X86_64.Generation.generatorStep Sq.mm M.mm p.core.len) I Q :=
    { baseBound := by decide
      totalBound := by decide
      usedBound := by decide
      pointerBound := by decide
      usedNotScratch := by decide
      pointerNotScratch := by decide
      widthBound := hw.2
      widthPositive := hw.1
      totalFits := p.tapeFits
      stable := generatorInvariant_stable p (p.remaining 0) s
      finish := generatorFinished_stable p (p.remaining 0) s
      view := by
        rintro used t ⟨Wt, ht, h20, _, _, _, _⟩
        obtain ⟨Vt, Rt⟩ := ht.rep
        exact ⟨Vt, Wt, ht.layout, Rt, h20, ht.tapeLength⟩
      done := by
        intro used u v Vt Wt hi hex _ R Lu Ru fu ku
        exact generator_done hi hex R Lu Ru fu ku
      step := by
        intro used u v Vt Wt hi hav _ R _ Lv Rv fv kv
        exact generator_body_ok M Sq hi (by omega) R Lv Rv fv kv }
  obtain ⟨V, R⟩ := h.rep
  apply driver.run_ok h.layout R
  intro t Lt Rt ft kt
  have ff : Frame p.core.changed s.mem t.mem := by
    intro a ha
    apply ft a
    right
    have hn := ha ⟨p.core.F, frameBytes⟩ (by simp [GeneratorPlan.changed])
    change ¬ ofs p.core.F a < frameBytes at hn
    change 168 ≤ ofs p.core.F a
    unfold frameBytes at hn
    omega
  refine ⟨upd W 20 0, h.frame Lt ⟨V, Rt⟩ ?_ ff kt.2.1 kt.2.2,
    by simp [upd], rfl, ff, kt.2.1, kt.2.2⟩
  intro k hk
  simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Dsa.X86_64.Generation
