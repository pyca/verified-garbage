module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterInvariant
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTest

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterBody
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeLoop
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame

/-! # Complete finite native DSA parameter search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.Generation (seedTape)

theorem nativeParameters_ok (H : GenerationHashes) (M : Mont) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State} {randUsed : Nat}
    (h : GenerationMemory p W s) (h16 : W 16 = BitVec.ofNat 64 randUsed) (hu : randUsed ≤ p.rand.bytes.length) :
    WP isa (Impl.Dsa.AArch64.Generation.parameterSearch H.sha1 H.sha256 M.mm T.run p.geo.pLen p.geo.qLen) s
      (ParameterFinished p (p.remaining 0 randUsed) s) := by
  let I := ParameterInvariant p (p.remaining 0 randUsed) s
  let Q := ParameterFinished p (p.remaining 0 randUsed) s
  have hw : 0 < p.geo.qLen ∧ p.geo.qLen < 65536 := by
    rcases p.geo.qWidth with hh | hh <;> omega
  have driver : TapeDriver seedTape p.geo.F p.geo.hash p.geo.qLen p.seeds.bytes.length
      (Impl.Dsa.AArch64.Generation.seedAttempt H.sha1 H.sha256 M.mm T.run p.geo.pLen p.geo.qLen) I Q :=
    { baseBound := by decide
      totalBound := by decide
      usedBound := by decide
      pointerBound := by decide
      usedNotScratch := by decide
      pointerNotScratch := by decide
      widthBound := hw.2
      widthPositive := hw.1
      totalFits := p.seeds.size
      stable := parameterInvariant_stable p (p.remaining 0 randUsed) s
      finish := parameterFinished_stable p (p.remaining 0 randUsed) s
      view := by
        rintro used t ⟨Wt, _, ht, _, h10, _, _, _, _, _⟩
        obtain ⟨Vt, Rt⟩ := ht.rep
        exact ⟨Vt, Wt, ht.layout, Rt, h10, (ht.slots 9 (by simp [generationSlots])).trans p.seedsLengthSlot⟩
      done := by
        intro used u v Vt Wt hi hex _ R Lu Ru fu ku
        exact parameter_done hi hex R Lu Ru fu ku
      step := by
        intro used u v Vt Wt hi hav _ R _ Lv Rv fv kv
        exact parameter_body_ok H M T hi (by omega) R Lv Rv fv kv }
  obtain ⟨V, R⟩ := h.rep
  unfold Impl.Dsa.AArch64.Generation.parameterSearch
  apply driver.run_ok h.layout R
  intro t Lt Rt ft kt
  have ff : Frame p.changed s.mem t.mem := by
    apply GenerationContext.frame_single
    intro a ha
    apply ft a
    right
    have hn := ha ⟨p.geo.F, frameBytes⟩ (by simp)
    change ¬ ofs p.geo.F a < frameBytes at hn
    change 88 ≤ ofs p.geo.F a
    unfold frameBytes at hn
    omega
  have mt := h.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) ff kt.rd kt.wr
  exact ⟨upd W 10 0, randUsed, mt, hu, by simp [upd], by simpa [upd] using h16, rfl, ff, kt.rd, kt.wr⟩

end VG.Proof.Dsa.AArch64.Generation
