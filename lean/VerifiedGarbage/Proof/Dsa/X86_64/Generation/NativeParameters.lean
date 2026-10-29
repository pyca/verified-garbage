module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeLoop
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Dsa.Generation.SeedResult
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
import VerifiedGarbage.Spec.Ffdh
import Mathlib.Data.Nat.Basic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAttempt
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
/-! # Complete finite native DSA parameter search -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/ParameterSemantics.lean`, which only this module imported.
section

/-! # One complete seed chunk advances the outer parameter-generation specification -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG

theorem GenerationContext.remaining_step (p : GenerationContext) (used randUsed : Nat)
    (room : used + p.geo.qLen ≤ p.seeds.bytes.length) :
    p.remaining used randUsed =
      match VG.Proof.Dsa.Generation.seedResult (8 * p.geo.pLen) (8 * p.geo.qLen)
        ((p.seeds.bytes.drop used).take p.geo.qLen)
        ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop randUsed) with
      | none => none
      | some (none, rest) => Spec.Dsa.generateParameters.attempt (8 * p.geo.pLen)
          ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (8 * p.geo.qLen)
          (Spec.Dsa.generationChunks p.geo.qLen (p.seeds.bytes.drop (used + p.geo.qLen))) rest
      | some (some a, _) => some a := by
  have hw : 0 < p.geo.qLen := by rcases p.geo.qWidth with h | h <;> omega
  unfold remaining
  rw [VG.Proof.Dsa.Generation.generationChunks_step (bytes := p.seeds.bytes.drop used) hw
    (by simp only [List.length_drop]; omega)]
  rw [VG.Proof.Dsa.Generation.parameterAttempt_seedResult _ _ _ _ _ _ (by
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left (by omega)])]
  simp only [List.drop_drop]
  rfl

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/ParameterBody.lean`, which only this module imported.
section

/-! # Each native seed iteration advances the seed and witness tapes exactly -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64


variable {checkName : String}

theorem parameter_body_ok (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    {p : GenerationContext} {expected : Option Spec.Dsa.Params} {initial : State}
    {used : Nat} {s t : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (hi : ParameterInvariant p expected initial used s) (room : used + p.geo.qLen ≤ p.seeds.bytes.length)
    (R : Rep s.mem p.geo.F p.geo.hash V W) (Lt : Lay t p.geo.F p.geo.hash)
    (Rt : Rep t.mem p.geo.F p.geo.hash V
      (upd (upd W 1 (off (W 8) used)) 10 (BitVec.ofNat 64 (used + p.geo.qLen))))
    (ft : Frame [⟨p.geo.F, frameBytes⟩] s.mem t.mem) (kt : Keep [.rax, .rcx] s t) :
    WP isa (Impl.Dsa.X86_64.Generation.seedAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run p.geo.pLen p.geo.qLen) t fun u =>
      ∃ V' W', Lay u p.geo.F p.geo.hash ∧ Rep u.mem p.geo.F p.geo.hash V' W' ∧
        (if W' 19 = 3 then ParameterInvariant p expected initial (used + p.geo.qLen) u
          else ParameterFinished p expected initial u) := by
  obtain ⟨Wi, randUsed, h, bound, _, h16, he, fi, ri, wi⟩ := hi
  obtain ⟨Vi, Ri⟩ := h.rep
  have words : ∀ k < 37, W k = Wi k := fun k hk => (R.fr k hk).symm.trans (Ri.fr k hk)
  let Wt := upd (upd W 1 (off (W 8) used)) 10 (BitVec.ofNat 64 (used + p.geo.qLen))
  have ff := p.frame_single ft
  have ht : GenerationMemory p Wt t := h.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Wt, upd] <;> exact words _ (by decide)) ff kt.2.1 kt.2.2
  let seed := p.seeds.slice used p.geo.qLen room
  have hlen : seed.bytes.length = p.geo.qLen := by
    change ((p.seeds.bytes.drop used).take p.geo.qLen).length = p.geo.qLen
    simp only [List.length_take, List.length_drop, Nat.min_eq_left (by omega : p.geo.qLen ≤ p.seeds.bytes.length - used)]
  have h1 : Wt 1 = seed.ptr := by
    have h8 := (h.slots 8 (by simp [generationSlots])).trans p.seedsSlot
    simp [Wt, upd, words 8 (by decide), h8, seed, GenerationTape.slice]
  have ht16 : Wt 16 = BitVec.ofNat 64 randUsed := by
    simpa [Wt, upd, words 16 (by decide)] using h16
  refine WP.mono (seedAttempt_ok (checkName := checkName) H M Sq T ht seed hlen (ht.seeds.slice room) h1 ht16 bound)
    fun u ⟨Wu, randUsed', mu, bound', u16, slots, result, fu, ru, wu⟩ => ?_
  have frame := (fi.trans ff).trans fu
  have rd := ru.trans (kt.2.1.trans ri)
  have wr := wu.trans (kt.2.2.trans wi)
  have u10 : Wu 10 = BitVec.ofNat 64 (used + p.geo.qLen) := by
    simpa [Wt, upd] using slots 10 (by simp [searchSlots])
  have step := he.trans (p.remaining_step used randUsed room)
  change SeedOutcome p (VG.Proof.Dsa.Generation.seedResult (8 * p.geo.pLen) (8 * p.geo.qLen)
    ((p.seeds.bytes.drop used).take p.geo.qLen)
    ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (p.rand.bytes.drop randUsed)) Wu randUsed' u at result
  obtain ⟨Vu, Ru⟩ := mu.rep
  refine ⟨Vu, Wu, mu.layout, Ru, ?_⟩
  rcases result with ⟨h19, hr⟩ | ⟨h19, hr⟩ | ⟨h19, a, hr, bytes⟩
  · rw [ite_eq_right (by rw [h19]; decide)]
    rw [hr] at step
    exact ⟨Wu, mu, Or.inl ⟨Or.inl h19, step⟩, frame, rd, wr⟩
  · rw [ite_eq_left h19]
    rw [hr] at step
    exact ⟨Wu, randUsed', mu, bound', u10, u16, step, frame, rd, wr⟩
  · rw [ite_eq_right (by rw [h19]; decide)]
    rw [hr] at step
    exact ⟨Wu, mu, Or.inr ⟨h19, a, step, bytes⟩, frame, rd, wr⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.X86_64
open VG.Impl.Dsa.X86_64.Generation (seedTape)


variable {checkName : String}

theorem nativeParameters_ok (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State} {randUsed : Nat}
    (h : GenerationMemory p W s) (h16 : W 16 = BitVec.ofNat 64 randUsed) (hu : randUsed ≤ p.rand.bytes.length) :
    WP isa (Impl.Dsa.X86_64.Generation.parameterSearch (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run p.geo.pLen p.geo.qLen) s
      (ParameterFinished p (p.remaining 0 randUsed) s) := by
  let I := ParameterInvariant p (p.remaining 0 randUsed) s
  let Q := ParameterFinished p (p.remaining 0 randUsed) s
  have hw : 0 < p.geo.qLen ∧ p.geo.qLen < 2 ^ 31 := by
    rcases p.geo.qWidth with hh | hh <;> omega
  have driver : TapeDriver seedTape p.geo.F p.geo.hash p.geo.qLen p.seeds.bytes.length
      (Impl.Dsa.X86_64.Generation.seedAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run p.geo.pLen p.geo.qLen) I Q :=
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
        exact parameter_body_ok (checkName := checkName) H M Sq T hi (by omega) R Lv Rv fv kv }
  obtain ⟨V, R⟩ := h.rep
  unfold Impl.Dsa.X86_64.Generation.parameterSearch
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
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) ff kt.2.1 kt.2.2
  exact ⟨upd W 10 0, randUsed, mt, hu, by simp [upd], by simpa [upd] using h16, rfl, ff, kt.2.1, kt.2.2⟩

end VG.Proof.Dsa.X86_64.Generation
