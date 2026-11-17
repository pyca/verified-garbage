module

public import VerifiedGarbage.Proof.Dsa.Generation.PDomain
public import VerifiedGarbage.Proof.Dsa.Generation.GeneratorCount
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorSearchMemory
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Dsa.Generation.GeneratorDomain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextGenerator
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.Encoding
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorInvariant
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeIteration
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeState

/-! ### `Dsa.X86_64.Generation.TapeLoop`, which only this module used -/

section

/-! # Termination of native seed and generator tape searches -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Dsa.X86_64.Generation

/-- The body provides algorithm-specific progress; the tape controller
owns complete-chunk selection, cursor advancement, and loop termination. -/
structure TapeDriver (slots : TapeSlots) (F S : Addr) (width total : Nat)
    (body : Prog isa) (I : Nat → State → Prop) (Q : State → Prop) : Prop where
  baseBound : slots.base < 37
  totalBound : slots.total < 37
  usedBound : slots.used < 37
  pointerBound : slots.pointer < 37
  usedNotScratch : slots.used ≠ 14
  pointerNotScratch : slots.pointer ≠ 14
  widthBound : width < 2 ^ 31
  widthPositive : 0 < width
  totalFits : total < 2 ^ 64
  stable : ∀ n, TapeStable (I n)
  finish : TapeStable Q
  view : ∀ n s, I n s → TapeView slots F S n total s
  done : ∀ used s t V W, I used s → total - used < width →
    Lay s F S → Rep s.mem F S V W →
    Lay t F S → Rep t.mem F S V (upd W 19 3) →
    Outside F 152 8 s.mem t.mem → Keep [.rax] s t → Q t
  step : ∀ used s t V W, I used s → width ≤ total - used →
    Lay s F S → Rep s.mem F S V W → W slots.used = BitVec.ofNat 64 used →
    Lay t F S → Rep t.mem F S V
      (upd (upd W slots.pointer (off (W slots.base) used)) slots.used (BitVec.ofNat 64 (used + width))) →
    Frame [⟨F, frameBytes⟩] s.mem t.mem → Keep [.rax, .rcx] s t →
    WP isa body t fun u => ∃ V' W', Lay u F S ∧ Rep u.mem F S V' W' ∧
      (if W' 19 = 3 then I (used + width) u else Q u)

theorem TapeDriver.loop_ok {slots : TapeSlots} {F S : Addr} {width total : Nat}
    {body : Prog isa} {I : Nat → State → Prop} {Q : State → Prop}
    (d : TapeDriver slots F S width total body I Q)
    {s : State} {used : Nat} (hle : used ≤ total) (hi : I used s) :
    WP isa (.loop (tapeIteration slots width body) .e) s Q := by
  exact WP.loop
    (fun n t => ∃ used, n = total - used + 1 ∧ used ≤ total ∧ I used t)
    (fun n t ⟨u, hn, hu, hit⟩ =>
      WP.mono (tapeIteration_ok d.baseBound d.totalBound d.usedBound d.pointerBound
        d.usedNotScratch d.pointerNotScratch d.widthBound d.totalFits
        d.stable d.finish d.view (d.done u) (d.step u) hu hit)
        fun t' ht => ht.imp (fun h => h) fun ⟨hz, hi', hbound⟩ =>
          ⟨hz, total - (u + width) + 1, by omega_using [d.widthPositive, hn, hu, hbound],
            u + width, rfl, hbound, hi'⟩)
    (total - used + 1) s ⟨used, rfl, hle, hi⟩

/-- Resetting the cursor makes each generator search reuse the original h
tape, and each top-level call begin at the first seed. -/
theorem TapeDriver.run_ok {slots : TapeSlots} {F S : Addr} {width total : Nat}
    {body : Prog isa} {I : Nat → State → Prop} {Q : State → Prop}
    (d : TapeDriver slots F S width total body I Q)
    {s : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (start : ∀ t, Lay t F S → Rep t.mem F S V (upd W slots.used 0) →
      Outside F (8 * slots.used) 8 s.mem t.mem → Keep [.rax] s t → I 0 t) :
    WP isa (tapeLoop slots width body) s Q := by
  unfold tapeLoop
  refine WP.seq (WP.mono (tapeReset_ok L R slots d.usedBound d.usedNotScratch)
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_)
  exact d.loop_ok (Nat.zero_le _) (start t Lt Rt ft kt)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Complete generator search on an accepted native p candidate -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/ContextGeneratorFrame.lean`, which only this module imported.
section

/-! # Generator writes preserve the outer seed state and saved q -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem GenerationContext.generator_frame {p : GenerationContext} {m m' : Mem}
    (hf : Frame p.geo.gWork m m') : Frame p.changed m m' := by
  apply GenerationContext.frame_parts hf
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with h | h | h <;> omega
  have part (d n : Nat) (bound : d + n ≤ usedBytes p.geo.pLen) :
      ∃ out ∈ p.changed, Region.Sub (p.geo.part d n) out :=
    ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed], p.geo.part_sub bound⟩
  intro r hr
  simp only [GenerationGeometry.gWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact part arithmetic arithmeticBytes (p.geo.small_bound (by decide) (by rfl))
  · simpa [GenerationGeometry.part, off] using part 0 Impl.Dsa.Layout.activeBytes (by simpa using p.geo.parentRoom)
  · exact part g p.geo.pLen (p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega))
  · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩

theorem GenerationGeometry.generator_q {p : GenerationGeometry} {m m' : Mem}
    (hf : Frame p.gWork m m') :
    Spec.Rsa.bytesAt m' (off p.B q) p.qLen = Spec.Rsa.bytesAt m (off p.B q) p.qLen := by
  have qn : p.qLen ≤ 32 := by rcases p.qWidth with h | h <;> omega
  exact VG.Proof.Dsa.Generation.frame_bytesAt hf
    (p.gWork_separate (d := q) (n := p.qLen) (by rfl) (by unfold q g; omega)) (by omega)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorBody.lean`, which only this module imported.
section

/-! # A consumed h chunk either finishes or advances the exact generator search -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem generator_body_ok (M : Mont) (Sq : MontS)
    {p : GeneratorSearchPlan} {expected : Option Nat} {final : Nat} {initial : State}
    {used : Nat} {s t : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (hi : GeneratorInvariant p expected final initial used s) (room : used + p.core.len ≤ p.tape.length)
    (R : Rep s.mem p.core.F p.core.S V W)
    (Lt : Lay t p.core.F p.core.S)
    (Rt : Rep t.mem p.core.F p.core.S V
      (upd (upd W 21 (off (W 11) used)) 20 (BitVec.ofNat 64 (used + p.core.len))))
    (ft : Frame [⟨p.core.F, frameBytes⟩] s.mem t.mem) (kt : Keep [.rax, .rcx] s t) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorStep Sq.mm M.mm p.core.len) t fun u =>
      ∃ V' W', Lay u p.core.F p.core.S ∧ Rep u.mem p.core.F p.core.S V' W' ∧
        (if W' 19 = 3 then GeneratorInvariant p expected final initial (used + p.core.len) u
          else GeneratorFinished p expected final initial u) := by
  obtain ⟨Wi, h, _, he, hcount, fi, ri, wi⟩ := hi
  obtain ⟨Vi, Ri⟩ := h.rep
  have words : ∀ k < 37, W k = Wi k := fun k hk => (R.fr k hk).symm.trans (Ri.fr k hk)
  let Wt := upd (upd W 21 (off (W 11) used)) 20 (BitVec.ofNat 64 (used + p.core.len))
  have ff : Frame p.core.changed s.mem t.mem := ft.mono (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [GeneratorPlan.changed])
  have ht : GeneratorSearchMemory p Wt t := h.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Wt, upd] <;> exact words _ (by decide)) ff kt.2.1 kt.2.2
  have hc := ht.chunk room (by
    change Wt 21 = off p.tapePtr used
    simp [Wt, upd, words 11 (by decide), h.tapeBase])
  refine WP.mono (generatorStep_ok M Sq (p := p.chunk used room) hc) fun u ⟨hu, hg, fu, ku⟩ => ?_
  let Wu := upd Wt 19 (if (p.chunk used room).accepts then 1 else 3)
  have mem : GeneratorSearchMemory p Wu u := ht.frame hu.layout hu.rep (by
    intro k hk
    simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) fu ku.2.1 ku.2.2
  have frame := (fi.trans ff).trans fu
  have rd := ku.2.1.trans (kt.2.1.trans ri)
  have wr := ku.2.2.trans (kt.2.2.trans wi)
  have rem := he.trans (p.remaining_step room)
  have cnt := hcount.trans (congrArg (used + p.core.len * ·) (p.count_step room))
  have h20 : Wu 20 = BitVec.ofNat 64 (used + p.core.len) := by simp [Wu, Wt, upd]
  obtain ⟨Vu, Ru⟩ := mem.rep
  refine ⟨Vu, Wu, mem.layout, Ru, ?_⟩
  by_cases accepted : (p.chunk used room).accepts
  · have h19 : Wu 19 = 1 := by simp [Wu, upd, accepted]
    rw [ite_eq_right (by rw [h19]; decide)]
    rw [ite_eq_left accepted, Nat.mul_one] at cnt
    exact ⟨Wu, mem, cnt ▸ h20, Or.inr ⟨(p.chunk used room).value, h19,
      by simpa only [accepted, ite_true] using rem, hg accepted⟩, frame, rd, wr⟩
  · have h19 : Wu 19 = 3 := by simp [Wu, upd, accepted]
    rw [ite_eq_left h19]
    rw [ite_eq_right accepted, Nat.mul_succ] at cnt
    exact ⟨Wu, mem, h20,
      by simpa only [accepted, ite_false] using rem, by omega, frame, rd, wr⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/NativeGenerator.lean`, which only this module imported.
section

/-! # Complete native generator search against the byte-tape specification -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86_64.Generation (generatorTape)

theorem nativeGenerator_ok (M : Mont) (Sq : MontS)
    {p : GeneratorSearchPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorSearchMemory p W s) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorSearch Sq.mm M.mm p.core.len) s
      (GeneratorFinished p (p.remaining 0) (p.core.len * p.count 0) s) := by
  let I := GeneratorInvariant p (p.remaining 0) (p.core.len * p.count 0) s
  let Q := GeneratorFinished p (p.remaining 0) (p.core.len * p.count 0) s
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
      stable := generatorInvariant_stable p (p.remaining 0) _ s
      finish := generatorFinished_stable p (p.remaining 0) _ s
      view := by
        rintro used t ⟨Wt, ht, h20, _, _, _, _, _⟩
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
    by simp [upd], rfl, (Nat.zero_add _).symm, ff, kt.2.1, kt.2.2⟩
  intro k hk
  simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem seedGenerator_ok (M : Mont) (Sq : MontS)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (value qval : Nat)
    (domain : VG.Proof.Dsa.Generation.PDomain p.geo.pLen value)
    (bp : Spec.Rsa.bytesAt s.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value)
    (be : Spec.Rsa.bytesAt s.mem (off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / qval))
    (bq : Spec.Rsa.bytesAt s.mem (off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorSearch Sq.mm M.mm p.geo.pLen) s fun t =>
      let result := Spec.Dsa.generator value qval
        ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE)
      ∃ W', GenerationMemory p W' t ∧ (∀ k ∈ generatorSlots, W' k = W k) ∧
        W' 20 = BitVec.ofNat 64 (p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount value qval
          ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE)) ∧
        Spec.Rsa.bytesAt t.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value ∧
        Spec.Rsa.bytesAt t.mem (off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval ∧
        ((W' 19 = 3 ∧ result = none) ∨
         ∃ gv, W' 19 = 1 ∧ result = some gv ∧ 1 < gv ∧ gv < value ∧
           Spec.Rsa.bytesAt t.mem (off p.geo.B g) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen gv) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have fit : value < 256 ^ p.geo.pLen := by
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using domain.upper
  have decode := VG.Proof.Dsa.decodeBE_encodeBE fit
  have expFit : (value - 1) / qval < 256 ^ p.geo.pLen :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)) fit
  have expDecode := VG.Proof.Dsa.decodeBE_encodeBE expFit
  have positive : 1 < Spec.Dsa.decodeBE (Spec.Dsa.encodeBE p.geo.pLen value) := by
    rw [decode]; omega_using [domain.large]
  have odd : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE p.geo.pLen value) % 2 = 1 := by rw [decode]; exact domain.odd
  have exponentValue : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / qval)) =
      (Spec.Dsa.decodeBE (Spec.Dsa.encodeBE p.geo.pLen value) - 1) / qval := by rw [decode, expDecode]
  let a := p.generatorPlan W _ _ (VG.Proof.Dsa.encodeBE_length _ _) (VG.Proof.Dsa.encodeBE_length _ _) positive odd qval exponentValue
  have state := h.generatorState _ _ (VG.Proof.Dsa.encodeBE_length _ _) (VG.Proof.Dsa.encodeBE_length _ _)
    positive odd qval exponentValue bp be
  have remaining : a.remaining 0 = Spec.Dsa.generator value qval
      ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) := by
    change Spec.Dsa.generator (Spec.Dsa.decodeBE (Spec.Dsa.encodeBE p.geo.pLen value)) qval
      ((Spec.Dsa.generationChunks p.geo.pLen (p.hs.bytes.drop 0)).map Spec.Dsa.decodeBE) = _
    rw [decode, List.drop_zero]
  have count : a.core.len * a.count 0 = p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount value qval
      ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) := by
    change p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount
      (Spec.Dsa.decodeBE (Spec.Dsa.encodeBE p.geo.pLen value)) qval
      ((Spec.Dsa.generationChunks p.geo.pLen (p.hs.bytes.drop 0)).map Spec.Dsa.decodeBE) = _
    rw [decode, List.drop_zero]
  refine WP.mono (nativeGenerator_ok M Sq state) fun t ⟨Wt, mt, h20, result, ft, rd, wr⟩ => ?_
  have fg : Frame p.geo.gWork s.mem t.mem := ft
  have ff := p.generator_frame fg
  have slots : ∀ k ∈ generatorSlots, Wt k = W k := mt.slots
  have mem := h.frame mt.layout mt.rep (fun k hk => slots k (by
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [generatorSlots])) ff rd wr
  refine ⟨Wt, mem, slots, count ▸ h20, ?_, (p.geo.generator_q fg).trans bq, ?_, ff, rd, wr⟩
  · have bytes := source_octets mt.pArithmetic
    change Spec.Rsa.bytesAt t.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p)
      (Spec.Dsa.encodeBE p.geo.pLen value).length = Spec.Dsa.encodeBE p.geo.pLen value at bytes
    simpa only [VG.Proof.Dsa.encodeBE_length] using bytes
  · rcases result with fail | ⟨gv, h19, hr, bg⟩
    · exact Or.inl ⟨fail.1, remaining ▸ fail.2⟩
    · have hr' := remaining ▸ hr
      have bounds := VG.Proof.Dsa.Generation.generator_bounds (by omega_using [domain.large]) _ hr'
      exact Or.inr ⟨gv, h19, hr', bounds.1, bounds.2, bg⟩

end VG.Proof.Dsa.X86_64.Generation
