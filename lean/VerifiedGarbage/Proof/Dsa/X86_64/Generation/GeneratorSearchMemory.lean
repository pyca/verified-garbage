module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Finish
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorPlan
public import VerifiedGarbage.Spec.Dsa.Generate

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceSlice
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorOutput
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorStages
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
import VerifiedGarbage.Proof.Framework.Offset
/-! # Preserve the whole h tape while testing successive complete chunks -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorStep.lean`, which only this module imported.
section

/-! # Complete native generator attempt: input filter, power, output filter -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def GeneratorPlan.accepts (p : GeneratorPlan) : Prop :=
  1 < Spec.Dsa.decodeBE p.hb ∧ Spec.Dsa.decodeBE p.hb < Spec.Dsa.decodeBE p.pb - 1 ∧ 1 < p.value

instance (p : GeneratorPlan) : Decidable p.accepts := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem generatorStep_ok (M : Mont) (Sq : MontS)
    {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State} (h : GeneratorMemory p W s) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorStep Sq.mm M.mm p.len) s fun t =>
      GeneratorMemory p (upd W 19 (if p.accepts then 1 else 3)) t ∧
      (p.accepts → Spec.Rsa.bytesAt t.mem (off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value) ∧
      Frame p.changed s.mem t.mem ∧ Keep coreRegs s t := by
  unfold Impl.Dsa.X86_64.Generation.generatorStep
  refine WP.seq (WP.mono (generatorInputRange_ok h) fun u ⟨hr, hu, fu, ku⟩ => ?_)
  refine WP.seq (WP.mono (generatorTest_ok hu hr) fun v ⟨hz, hv, hm, kv⟩ => ?_)
  have fv : Frame p.changed s.mem v.mem := hm ▸ fu
  by_cases input : 1 < Spec.Dsa.decodeBE p.hb ∧ Spec.Dsa.decodeBE p.hb < Spec.Dsa.decodeBE p.pb - 1
  · refine WP.ite false (by simp [eval, hz, input]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    change WP isa (.seq _ (.seq _ (.seq _ _))) v _
    refine WP.seq (WP.mono (generatorEvaluateStage_ok M Sq hv) fun w ⟨gw, hw, fw, kw⟩ => ?_)
    refine WP.seq (WP.mono (generatorOutputRange_ok hw gw) fun x ⟨rx, hx, gx, fx, kx⟩ => ?_)
    refine WP.seq (WP.mono (generatorTest_ok hx rx) fun y ⟨zy, hy, my, ky⟩ => ?_)
    have fy : Frame p.changed s.mem y.mem := my ▸ ((fv.trans fw).trans fx)
    have gy : Spec.Rsa.bytesAt y.mem (off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value := my ▸ gx
    have keep := (((ku.trans kv).trans kw).trans kx).trans ky
    by_cases output : 1 < p.value
    · have accepted : p.accepts := ⟨input.1, input.2, output⟩
      refine WP.ite false (by simp [eval, zy, output]) (fun he => Bool.noConfusion he) (fun _ => ?_)
      refine WP.mono (generatorSetStatus_ok hy 1 (by decide)) fun t ⟨ht, gt, ft, kt⟩ => ?_
      exact ⟨by simpa [accepted] using ht, fun _ => gt.trans gy,
        fy.trans ft, (keep.trans kt).mono (by decide)⟩
    · have rejected : ¬ p.accepts := fun ha => output ha.2.2
      refine WP.ite true (by simp [eval, zy, output]) (fun _ => ?_) (fun he => Bool.noConfusion he)
      refine WP.mono (generatorSetStatus_ok hy 3 (by decide)) fun t ⟨ht, _, ft, kt⟩ => ?_
      exact ⟨by simpa [rejected] using ht, fun ha => (rejected ha).elim,
        fy.trans ft, (keep.trans kt).mono (by decide)⟩
  · have rejected : ¬ p.accepts := fun ha => input ⟨ha.1, ha.2.1⟩
    refine WP.ite true (by simp [eval, hz, input]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (generatorSetStatus_ok hv 3 (by decide)) fun t ⟨ht, _, ft, kt⟩ => ?_
    exact ⟨by simpa [rejected] using ht, fun ha => (rejected ha).elim,
      fv.trans ft, ((ku.trans kv).trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorSearchPlan.lean`, which only this module imported.
section

/-! # Original h tape and per-chunk plans for the native generator loop -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure GeneratorSearchPlan where
  core : GeneratorPlan
  saved : Nat → BitVec 64
  tape : List Byte
  tapePtr : Addr
  tapeFits : tape.length < 2 ^ 64
  tapeSeparate : ∀ r ∈ core.changed, (⟨tapePtr, tape.length⟩ : Region).Disjoint r
  q : Nat
  exponentValue : Spec.Dsa.decodeBE core.eb = (Spec.Dsa.decodeBE core.pb - 1) / q

def GeneratorSearchPlan.chunk (p : GeneratorSearchPlan) (used : Nat)
    (room : used + p.core.len ≤ p.tape.length) : GeneratorPlan :=
  { p.core with
    hp := off p.tapePtr used
    hb := (p.tape.drop used).take p.core.len
    hLength := by simp only [List.length_take, List.length_drop]; omega
    hSeparate := by
      intro r hr
      exact fun a ha hb => p.tapeSeparate r hr a (Offset.sub_base p.tapePtr room a ha) hb }

def GeneratorSearchPlan.remaining (p : GeneratorSearchPlan) (used : Nat) : Option Nat :=
  Spec.Dsa.generator (Spec.Dsa.decodeBE p.core.pb) p.q
    ((Spec.Dsa.generationChunks p.core.len (p.tape.drop used)).map Spec.Dsa.decodeBE)

theorem GeneratorSearchPlan.remaining_done (p : GeneratorSearchPlan) {used : Nat}
    (h : p.tape.length - used < p.core.len) : p.remaining used = none := by
  unfold remaining
  rw [VG.Proof.Dsa.Generation.generationChunks_done (by simpa only [List.length_drop] using h)]
  rfl

theorem GeneratorSearchPlan.remaining_step (p : GeneratorSearchPlan) {used : Nat}
    (room : used + p.core.len ≤ p.tape.length) :
    p.remaining used = if (p.chunk used room).accepts then some (p.chunk used room).value
      else p.remaining (used + p.core.len) := by
  have hw : 0 < p.core.len := by rcases p.core.width with hh | hh | hh <;> omega
  rw [remaining, VG.Proof.Dsa.Generation.generator_chunks_step hw (by
    simp only [List.length_drop]; omega)]
  simp only [GeneratorPlan.accepts, GeneratorPlan.value, chunk, p.exponentValue,
    remaining, List.drop_drop]

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def generatorSlots : List Nat := [1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 28]

structure GeneratorSearchMemory (p : GeneratorSearchPlan) (W : Nat → BitVec 64) (s : State) : Prop where
  layout : Lay s p.core.F p.core.S
  rep : ∃ V, Rep s.mem p.core.F p.core.S V W
  base : W 5 = p.core.B
  tapeBase : W 11 = p.tapePtr
  tapeLength : W 12 = BitVec.ofNat 64 p.tape.length
  slots : ∀ k ∈ generatorSlots, W k = p.saved k
  arithmetic : Scr s p.core.A p.core.Z
  parent : Scr s p.core.B Impl.Dsa.Layout.activeBytes
  pArithmetic : Src s p.core.A p.core.Z (off p.core.B Impl.Dsa.Generation.Layout.p) p.core.pb
  tapeArithmetic : Src s p.core.A p.core.Z p.tapePtr p.tape
  eArithmetic : Src s p.core.A p.core.Z (off p.core.B exponent) p.core.eb
  pParent : Src s p.core.B Impl.Dsa.Layout.activeBytes (off p.core.B Impl.Dsa.Generation.Layout.p) p.core.pb
  tapeParent : Src s p.core.B Impl.Dsa.Layout.activeBytes p.tapePtr p.tape
  eParent : Src s p.core.B Impl.Dsa.Layout.activeBytes (off p.core.B exponent) p.core.eb
  gWrite : ∀ i < p.core.len, InRegions s.wr (off (off p.core.B g) i) 1

theorem GeneratorSearchMemory.frame {p : GeneratorSearchPlan} {W W' : Nat → BitVec 64} {s t : State}
    (h : GeneratorSearchMemory p W s) (L : Lay t p.core.F p.core.S)
    (R : ∃ V, Rep t.mem p.core.F p.core.S V W')
    (hw : ∀ k ∈ generatorSlots, W' k = W k)
    (hf : Frame p.core.changed s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    GeneratorSearchMemory p W' t := by
  have hn : p.core.len < 2 ^ 64 := by rcases p.core.width with hh | hh | hh <;> omega
  have fp : ∀ r ∈ p.core.changed, (⟨off p.core.B Impl.Dsa.Generation.Layout.p, p.core.pb.length⟩ : Region).Disjoint r := by
    rw [p.core.pLength]; exact p.core.pSeparate
  have fe : ∀ r ∈ p.core.changed, (⟨off p.core.B exponent, p.core.eb.length⟩ : Region).Disjoint r := by
    rw [p.core.eLength]; exact p.core.eSeparate
  exact ⟨L, R, (hw 5 (by simp [generatorSlots])).trans h.base, (hw 11 (by simp [generatorSlots])).trans h.tapeBase,
    (hw 12 (by simp [generatorSlots])).trans h.tapeLength,
    fun k hk => (hw k hk).trans (h.slots k hk), h.arithmetic.congr hwr, h.parent.congr hwr,
    source_of_frame h.pArithmetic hf fp (p.core.pLength ▸ hn) hrd hwr,
    source_of_frame h.tapeArithmetic hf p.tapeSeparate p.tapeFits hrd hwr,
    source_of_frame h.eArithmetic hf fe (p.core.eLength ▸ hn) hrd hwr,
    source_of_frame h.pParent hf fp (p.core.pLength ▸ hn) hrd hwr,
    source_of_frame h.tapeParent hf p.tapeSeparate p.tapeFits hrd hwr,
    source_of_frame h.eParent hf fe (p.core.eLength ▸ hn) hrd hwr,
    fun i hi => by rw [hwr]; exact h.gWrite i hi⟩

theorem GeneratorSearchMemory.chunk {p : GeneratorSearchPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorSearchMemory p W s) {used : Nat} (room : used + p.core.len ≤ p.tape.length)
    (ptr : W 21 = off p.tapePtr used) : GeneratorMemory (p.chunk used room) W s :=
  ⟨h.layout, h.rep, h.base, ptr, h.arithmetic, h.parent,
    h.pArithmetic, source_slice h.tapeArithmetic room, h.eArithmetic,
    h.pParent, source_slice h.tapeParent room, h.eParent, h.gWrite⟩

end VG.Proof.Dsa.X86_64.Generation
