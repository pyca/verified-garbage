module

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextGeneratorFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeGenerator
public import VerifiedGarbage.Proof.Dsa.Generation.PDomain
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchMemory
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
import VerifiedGarbage.Proof.Dsa.Generation.GeneratorDomain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextGenerator
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.Encoding

/-! # Complete generator search on an accepted native p candidate -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem seedGenerator_ok (M : Mont)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (value qval : Nat)
    (domain : VG.Proof.Dsa.Generation.PDomain p.geo.pLen value)
    (bp : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value)
    (be : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / qval))
    (bq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval) :
    WP isa (Impl.Dsa.AArch64.Generation.generatorSearch M.mm p.geo.pLen) s fun t =>
      let result := Spec.Dsa.generator value qval
        ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE)
      ∃ W', GenerationMemory p W' t ∧ (∀ k ∈ generatorSlots, W' k = W k) ∧
        Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value ∧
        Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval ∧
        ((W' 19 = 3 ∧ result = none) ∨
         ∃ gv, W' 19 = 1 ∧ result = some gv ∧ 1 < gv ∧ gv < value ∧
           Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off p.geo.B g) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen gv) ∧
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
  refine WP.mono (nativeGenerator_ok M state) fun t ⟨Wt, mt, result, ft, rd, wr⟩ => ?_
  have fg : Frame p.geo.gWork s.mem t.mem := ft
  have ff := p.generator_frame fg
  have slots : ∀ k ∈ generatorSlots, Wt k = W k := mt.slots
  have mem := h.frame mt.layout mt.rep (fun k hk => slots k (by
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [generatorSlots])) ff rd wr
  refine ⟨Wt, mem, slots, ?_, (p.geo.generator_q fg).trans bq, ?_, ff, rd, wr⟩
  · have bytes := source_octets mt.pArithmetic
    change Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off p.geo.B VG.Impl.Dsa.Generation.Layout.p)
      (Spec.Dsa.encodeBE p.geo.pLen value).length = Spec.Dsa.encodeBE p.geo.pLen value at bytes
    simpa only [VG.Proof.Dsa.encodeBE_length] using bytes
  · rcases result with fail | ⟨gv, h19, hr, bg⟩
    · exact Or.inl ⟨fail.1, remaining ▸ fail.2⟩
    · have hr' := remaining ▸ hr
      have bounds := VG.Proof.Dsa.Generation.generator_bounds (by omega_using [domain.large]) _ hr'
      exact Or.inr ⟨gv, h19, hr', bounds.1, bounds.2, bg⟩

end VG.Proof.Dsa.AArch64.Generation
