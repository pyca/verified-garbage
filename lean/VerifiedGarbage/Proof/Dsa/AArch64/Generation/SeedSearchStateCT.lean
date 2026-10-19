module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSearchPlanCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchInitCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # Instantiate the public prime-search state from actual persistent-frame words -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem seedPrime_memory {p : SeedPublic} {s : State} {W : Nat → BitVec 64}
    (hm : GenerationMemory p.context W s) (seed : GenerationTapeMemory p.seed s)
    (h1 : W 1 = p.seed.ptr) (h10 : W 10 = p.seedCursor)
    (hq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.context.geo.B q) p.context.geo.qLen =
      Spec.Dsa.encodeBE p.context.geo.qLen (Spec.Dsa.qCandidate (8 * p.context.geo.qLen) p.seed.bytes)) :
    SearchMemory p.searchPlan W s := by
  have state := hm.searchState p.seed p.length seed h1 hq
  have h5 : W 5 = p.context.saved 5 := hm.slots 5 (by simp [generationSlots])
  refine {
    layout := state.layout
    rep := state.rep
    slots := seedPrime_words hm h1 h10
    label := state.label.congr rfl rfl rfl ?_
    seedRead := state.seedRead
    wrappedWrite := state.wrappedWrite
    hashWrite := state.hashWrite
    seed := state.seed
    scratch := state.scratch
    qSource := ?_
    tape := state.tape
    shapedWrite := ?_
    pWrite := ?_
    exponentWrite := ?_
    witnessWrite := ?_ }
  · change p.context.saved 26 = W 26
    exact (hm.slots 26 (by simp [generationSlots])).symm
  · have src := state.qSource
    change Src s (VG.Proof.Bignum.off p.context.geo.B arithmetic) arithmeticBytes (VG.Proof.Bignum.off (W 5) q) _ at src
    change Src s (VG.Proof.Bignum.off p.context.geo.B arithmetic) arithmeticBytes (VG.Proof.Bignum.off (p.context.saved 5) q) _
    rw [h5] at src
    exact src
  · have write := state.shapedWrite
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) shaped) i) 1 at write
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (p.context.saved 5) shaped) i) 1
    rw [h5] at write
    exact write
  · have write := state.pWrite
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p) i) 1 at write
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (p.context.saved 5) VG.Impl.Dsa.Generation.Layout.p) i) 1
    rw [h5] at write
    exact write
  · have write := state.exponentWrite
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) exponent) i) 1 at write
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (p.context.saved 5) exponent) i) 1
    rw [h5] at write
    exact write
  · have write := state.witnessWrite
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) witness) i) 1 at write
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (p.context.saved 5) witness) i) 1
    rw [h5] at write
    exact write

theorem seedPrime_start {pLen qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedPrimeBefore pLen qLen p s) : SearchStart pLen qLen p.search s := by
  obtain ⟨⟨⟨W, hm, h1, h16, h10⟩, seed, heQ⟩, heP, hq⟩ := h
  exact ⟨⟨W, seedPrime_memory hm seed h1 h10 hq, h16⟩,
    hm.scratch.sub (p.context.geo.small_bound (d := control) (n := 24) (by decide) (by decide)) (by decide),
    p.bound, heP, heQ, rfl⟩

end VG.Proof.Dsa.AArch64.Generation
