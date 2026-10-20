module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometrySubgroup
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import VerifiedGarbage.Proof.Framework.Omega

/-! # The persistent search state supplies every precondition of the q phase -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def GenerationMemory.subgroupPlan {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (h0 : W 0 = off p.geo.B q) : SubgroupPlan :=
  p.geo.subgroupPlan p.rand seed hlen W
    ((h.slots 5 (by simp [generationSlots])).trans p.baseSlot) h0
    ((h.slots 13 (by simp [generationSlots])).trans p.randSlot)
    ((h.slots 15 (by simp [generationSlots])).trans p.randLengthSlot)

theorem GenerationMemory.subgroupState {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h0 : W 0 = off p.geo.B q)
    (h27 : W 27 = seed.ptr) {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used)
    (hu : used ≤ p.rand.bytes.length) : SubgroupState (h.subgroupPlan seed hlen h0) used s := by
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega
  have ha := p.geo.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have hq := p.geo.small_bound (d := q) (n := p.geo.qLen) (by decide) (by unfold arithmeticBytes; omega)
  have hw := p.geo.small_bound (d := witness) (n := p.geo.qLen) (by decide) (by unfold arithmeticBytes; omega)
  refine {
    layout := h.layout
    rep := h.rep
    label := ?_
    seed := ?_
    scratch := h.scratch.sub (n := arithmeticBytes) ha (by decide)
    tape := h.rand.source ha
    outputWrite := ?_
    witnessWrite := ?_
    usedSlot := h16
    usedBound := hu }
  · change LabAt s p.geo.F p.geo.hash W seed.ptr p.geo.qLen
    refine ⟨h27, (h.slots 28 (by simp [generationSlots])).trans p.hashLenSlot, by omega, ?_, ?_, ?_⟩
    · simpa only [hlen] using hseed.cover
    · simpa only [hlen, GenerationGeometry.part, GenerationGeometry.hash] using seed.part hh
    · simpa only [hlen] using (seed.stack.sub_right (below_sub (a := 16) (by decide) (by decide))).symm
  · change Spec.Rsa.bytesAt s.mem seed.ptr p.geo.qLen = seed.bytes
    rw [← hlen]
    exact hseed.bytes
  · change ∀ i < p.geo.qLen, InRegions s.wr (off (off p.geo.B q) i) 1
    intro i hi
    rw [off_off]
    exact h.scratch.region (by omega) (by decide)
  · change ∀ i < p.geo.qLen, InRegions s.wr (off (off p.geo.B witness) i) 1
    intro i hi
    rw [off_off]
    exact h.scratch.region (by omega) (by decide)

end VG.Proof.Dsa.X86_64.Generation
