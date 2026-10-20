module

public import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! Canonical public generation contexts are immutable across native attempts. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def cachedRegion (p : Inputs) : Region := ⟨State.addr p.cachedContext, 8 * p.cachedWords⟩

structure CachedGenerationContext (p : Inputs) (s : State) : Prop where
  canonical : Spec.Ffdh.generationContextAt s.mem (State.addr p.cachedContext)
    p.cachedWords p.k p.dom
  valid : Spec.Ffdh.domainValid p.k p.dom
  fit : p.cachedContext.toNat + 8 * p.cachedWords ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (State.addr p.cachedContext) (8 * p.cachedWords)
  separate : ∀ r ∈ keyCallWrites p s, (cachedRegion p).Disjoint r

theorem CachedGenerationContext.after {p : Inputs} {s t : State}
    (h : CachedGenerationContext p s) (frame : Frame (keyCallWrites p s) s.mem t.mem)
    (rest : Rest VG.Proof.Bignum.Arm.roundClobbers s t) : CachedGenerationContext p t := by
  have words : Spec.Rsa.wordsAt t.mem (State.addr p.cachedContext) p.cachedWords =
      Spec.Rsa.wordsAt s.mem (State.addr p.cachedContext) p.cachedWords := by
    unfold Spec.Rsa.wordsAt
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    apply frame.readW (r := cachedRegion p) _ h.separate (by decide)
    simp only [cachedRegion, Region.Contains, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.fit; omega : 8 * i < 2 ^ 64)]
    omega
  refine ⟨?_, h.valid, h.fit, ?_, ?_⟩
  · simpa only [Spec.Ffdh.generationContextAt, words] using h.canonical
  · rw [rest.rd, rest.wr]; exact h.readable
  · simpa only [keyCallWrites, keyWrites, rest.sp] using h.separate

def cachedGenerationEnvironment : SampleEnvironment where
  holds := CachedGenerationContext
  publicRel := fun _ _ => True
  stable := fun h frame rest _ => h.after frame rest
  public_stable := fun _ _ _ => trivial

end VG.Proof.Ffdh.Arm
