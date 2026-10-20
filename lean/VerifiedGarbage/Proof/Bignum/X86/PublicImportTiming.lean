module
public import VerifiedGarbage.Proof.Bignum.X86.PublicPair

import VerifiedGarbage.Proof.Bignum.X86.PublicLoadTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Both RSA integer imports have traces fixed by public call geometry -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext

theorem importNumbers_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (PublicPair base bytes len args) (PublicFn.importNumbers (Spec.Rsa.modulusWords len))
      (PublicPair base bytes len args) := by
  have One (i j slotIndex : Nat) (hi : i < 10) (hj : j < 10) (hs : slotIndex < 8)
      (geometry : ∀ s, PublicInputs base bytes len args s →
        args j = BitVec.ofNat 32 len ∧ (args i).toNat + len ≤ 2 ^ 32 ∧
        InRegions (s.rd ++ s.wr) (byteAddr (args i)) len ∧
        Region.Disjoint ⟨byteAddr (args i), len⟩ ⟨base, bytes⟩) :
      RelCT isa (PublicPair base bytes len args)
        (loadArgument i j (Spec.Rsa.modulusWords len) (slot (Spec.Rsa.modulusWords len) slotIndex))
        (PublicPair base bytes len args) := by
    intro s t tr ur sf tf H E F
    have Gs := geometry s H.left
    have Gt := geometry t H.right
    have bound := PublicContext.slot_bound (n := Spec.Rsa.modulusWords len) hs
    have space := H.left.space
    simp only [stride] at bound
    exact loadArgument_relCT base bytes len _ _ i j args hi hj Gs.1 H.left.dimensions.1
      H.left.dimensions.2.2 (by omega) Gs.2.1 Gs.2.2.2 _ _ _ _ _ _ ⟨H, Gs.2.2.1, Gt.2.2.1⟩ E F
  apply VG.RelCT.assoc
  exact VG.RelCT.seq (One 2 3 0 (by decide) (by decide) (by decide)
    (fun _ H => ⟨H.nLen, H.nFit, H.nRead, H.nApart⟩))
    (One 6 7 6 (by decide) (by decide) (by decide)
      (fun _ H => ⟨H.inLen, H.inFit, H.inRead, H.inApart⟩))

end VG.Proof.Bignum.X86
