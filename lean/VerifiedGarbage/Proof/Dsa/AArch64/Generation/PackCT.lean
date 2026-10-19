module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PackMemoryCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PackMemoryCT

/-! # Timing of packing the complete generated domain -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.Generation.Layout VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem packPart_context_ct (src dst len : Nat) (hsrc : src + len ≤ packed) (hdst : packed ≤ dst)
    (hend : dst + len ≤ packed + 800) (hlen : 2 ≤ len ∧ len ≤ 384)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (packArgs src dst len)) hc).isSome = true) :
    RelCT isa (Two GenerationMemoryBefore) (packPart src dst len) (Two GenerationMemoryBefore) := by
  refine two_post (two_map GenerationContext.packPublic (fun _ _ h => generationMemory_pack h)
    (packPart_ct src dst len (by unfold packed at hsrc; omega) (by unfold packed at hend; omega)
      (by omega) ht)) ?_
  exact fun _ _ h => packPart_memory h src dst len hsrc hdst hend hlen

theorem pack_ct (pLen qLen : Nat)
    (sizes : (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ qLen = 32) ∨ (pLen = 384 ∧ qLen = 32)) :
    RelCT isa (Two GenerationMemoryBefore) (pack pLen qLen) (Two GenerationMemoryBefore) := by
  unfold pack
  simp only [seqs]
  rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    exact RelCT.seq (packPart_context_ct _ _ _ (by decide) (by decide) (by decide) (by decide) (by taint_decide))
      (RelCT.seq (packPart_context_ct _ _ _ (by decide) (by decide) (by decide) (by decide) (by taint_decide))
        (packPart_context_ct _ _ _ (by decide) (by decide) (by decide) (by decide) (by taint_decide)))

end VG.Proof.Dsa.AArch64.Generation
