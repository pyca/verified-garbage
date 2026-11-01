module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2

/-! # Fast R² setup retains the saved c-1 and the prepared exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PreparedR2
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86

theorem preserve {g : Geometry} (v : g.Valid) {s t : Mem} (F : WorkspaceFrame g (ranges g) s t)
    {j : Nat} (index : j = 5 ∨ j = 27) :
    val32 t g.W (g.array j) g.words = val32 s g.W (g.array j) g.words := by
  apply F.val32 (v.arrayFit (by omega))
  intro r mem
  simp only [ranges, coreRanges, phaseRanges, montWrites, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at mem
  rcases index with rfl | rfl <;>
    rcases mem with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl <;>
    simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
      VG.Proof.Mont.X86.accLen, VG.Impl.Bignum.X86.PublicContext.modulus, VG.Impl.Mont.X86.words] <;> omega

end VG.Proof.RsaKeyGen.X86.PreparedR2
