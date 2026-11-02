module

public import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame
public import VerifiedGarbage.TCB.Mem

/-! # Preparing one and minus one preserves R², c-1 and the exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Constants
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86

def ranges (g : Geometry) : List (Nat × Nat) := montWrites g 6 ++ [(g.array 9, 4 * g.words), (g.array 10, 4 * g.words)]

theorem preserve {g : Geometry} (v : g.Valid) {s t : Mem} (F : WorkspaceFrame g (ranges g) s t)
    {j : Nat} (index : j = 4 ∨ j = 5 ∨ j = 27) :
    val32 t g.W (g.array j) g.words = val32 s g.W (g.array j) g.words := by
  apply F.val32 (v.arrayFit (by omega))
  intro r mem
  simp only [ranges, montWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases index with rfl | rfl | rfl <;>
    rcases mem with (rfl | rfl | rfl) | (rfl | rfl) <;>
    simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega

end VG.Proof.RsaKeyGen.X86.Constants
