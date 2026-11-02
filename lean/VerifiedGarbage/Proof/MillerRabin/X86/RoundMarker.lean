module

public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.MillerRabin.X86.MarkerPointer

/-! # The prepared exponent marker survives every round write -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86 VG.Proof.Mont

theorem roundFrame_marker32 {g : Geometry} (v : g.Valid) {m m' : Mem}
    (F : WorkspaceFrame g (roundWrites g) m m') {extra : Nat} (half : extra = 0 ∨ extra = 4) :
    m'.readW (off g.W (g.array aExponent + 4 * g.words + extra)) 32 =
      m.readW (off g.W (g.array aExponent + 4 * g.words + extra)) 32 := by
  apply F.read32 (by have := v.markerFit; omega)
  intro r mem
  simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> right <;>
    unfold Geometry.array Geometry.words aExponent Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes <;> omega

end VG.Proof.MillerRabin.X86
