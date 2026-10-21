module

public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Proof.Framework.Mem

/-! # A frame disjoint from the workspace preserves all of its bytes -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86
open VG VG.Proof.MillerRabin.X86

theorem workspace_of_frame {g : Geometry} {rs : List Region} {m m' : Mem}
    (F : Frame rs m m') (fit : g.W.toNat + g.L ≤ 2 ^ 32)
    (apart : ∀ r ∈ rs, (⟨g.W, g.L⟩ : Region).Disjoint r) : WorkspaceFrame g [] m m' := by
  intro i index _
  exact F.bytes (R := ⟨g.W, g.L⟩) apart (by change g.L ≤ 2 ^ 64; omega) index

end VG.Proof.RsaKeyGen.X86
