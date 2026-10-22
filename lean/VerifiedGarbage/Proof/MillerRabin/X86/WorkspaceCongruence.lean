module

public import VerifiedGarbage.Proof.MillerRabin.Workspace
public import VerifiedGarbage.Proof.MillerRabin.X86.Entry
import VerifiedGarbage.Proof.Framework.Offset

/-! # Reuse the existing target-independent prepared-workspace congruence -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt numAt wOf wordAt)

export VG.Proof.MillerRabin.Workspace (workspace_congr)

theorem frame_workspace_same {s t : State} (A : RoundABI s) (F : Frame [entryFrame s] s.mem t.mem) :
    ∀ i < 8 * (arg s 1).toNat, t.mem (off (wsOf s) i) = s.mem (off (wsOf s) i) := by
  intro i hi
  have fit := A.ws_fit
  apply F
  intro r hr hc
  rw [List.mem_singleton.mp hr] at hc
  exact A.frame_apart _ hc (Offset.contains_base _ (by dsimp only [bytesOf] at fit ⊢; omega) (by omega))

end VG.Proof.MillerRabin.X86
