module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryResult
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryStart
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Hashes
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryBody
import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryPermissions
import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryReady
import VerifiedGarbage.Proof.Dsa.X86.Generation.Reframe

/-! # Run the inner body using only subregions of the caller's actual permissions -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem entryBody_narrow_ok (H : GenerationHashes) (F : KeyRandom.CheckCall.CheckFn)
    {s t : State} {A : ParameterABI s} (R : EntryStart A t) :
    WP isa (entryBody H.sha1 H.sha256 F.name F.code) t (EntryResult s t) := by
  let W : Nat → BitVec 32 := fun i => t.mem.readW (off A.geometry.frameBase (4 * i)) 32
  have words : FrameWords (t.withRegions s.rd (bodyWrites A)).mem A.geometry.frameBase W := fun _ _ => rfl
  have run := entryBody_ok H F R.resources words (by
    intro i hi
    exact ⟨argRegion s 0 (arg s 1).toNat, by simp [bodyWrites], Offset.contains_base _ (by omega) (by have := (arg s 1).isLt; omega)⟩)
  have result : WP isa (entryBody H.sha1 H.sha256 F.name F.code) (t.withRegions s.rd (bodyWrites A))
      (EntryResult s (t.withRegions s.rd (bodyWrites A))) := WP.mono run fun _ h => generationResult_external h
  refine wp_reframe result R.covers.1 R.covers.2 (fun _ h => ⟨h.2.2.2.1, h.2.2.2.2.1⟩) ?_
  intro u rd wr h
  exact ⟨h.1, h.2.1, h.2.2.1, rd, wr, h.2.2.2.2.2⟩
end VG.Proof.Dsa.X86.Generation
