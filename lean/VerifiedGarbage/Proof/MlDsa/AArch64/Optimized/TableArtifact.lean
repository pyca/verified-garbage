import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableDecode

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

/-- Exact immutable 64-bit artifact contents, before splitting into SIMD lanes. -/
def ExpandedArtifact (m : Mem) (p : Addr) : Prop :=
  ∀ i<488, m.readW (p+BitVec.ofNat 64 (8*i)) 64=staticNttWords[i]!

theorem ExpandedArtifact.words {m : Mem} {p : Addr} (h : ExpandedArtifact m p) :
    ExpandedWords m p := by
  intro k hk
  have hi : k/2<488 := by omega
  have hv := h (k/2) hi
  have hr : k%2=0 ∨ k%2=1 := by omega
  rcases hr with hr | hr
  · have he : k=2*(k/2) := by omega
    have hx := congrArg (fun v : BitVec 64 => v.extractLsb' 0 32) hv
    rw [readW64_lo,TableConstants.staticNttWords_low hi] at hx
    simpa only [show 8*(k/2)=4*k by omega,← he] using hx
  · have he : k=2*(k/2)+1 := by omega
    have hx := congrArg (fun v : BitVec 64 => v.extractLsb' 32 32) hv
    rw [readW64_hi,TableConstants.staticNttWords_high hi,BitVec.add_assoc,
      ← BitVec.ofNat_add (8*(k/2)) 4] at hx
    simpa only [show 8*(k/2)+4=4*k by omega,← he] using hx

theorem ExpandedArtifact.roots {m : Mem} {p : Addr} (h : ExpandedArtifact m p) :
    HoistedTable m p ordinaryRoot ∧ RootTable m p innerRoot tailRoot :=
  ⟨h.words.hoisted,h.words.roots⟩

end VG.Proof.MlDsa.AArch64.Optimized
