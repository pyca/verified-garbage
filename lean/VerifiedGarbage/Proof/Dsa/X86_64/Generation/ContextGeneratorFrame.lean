module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryGeneratorWork
import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.Generation.Memory

/-! # Generator writes preserve the outer seed state and saved q -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem GenerationContext.generator_frame {p : GenerationContext} {m m' : Mem}
    (hf : Frame p.geo.gWork m m') : Frame p.changed m m' := by
  apply GenerationContext.frame_parts hf
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with h | h | h <;> omega
  have part (d n : Nat) (bound : d + n ≤ usedBytes p.geo.pLen) :
      ∃ out ∈ p.changed, Region.Sub (p.geo.part d n) out :=
    ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed], p.geo.part_sub bound⟩
  intro r hr
  simp only [GenerationGeometry.gWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact part arithmetic arithmeticBytes (p.geo.small_bound (by decide) (by rfl))
  · simpa [GenerationGeometry.part, off] using part 0 Impl.Dsa.Layout.activeBytes (by simpa using p.geo.parentRoom)
  · exact part g p.geo.pLen (p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega))
  · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩

theorem GenerationGeometry.generator_q {p : GenerationGeometry} {m m' : Mem}
    (hf : Frame p.gWork m m') :
    Spec.Rsa.bytesAt m' (off p.B q) p.qLen = Spec.Rsa.bytesAt m (off p.B q) p.qLen := by
  have qn : p.qLen ≤ 32 := by rcases p.qWidth with h | h <;> omega
  exact VG.Proof.Dsa.Generation.frame_bytesAt hf
    (p.gWork_separate (d := q) (n := p.qLen) (by rfl) (by unfold q g; omega)) (by omega)

end VG.Proof.Dsa.X86_64.Generation
