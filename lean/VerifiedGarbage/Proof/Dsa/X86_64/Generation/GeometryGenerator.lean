module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryGeneratorWork
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorSearchPlan
import VerifiedGarbage.Proof.Framework.Omega

/-! # Concrete generator plan over the saved p and exponent buffers -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.generatorPlan (p : GenerationGeometry) (pb eb : List Byte)
    (hp : pb.length = p.pLen) (he : eb.length = p.pLen)
    (positive : 1 < Spec.Dsa.decodeBE pb) (odd : Spec.Dsa.decodeBE pb % 2 = 1) : GeneratorPlan := by
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega
  have ha := p.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have hh := p.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have hg := p.small_bound (d := g) (n := p.pLen) (by decide) (by unfold arithmeticBytes; omega)
  have parent : 0 + Impl.Dsa.Layout.activeBytes ≤ usedBytes p.pLen := by simpa using p.parentRoom
  have gp : (p.part g p.pLen).Disjoint ⟨p.B, Impl.Dsa.Layout.activeBytes⟩ := by
    simpa [GenerationGeometry.part, off] using p.parts_disjoint hg parent (Or.inr (by decide))
  have ga := p.parts_disjoint hg ha (Or.inl (by unfold g arithmetic; omega))
  have ps := p.gWork_separate (d := VG.Impl.Dsa.Generation.Layout.p) (n := p.pLen)
    (by decide) (by unfold VG.Impl.Dsa.Generation.Layout.p g; omega)
  have es := p.gWork_separate (d := exponent) (n := p.pLen)
    (by decide) (by unfold exponent g; omega)
  refine {
    B := p.B
    A := off p.B arithmetic
    F := p.F
    S := p.hash
    hp := off p.B VG.Impl.Dsa.Generation.Layout.p
    Z := arithmeticBytes
    len := p.pLen
    pb := pb
    hb := pb
    eb := eb
    width := p.width
    arithmeticBase := rfl
    workspaceRoom := by rcases p.width with h | h | h <;> rw [h] <;> decide
    pLength := hp
    hLength := hp
    eLength := he
    pPositive := positive
    pOdd := odd
    frameHeaders := p.frame_headers
    frameOutside := p.frame_outside
    frameSeparate := ?_
    hashSeparate := ?_
    pSeparate := ps
    hSeparate := ps
    eSeparate := es
    gArithmeticSeparate := ga
    gParentOutside := ?_
    gArithmeticOutside := ?_ }
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact p.frame_part ha
    · simpa [GenerationGeometry.part, off] using p.frame_part parent
    · exact p.frame_part hg
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact p.parts_disjoint hh ha (Or.inl (by decide))
    · simpa [GenerationGeometry.part, GenerationGeometry.hash, off] using
        p.parts_disjoint hh parent (Or.inr (by decide))
    · exact p.parts_disjoint hh hg (Or.inl (by decide))
  · intro i hi
    exact out_scr gp (Offset.contains_base _ (by omega) (by omega))
  · intro i hi
    exact out_scr ga (Offset.contains_base _ (by omega) (by omega))

end VG.Proof.Dsa.X86_64.Generation
