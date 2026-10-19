module
public import Mathlib.Tactic.Conv
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryTape
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import VerifiedGarbage.Proof.Framework.Omega

/-! # Geometry of the generator's parent and arithmetic workspaces -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def GenerationGeometry.gWork (p : GenerationGeometry) : List Region :=
  [p.part arithmetic arithmeticBytes, ⟨p.B, Impl.Dsa.Layout.activeBytes⟩,
    p.part g p.pLen, ⟨p.F, frameBytes⟩]

theorem GenerationGeometry.parentRoom (p : GenerationGeometry) :
    Impl.Dsa.Layout.activeBytes ≤ usedBytes p.pLen := by
  rcases p.width with h | h | h <;> rw [h] <;> decide

theorem GenerationGeometry.gWork_separate (p : GenerationGeometry) {d n : Nat}
    (hd : q ≤ d) (hn : d + n ≤ g) : ∀ r ∈ p.gWork, (p.part d n).Disjoint r := by
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega
  have hb : d + n ≤ usedBytes p.pLen := by
    have hh := p.small_bound (d := g) (n := 0) (by decide) (by decide)
    omega
  have ha := p.small_bound (d := arithmetic) (n := arithmeticBytes) (by decide) (by rfl)
  have hg := p.small_bound (d := g) (n := p.pLen) (by decide) (by unfold arithmeticBytes; omega)
  intro r hr
  simp only [gWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact p.parts_disjoint hb ha (Or.inl (by unfold g arithmetic at *; omega))
  · simpa [GenerationGeometry.part, off] using
      p.parts_disjoint hb (e := 0) (k := Impl.Dsa.Layout.activeBytes) (by simpa using p.parentRoom)
        (Or.inr (by unfold q Impl.Dsa.Layout.activeBytes at *; omega))
  · exact p.parts_disjoint hb hg (Or.inl hn)
  · exact (p.frame_part hb).symm

theorem GenerationTape.gWork {p : GenerationGeometry} (t : GenerationTape p) :
    ∀ r ∈ p.gWork, (⟨t.ptr, t.bytes.length⟩ : Region).Disjoint r := by
  have pn : p.pLen ≤ 384 := by rcases p.width with h | h | h <;> omega
  intro r hr
  simp only [GenerationGeometry.gWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact t.part (p.small_bound (by decide) (by rfl))
  · simpa [GenerationGeometry.part, off] using
      t.part (d := 0) (n := Impl.Dsa.Layout.activeBytes) (by simpa using p.parentRoom)
  · exact t.part (p.small_bound (by decide) (by unfold arithmeticBytes; omega))
  · exact t.frame

end VG.Proof.Dsa.X86_64.Generation
