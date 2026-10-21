module

public import VerifiedGarbage.Impl.Mont.X86.CombPower
import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! Zero padding retains the exponent's value at a wider public storage width. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem padWords_ok {s : State} {base : Addr} {size o used total : Nat}
    (hs : Scr s base size) (hu : used≤total) (ho : o+4*total≤size) :
    WP isa (VG.Impl.Mont.X86.Comb.padWords o used total) s fun t =>
      Outside base (o+4*used) (4*(total-used)) s.mem t.mem ∧
      val32 t.mem base o total=val32 s.mem base o used ∧ Keeps [.eax,.ebp,.edx] s t := by
  unfold VG.Impl.Mont.X86.Comb.padWords
  split
  next h =>
    refine WP.mono (zerosW_ok hs (by omega) (by omega)) fun t ⟨O,V,K⟩ => ⟨O,?_,K⟩
    have hn := hs.nowrap
    have bound : o+4*used≤2^64 := by omega
    have eq : total=used+(total-used) := by omega
    rw [eq,val32_append,O.val32 (.inl (by omega)) bound,V,Nat.mul_zero,Nat.add_zero]
  next h =>
    have eq : total=used := by omega
    subst total
    exact WP.block_nil ⟨Outside.refl _ _ _ _,rfl,Keeps.refl _ _⟩

end VG.Proof.Mont.X86.Comb
