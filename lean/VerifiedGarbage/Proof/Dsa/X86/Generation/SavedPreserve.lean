module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.OuterSetup
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryResult
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The search's actual stack footprint excludes the saved caller registers -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem ParameterABI.savedApart {s : State} (A : ParameterABI s) :
    ∀ r ∈ entryWrites s, (⟨outerBase s, 16⟩ : Region).Disjoint r := by
  have sub : Region.Sub ⟨outerBase s, 16⟩ ⟨(s.gpr .esp).setWidth 64 - 292#64, 292⟩ := by
    rw [A.outerBase_eq]
    exact fun x hx => Offset.below_mono _ (a := 16) (b := 292) (by decide) (by decide) x hx
  intro r hr
  simp only [entryWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.stackScratch.sub_left sub
  · exact A.stackOut.sub_left sub
  · rw [A.outerBase_eq, Offset.sub_ofNat_eq _ (a := 16) (b := 292) (by decide)]
    exact Offset.disjoint_base _ (by decide) (by decide)

theorem SavedRegisters.searchKeep {s : State} {m m' : Mem} (A : ParameterABI s)
    (saved : SavedRegisters s (outerBase s) m) (O : Frame (entryWrites s) m m') :
    SavedRegisters s (outerBase s) m' := by
  have words (j : Nat) (bound : j < 4) :
      m'.readW (off (outerBase s) (4 * j)) 32 = m.readW (off (outerBase s) (4 * j)) 32 :=
    O.readW (Offset.contains_base _ (by omega) (by omega)) A.savedApart (by decide)
  exact ⟨(words 0 (by decide)).trans saved.1, (words 1 (by decide)).trans saved.2.1,
    (words 2 (by decide)).trans saved.2.2.1, (words 3 (by decide)).trans saved.2.2.2⟩
end VG.Proof.Dsa.X86.Generation
