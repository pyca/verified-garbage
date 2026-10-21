module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportState
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Import
import VerifiedGarbage.Proof.Framework.Mem

/-! # A complete candidate or witness import, with exact reversed words -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Import

theorem code_ok {g : Geometry} {s : State} (C : Context g s)
    (source : s.gpr .esi = g.sourcePtr 0) (destination : s.gpr .ebx = g.destPtr 0)
    (count : s.gpr .ecx = BitVec.ofNat 32 g.count) :
    WP isa code s (StateAt g s g.count) := by
  let Inv := fun q t => ∃ i, i + q = g.count ∧ 0 < q ∧ StateAt g s i t
  unfold code
  refine WP.loop (M := isa) Inv ?_ g.count s ?_
  · rintro q t ⟨i, iq, positive, T⟩
    refine WP.mono (T.step C (by omega)) fun u ⟨U, Z⟩ => ?_
    by_cases done : i + 1 = g.count
    · left
      refine ⟨?_, done ▸ U⟩
      change u.zf.map Bool.not = some false
      rw [Z, decide_eq_true done]
      rfl
    · right
      refine ⟨?_, q - 1, by omega, i + 1, by omega, by omega, U⟩
      change u.zf.map Bool.not = some true
      rw [Z, decide_eq_false done]
      rfl
  · exact ⟨0, by omega, C.positive, by omega, source, destination,
      by simpa only [Nat.sub_zero] using count, by intro j h; omega, Frame.refl _ _, Keeps.refl _ _⟩

end VG.Proof.RsaKeyGen.X86.Import
