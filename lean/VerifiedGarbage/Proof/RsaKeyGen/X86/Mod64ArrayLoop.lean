module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayStep

/-! # Reduce every native word while preserving the full modular prefix invariant -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem loop_ok {g : ArrayGeometry} (v : g.Valid) {candidate exponent : Nat} {s : State}
    (S : ArrayState g candidate exponent 0 s) :
    WP isa (.loop (arrayStep g.exponent) .ne) s fun t =>
      ArrayState g candidate exponent g.n t ∧ Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let Inv := fun q t => ∃ i, i + q = g.n ∧ 0 < q ∧ ArrayState g candidate exponent i t ∧
    Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  refine WP.loop (M := isa) Inv ?_ g.n s ⟨0, by omega, v.positive, S, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  rintro q t ⟨i, count, positive, T, O, K⟩
  refine WP.mono (T.step v (by omega)) fun u ⟨U, Z, Ou, Ku⟩ => ?_
  by_cases done : i + 1 = g.n
  · left
    refine ⟨?_, done ▸ U, O.trans Ou, K.trans Ku⟩
    change u.zf.map Bool.not = some false
    rw [Z, decide_eq_true done]
    rfl
  · right
    refine ⟨?_, q - 1, by omega, i + 1, by omega, by omega, U, O.trans Ou, K.trans Ku⟩
    change u.zf.map Bool.not = some true
    rw [Z, decide_eq_false done]
    rfl

end VG.Proof.RsaKeyGen.X86.Mod64
