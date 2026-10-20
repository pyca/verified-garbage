module

public import VerifiedGarbage.Proof.MillerRabin.X86.Data
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
import VerifiedGarbage.Proof.MillerRabin.X86.Copy

/-! # Copying a prepared array as a value-state transition -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Data.copy {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V : Nat → BitVec 32} {Ds : List Nat} {s : State} (D : Data g A Js V Ds s)
    (dst src : Nat) (dstIndex : dst < 28) (srcKnown : src ∈ Js) :
    WP isa (copy dst src) s fun t =>
      Data g (setAt A dst (A src)) (dst :: Js) V Ds t ∧
      Outside g.W (g.array dst) (4 * g.words) s.mem t.mem ∧
      Keeps [.eax, .ebx, .edx, .ebp, .esi] s t := by
  have source := D.arrayValues src srcKnown
  refine WP.mono (copy_ok v D.context dst src dstIndex source.1) fun t ⟨Value, O, K, C⟩ => ?_
  refine ⟨⟨C, ?_, ?_⟩, O, K⟩
  · intro j known
    by_cases same : j = dst
    · subst j
      exact ⟨dstIndex, by rw [setAt_self, Value, source.2]⟩
    · have old : j ∈ Js := by
        rcases List.mem_cons.mp known with bad | old
        · exact False.elim (same bad)
        · exact old
      obtain ⟨index, read⟩ := D.arrayValues j old
      have sep := (g.arraysApart dst j).resolve_left (g.array_ne (fun eq => same eq.symm))
      refine ⟨index, ?_⟩
      rw [O.val32 (by omega) (by have := v.arrayFit index; have := C.ws.nowrap; omega), read,
        setAt_other A (A src) same]
  · intro d known
    obtain ⟨scratch, read⟩ := D.slotValues d known
    refine ⟨scratch, ?_⟩
    have header := v.arrayHeader dst
    have bound := scratch_fit scratch
    have unchanged := BitVec.eq_of_toNat_eq (O.w32 (d := d) (by omega) (by omega))
    exact unchanged.trans read

end VG.Proof.MillerRabin.X86
