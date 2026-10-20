module

public import VerifiedGarbage.Proof.MillerRabin.X86.Data

/-! # Updating a scratch word preserves all known array and other scalar values -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont

theorem Data.afterScalar {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V : Nat → BitVec 32} {Ds : List Nat} {s t : State} (D : Data g A Js V Ds s)
    (C : Context g t) (d : Nat) (scratch : scratchWord d) (value : BitVec 32)
    (O : Outside g.W d 4 s.mem t.mem) (stored : t.mem.readW (off g.W d) 32 = value) :
    Data g A Js (setAt V d value) (d :: Ds) t := by
  have fit := scratch_fit scratch
  refine ⟨C, ?_, ?_⟩
  · intro j known
    obtain ⟨index, read⟩ := D.arrayValues j known
    have header := v.arrayHeader j
    refine ⟨index, ?_⟩
    rw [O.val32 (by omega) (by have := v.arrayFit index; have := C.ws.nowrap; omega), read]
  · intro e known
    by_cases same : e = d
    · subst e
      exact ⟨scratch, by rw [setAt_self]; exact stored⟩
    · have old : e ∈ Ds := by
        rcases List.mem_cons.mp known with bad | old
        · exact False.elim (same bad)
        · exact old
      obtain ⟨es, read⟩ := D.slotValues e old
      have apart := scratch_apart es scratch same
      have bound := scratch_fit es
      refine ⟨es, ?_⟩
      have unchanged := BitVec.eq_of_toNat_eq (O.w32 (d := e) (by omega) (by omega))
      rw [unchanged, read, setAt_other V value same]

end VG.Proof.MillerRabin.X86
