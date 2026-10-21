module

public import VerifiedGarbage.Proof.MillerRabin.X86.Data
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
import VerifiedGarbage.Proof.MillerRabin.X86.Equal
import VerifiedGarbage.Proof.MillerRabin.X86.DataScalar

/-! # A prepared-array comparison records its exact equality bit -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Data.equal {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V : Nat → BitVec 32} {Ds : List Nat} {s : State} (D : Data g A Js V Ds s)
    (d a b : Nat) (scratch : scratchWord d) (aKnown : a ∈ Js) (bKnown : b ∈ Js) :
    WP isa (equal d a b) s fun t =>
      Data g A Js (setAt V d (BitVec.ofNat 32 (decide (A a = A b)).toNat)) (d :: Ds) t ∧
      Outside g.W d 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have av := D.arrayValues a aKnown
  have bv := D.arrayValues b bKnown
  have bound := scratch_fit scratch
  refine WP.mono (equal_ok v D.context d a b (by have := v.headerFit; omega) av.1 bv.1)
    fun t ⟨Value, O, K⟩ => ?_
  have C := D.context.keepScalar K (by decide) O scratch
  rw [av.2, bv.2] at Value
  have stored : t.mem.readW (off g.W d) 32 = BitVec.ofNat 32 (decide (A a = A b)).toNat := by
    apply BitVec.eq_of_toNat_eq
    change w32 t.mem g.W d = _
    rw [Value]
    cases decide (A a = A b) <;> rfl
  exact ⟨D.afterScalar v C d scratch _ O stored, O, K⟩

end VG.Proof.MillerRabin.X86
