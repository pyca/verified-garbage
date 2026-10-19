module
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCheckRegions

import VerifiedGarbage.Proof.Framework.Offset

/-! # Every check-stage write stays within the body footprint -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

theorem prefixWrite_sub {g : PrivGeometry} {d n : Nat} (fit : d + n ≤ frameBytes) :
    ∃ R ∈ bodyWrites g, (innerSlice g d n).Sub R :=
  ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ fit⟩

theorem pcPrefix_sub {g : PrivGeometry} : ∀ r ∈ pcPrefixWrites g, ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [pcPrefixWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simpa only [innerSlice, off, BitVec.add_zero] using prefixWrite_sub (g := g) (d := 0) (n := 8) (by decide)
  · exact prefixWrite_sub (by decide)

theorem pdPrefix_sub {g : PrivGeometry} : ∀ r ∈ pdPrefixWrites g, ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [pdPrefixWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simpa only [innerSlice, off, BitVec.add_zero] using prefixWrite_sub (g := g) (d := 0) (n := 24) (by decide)
  · exact prefixWrite_sub (by decide)

theorem calleeWrites_sub {g : PrivGeometry} {rs : List Region}
    (sub : ∀ r ∈ rs, ∃ R ∈ bodyWrites g, r.Sub R) :
    ∀ r ∈ rs ++ [g.calleeRegion], ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact sub r hr
  · simp only [List.mem_singleton] at hr
    subst r
    exact ⟨g.calleeRegion, by simp [bodyWrites], fun _ hx => hx⟩
end VG.Proof.Rsa.Arm
