module

public import VerifiedGarbage.Proof.X448.Contract
import VerifiedGarbage.Proof.X448.AArch64.Finish
public import VerifiedGarbage.Spec.X448.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.X448.AArch64.Env
import VerifiedGarbage.Proof.X448.AArch64.Bits
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.X25519
import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Proof.X448.Invert

/-!
# X448 on AArch64: the whole function

The contract the proof is written against (the facts of
`Proof.X448.x448Contract` it uses, stated for AArch64), and the correctness of
`vg_x448` against it: every write is in the working space but the result's, so
the arguments are read unchanged, the callee-saved registers restored from the
working space, and the return address kept.
-/

@[expose] public section

namespace VG.Proof.X448

open VG VG.AArch64 in
/-- `vg_x448(out = x0, scalar = x1, point = x2, scratch = x3)`. -/
def x448AArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 56⟩
    let scalar : Region := ⟨s.gpr .x1, 56⟩
    let point : Region := ⟨s.gpr .x2, 56⟩
    let scratch : Region := ⟨s.gpr .x3, 8192⟩
    s.rd = [scalar, point] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ point.Disjoint scratch ∧
      (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64
  post s s' := Spec.X448.bytesAt s'.mem (s.gpr .x0) 56 =
    Spec.X448.x448 (Spec.X448.bytesAt s.mem (s.gpr .x1) 56)
      (Spec.X448.bytesAt s.mem (s.gpr .x2) 56)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.X448

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Proof.X448

section
variable (s₀ : State)
abbrev outR : Region := ⟨s₀.gpr .x0, 56⟩
abbrev scalarR : Region := ⟨s₀.gpr .x1, 56⟩
abbrev pointR : Region := ⟨s₀.gpr .x2, 56⟩
abbrev scR : Region := ⟨s₀.gpr .x3, 8192⟩
end

/-- The precondition, by name. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [scalarR s₀, pointR s₀]
  wr : s₀.wr = [outR s₀, scR s₀]
  out_sc : (outR s₀).Disjoint (scR s₀)
  scalar_sc : (scalarR s₀).Disjoint (scR s₀)
  point_sc : (pointR s₀).Disjoint (scR s₀)
  sc_fit : (s₀.gpr .x3).toNat + 8192 ≤ 2 ^ 64

theorem Pre.of (s₀ : State) (h : Proof.X448.x448AArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega

theorem bytesAt_outside {base p : Addr} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hp : ∀ i < 56, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    Spec.X448.bytesAt m' p 56 = Spec.X448.bytesAt m p 56 := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact hp i hi

theorem far_output {base p : Addr} (hd : (⟨p, 56⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < 8192) : 56 ≤ ofs p (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192) (by omega) (by omega))
  simp only [Region.Contains]
  change ofs p (off base i) + 1 ≤ 56
  omega

end VG.Proof.X448.AArch64
