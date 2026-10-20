module
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.Lit


@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64

theorem gather_lanes {x y : BitVec 128} {A : Nat → Nat}
    (hx : Lanes x A) (hy : Lanes y (fun e => A (4+e))) :
    Lanes (VPermOp.eval .uzp1 .s4 x y) (fun e => A (2*e)) ∧
    Lanes (VPermOp.eval .uzp2 .s4 x y) (fun e => A (2*e+1)) := by
  constructor
  · intro e he
    rw [vword_uzp1_s4 _ _ he]
    split
    · exact hx _ (by omega)
    · rw [hy _ (by omega)]; dsimp only; congr 1; omega
  · intro e he
    rw [vword_uzp2_s4 _ _ he]
    split
    · exact hx _ (by omega)
    · rw [hy _ (by omega)]; dsimp only; congr 1; omega

def gather : List Instr :=
  [.vop (.perm .uzp1 .s4 .v6 .v0 .v1), .vop (.perm .uzp2 .s4 .v7 .v0 .v1),
   .vop (.perm .uzp1 .s4 .v19 .v4 .v5), .vop (.perm .uzp2 .s4 .v20 .v4 .v5)]

theorem gather_ok {rest : List Instr} {s : State} {Q : State → Prop} {F G : Nat → Nat}
    (f0 : Lanes (s.v .v0) F) (f1 : Lanes (s.v .v1) (fun e => F (4+e)))
    (g0 : Lanes (s.v .v4) G) (g1 : Lanes (s.v .v5) (fun e => G (4+e)))
    (k : ∀ s', VChg [.v6, .v7, .v19, .v20] s s' →
      Lanes (s'.v .v6) (fun e => F (2*e)) → Lanes (s'.v .v7) (fun e => F (2*e+1)) →
      Lanes (s'.v .v19) (fun e => G (2*e)) → Lanes (s'.v .v20) (fun e => G (2*e+1)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (gather ++ rest)) s Q := by
  simp only [gather, List.cons_append, List.nil_append]
  refine wp_vop (d := .v6) rfl fun s₁ h₁ => wp_vop (d := .v7) rfl fun s₂ h₂ =>
    wp_vop (d := .v19) rfl fun s₃ h₃ => wp_vop (d := .v20) rfl fun s₄ h₄ => ?_
  refine k s₄ (((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).mono ?_ ?_ ?_ ?_
  · rw [h₄.get .v6, h₃.get .v6, h₂.get .v6, h₁.v]; exact (gather_lanes f0 f1).1
  · rw [h₄.get .v7, h₃.get .v7, h₂.v, h₁.get .v0, h₁.get .v1]
    exact (gather_lanes f0 f1).2
  · rw [h₄.get .v19, h₃.v, h₂.get .v4, h₂.get .v5, h₁.get .v4, h₁.get .v5]
    exact (gather_lanes g0 g1).1
  · rw [h₄.v, h₃.get .v4, h₃.get .v5, h₂.get .v4, h₂.get .v5, h₁.get .v4, h₁.get .v5]
    exact (gather_lanes g0 g1).2

def loads : List Instr := [.ldrq .v0 .x1 0, .ldrq .v1 .x1 16, .ldrq .v4 .x2 0, .ldrq .v5 .x2 16]

theorem loads_ok {rest : List Instr} {s : State} {Q : State → Prop}
    (hf : ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (16*i)) 16)
    (hg : ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (16*i)) 16)
    (k : ∀ s', VChg [.v0, .v1, .v4, .v5] s s' →
      s'.v .v0 = s.mem.read (s.gpr .x1) 16 →
      s'.v .v1 = s.mem.read (s.gpr .x1 + BitVec.ofNat 64 16) 16 →
      s'.v .v4 = s.mem.read (s.gpr .x2) 16 →
      s'.v .v5 = s.mem.read (s.gpr .x2 + BitVec.ofNat 64 16) 16 →
      WP isa (.block rest) s' Q) :
    WP isa (.block (loads ++ rest)) s Q := by
  simp only [loads, List.cons_append, List.nil_append]
  refine wp_ldrq (by decide) rfl (hf 0 (by decide)) fun s₁ h₁ => ?_
  refine wp_ldrq (by decide) rfl (by rw [h₁.rd, h₁.wr, h₁.gpr]; exact hf 1 (by decide)) fun s₂ h₂ => ?_
  refine wp_ldrq (by decide) rfl (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, h₂.gpr, h₁.gpr]; exact hg 0 (by decide)) fun s₃ h₃ => ?_
  refine wp_ldrq (by decide) rfl (by rw [h₃.rd, h₃.wr, h₂.rd, h₂.wr, h₁.rd, h₁.wr, h₃.gpr, h₂.gpr, h₁.gpr]; exact hg 1 (by decide)) fun s₄ h₄ => ?_
  refine k s₄ (((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).mono ?_ ?_ ?_ ?_
  · rw [h₄.get .v0, h₃.get .v0, h₂.get .v0, h₁.v]; simp only [BitVec.add_zero]
  · rw [h₄.get .v1, h₃.get .v1, h₂.v, h₁.mem, h₁.gpr]
  · rw [h₄.get .v4, h₃.v, h₂.mem, h₁.mem, h₂.gpr, h₁.gpr]; simp only [BitVec.add_zero]
  · rw [h₄.v, h₃.mem, h₂.mem, h₁.mem, h₃.gpr, h₂.gpr, h₁.gpr]

end VG.Proof.MlKem.AArch64.Dot
