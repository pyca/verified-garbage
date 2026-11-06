module
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.Lit

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64

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
