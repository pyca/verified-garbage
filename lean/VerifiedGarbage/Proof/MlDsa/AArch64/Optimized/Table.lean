import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop wp_ldrq)

/-- One prearranged vector of roots and one of exact reciprocal multipliers. -/
theorem rootAt_ok (base : Reg) (i : Nat) (hi : i < 2048)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : InRegions (s.rd ++ s.wr) (s.gpr base + BitVec.ofNat 64 (32*i)) 16)
    (hb : InRegions (s.rd ++ s.wr) (s.gpr base + BitVec.ofNat 64 (32*i+16)) 16)
    (k : ∀ t, VChg [.v18,.v19] s t →
      t.v .v18 = s.mem.read (s.gpr base + BitVec.ofNat 64 (32*i)) 16 →
      t.v .v19 = s.mem.read (s.gpr base + BitVec.ofNat 64 (32*i+16)) 16 →
      WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.Ntt.rootAt base i ++ rest)) s Q := by
  refine wp_ldrq (by omega) rfl hr fun s₁ h₁ => ?_
  refine wp_ldrq (by omega) rfl ?_ fun s₂ h₂ => ?_
  · simpa only [h₁.rd, h₁.wr, h₁.gpr] using hb
  · refine k s₂ (h₁.chg.trans h₂.chg) ?_ ?_
    · rw [h₂.get .v18, h₁.v]
    · rw [h₂.v, h₁.mem, h₁.gpr]

/-- The first three layers broadcast paired ordinary roots and reciprocals
from the four hoisted vectors. -/
theorem rootPair_ok (src : VReg) (i : Nat) (hi : i < 2) (hs : src ≠ .v18)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v18,.v19] s t →
      (∀ e < 4, vword (t.v .v18) e = vword (s.v src) (2*i)) →
      (∀ e < 4, vword (t.v .v19) e = vword (s.v src) (2*i+1)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (.vop (.dupE .s4 .v18 src (2*i)) ::
      .vop (.dupE .s4 .v19 src (2*i+1)) :: rest)) s Q := by
  have he (t : State) (d : VReg) (j : Nat) (hj : j < 4) :
      (VOp.dupE .s4 d src j).eval t = some (d,
        VArr.s4.map2 (fun w _ _ => (t.v src).extractLsb' (w*j) w) 0 0) := by
    simp only [VOp.eval, VArr.esize, show 128 / 32 = 4 by decide, hj, ite_true]
  refine wp_vop (he s .v18 (2*i) (by omega)) fun s₁ h₁ =>
    wp_vop (he s₁ .v19 (2*i+1) (by omega)) fun s₂ h₂ => ?_
  refine k s₂ (h₁.chg.trans h₂.chg) ?_ ?_
  · intro e he4
    rw [h₂.get .v18, h₁.v, VG.AArch64.vword_map2 _ _ _ he4]
    rfl
  · intro e he4
    rw [h₂.v, VG.AArch64.vword_map2 _ _ _ he4, h₁.get src hs]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized
