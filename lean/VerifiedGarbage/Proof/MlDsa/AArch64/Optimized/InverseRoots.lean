import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Inverse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableDecode

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop wp_ldrq)

/-- Static table root and reciprocal, loaded without touching the live bank. -/
theorem rootLoads_ok (off : Nat) (ha : off%16=0) (hi : off+16<65536)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (off+16)) 16)
    (k : ∀ t, VChg [.v20,.v21] s t →
      t.v .v20=s.mem.read (s.gpr .x1+BitVec.ofNat 64 off) 16 →
      t.v .v21=s.mem.read (s.gpr .x1+BitVec.ofNat 64 (off+16)) 16 → WP isa (.block rest) t Q) :
    WP isa (.block (.ldrq .v20 .x1 off :: .ldrq .v21 .x1 (off+16) :: rest)) s Q := by
  refine wp_ldrq (by omega) rfl hr fun a h₁ => ?_
  refine wp_ldrq (by omega) rfl ?_ fun t h₂ => ?_
  · simpa only [h₁.rd,h₁.wr,h₁.gpr] using hb
  · refine k t (h₁.chg.trans h₂.chg) ?_ ?_
    · rw [h₂.get .v20,h₁.v]
    · rw [h₂.v,h₁.mem,h₁.gpr]

/-- Hoisted roots and reciprocals occupy separate vectors in the inverse pass. -/
theorem rootDup_ok (src recip : VReg) (i : Nat) (hi : i<4) (hr : recip≠.v20)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v20,.v21] s t →
      (∀ e<4, vword (t.v .v20) e=vword (s.v src) i) →
      (∀ e<4, vword (t.v .v21) e=vword (s.v recip) i) → WP isa (.block rest) t Q) :
    WP isa (.block (.vop (.dupE .s4 .v20 src i) :: .vop (.dupE .s4 .v21 recip i) :: rest)) s Q := by
  have he (t : State) (d a : VReg) : (VOp.dupE .s4 d a i).eval t=some (d,
      VArr.s4.map2 (fun w _ _ => (t.v a).extractLsb' (w*i) w) 0 0) := by
    simp only [VOp.eval,VArr.esize,show 128/32=4 by decide,hi,ite_true]
  refine wp_vop (he s .v20 src) fun a h₁ => wp_vop (he a .v21 recip) fun t h₂ => ?_
  refine k t (h₁.chg.trans h₂.chg) ?_ ?_
  · intro e h4
    rw [h₂.get .v20,h₁.v,VG.AArch64.vword_map2 _ _ _ h4]
    rfl
  · intro e h4
    rw [h₂.v,VG.AArch64.vword_map2 _ _ _ h4,h₁.get recip hr]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
