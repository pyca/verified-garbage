import VerifiedGarbage.Impl.Weierstrass.X86.NafPrep
import VerifiedGarbage.Proof.Mont.X86.Chain

/-! Subtracting a register from one word of the public NAF residual. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem nafSubWord_ok {s : State} {base : Addr} {size work i : Nat}
    (hs : Scr s base size) (ha : work+4*i+4≤size) {r : Reg} (hr : r≠.eax)
    {op : AluOp} {cin : Bool}
    (hop : (op=.sub ∧ cin=false) ∨ (op=.sbb ∧ s.cf=some cin)) :
    WP isa (.block (Naf.subWord op work i r)) s fun u =>
      Outside base (work+4*i) 4 s.mem u.mem ∧
      (∃ c, u.cf=some c ∧ w32 u.mem base (work+4*i)+(s.gpr r).toNat+cin.toNat =
        w32 s.mem base (work+4*i)+2^32*c.toNat) ∧ Keeps [.eax] s u := by
  have hn := hs.nowrap
  unfold Naf.subWord
  refine wp_movS (readSrc_sc hs ha) fun s₁ u₁ cf₁ => ?_
  have hs₁ := hs.of_keeps u₁.keeps (by decide)
  have hx := (s.mem.readW (off base (work+4*i)) 32).isLt
  have hy := (s.gpr r).isLt
  rcases hop with ⟨rfl,rfl⟩ | ⟨rfl,hc⟩
  · refine wp_subS rfl fun s₂ u₂ c₂ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    refine wp_storeS (hs₂.ea (by omega)) (hs₂.write ha) fun u m => WP.block_nil
      ⟨?_,⟨_,by rw [m.cf,c₂],?_⟩,(u₁.keeps.trans u₂.keeps).trans (m.keeps _)⟩
    · rw [m.mem,u₂.mem,u₁.mem]; exact writeW32_outside _ _ _ (by omega)
    · rw [m.mem,w32_write_self,u₂.gpr,sub_toNat,u₁.gpr,u₁.other _ hr]
      simp only [w32,Bool.toNat_false]
      by_cases h : (s.mem.readW (off base (work+4*i)) 32).toNat < (s.gpr r).toNat <;>
        simp only [h,decide_true,decide_false,Bool.toNat_true,Bool.toNat_false] <;> omega
  · refine wp_sbbS rfl (by rw [cf₁]; exact hc) fun s₂ u₂ c₂ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    refine wp_storeS (hs₂.ea (by omega)) (hs₂.write ha) fun u m => WP.block_nil
      ⟨?_,⟨_,by rw [m.cf,c₂],?_⟩,(u₁.keeps.trans u₂.keeps).trans (m.keeps _)⟩
    · rw [m.mem,u₂.mem,u₁.mem]; exact writeW32_outside _ _ _ (by omega)
    · rw [m.mem,w32_write_self,u₂.gpr,sub3_toNat,u₁.gpr,u₁.other _ hr]
      simp only [w32]
      have := Bool.toNat_le cin
      by_cases h : (s.mem.readW (off base (work+4*i)) 32).toNat < (s.gpr r).toNat+cin.toNat <;>
        simp only [h,decide_true,decide_false,Bool.toNat_true,Bool.toNat_false] <;> omega

end VG.Proof.Weierstrass.X86
