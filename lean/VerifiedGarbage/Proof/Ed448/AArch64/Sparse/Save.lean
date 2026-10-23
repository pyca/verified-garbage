module

import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Env
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.MOp
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Impl.X448.AArch64.Fast
public import VerifiedGarbage.Spec.Ed448
public import VerifiedGarbage.Spec.X448

/-! The affine formula's temporary GPR save area is disjoint from field slots. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot)
open VG.Impl.X448.AArch64.Fast (saved)
open VG.Proof.X448.AArch64 (Scr Keeps Outside word limbs)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv)
open VG.Proof.Curve448.AArch64.Fast (stw_ok ld_ok)

/-- Eight words outside all field slots and both signed-digit buffers. -/
abbrev GSAVE : Nat := 7360

def Saved (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ i<8,word m base (GSAVE+8*i)=g (saved i)

theorem save_ok {s:State} {base:Addr} (hs:Scr s base) :
    WP isa (.block ((List.range 8).map fun i => st (saved i) (GSAVE+8*i))) s fun t =>
      Saved base s.gpr t.mem ∧ Outside base GSAVE 64 s.mem t.mem ∧
      t.gpr=s.gpr ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have he:(List.range 8).map (fun i => st (saved i) (GSAVE+8*i))=
      (List.range 8).flatMap (fun i => [st (saved i) (GSAVE+8*i)]) := by
    exact List.map_eq_flatMap
  rw [he]
  let inv:=fun n (t:State) =>
    (∀ i<n,word t.mem base (GSAVE+8*i)=s.gpr (saved i)) ∧
    Outside base GSAVE 64 s.mem t.mem ∧ t.gpr=s.gpr ∧ t.rd=s.rd ∧ t.wr=s.wr
  refine wp_range_flatMap (M:=isa) (N:=8) inv (fun n t hn ⟨tv,fo,tg,tr,tw⟩ => ?_)
    8 (by decide) s ⟨fun _ h => by omega,Outside.refl _ _ _ _,rfl,rfl,rfl⟩
  have ht:Scr t base:=⟨by rw [tg];exact hs.x3,by rw [tg];exact hs.mask,tw ▸ hs.wr,hs.nowrap⟩
  refine WP.mono (stw_ok ht (saved n) (d:=GSAVE+8*n) (by simp only [GSAVE];omega) (by simp only [GSAVE];omega))
    fun u ⟨uw,uo,ug,ur,uwr⟩ => ⟨fun i hi => ?_,fo.trans (uo.mono (by simp only [GSAVE];omega) (by simp only [GSAVE];omega)),
      ug.trans tg,ur.trans tr,uwr.trans tw⟩
  rw [uw _ (by simp only [GSAVE];omega) (by simp only [GSAVE];omega)]
  by_cases h:i=n
  · subst i
    rw [ite_eq_left rfl,tg]
  · rw [ite_eq_right (by simp only [GSAVE];omega)]
    exact tv i (by omega)

theorem restore_ok {s:State} {base:Addr} (hs:Scr s base) {g:Reg → BitVec 64}
    (hsv:Saved base g s.mem) :
    WP isa (.block ((List.range 8).map fun i => ld (saved i) (GSAVE+8*i))) s fun t =>
      (∀ i<8,t.gpr (saved i)=g (saved i)) ∧ t.mem=s.mem ∧
      Keeps [.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28] s t := by
  have he:(List.range 8).map (fun i => ld (saved i) (GSAVE+8*i))=
      (List.range 8).flatMap (fun i => [ld (saved i) (GSAVE+8*i)]) := by
    exact List.map_eq_flatMap
  rw [he]
  have sinj:∀ i<8,∀ j<8,j≠i → saved j≠saved i := by decide
  have smem:∀ i<8,saved i∈[Reg.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28] := by decide
  let inv:=fun n (t:State) =>
    (∀ i<n,t.gpr (saved i)=g (saved i)) ∧ t.mem=s.mem ∧
      Keeps [.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28] s t
  refine wp_range_flatMap (M:=isa) (N:=8) inv (fun n t hn ⟨tv,tm,tk⟩ => ?_)
    8 (by decide) s ⟨fun _ h => by omega,rfl,Keeps.refl _ _⟩
  refine WP.mono (ld_ok (hs.of_keeps tk (by decide)) (saved n) (d:=GSAVE+8*n)
    (by simp only [GSAVE];omega) (by simp only [GSAVE];omega)) fun u ⟨uv,um,uk⟩ => ⟨fun i hi => ?_,um.trans tm,tk.trans (uk.mono ?_)⟩
  · by_cases h:i=n
    · subst i
      rw [uv,tm]
      exact hsv n hn
    · rw [uk.1 _ (by simp only [List.mem_singleton];exact sinj n hn i (by omega) h)]
      exact tv i (by omega)
  · intro r hr
    simp only [List.mem_singleton] at hr
    rw [hr]
    exact smem n hn

theorem save_env {base:Addr} {m m':Mem} (h:Outside base GSAVE 64 m m') :
    VG.Proof.X448.AArch64.Weak.E m' base=VG.Proof.X448.AArch64.Weak.E m base := by
  funext i
  have hi:=i.isLt
  unfold VG.Proof.X448.AArch64.Weak.E VG.Proof.X448.AArch64.Weak.F
  apply congrArg VG.Proof.X448.toFe
  apply VG.Proof.X448.Wide.valN_congr
  intro j hj
  exact h.limbs (Or.inl (by simp only [slot,GSAVE];omega)) (by simp only [slot];omega) (by omega)

theorem save_bounds {base:Addr} {m m':Mem} (h:Outside base GSAVE 64 m m')
    (hb:BEnv m base) : BEnv m' base := by
  intro i j hj
  have hi:=i.isLt
  rw [h.limbs (Or.inl (by simp only [slot,GSAVE];omega)) (by simp only [slot];omega) (by omega)]
  exact hb i j hj

end VG.Proof.Ed448.AArch64.Sparse
