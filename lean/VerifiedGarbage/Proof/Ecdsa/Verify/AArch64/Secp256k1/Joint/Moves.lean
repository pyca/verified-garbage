module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.State
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Framework.Block

/-! Moving projective triples without changing their representatives. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

structure CopyLayout (o a : Pt) : Prop where
  end_le : ∀ x ∈ coordinates o ++ coordinates a,x+32 ≤ 8192
  aligned : ∀ x ∈ coordinates o ++ coordinates a,x % 8 = 0
  apart : ∀ x ∈ coordinates o,∀ y ∈ coordinates o ++ coordinates a,x ≠ y →
    x+32 ≤ y ∨ y+32 ≤ x
  different : ∀ x ∈ coordinates o,x ∉ coordinates a
  nodup : o.x ≠ o.y ∧ o.x ≠ o.z ∧ o.y ≠ o.z

theorem copy_point {base : Addr} {s : State} (hs : Scr s base 8192) {a o : Pt}
    (hL : CopyLayout o a) {P : Point C} (hp : PointAt base s a P) :
    WP isa (.block (copyPt 4 o a)) s fun t =>
      Changes base ((coordinates o).map (·,32)) s t ∧ PointAt base t o P ∧
      t.gpr .x19 = s.gpr .x19 := by
  have hle : ∀ x ∈ [o.x,o.y,o.z,a.x,a.y,a.z],x+8*4 ≤ 8192 := by
    simpa only [coordinates,List.cons_append,List.nil_append] using hL.end_le
  have hal : ∀ x ∈ [o.x,o.y,o.z,a.x,a.y,a.z],x % 8 = 0 := by
    simpa only [coordinates,List.cons_append,List.nil_append] using hL.aligned
  have hap : ∀ x ∈ [o.x,o.y,o.z],∀ y ∈ [o.x,o.y,o.z,a.x,a.y,a.z],x ≠ y →
      x+8*4 ≤ y ∨ y+8*4 ≤ x := by
    simpa only [coordinates,List.cons_append,List.nil_append] using hL.apart
  refine WP.mono (copyPt_ok hs hle hal hap hL.different hL.nodup) fun t ⟨x,y,z,k,u⟩ => ?_
  refine ⟨⟨k.gpr _ (by decide),k.rd,k.wr,k.sp,u⟩,⟨?_,?_⟩,k.gpr _ (by decide)⟩
  · intro p hp'
    simp only [coordinates,List.mem_cons,List.not_mem_nil,or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    · rw [show num base t o.x = num base s a.x from x]; exact hp.1 _ (by simp)
    · rw [show num base t o.y = num base s a.y from y]; exact hp.1 _ (by simp)
    · rw [show num base t o.z = num base s a.z from z]; exact hp.1 _ (by simp)
  · have vx : val base t o.x = val base s a.x := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) x
    have vy : val base t o.y = val base s a.y := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) y
    have vz : val base t o.z = val base s a.z := congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) z
    rw [vx,vy,vz]; exact hp.2

theorem entry_from_result : CopyLayout entry resultPt := ⟨by decide,by decide,by decide,by decide,by decide⟩

/-- The all-zero scalar pair starts from the standard projective infinity. -/
theorem infinity_ok {base : Addr} {s : State} (hs : Scr s base 8192)
    (hc : BaseCfgOk cfg) (hC : Law C) :
    WP isa (.block infinity) s fun t =>
      Changes base ((coordinates resultPt).map (·,32)) s t ∧
      PointAt base t resultPt .infinity ∧ t.gpr .x19 = s.gpr .x19 := by
  have hn := hs.nowrap
  have hn8 : cfg.n = 4 := rfl
  have hex : resultPt.x+32 ≤ 8192 := by decide
  have hey : resultPt.y+32 ≤ 8192 := by decide
  have hm0 : 0 < C.p := by change 0 < cfg.C.p; have := hc.p_ge; omega
  have hm1 : cfg.mont 1 < C.p := Nat.mod_lt _ hm0
  have hm1r : cfg.mont 1 < 2 ^ (64*cfg.n) := Nat.lt_trans hm1 hc.p_lt
  rw [infinity,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (setConst_ok hs (n:=cfg.n) (o:=resultPt.x) (x:=0) (by decide) (by decide) (Nat.pow_pos (by decide)))
    fun s₁ ⟨x,k₁,u₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.mono (setConst_ok hs₁ (n:=cfg.n) (o:=resultPt.y) (by decide) (by decide) hm1r)
    fun s₂ ⟨y,k₂,u₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (setConst_ok hs₂ (n:=cfg.n) (o:=resultPt.z) (x:=0) (by decide) (by decide) (Nat.pow_pos (by decide)))
    fun t ⟨z,k₃,u₃⟩ => ?_
  have kt := (k₁.trans k₂).trans k₃
  have xt : num base t resultPt.x = 0 := by
    unfold num
    rw [u₃.wordsVal (by decide) (by have := hs.nowrap; omega),
      u₂.wordsVal (by decide) (by have := hs.nowrap; omega)]; exact x
  have yt : num base t resultPt.y = cfg.mont 1 := by
    unfold num
    rw [u₃.wordsVal (by decide) (by have := hs.nowrap; omega)]; exact y
  have zt : num base t resultPt.z = 0 := z
  have ut : Unch base ((coordinates resultPt).map (·,32)) s.mem t.mem :=
    (u₁.unch.trans (u₂.unch.trans u₃.unch)).mono (by
      intro w hw
      simp only [List.mem_append,List.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> decide)
  refine ⟨⟨kt.gpr _ (by decide),kt.rd,kt.wr,kt.sp,ut⟩,⟨?_,?_⟩,kt.gpr _ (by decide)⟩
  · intro p hp
    simp only [coordinates,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · rw [xt]; exact hm0
    · rw [yt]; exact hm1
    · rw [zt]; exact hm0
  · have vx : val base t resultPt.x = 0 :=
      (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) xt).trans (toM_zero _ _)
    have vy : val base t resultPt.y = 1 :=
      (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) yt).trans (toM_cmont hc 1)
    have vz : val base t resultPt.z = 0 :=
      (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) zt).trans (toM_zero _ _)
    rw [vx,vy,vz]; exact rep_infinity' hC

end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
