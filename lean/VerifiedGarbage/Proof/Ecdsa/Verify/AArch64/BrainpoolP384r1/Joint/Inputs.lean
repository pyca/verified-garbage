module

import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.State
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages

/-! ### `Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Moves`, which this module and modules that import it used -/

section

/-! Moving projective triples without changing their representatives. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

structure CopyLayout (o a : Pt) : Prop where
  end_le : ∀ x ∈ coordinates o ++ coordinates a,x+48 ≤ 8192
  aligned : ∀ x ∈ coordinates o ++ coordinates a,x % 8 = 0
  apart : ∀ x ∈ coordinates o,∀ y ∈ coordinates o ++ coordinates a,x ≠ y →
    x+48 ≤ y ∨ y+48 ≤ x
  different : ∀ x ∈ coordinates o,x ∉ coordinates a
  nodup : o.x ≠ o.y ∧ o.x ≠ o.z ∧ o.y ≠ o.z

theorem copy_point {base : Addr} {s : State} (hs : Scr s base 8192) {a o : Pt}
    (hL : CopyLayout o a) {P : Point C} (hp : PointAt base s a P) :
    WP isa (.block (copyPt 6 o a)) s fun t =>
      Changes base ((coordinates o).map (·,48)) s t ∧ PointAt base t o P ∧
      t.gpr .x19 = s.gpr .x19 := by
  have hle : ∀ x ∈ [o.x,o.y,o.z,a.x,a.y,a.z],x+8*6 ≤ 8192 := by
    simpa only [coordinates,List.cons_append,List.nil_append] using hL.end_le
  have hal : ∀ x ∈ [o.x,o.y,o.z,a.x,a.y,a.z],x % 8 = 0 := by
    simpa only [coordinates,List.cons_append,List.nil_append] using hL.aligned
  have hap : ∀ x ∈ [o.x,o.y,o.z],∀ y ∈ [o.x,o.y,o.z,a.x,a.y,a.z],x ≠ y →
      x+8*6 ≤ y ∨ y+8*6 ≤ x := by
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
      Changes base ((coordinates resultPt).map (·,48)) s t ∧
      PointAt base t resultPt .infinity ∧ t.gpr .x19 = s.gpr .x19 := by
  have hn := hs.nowrap
  have hn8 : cfg.n = 6 := rfl
  have hex : resultPt.x+48 ≤ 8192 := by decide
  have hey : resultPt.y+48 ≤ 8192 := by decide
  have hm0 : 0 < C.p := by change 0 < cfg.C.p; have := hc.p_ge; omega_using [this]
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
    rw [u₃.wordsVal (by decide) (by have := hs.nowrap; omega_using [hn8, hex]),
      u₂.wordsVal (by decide) (by have := hs.nowrap; omega_using [hn8, hex])]; exact x
  have yt : num base t resultPt.y = cfg.mont 1 := by
    unfold num
    rw [u₃.wordsVal (by decide) (by have := hs.nowrap; omega_using [hn8, hey])]; exact y
  have zt : num base t resultPt.z = 0 := z
  have ut : Unch base ((coordinates resultPt).map (·,48)) s.mem t.mem :=
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

end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

end

end

/-! The constants and affine input points remain unchanged during joint multiplication. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

abbrev gSource : Pt := cfg.pt GX GY ONEP
abbrev qSource : Pt := cfg.pt PX PY ONEP
abbrev arithmeticWork := loopWork ++ [(tableAt,2160)]

theorem Changes.cover {base : Addr} {W W' : List (Nat × Nat)} {s t : State}
    (h : Changes base W s t)
    (hs : ∀ w ∈ W,∃ w' ∈ W',w'.1 ≤ w.1 ∧ w.1+w.2 ≤ w'.1+w'.2) : Changes base W' s t :=
  ⟨h.x0,h.rd,h.wr,h.sp,h.mem.cover hs⟩

structure Inputs (base : Addr) (P Q : Point C) (s : State) : Prop where
  scr : Scr s base 8192
  mod : ModOkA cfg.MP' 8192 C.p s.mem base
  a_lt : num base s (cfg.sl AP) < C.p
  b_lt : num base s (cfg.sl EXPP) < C.p
  a : val base s (cfg.sl AP) = Fin.ofNat C.p C.a
  b : val base s (cfg.sl EXPP) = Fin.ofNat C.p (3*C.b)
  generator : PointAt base s gSource P
  peer : PointAt base s qSource Q

theorem Inputs.unch {base : Addr} {P Q : Point C} {s t : State} (h : Inputs base P Q s)
    (k : Changes base arithmeticWork s t) : Inputs base P Q t := by
  have hn8 : cfg.n = 6 := rfl
  have en (o : Nat) (hl : o+48 ≤ 8192)
      (hap : ∀ w ∈ arithmeticWork,o+48 ≤ w.1 ∨ w.1+w.2 ≤ o) : num base t o = num base s o :=
    k.mem.wordsVal hap (by have := h.scr.nowrap; omega_using [hn8, hl])
  have ea := en (cfg.sl AP) (by decide) (by decide)
  have eb := en (cfg.sl EXPP) (by decide) (by decide)
  refine ⟨k.scr h.scr,h.mod.unch k.mem (by decide) h.scr.nowrap,?_,?_,?_,?_,?_,?_⟩
  · rw [ea]; exact h.a_lt
  · rw [eb]; exact h.b_lt
  · exact (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) ea).trans h.a
  · exact (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) eb).trans h.b
  · exact k.point h.scr h.generator (by decide) (by decide)
  · exact k.point h.scr h.peer (by decide) (by decide)

theorem entryWork_sub : ∀ w ∈ entryWork,w ∈ loopWork := by
  intro w h; exact List.mem_append_right _ h

theorem addWork_sub : ∀ w ∈ addWork,w ∈ loopWork := by
  intro w h; exact List.mem_append_left _ h

theorem loopWork_sub : ∀ w ∈ loopWork,w ∈ arithmeticWork := by
  intro w h; exact List.mem_append_left _ h

theorem double_points {base : Addr} {P Q A : Point C} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hI : Inputs base P Q s)
    (hA : onCurve C A = true) (hp : PointAt base s resultPt A) :
    WP isa double s fun t => Changes base loopWork s t ∧ Inputs base P Q t ∧
      PointAt base t resultPt (add A A) ∧ t.gpr .x19 = s.gpr .x19 := by
  rw [double]
  refine WP.seq (WP.mono (copy_point hI.scr entry_from_result hp) fun s₁ ⟨k₁,p₁,c₁⟩ => ?_)
  have W₁ := k₁.mono entryWork_sub
  have I₁ := hI.unch (W₁.mono loopWork_sub)
  have p₁' := k₁.point hI.scr hp (by decide) (by decide)
  refine WP.mono (sum_points hc hC I₁.scr I₁.mod I₁.a I₁.b I₁.a_lt I₁.b_lt hA hA p₁ p₁')
    fun t ⟨k₂,p₂,c₂⟩ => ?_
  have W₂ := k₂.mono addWork_sub
  have W := W₁.trans W₂
  exact ⟨W,hI.unch (W.mono loopWork_sub),p₂,c₂.trans c₁⟩
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
