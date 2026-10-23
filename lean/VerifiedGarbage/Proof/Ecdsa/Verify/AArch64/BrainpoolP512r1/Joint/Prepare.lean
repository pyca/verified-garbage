module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Loop
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Scalars
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Digit

/-! Preparing the two bit tables and the general complete-addition coefficient. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64 (U V)
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint

abbrev prepWork : List (Nat × Nat) := [(bitsU,1024),(cfg.sl EXPP,64)]

theorem generator_point {base : Addr} {s : State} {g : Reg → BitVec 64}
    (hc : BaseCfgOk cfg) (hC : Law C) (hf : Fixed cfg base g s.mem) :
    PointAt base s gSource (G C) := by
  have hp : 0 < cfg.C.p := by have := hc.p_ge; omega
  have hm (x : Nat) : cfg.mont x < C.p := Nat.mod_lt _ hp
  have e1 : num base s (cfg.sl ONEP)=cfg.mont 1 := by
    rw [num,hf.onep]; simp only [Cfg.mont,Cfg.R,Nat.one_mul]
  refine ⟨?_,?_⟩
  · intro x hx
    simp only [coordinates,gSource,Cfg.pt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [num,hf.gx]; exact hm _
    · rw [num,hf.gy]; exact hm _
    · rw [e1]; exact hm _
  · have ex : val base s gSource.x=Fin.ofNat C.p C.gx :=
      (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) hf.gx).trans (toM_cmont hc _)
    have ey : val base s gSource.y=Fin.ofNat C.p C.gy :=
      (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) hf.gy).trans (toM_cmont hc _)
    have ez : val base s gSource.z=1 :=
      (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) e1).trans (toM_cmont hc 1)
    rw [ex,ey,ez]
    exact rep_affine' hC _ _

theorem prepare_ok {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hM : Mid cfg s₀ base g s)
    (hrep : Rep C (val base s qSource.x) (val base s qSource.y) (val base s qSource.z) P) :
    WP isa prepare s fun t =>
      Changes base prepWork s t ∧ Inputs base (G C) P t ∧
      Bits base (sv cfg base s U) (sv cfg base s V) t := by
  have hn8 : cfg.n=8 := rfl
  have boundV : cfg.sl V+64 ≤ 8192 := by decide
  have hs := hM.scr
  have hn := hs.nowrap
  have hm0 : 0 < cfg.C.p := by have := hc.p_ge; omega
  have hm (x : Nat) : cfg.mont x < C.p := Nat.mod_lt _ hm0
  have hbconst : cfg.mont (3*cfg.C.b) < 2^(64*cfg.n) := Nat.lt_trans (hm _) hc.p_lt
  rw [prepare]
  refine WP.seq (WP.mono (bits_ok hs (n:=8) (src:=cfg.sl U) (dst:=bitsU)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide)))
    fun s₁ ⟨b₁,k₁,u₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have v₁ : wordsVal s₁.mem base (cfg.sl V) 8=wordsVal s.mem base (cfg.sl V) 8 :=
    u₁.wordsVal (by decide) (by omega)
  refine WP.seq (WP.mono (bits_ok hs₁ (n:=8) (src:=cfg.sl V) (dst:=bitsV)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide)))
    fun s₂ ⟨b₂,k₂,u₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (setConst_ok hs₂ (n:=cfg.n) (o:=cfg.sl EXPP) (by decide) (by decide) hbconst)
    fun t ⟨b₃,k₃,u₃⟩ => ?_
  have W : Changes base prepWork s t := by
    have kt := (k₁.trans k₂).trans (k₃.mono (by decide))
    refine ⟨kt.gpr _ (by decide),kt.rd,kt.wr,kt.sp,?_⟩
    exact (u₁.unch.trans (u₂.unch.trans u₃.unch)).cover (by
      intro w hw
      simp only [List.mem_append,List.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact ⟨(bitsU,1024),by simp,by decide,by decide⟩
      · exact ⟨(bitsU,1024),by simp,by decide,by decide⟩
      · exact ⟨(cfg.sl EXPP,64),by simp,by decide,by decide⟩)
  have F := hM.fixed.unch hc.n10 hn (by unfold FixedOk prepWork; decide) W.mem
  have hqp : PointAt base s qSource P := by
    refine ⟨?_,hrep⟩
    intro x hx
    simp only [coordinates,qSource,Cfg.pt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hM.px_lt
    · exact hM.py_lt
    · rw [num,hM.fixed.onep]; exact Nat.mod_lt _ hm0
  have I : Inputs base (G C) P t := by
    refine ⟨W.scr hs,modP_of hc F.mp,?_,?_,?_,?_,generator_point hc hC F,
      W.point hs hqp (by decide) (by decide)⟩
    · rw [num,F.ap]; exact hm _
    · rw [num,b₃]; exact hm _
    · exact (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) F.ap).trans (toM_cmont hc _)
    · exact (congrArg (fun x => toM cfg.C.p (2^(64*cfg.n)) x) b₃).trans (toM_cmont hc _)
  refine ⟨W,I,?_,?_⟩
  · intro j hj
    rw [u₃.unch.byte (by intro w hw; rw [List.mem_singleton.mp hw]; change _ ≤ _ ∨ 832+64 ≤ 2944+j; omega)
        (by change 2944+j < 2^64; omega),
      u₂.unch.byte (by intro w hw; rw [List.mem_singleton.mp hw]; change 2944+j+1 ≤ 3456 ∨ _; omega)
        (by change 2944+j < 2^64; omega),b₁ j hj]
    rfl
  · intro j hj
    rw [u₃.unch.byte (by intro w hw; rw [List.mem_singleton.mp hw]; change _ ≤ _ ∨ 832+64 ≤ 3456+j; omega)
        (by change 3456+j < 2^64; omega),b₂ j hj,v₁]
    rfl
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint
