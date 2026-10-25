module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.CompactLoop

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Prepare
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.ProjectiveFlags
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.LoopOps
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Math
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Table
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.TableLayout
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Loop
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Moves
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Math

/-! The joint multiplier feeds the unchanged complete ECDSA final check. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64 (U V RM')
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

theorem arithmeticWork_sub : ∀ w ∈ arithmeticWork,w ∈ work := by decide
theorem prepWork_sub : ∀ w ∈ prepWork,w ∈ work := by decide

theorem setup_ok {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hM : Mid cfg s₀ base g s)
    (hrep : Rep C (val base s qSource.x) (val base s qSource.y) (val base s qSource.z) P) :
    WP isa setup s fun t => Changes base work s t ∧
      Running base (G C) P (sv cfg base s U) (sv cfg base s V) 128 t := by
  rw [setup]
  refine WP.seq (WP.mono (prepare_ok hc hC hM hrep) fun s₁ ⟨k₁,I₁,B₁⟩ => ?_)
  refine WP.seq (WP.mono (buildTable_ok hc hC hc.onG hP I₁) fun s₂ ⟨k₂,I₂,T₂⟩ => ?_)
  have B₂ := k₂.bits B₁
  rw [WP.block_append_iff]
  refine WP.mono (infinity_ok I₂.scr hc hC) fun s₃ ⟨k₃,R₃,_⟩ => ?_
  have W₃ := k₃.mono resultWork_sub
  have I₃ := I₂.unch (W₃.mono loopWork_sub)
  have B₃ := (W₃.mono loopWork_sub).bits B₂
  have T₃ := T₂.of_changes I₂.scr W₃
  refine WP.mono (setCounter_ok s₃ (j:=128) (by decide)) fun s₄ ⟨c₄,k₄⟩ => ?_
  have W₄ : Changes base loopWork s₃ s₄ := Changes.of_keeps k₄ (by decide)
  have I₄ := I₃.unch (W₄.mono loopWork_sub)
  have B₄ := (W₄.mono loopWork_sub).bits B₃
  have T₄ := T₃.of_changes I₃.scr W₄
  have R₄ := R₃.of_mem k₄.mem
  have hu := Nat.lt_trans hM.u_lt hc.n_lt
  have hv := Nat.lt_trans hM.v_lt hc.n_lt
  have hstart := at_top (G C) P (n:=cfg.n) hu hv
  rw [show 32*cfg.n=128 from rfl] at hstart
  rw [←hstart] at R₄
  exact ⟨(((k₁.mono prepWork_sub).trans (k₂.mono arithmeticWork_sub)).trans
    ((W₃.mono loopWork_sub).mono arithmeticWork_sub)).trans
    ((W₄.mono loopWork_sub).mono arithmeticWork_sub),⟨I₄,B₄,T₄,c₄,R₄⟩⟩

theorem points_raw {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hM : Mid cfg s₀ base g s)
    (hrep : Rep C (val base s qSource.x) (val base s qSource.y) (val base s qSource.z) P) :
    WP isa points s fun t =>
      Changes base work s t ∧ PointAt base t resultPt
        (add (mul (sv cfg base s U) (G C)) (mul (sv cfg base s V) P)) := by
  rw [points]
  refine WP.seq (WP.mono (setup_ok hc hC hP hM hrep) fun s₄ ⟨k₄,R₄⟩ => ?_)
  refine WP.mono (loop_ok hc hC hc.onG hP R₄) fun t ⟨k₅,h₅⟩ => ?_
  have W := k₄.trans ((k₅.mono loopWork_sub).mono arithmeticWork_sub)
  have p := h₅.point
  rw [at_zero] at p
  exact ⟨W,p⟩

theorem final_state {base : Addr} {s₀ s t : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hM : Mid cfg s₀ base g s) (h : Changes base work s t)
    (hp : PointAt base t resultPt P) : FinalState cfg s₀ base g t := by
  have hn := hM.scr.nowrap
  have flagBound : cfg.sl FLAG+8 ≤ 8192 := by decide
  have hn8 : cfg.n=4 := rfl
  have same (i : Nat) (hle : cfg.sl i+32 ≤ 8192)
      (hap : ∀ w ∈ work,cfg.sl i+32 ≤ w.1 ∨ w.1+w.2 ≤ cfg.sl i) :
      sv cfg base t i=sv cfg base s i :=
    h.mem.wordsVal hap (by omega)
  have r := same RM' (by decide) (by decide)
  have k := same K (by decide) (by decide)
  refine ⟨h.scr hM.scr,h.wr.trans hM.wr,h.rd.trans hM.rd,
    hM.fixed.unch hc.n10 hn (by unfold FixedOk work loopWork addWork entryWork; decide) h.mem,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [h.mem.word (by decide) (by omega)]
    exact hM.flag
  · rw [r]; exact hM.rm_lt
  · rw [r]; exact hM.rm
  · exact hp.1 _ (by decide)
  · exact (hM.unch.trans h.mem).cover (by
      intro w hw
      refine ⟨(0,8192),by simp,by omega,?_⟩
      rcases List.mem_append.mp hw with hw | hw
      · rw [List.mem_singleton.mp hw]
      · have hd : ∀ w ∈ work,w.1+w.2 ≤ 8192 := by decide
        exact hd w hw)
  · exact k.trans hM.k
  · exact hp.1 _ (by decide)

theorem points_ok {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hM : Mid cfg s₀ base g s)
    (hrep : Rep C (val base s qSource.x) (val base s qSource.y) (val base s qSource.z) P) :
    WP isa points s fun t => FinalState cfg s₀ base g t ∧
      Rep C (val base t resultPt.x) (val base t resultPt.y) (val base t resultPt.z)
        (add (mul (sv cfg base s U) (G C)) (mul (sv cfg base s V) P)) :=
  WP.mono (points_raw hc hC hP hM hrep) fun _ ⟨W,p⟩ => ⟨final_state hc hM W p,p.2⟩
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
