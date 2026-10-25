module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Moves
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.State

/-! The constants and affine input points remain unchanged during joint multiplication. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

abbrev gSource : Pt := cfg.pt GX GY ONEP
abbrev qSource : Pt := cfg.pt PX PY ONEP
abbrev arithmeticWork := loopWork ++ [(tableAt,1440)]

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
  have hn8 : cfg.n = 4 := rfl
  have en (o : Nat) (hl : o+32 ≤ 8192)
      (hap : ∀ w ∈ arithmeticWork,o+32 ≤ w.1 ∨ w.1+w.2 ≤ o) : num base t o = num base s o :=
    k.mem.wordsVal hap (by have := h.scr.nowrap; omega)
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
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
