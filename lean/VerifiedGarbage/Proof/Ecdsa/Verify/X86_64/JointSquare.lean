import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFinal
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField

/-! Square the Jacobian denominator before the existing projective comparison. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 Spec.Weierstrass

theorem jointSquare_ok {c : Cfg} (hc : CfgOk c)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (h : ProjectiveInput c s₀ base g s) :
    WP isa (ForwardField.programB c.MP' [.mul (c.sl RZ) (c.sl RZ) (c.sl RZ)]).inline s fun t =>
      ProjectiveInput c s₀ base g t ∧
      tmv c.C c.n base t (c.sl RX)=tmv c.C c.n base s (c.sl RX) ∧
      tmv c.C c.n base t (c.sl RZ)=tmv c.C c.n base s (c.sl RZ)*tmv c.C c.n base s (c.sl RZ) := by
  have lay : Lay c.MP' size (·∈[c.sl RX,c.sl RZ]) := lay_map hc rfl rfl rfl (l:=[RX,RZ]) (by decide)
  have hi : Inv c.MP' base size c.C.p (·∈[c.sl RX,c.sl RZ]) [c.sl RX,c.sl RZ] (tmv c.C c.n base s) s := by
    refine ⟨h.scr,modP_of hc h.fixed.mp,fun _ hx => hx,?_,fun _ _ => rfl⟩
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact h.rx_lt
    · exact h.rz_lt
  refine WP.mono (ForwardField.programB_ok lay
    (unitMod_pow_two hc.p_odd _) [.mul (c.sl RZ) (c.sl RZ) (c.sl RZ)] hi
    (by intro op hop x hx; simp only [List.mem_singleton] at hop; subst op; simpa only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false,or_self] using Or.inr hx)
    (by simp [readsOk,FOp.ins])) fun t ⟨kt,it⟩ => ?_
  have un := kt.unch
  change Unch base (slW c [RZ,TMP]) s.mem t.mem at un
  have rx : sv c base t RX=sv c base s RX :=
    sv_unch un hc.n10 h.scr.nowrap (by decide) (apart_slW (by decide))
  have flag : word t.mem base (c.sl FLAG)=word s.mem base (c.sl FLAG) := by
    apply un.word
    · intro w hw
      have hh := apart_slW (c:=c) (i:=FLAG) (l:=[RZ,TMP]) (by decide) w hw
      have := hc.n0
      omega
    · have := sl_le c hc.n10 (i:=FLAG) (by decide)
      have := h.scr.nowrap
      have := hc.n0
      omega
  have rzv := it.val (c.sl RZ) (by simp [validAfter,FOp.out])
  have rzlt := it.lt (c.sl RZ) (by simp [validAfter,FOp.out])
  refine ⟨⟨it.scr,h.fixed.unch hc.n10 h.scr.nowrap (fixedOk_slW (by decide)) un,
    (sv_unch un hc.n10 h.scr.nowrap (by decide) (apart_slW (by decide))).trans h.k,
    flag.trans h.flag,rx ▸ h.rx_lt,rzlt⟩,?_,?_⟩
  · exact congrArg (fun x => toM c.C.p (2^(64*c.n)) x) rx
  · simpa only [MP'_n,tmv,runOps,List.foldl_cons,List.foldl_nil,FOp.run,Function.update_self] using rzv

end VG.Proof.Ecdsa.Verify.X86_64
